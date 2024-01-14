local type lexer = require("teal.lexer")
local type Token = lexer.Token
local type TokenKind = lexer.TokenKind

local type errors = require("teal.errors")
local type Error = errors.Error

local type types = require("teal.types")
local type ArrayType = types.ArrayType
local type EnumType = types.EnumType
local type FunctionType = types.FunctionType
local type HasTypeArgs = types.HasTypeArgs
local type RecordType = types.RecordType
local type TupleType = types.TupleType
local type Type = types.Type
local type TypeAliasType = types.TypeAliasType
local type TypeDeclType = types.TypeDeclType
local type TypeName = types.TypeName
local type UnionType = types.UnionType

local record parser
end

local record ParseState
   tokens: {Token}
   errs: {Error}
   filename: string
   end_alignment_hint: Error

   required_modules: {string}
end

local enum ParseTypeListMode
   "rets"
   "decltuple"
   "casttype"
end

local record Operator
   y: integer
   x: integer
   arity: integer
   op: string
   prec: integer
end

local attributes <total>: {Attribute: boolean} = {
   ["const"] = true,
   ["close"] = true,
   ["total"] = true,
}
local is_attribute <const>: {string:boolean} = attributes as {string:boolean}

local function is_number_type(t:Type): boolean
   return t.typename == "number" or t.typename == "integer"
end

local parse_type_list: function(ParseState, integer, ParseTypeListMode): integer, TupleType
local parse_expression: function(ParseState, integer): integer, Node, integer
local parse_expression_and_tk: function(ps: ParseState, i: integer, tk: string): integer, Node
local parse_statements: function(ParseState, integer, ? boolean): integer, Node
local parse_argument_list: function(ParseState, integer): integer, Node, integer
local parse_argument_type_list: function(ParseState, integer): integer, TupleType, boolean, integer
local parse_type: function(ParseState, integer): integer, Type, integer
local parse_newtype: function(ps: ParseState, i: integer): integer, Node
local parse_interface_name: function(ps: ParseState, i: integer): integer, Type, integer

local type ParseBody = function(ps: ParseState, i: integer, def: Type, node: Node): integer, Node
local parse_enum_body: function(ps: ParseState, i: integer, def: EnumType, node: Node): integer, Node
local parse_record_body: function(ps: ParseState, i: integer, def: Type, node: Node): integer, Node
local parse_type_body_fns: {TypeName:ParseBody}

local function fail(ps: ParseState, i: integer, msg: string): integer
   if not ps.tokens[i] then
      local eof = ps.tokens[#ps.tokens]
      table.insert(ps.errs, { filename = ps.filename, y = eof.y, x = eof.x, msg = msg or "unexpected end of file" })
      return #ps.tokens
   end
   table.insert(ps.errs, { filename = ps.filename, y = ps.tokens[i].y, x = ps.tokens[i].x, msg = assert(msg, "syntax error, but no error message provided") })
   return math.min(#ps.tokens, i + 1)
end

local function end_at(node: Node, tk: Token)
   node.yend = tk.y
   node.xend = tk.x + #tk.tk - 1
end

local function verify_tk(ps: ParseState, i: integer, tk: string): integer
   if ps.tokens[i].tk == tk then
      return i + 1
   end
   return fail(ps, i, "syntax error, expected '" .. tk .. "'")
end

local function verify_end(ps: ParseState, i: integer, istart: integer, node: Node): integer
   if ps.tokens[i].tk == "end" then
      local endy, endx = ps.tokens[i].y, ps.tokens[i].x
      node.yend = endy
      node.xend = endx + 2
      if node.kind ~= "function" and endy ~= node.y and endx ~= node.x then
         if not ps.end_alignment_hint then
            ps.end_alignment_hint = { filename = ps.filename, y = node.y, x = node.x, msg = "syntax error hint: construct starting here is not aligned with its 'end' at " .. ps.filename .. ":" .. endy .. ":" .. endx .. ":" }
         end
      end
      return i + 1
   end
   end_at(node, ps.tokens[i])
   if ps.end_alignment_hint then
      table.insert(ps.errs, ps.end_alignment_hint)
      ps.end_alignment_hint = nil
   end
   return fail(ps, i, "syntax error, expected 'end' to close construct started at " .. ps.filename .. ":" .. ps.tokens[istart].y .. ":" .. ps.tokens[istart].x .. ":")
end

local function new_node(tokens: {Token}, i: integer, kind?: NodeKind): Node
   local t = tokens[i]
   return { y = t.y, x = t.x, tk = t.tk, kind = kind or (t.kind as NodeKind) }
end

local function a_type<T is Type>(typename: TypeName, t: T): T
   t.typeid = new_typeid()
   t.typename = typename
   return t
end

local function edit_type(t: Type, typename: TypeName): Type
   t.typeid = new_typeid()
   t.typename = typename
   return t
end

local function new_type(ps: ParseState, i: integer, typename: TypeName): Type
   local token = ps.tokens[i]
   return a_type(typename, {
      filename = ps.filename,
      y = token.y,
      x = token.x,
      --tk = token.tk
   })
end

local function new_typedecl(ps: ParseState, i: integer, def: Type): Type
   local t = new_type(ps, i, "typedecl") as TypeDeclType
   t.def = def
   return t
end

local macroexp a_typedecl(def: Type): TypeDeclType
   return a_type("typedecl", { def = def } as TypeDeclType)
end

local macroexp a_tuple(t: {Type}): TupleType
   return a_type("tuple", { tuple = t } as TupleType)
end

local macroexp a_union(t: {Type}): UnionType
   return a_type("union", { types = t } as UnionType)
end

--local macroexp a_poly(t: {FunctionType}): PolyType
--   return a_type("poly", { types = t } as PolyType)
--end
--
local function a_function(t: FunctionType): FunctionType
   assert(t.min_arity)
   return a_type("function", t)
end

local record Opt
   where self.opttype

   opttype: Type
end

--local function OPT(t: Type): Opt
--   return { opttype = t }
--end
--
local record Args
   is {Type|Opt}

   is_va: boolean
end

local function va_args(args: Args): Args
   args.is_va = true
   return args
end

local record FuncArgs
   is HasTypeArgs

   args: Args
   rets: Args
   needs_compat: boolean
end

local function a_fn(f: FuncArgs): FunctionType
   local args_t = a_tuple {}
   local tup = args_t.tuple
   args_t.is_va = f.args.is_va
   local min_arity = f.args.is_va and -1 or 0
   for _, a in ipairs(f.args) do
      if a is Opt then
         table.insert(tup, a.opttype)
      else
         table.insert(tup, a)
         min_arity = min_arity + 1
      end
   end

   local rets_t = a_tuple {}
   tup = rets_t.tuple
   rets_t.is_va = f.rets.is_va
   for _, a in ipairs(f.rets) do
      assert(a is Type)
      table.insert(tup, a)
   end

   return a_type("function", {
      args = args_t,
      rets = rets_t,
      min_arity = min_arity,
      needs_compat = f.needs_compat,
      typeargs = f.typeargs,
   } as FunctionType)
end

local function a_vararg(t: {Type}): TupleType
   local typ = a_tuple(t)
   typ.is_va = true
   return typ
end

local macroexp an_array(t: Type): ArrayType
   return a_type("array", { elements = t } as ArrayType)
end

local macroexp a_map(k: Type, v: Type): MapType
   return a_type("map", { keys = k, values = v } as MapType)
end

local NIL = a_type("nil", {})
local ANY = a_type("any", {})
local TABLE = a_map(ANY, ANY)
local NUMBER = a_type("number", {})
local STRING = a_type("string", {})
local THREAD = a_type("thread", {})
local BOOLEAN = a_type("boolean", {})
local INTEGER = a_type("integer", {})

local function shallow_copy_new_type<T is Type>(t: T): T
   local copy: {any:any} = {}
   for k, v in pairs(t as {any:any}) do
      copy[k] = v
   end
   copy.typeid = new_typeid()
   return copy as T
end

local function shallow_copy_table<T>(t: T): T
   local copy: {any:any} = {}
   for k, v in pairs(t as {any:any}) do
      copy[k] = v
   end
   return copy as T
end

local function verify_kind(ps: ParseState, i: integer, kind: TokenKind, node_kind?: NodeKind): integer, Node
   if ps.tokens[i].kind == kind then
      return i + 1, new_node(ps.tokens, i, node_kind)
   end
   return fail(ps, i, "syntax error, expected " .. kind)
end

local type SkipFunction = function(ParseState, integer): integer, Node

local function skip(ps: ParseState, i: integer, skip_fn: SkipFunction): integer, Node
   local err_ps: ParseState = {
      filename = ps.filename,
      tokens = ps.tokens,
      errs = {},
      required_modules = {},
   }
   return skip_fn(err_ps, i)
end

local function failskip(ps: ParseState, i: integer, msg: string, skip_fn: SkipFunction, starti?: integer): integer
   local skip_i = skip(ps, starti or i, skip_fn)
   fail(ps, i, msg)
   return skip_i
end

local function skip_type_body(ps: ParseState, i: integer): integer, Node
   local tn = ps.tokens[i].tk as TypeName
   i = i + 1
   assert(parse_type_body_fns[tn], tn .. " has no parse body function")
   return parse_type_body_fns[tn](ps, i, {}, { kind = "function" --[[ skip end_alignment_hint ]] })
end

local function parse_table_value(ps: ParseState, i: integer): integer, Node, integer
   local next_word = ps.tokens[i].tk
   if next_word == "record" or next_word == "interface" then
      local skip_i, e = skip(ps, i, skip_type_body)
      if e then
         fail(ps, i, next_word == "record"
                     and "syntax error: this syntax is no longer valid; declare nested record inside a record"
                     or  "syntax error: cannot declare interface inside a table; use a statement")
         return skip_i, new_node(ps.tokens, i, "error_node")
      end
   elseif next_word == "enum" and ps.tokens[i + 1].kind == "string" then
      i = failskip(ps, i, "syntax error: this syntax is no longer valid; declare nested enum inside a record", skip_type_body)
      return i, new_node(ps.tokens, i - 1, "error_node")
   end

   local e: Node
   i, e = parse_expression(ps, i)
   if not e then
      e = new_node(ps.tokens, i - 1, "error_node")
   end
   return i, e
end

local function parse_table_item(ps: ParseState, i: integer, n?: integer): integer, Node, integer
   local node = new_node(ps.tokens, i, "literal_table_item")
   if ps.tokens[i].kind == "$EOF$" then
      return fail(ps, i, "unexpected eof")
   end

   if ps.tokens[i].tk == "[" then
      node.key_parsed = "long"
      i = i + 1
      i, node.key = parse_expression_and_tk(ps, i, "]")
      i = verify_tk(ps, i, "=")
      i, node.value = parse_table_value(ps, i)
      return i, node, n
   elseif ps.tokens[i].kind == "identifier" then
      if ps.tokens[i+1].tk == "=" then
         node.key_parsed = "short"
         i, node.key = verify_kind(ps, i, "identifier", "string")
         node.key.conststr = node.key.tk
         node.key.tk = '"' .. node.key.tk .. '"'
         i = verify_tk(ps, i, "=")
         i, node.value = parse_table_value(ps, i)
         return i, node, n
      elseif ps.tokens[i+1].tk == ":" then
         node.key_parsed = "short"
         local orig_i = i
         local try_ps: ParseState = {
            filename = ps.filename,
            tokens = ps.tokens,
            errs = {},
            required_modules = ps.required_modules,
         }
         i, node.key = verify_kind(try_ps, i, "identifier", "string")
         node.key.conststr = node.key.tk
         node.key.tk = '"' .. node.key.tk .. '"'
         i = verify_tk(try_ps, i, ":")
         i, node.itemtype = parse_type(try_ps, i)
         if node.itemtype and ps.tokens[i].tk == "=" then
            i = verify_tk(try_ps, i, "=")
            i, node.value = parse_table_value(try_ps, i)
            if node.value then
               for _, e in ipairs(try_ps.errs) do
                  table.insert(ps.errs, e)
               end
               return i, node, n
            end
         end
         -- backtrack:
         node.itemtype = nil
         i = orig_i
      end
   end

   node.key = new_node(ps.tokens, i, "integer")
   node.key_parsed = "implicit"
   node.key.constnum = n
   node.key.tk = tostring(n)
   i, node.value = parse_expression(ps, i)
   if not node.value then
      return fail(ps, i, "expected an expression")
   end
   return i, node, n + 1
end

local type ParseItem = function<T>(ParseState, integer, ? integer): integer, T, integer

local enum SeparatorMode
   "sep"
   "term"
end

local function parse_list<T>(ps: ParseState, i: integer, list: {T}, close: {string:boolean}, sep: SeparatorMode, parse_item: ParseItem<T>): integer, {T}
   local n = 1
   while ps.tokens[i].kind ~= "$EOF$" do
      if close[ps.tokens[i].tk] then
         end_at(list as Node, ps.tokens[i])
         break
      end
      local item: T
      local oldn = n
      i, item, n = parse_item(ps, i, n)
      n = n or oldn
      table.insert(list, item)
      if ps.tokens[i].tk == "," then
         i = i + 1
         if sep == "sep" and close[ps.tokens[i].tk] then
            fail(ps, i, "unexpected '" .. ps.tokens[i].tk .. "'")
            return i, list
         end
      elseif sep == "term" and ps.tokens[i].tk == ";" then
         i = i + 1
      elseif not close[ps.tokens[i].tk] then
         local options = {}
         for k, _ in pairs(close) do
            table.insert(options, "'" .. k .. "'")
         end
         table.sort(options)
         local first = options[1]:sub(2, -2)
         local msg: string
         -- heuristic for parenthesized lists
         if first == ")" and ps.tokens[i].tk == "=" then
            msg = "syntax error, cannot perform an assignment here (did you mean '=='?)"
            i = failskip(ps, i, msg, parse_expression, i + 1)
         else
            table.insert(options, "','")
            msg = "syntax error, expected one of: " .. table.concat(options, ", ")
            fail(ps, i, msg)
         end
         -- heuristic for error recovery to avoid a cascade of errors:
         -- * if we're parsing a bracketed list, assume the missing token is a separator;
         -- * otherwise, if we have a line break, insert expected terminator token.
         if first ~= "}" and ps.tokens[i].y ~= ps.tokens[i-1].y then
            -- FIXME closing token may not be a keyword (but non-keywords are checked with verify_tk, so it should work)
            table.insert(ps.tokens, i, { tk = first, y = ps.tokens[i-1].y, x = ps.tokens[i-1].x + 1, kind = "keyword" })
            return i, list
         end
      end
   end
   return i, list
end

local function parse_bracket_list<T>(ps: ParseState, i: integer, list: {T}, open: string, close: string, sep: SeparatorMode, parse_item: ParseItem<T>): integer, {T}
   i = verify_tk(ps, i, open)
   i = parse_list(ps, i, list, { [close] = true }, sep, parse_item)
   i = verify_tk(ps, i, close)
   return i, list
end

local function parse_table_literal(ps: ParseState, i: integer): integer, Node
   local node = new_node(ps.tokens, i, "literal_table")
   return parse_bracket_list(ps, i, node, "{", "}", "term", parse_table_item)
end

local function parse_trying_list<T>(ps: ParseState, i: integer, list: {T}, parse_item: ParseItem<T>): integer, {T}
   local try_ps: ParseState = {
      filename = ps.filename,
      tokens = ps.tokens,
      errs = {},
      required_modules = ps.required_modules,
   }
   local tryi, item: integer, T = parse_item(try_ps, i)
   if not item then
      return i, list
   end
   for _, e in ipairs(try_ps.errs) do
      table.insert(ps.errs, e)
   end
   i = tryi
   table.insert(list, item)
   if ps.tokens[i].tk == "," then
      while ps.tokens[i].tk == "," do
         i = i + 1
         i, item = parse_item(ps, i)
         table.insert(list, item)
      end
   end
   return i, list
end

local function parse_anglebracket_list<T is Type>(ps: ParseState, i: integer, parse_item: ParseItem<T>): integer, {T}
   if ps.tokens[i+1].tk == ">" then
      return fail(ps, i+1, "type argument list cannot be empty")
   end
   local types: {T} = {}
   i = verify_tk(ps, i, "<")
   i = parse_list(ps, i, types, { [">"] = true, [">>"] = true, }, "sep", parse_item)
   if ps.tokens[i].tk == ">" then
      i = i + 1
   elseif ps.tokens[i].tk == ">>" then
      -- tokenizer hack: consume one bracket from '>>', don't increment i
      ps.tokens[i].tk = ">"
   else
      return fail(ps, i, "syntax error, expected '>'")
   end
   return i, types
end

local function parse_typearg(ps: ParseState, i: integer): integer, TypeArgType, integer
   local name = ps.tokens[i].tk
   local constraint: Type
   i = verify_kind(ps, i, "identifier")
   if ps.tokens[i].tk == "is" then
      i = i + 1
      i, constraint = parse_interface_name(ps, i) -- FIXME what about generic interfaces
   end
   return i, a_type("typearg", {
      y = ps.tokens[i - 2].y,
      x = ps.tokens[i - 2].x,
      typearg = name,
      constraint = constraint,
   } as TypeArgType)
end

local function parse_return_types(ps: ParseState, i: integer): integer, TupleType
   return parse_type_list(ps, i, "rets")
end

local function parse_function_type(ps: ParseState, i: integer): integer, FunctionType
   local typ = new_type(ps, i, "function") as FunctionType
   i = i + 1
   if ps.tokens[i].tk == "<" then
      i, typ.typeargs = parse_anglebracket_list(ps, i, parse_typearg)
   end
   if ps.tokens[i].tk == "(" then
      i, typ.args, typ.is_method, typ.min_arity = parse_argument_type_list(ps, i)
      i, typ.rets = parse_return_types(ps, i)
   else
      typ.args = a_vararg { ANY }
      typ.rets = a_vararg { ANY }
   end
   return i, typ
end

local simple_types: {string:Type} = {
   ["nil"] = NIL,
   ["any"] = ANY,
   ["table"] = TABLE,
   ["number"] = NUMBER,
   ["string"] = STRING,
   ["thread"] = THREAD,
   ["boolean"] = BOOLEAN,
   ["integer"] = INTEGER,
}

local function parse_simple_type_or_nominal(ps: ParseState, i: integer): integer, Type
   local tk = ps.tokens[i].tk
   local st = simple_types[tk]
   if st then
      return i + 1, st
   end
   local typ = new_type(ps, i, "nominal") as NominalType
   typ.names = { tk }
   i = i + 1
   while ps.tokens[i].tk == "." do
      i = i + 1
      if ps.tokens[i].kind == "identifier" then
         table.insert(typ.names, ps.tokens[i].tk)
         i = i + 1
      else
         return fail(ps, i, "syntax error, expected identifier")
      end
   end

   if ps.tokens[i].tk == "<" then
      i, typ.typevals = parse_anglebracket_list(ps, i, parse_type)
   end
   return i, typ
end

local function parse_base_type(ps: ParseState, i: integer): integer, Type, integer
   local tk = ps.tokens[i].tk
   if ps.tokens[i].kind == "identifier" then
      return parse_simple_type_or_nominal(ps, i)
   elseif tk == "{" then
      local istart = i
      i = i + 1
      local t: Type
      i, t = parse_type(ps, i)
      if not t then
         return i
      end
      if ps.tokens[i].tk == "}" then
         local decl = new_type(ps, istart, "array") as ArrayType
         decl.elements = t
         end_at(decl as Node, ps.tokens[i])
         i = verify_tk(ps, i, "}")
         return i, decl
      elseif ps.tokens[i].tk == "," then
         local decl = new_type(ps, istart, "tupletable") as TupleTableType
         decl.types = { t }
         local n = 2
         repeat
            i = i + 1
            i, decl.types[n] = parse_type(ps, i)
            if not decl.types[n] then
               break
            end
            n = n + 1
         until ps.tokens[i].tk ~= ","
         end_at(decl as Node, ps.tokens[i])
         i = verify_tk(ps, i, "}")
         return i, decl
      elseif ps.tokens[i].tk == ":" then
         local decl = new_type(ps, istart, "map") as MapType
         i = i + 1
         decl.keys = t
         i, decl.values = parse_type(ps, i)
         if not decl.values then
            return i
         end
         end_at(decl as Node, ps.tokens[i])
         i = verify_tk(ps, i, "}")
         return i, decl
      end
      return fail(ps, i, "syntax error; did you forget a '}'?")
   elseif tk == "function" then
      return parse_function_type(ps, i)
   elseif tk == "nil" then
      return i + 1, simple_types["nil"]
   elseif tk == "table" then
      local typ = new_type(ps, i, "map") as MapType
      typ.keys = ANY
      typ.values = ANY
      return i + 1, typ
   end
   return fail(ps, i, "expected a type")
end

parse_type = function(ps: ParseState, i: integer): integer, Type, integer
   if ps.tokens[i].tk == "(" then
      i = i + 1
      local t: Type
      i, t = parse_type(ps, i)
      i = verify_tk(ps, i, ")")
      return i, t
   end

   local bt: Type
   local istart = i
   i, bt = parse_base_type(ps, i)
   if not bt then
      return i
   end
   if ps.tokens[i].tk == "|" then
      local u = new_type(ps, istart, "union") as UnionType
      u.types = { bt }
      while ps.tokens[i].tk == "|" do
         i = i + 1
         i, bt = parse_base_type(ps, i)
         if not bt then
            return i
         end
         table.insert(u.types, bt)
      end
      bt = u
   end
   return i, bt
end

local function new_tuple(ps: ParseState, i: integer): TupleType, {Type}
   local t = new_type(ps, i, "tuple") as TupleType
   t.tuple = {}
   return t, t.tuple
end

parse_type_list = function(ps: ParseState, i: integer, mode: ParseTypeListMode): integer, TupleType
   local t, list = new_tuple(ps, i)

   local first_token = ps.tokens[i].tk
   if mode == "rets" or mode == "decltuple" then
      if first_token == ":" then
         i = i + 1
      else
         return i, t
      end
   end

   local optional_paren = false
   if ps.tokens[i].tk == "(" then
      optional_paren = true
      i = i + 1
   end

   local prev_i = i
   i = parse_trying_list(ps, i, list, parse_type)
   if i == prev_i and ps.tokens[i].tk ~= ")" then
      fail(ps, i - 1, "expected a type list")
   end

   if mode == "rets" and ps.tokens[i].tk == "..." then
      i = i + 1
      local nrets = #list
      if nrets > 0 then
         t.is_va = true
      else
         fail(ps, i, "unexpected '...'")
      end
   end

   if optional_paren then
      i = verify_tk(ps, i, ")")
   end

   return i, t
end

local function parse_function_args_rets_body(ps: ParseState, i: integer, node: Node): integer, Node
   local istart = i - 1
   if ps.tokens[i].tk == "<" then
      i, node.typeargs = parse_anglebracket_list(ps, i, parse_typearg)
   end
   i, node.args, node.min_arity = parse_argument_list(ps, i)
   i, node.rets = parse_return_types(ps, i)
   i, node.body = parse_statements(ps, i)
   end_at(node, ps.tokens[i])
   i = verify_end(ps, i, istart, node)
   return i, node
end

local function parse_function_value(ps: ParseState, i: integer): integer, Node
   local node = new_node(ps.tokens, i, "function")
   i = verify_tk(ps, i, "function")
   return parse_function_args_rets_body(ps, i, node)
end

local function unquote(str: string): string, boolean
   local f = str:sub(1, 1)
   if f == '"' or f == "'" then
      return str:sub(2, -2), false
   end
   f = str:match("^%[=*%[")
   local l = #f + 1
   return str:sub(l, -l), true
end

local function parse_literal(ps: ParseState, i: integer): integer, Node
   local tk = ps.tokens[i].tk
   local kind = ps.tokens[i].kind
   if kind == "identifier" then
      return verify_kind(ps, i, "identifier", "variable")
   elseif kind == "string" then
      local node = new_node(ps.tokens, i, "string")
      node.conststr, node.is_longstring = unquote(tk)
      return i + 1, node
   elseif kind == "number" or kind == "integer" then
      local n = tonumber(tk)
      local node: Node
      i, node = verify_kind(ps, i, kind)
      node.constnum = n
      return i, node
   elseif tk == "true" then
      return verify_kind(ps, i, "keyword", "boolean")
   elseif tk == "false" then
      return verify_kind(ps, i, "keyword", "boolean")
   elseif tk == "nil" then
      return verify_kind(ps, i, "keyword", "nil")
   elseif tk == "function" then
      return parse_function_value(ps, i)
   elseif tk == "{" then
      return parse_table_literal(ps, i)
   elseif kind == "..." then
      return verify_kind(ps, i, "...")
   elseif kind == "$ERR invalid_string$" then
      return fail(ps, i, "malformed string")
   elseif kind == "$ERR invalid_number$" then
      return fail(ps, i, "malformed number")
   end
   return fail(ps, i, "syntax error")
end

local function node_is_require_call(n: Node): string
   if n.e1 and n.e2 -- literal require call
      and n.e1.kind == "variable" and n.e1.tk == "require"
      and n.e2.kind == "expression_list" and #n.e2 == 1
      and n.e2[1].kind == "string"
   then
      return n.e2[1].conststr
   elseif n.op and n.op.op == "@funcall" -- pcall(require, "str")
      and n.e1 and n.e1.tk == "pcall"
      and n.e2 and #n.e2 == 2
      and n.e2[1].kind == "variable" and n.e2[1].tk == "require"
      and n.e2[2].kind == "string" and n.e2[2].conststr
   then
      return n.e2[2].conststr
   else
      return nil -- table.insert cares about arity
   end
end

local an_operator: function(Node, integer, string): Operator

do
   local precedences: {integer:{string:integer}} = {
      [1] = {
         ["not"] = 11,
         ["#"] = 11,
         ["-"] = 11,
         ["~"] = 11,
      },
      [2] = {
         ["or"] = 1,
         ["and"] = 2,
         ["is"] = 3,
         ["<"] = 3,
         [">"] = 3,
         ["<="] = 3,
         [">="] = 3,
         ["~="] = 3,
         ["=="] = 3,
         ["|"] = 4,
         ["~"] = 5,
         ["&"] = 6,
         ["<<"] = 7,
         [">>"] = 7,
         [".."] = 8,
         ["+"] = 9,
         ["-"] = 9,
         ["*"] = 10,
         ["/"] = 10,
         ["//"] = 10,
         ["%"] = 10,
         ["^"] = 12,
         ["as"] = 50,
         ["@funcall"] = 100,
         ["@index"] = 100,
         ["."] = 100,
         [":"] = 100,
      },
   }

   local is_right_assoc: {string:boolean} = {
      ["^"] = true,
      [".."] = true,
   }

   local function new_operator(tk: Token, arity: integer, op: string): Operator
      return { y = tk.y, x = tk.x, arity = arity, op = op, prec = precedences[arity][op] }
   end

   an_operator = function(node: Node, arity: integer, op: string): Operator
      return { y = node.y, x = node.x, arity = arity, op = op, prec = precedences[arity][op] }
   end

   local args_starters: {TokenKind:boolean} = {
      ["("] = true,
      ["{"] = true,
      ["string"] = true,
   }

   local E: function(ParseState, integer, Node, integer): integer, Node

   local function after_valid_prefixexp(ps: ParseState, prevnode: Node, i: integer): boolean
      return ps.tokens[i - 1].kind == ")" -- '(' exp ')'
         or (prevnode.kind == "op"
             and (prevnode.op.op == "@funcall"
                  or prevnode.op.op == "@index"
                  or prevnode.op.op == "."
                  or prevnode.op.op == ":")
             )
         or prevnode.kind == "identifier"
         or prevnode.kind == "variable"
   end

   -- small hack: for the sake of `tl types`, parse an invalid binary exp
   -- as a paren to produce a unary indirection on e1 and save its location.
   local function failstore(tkop: Token, e1: Node): Node
      return { y = tkop.y, x = tkop.x, kind = "paren", e1 = e1, failstore = true }
   end

   local function P(ps: ParseState, i: integer): integer, Node
      if ps.tokens[i].kind == "$EOF$" then
         return i
      end
      local e1: Node
      local t1 = ps.tokens[i]
      if precedences[1][t1.tk] ~= nil then
         local op: Operator = new_operator(t1, 1, t1.tk)
         i = i + 1
         local prev_i = i
         i, e1 = P(ps, i)
         if not e1 then
            fail(ps, prev_i, "expected an expression")
            return i
         end
         e1 = { y = t1.y, x = t1.x, kind = "op", op = op, e1 = e1 }
      elseif ps.tokens[i].tk == "(" then
         i = i + 1
         local prev_i = i
         i, e1 = parse_expression_and_tk(ps, i, ")")
         if not e1 then
            fail(ps, prev_i, "expected an expression")
            return i
         end
         e1 = { y = t1.y, x = t1.x, kind = "paren", e1 = e1 }
      else
         i, e1 = parse_literal(ps, i)
      end

      if not e1 then
         return i
      end

      while true do
         local tkop = ps.tokens[i]
         if tkop.kind == "," or tkop.kind == ")" then -- check most common terminators first
            break
         end
         if tkop.tk == "." or tkop.tk == ":" then
            local op: Operator = new_operator(tkop, 2, tkop.tk)

            local prev_i = i

            local key: Node
            i = i + 1
            if ps.tokens[i].kind ~= "identifier" then
               local skipped = skip(ps, i, parse_type as SkipFunction)
               if skipped > i + 1 then
                  fail(ps, i, "syntax error, cannot declare a type here (missing 'local' or 'global'?)")
                  return skipped, failstore(tkop, e1)
               end
            end
            i, key = verify_kind(ps, i, "identifier")
            if not key then
               return i, failstore(tkop, e1)
            end

            if op.op == ":" then
               if not args_starters[ps.tokens[i].kind] then
                  if ps.tokens[i].tk == "=" then
                     fail(ps, i, "syntax error, cannot perform an assignment here (missing 'local' or 'global'?)")
                  else
                     fail(ps, i, "expected a function call for a method")
                  end
                  return i, failstore(tkop, e1)
               end

               if not after_valid_prefixexp(ps, e1, prev_i) then
                  fail(ps, prev_i, "cannot call a method on this expression")
                  return i, failstore(tkop, e1)
               end
            end

            e1 = { y = tkop.y, x = tkop.x, kind = "op", op = op, e1 = e1, e2 = key }
         elseif tkop.tk == "(" then
            local op: Operator = new_operator(tkop, 2, "@funcall")

            local prev_i = i

            local args = new_node(ps.tokens, i, "expression_list")
            i, args = parse_bracket_list(ps, i, args, "(", ")", "sep", parse_expression)

            if not after_valid_prefixexp(ps, e1, prev_i) then
               fail(ps, prev_i, "cannot call this expression")
               return i, failstore(tkop, e1)
            end

            e1 = { y = args.y, x = args.x, kind = "op", op = op, e1 = e1, e2 = args }

            table.insert(ps.required_modules, node_is_require_call(e1))
         elseif tkop.tk == "[" then
            local op: Operator = new_operator(tkop, 2, "@index")

            local prev_i = i

            local idx: Node
            i = i + 1
            i, idx = parse_expression_and_tk(ps, i, "]")

            if not after_valid_prefixexp(ps, e1, prev_i) then
               fail(ps, prev_i, "cannot index this expression")
               return i, failstore(tkop, e1)
            end

            e1 = { y = tkop.y, x = tkop.x, kind = "op", op = op, e1 = e1, e2 = idx }
         elseif tkop.kind == "string" or tkop.kind == "{" then
            local op: Operator = new_operator(tkop, 2, "@funcall")

            local prev_i = i

            local args = new_node(ps.tokens, i, "expression_list")
            local argument: Node
            if tkop.kind == "string" then
               argument = new_node(ps.tokens, i)
               argument.conststr = unquote(tkop.tk)
               i = i + 1
            else
               i, argument = parse_table_literal(ps, i)
            end

            if not after_valid_prefixexp(ps, e1, prev_i) then
               if tkop.kind == "string" then
                  fail(ps, prev_i, "cannot use a string here; if you're trying to call the previous expression, wrap it in parentheses")
               else
                  fail(ps, prev_i, "cannot use a table here; if you're trying to call the previous expression, wrap it in parentheses")
               end
               return i, failstore(tkop, e1)
            end

            table.insert(args, argument)
            e1 = { y = args.y, x = args.x, kind = "op", op = op, e1 = e1, e2 = args }

            table.insert(ps.required_modules, node_is_require_call(e1))
         elseif tkop.tk == "as" or tkop.tk == "is" then
            local op: Operator = new_operator(tkop, 2, tkop.tk)

            i = i + 1
            local cast = new_node(ps.tokens, i, "cast")
            if ps.tokens[i].tk == "(" then
               i, cast.casttype = parse_type_list(ps, i, "casttype")
            else
               i, cast.casttype = parse_type(ps, i)
            end
            if not cast.casttype then
               return i, failstore(tkop, e1)
            end
            e1 = { y = tkop.y, x = tkop.x, kind = "op", op = op, e1 = e1, e2 = cast, conststr = e1.conststr }
         else
            break
         end
      end

      return i, e1
   end

   E = function(ps: ParseState, i: integer, lhs: Node, min_precedence: integer): integer, Node
      local lookahead = ps.tokens[i].tk
      while precedences[2][lookahead] and precedences[2][lookahead] >= min_precedence do
         local t1 = ps.tokens[i]
         local op: Operator = new_operator(t1, 2, t1.tk)
         i = i + 1
         local rhs: Node
         i, rhs = P(ps, i)
         if not rhs then
            fail(ps, i, "expected an expression")
            return i
         end
         lookahead = ps.tokens[i].tk
         while precedences[2][lookahead] and ((precedences[2][lookahead] > (precedences[2][op.op]))
            or (is_right_assoc[lookahead] and (precedences[2][lookahead] == precedences[2][op.op]))) do
            i, rhs = E(ps, i, rhs, precedences[2][lookahead])
            if not rhs then
               fail(ps, i, "expected an expression")
               return i
            end
            lookahead = ps.tokens[i].tk
         end
         lhs = { y = t1.y, x = t1.x, kind = "op", op = op, e1 = lhs, e2 = rhs, }
      end
      return i, lhs
   end

   parse_expression = function(ps: ParseState, i: integer): integer, Node, integer
      local lhs: Node
      local istart = i
      i, lhs = P(ps, i)
      if lhs then
         i, lhs = E(ps, i, lhs, 0)
      end
      if lhs then
         return i, lhs, 0
      end
      -- if cursor moved, a more specific error was already thrown
      if i == istart then
         i = fail(ps, i, "expected an expression")
      end
      return i
   end
end

parse_expression_and_tk = function(ps: ParseState, i: integer, tk: string): integer, Node
   local e: Node
   i, e = parse_expression(ps, i)
   if not e then
      e = new_node(ps.tokens, i - 1, "error_node")
   end
   if ps.tokens[i].tk == tk then
      i = i + 1
   else
      local msg = "syntax error, expected '" .. tk .. "'"
      if ps.tokens[i].tk == "=" then
         msg = "syntax error, cannot perform an assignment here (did you mean '=='?)"
      end

      -- try to resync the parser for a bit
      for n = 0, 19 do
         local t = ps.tokens[i + n]
         if t.kind == "$EOF$" then
            break
         end
         if t.tk == tk then
            fail(ps, i, msg)
            return i + n + 1, e
         end
      end
      i = fail(ps, i, msg)
   end
   return i, e
end

local function parse_variable_name(ps: ParseState, i: integer): integer, Node, integer
   local node: Node
   i, node = verify_kind(ps, i, "identifier")
   if not node then
      return i
   end
   if ps.tokens[i].tk == "<" then
      i = i + 1
      local annotation: Node
      i, annotation = verify_kind(ps, i, "identifier")
      if annotation then
         if not is_attribute[annotation.tk] then
            fail(ps, i, "unknown variable annotation: " .. annotation.tk)
         end
         node.attribute = annotation.tk as Attribute
      else
         fail(ps, i, "expected a variable annotation")
      end
      i = verify_tk(ps, i, ">")
   end
   return i, node
end

local function parse_argument(ps: ParseState, i: integer): integer, Node, integer
   local node: Node
   if ps.tokens[i].tk == "..." then
      i, node = verify_kind(ps, i, "...", "argument")
      node.opt = true
   else
      i, node = verify_kind(ps, i, "identifier", "argument")
   end
   if ps.tokens[i].tk == "..." then
      fail(ps, i, "'...' needs to be declared as a typed argument")
   end
   if ps.tokens[i].tk == "?" then
      i = i + 1
      node.opt = true
   end
   if ps.tokens[i].tk == ":" then
      i = i + 1
      local argtype: Type

      i, argtype = parse_type(ps, i)

      if node then
         node.argtype = argtype
      end
   end
   return i, node, 0
end

parse_argument_list = function(ps: ParseState, i: integer): integer, Node, integer
   local node = new_node(ps.tokens, i, "argument_list")
   i, node = parse_bracket_list(ps, i, node, "(", ")", "sep", parse_argument)
   local opts = false
   local min_arity = 0
   for a, fnarg in ipairs(node) do
      if fnarg.tk == "..." then
         if a ~= #node then
            fail(ps, i, "'...' can only be last argument")
            break
         end
      elseif fnarg.opt then
         opts = true
      elseif opts then
         return fail(ps, i, "non-optional arguments cannot follow optional arguments")
      else
         min_arity = min_arity + 1
      end
   end
   return i, node, min_arity
end

local record ArgumentInfo
   i: integer
   type: Type
   is_va: boolean
   is_self: boolean
   opt: boolean
end

local function parse_argument_type(ps: ParseState, i: integer): integer, ArgumentInfo, integer
   local opt = false
   local is_va = false
   local is_self = false
   local argument_name: string = nil

   if ps.tokens[i].kind == "identifier" then
      argument_name = ps.tokens[i].tk
      if ps.tokens[i + 1].tk == "?" then
         opt = true
         if ps.tokens[i + 2].tk == ":" then
            i = i + 3
         end
      elseif ps.tokens[i + 1].tk == ":" then
         i = i + 2
      end
   elseif ps.tokens[i].kind == "?" then
      opt = true
      i = i + 1
   elseif ps.tokens[i].tk == "..." then
      if ps.tokens[i + 1].tk == ":" then
         i = i + 2
         is_va = true
      else
         return fail(ps, i, "cannot have untyped '...' when declaring the type of an argument")
      end
   end

   local typ: Type; i, typ = parse_type(ps, i)
   if typ then
      if not is_va and ps.tokens[i].tk == "..." then
         i = i + 1
         is_va = true
      end

      if argument_name == "self" then
         is_self = true
      end
   end

   return i, { i = i, type = typ, is_va = is_va, is_self = is_self, opt = opt or is_va }, 0
end

parse_argument_type_list = function(ps: ParseState, i: integer): integer, Type, boolean, integer
   local ars: {ArgumentInfo} = {}
   i = parse_bracket_list(ps, i, ars, "(", ")", "sep", parse_argument_type)
   local t, list = new_tuple(ps, i)
   local n = #ars
   local min_arity = 0
   for l, ar in ipairs(ars) do
      list[l] = ar.type
      if ar.is_va and l < n then
         fail(ps, ar.i, "'...' can only be last argument")
      end
      if not ar.opt then
         min_arity = min_arity + 1
      end
   end
   if n > 0 and ars[n].is_va then
      t.is_va = true
   end
   return i, t, (n > 0 and ars[1].is_self), min_arity
end

local function parse_identifier(ps: ParseState, i: integer): integer, Node, integer
   if ps.tokens[i].kind == "identifier" then
      return i + 1, new_node(ps.tokens, i, "identifier")
   end
   i = fail(ps, i, "syntax error, expected identifier")
   return i, new_node(ps.tokens, i, "error_node")
end

local function parse_local_function(ps: ParseState, i: integer): integer, Node
   i = verify_tk(ps, i, "local")
   i = verify_tk(ps, i, "function")
   local node = new_node(ps.tokens, i - 2, "local_function")
   i, node.name = parse_identifier(ps, i)
   return parse_function_args_rets_body(ps, i, node)
end

local enum FunctionKind
   "global"
   "record"
end

local function parse_function(ps: ParseState, i: integer, fk: FunctionKind): integer, Node
   local orig_i = i
   i = verify_tk(ps, i, "function")
   local fn = new_node(ps.tokens, i - 1, "global_function")
   local names: {Node} = {}
   i, names[1] = parse_identifier(ps, i)
   while ps.tokens[i].tk == "." do
      i = i + 1
      i, names[#names + 1] = parse_identifier(ps, i)
   end
   if ps.tokens[i].tk == ":" then
      i = i + 1
      i, names[#names + 1] = parse_identifier(ps, i)
      fn.is_method = true
   end

   if #names > 1 then
      fn.kind = "record_function"
      local owner = names[1]
      owner.kind = "type_identifier"
      for i2 = 2, #names - 1 do
         local dot = an_operator(names[i2], 2, ".")
         names[i2].kind = "identifier"
         owner = { y = names[i2].y, x = names[i2].x, kind = "op", op = dot, e1 = owner, e2 = names[i2] }
      end
      fn.fn_owner = owner
   end
   fn.name = names[#names]

   local selfx, selfy = ps.tokens[i].x, ps.tokens[i].y
   i = parse_function_args_rets_body(ps, i, fn)
   if fn.is_method and fn.args then
      table.insert(fn.args, 1, { x = selfx, y = selfy, tk = "self", kind = "identifier", is_self = true })
      fn.min_arity = fn.min_arity + 1
   end

   if not fn.name then
      return orig_i + 1
   end

   if fn.kind == "record_function" and fk == "global" then
      fail(ps, orig_i, "record functions cannot be annotated as 'global'")
   elseif fn.kind == "global_function" and fk == "record" then
      fn.implicit_global_function = true
   end

   return i, fn
end

local function parse_if_block(ps: ParseState, i: integer, n: integer, node: Node, is_else?: boolean): integer, Node
   local block = new_node(ps.tokens, i, "if_block")
   i = i + 1
   block.if_parent = node
   block.if_block_n = n
   if not is_else then
      i, block.exp = parse_expression_and_tk(ps, i, "then")
      if not block.exp then
         return i
      end
   end
   i, block.body = parse_statements(ps, i)
   if not block.body then
      return i
   end
   end_at(block.body, ps.tokens[i - 1])
   block.yend, block.xend = block.body.yend, block.body.xend
   table.insert(node.if_blocks, block)
   return i, node
end

local function parse_if(ps: ParseState, i: integer): integer, Node
   local istart = i
   local node = new_node(ps.tokens, i, "if")
   node.if_blocks = {}
   i, node = parse_if_block(ps, i, 1, node)
   if not node then
      return i
   end
   local n = 2
   while ps.tokens[i].tk == "elseif" do
      i, node = parse_if_block(ps, i, n, node)
      if not node then
         return i
      end
      n = n + 1
   end
   if ps.tokens[i].tk == "else" then
      i, node = parse_if_block(ps, i, n, node, true)
      if not node then
         return i
      end
   end
   i = verify_end(ps, i, istart, node)
   return i, node
end

local function parse_while(ps: ParseState, i: integer): integer, Node
   local istart = i
   local node = new_node(ps.tokens, i, "while")
   i = verify_tk(ps, i, "while")
   i, node.exp = parse_expression_and_tk(ps, i, "do")
   i, node.body = parse_statements(ps, i)
   i = verify_end(ps, i, istart, node)
   return i, node
end

local function parse_fornum(ps: ParseState, i: integer): integer, Node
   local istart = i
   local node = new_node(ps.tokens, i, "fornum")
   i = i + 1
   i, node.var = parse_identifier(ps, i)
   i = verify_tk(ps, i, "=")
   i, node.from = parse_expression_and_tk(ps, i, ",")
   i, node.to = parse_expression(ps, i)
   if ps.tokens[i].tk == "," then
      i = i + 1
      i, node.step = parse_expression_and_tk(ps, i, "do")
   else
      i = verify_tk(ps, i, "do")
   end
   i, node.body = parse_statements(ps, i)
   i = verify_end(ps, i, istart, node)
   return i, node
end

local function parse_forin(ps: ParseState, i: integer): integer, Node
   local istart = i
   local node = new_node(ps.tokens, i, "forin")
   i = i + 1
   node.vars = new_node(ps.tokens, i, "variable_list")
   i, node.vars = parse_list(ps, i, node.vars, { ["in"] = true }, "sep", parse_identifier)
   i = verify_tk(ps, i, "in")
   node.exps = new_node(ps.tokens, i, "expression_list")
   i = parse_list(ps, i, node.exps, { ["do"] = true }, "sep", parse_expression)
   if #node.exps < 1 then
      return fail(ps, i, "missing iterator expression in generic for")
   elseif #node.exps > 3 then
      return fail(ps, i, "too many expressions in generic for")
   end
   i = verify_tk(ps, i, "do")
   i, node.body = parse_statements(ps, i)
   i = verify_end(ps, i, istart, node)
   return i, node
end

local function parse_for(ps: ParseState, i: integer): integer, Node
   if ps.tokens[i+1].kind == "identifier" and ps.tokens[i+2].tk == "=" then
      return parse_fornum(ps, i)
   else
      return parse_forin(ps, i)
   end
end

local function parse_repeat(ps: ParseState, i: integer): integer, Node
   local node = new_node(ps.tokens, i, "repeat")
   i = verify_tk(ps, i, "repeat")
   i, node.body = parse_statements(ps, i)
   node.body.is_repeat = true
   i = verify_tk(ps, i, "until")
   i, node.exp = parse_expression(ps, i)
   end_at(node, ps.tokens[i - 1])
   return i, node
end

local function parse_do(ps: ParseState, i: integer): integer, Node
   local istart = i
   local node = new_node(ps.tokens, i, "do")
   i = verify_tk(ps, i, "do")
   i, node.body = parse_statements(ps, i)
   i = verify_end(ps, i, istart, node)
   return i, node
end

local function parse_break(ps: ParseState, i: integer): integer, Node
   local node = new_node(ps.tokens, i, "break")
   i = verify_tk(ps, i, "break")
   return i, node
end

local function parse_goto(ps: ParseState, i: integer): integer, Node
   local node = new_node(ps.tokens, i, "goto")
   i = verify_tk(ps, i, "goto")
   node.label = ps.tokens[i].tk
   i = verify_kind(ps, i, "identifier")
   return i, node
end

local function parse_label(ps: ParseState, i: integer): integer, Node
   local node = new_node(ps.tokens, i, "label")
   i = verify_tk(ps, i, "::")
   node.label = ps.tokens[i].tk
   i = verify_kind(ps, i, "identifier")
   i = verify_tk(ps, i, "::")
   return i, node
end

local stop_statement_list: {string:boolean} = {
   ["end"] = true,
   ["else"] = true,
   ["elseif"] = true,
   ["until"] = true,
}

local stop_return_list: {string:boolean} = {
   [";"] = true,
   ["$EOF$"] = true,
}

for k, v in pairs(stop_statement_list) do
   stop_return_list[k] = v
end

local function parse_return(ps: ParseState, i: integer): integer, Node
   local node = new_node(ps.tokens, i, "return")
   i = verify_tk(ps, i, "return")
   node.exps = new_node(ps.tokens, i, "expression_list")
   i = parse_list(ps, i, node.exps, stop_return_list, "sep", parse_expression)
   if ps.tokens[i].kind == ";" then
      i = i + 1
   end
   return i, node
end

local function store_field_in_record(ps: ParseState, i: integer, field_name: string, t: Type, fields: {string: Type}, field_order: {string}): boolean
   if not fields[field_name] then
      fields[field_name] = t
      table.insert(field_order, field_name)
   else
      local prev_t = fields[field_name]
      if t is FunctionType and prev_t is FunctionType then
         local p = new_type(ps, i, "poly") as PolyType
         p.types = { prev_t, t }
         fields[field_name] = p
      elseif t is FunctionType and prev_t is PolyType then
         table.insert(prev_t.types, t)
      else
         fail(ps, i, "attempt to redeclare field '" .. field_name .. "' (only functions can be overloaded)")
         return false
      end
   end
   return true
end

local function parse_nested_type(ps: ParseState, i: integer, def: RecordLikeType, typename: TypeName, parse_body: ParseBody): integer, boolean
   i = i + 1 -- skip 'record' or 'enum'
   local iv = i

   local v: Node
   i, v = verify_kind(ps, i, "identifier", "type_identifier")
   if not v then
      return fail(ps, i, "expected a variable name")
   end

   local nt: Node = new_node(ps.tokens, i - 2, "newtype")
   local ndef = new_type(ps, i, typename)
   local iok = parse_body(ps, i, ndef, nt)
   if iok then
      i = iok
      nt.newtype = new_typedecl(ps, i, ndef)
   end

   store_field_in_record(ps, iv, v.tk, nt.newtype, def.fields, def.field_order)
   return i
end

parse_enum_body = function(ps: ParseState, i: integer, def: EnumType, node: Node): integer, Node
   local istart = i - 1
   def.enumset = {}
   while ps.tokens[i].tk ~= "$EOF$" and ps.tokens[i].tk ~= "end" do
      local item: Node
      i, item = verify_kind(ps, i, "string", "enum_item")
      if item then
         table.insert(node, item)
         def.enumset[unquote(item.tk)] = true
      end
   end
   i = verify_end(ps, i, istart, node)
   return i, node
end

local metamethod_names: {string:boolean} = {
   ["__add"] = true,
   ["__sub"] = true,
   ["__mul"] = true,
   ["__div"] = true,
   ["__mod"] = true,
   ["__pow"] = true,
   ["__unm"] = true,
   ["__idiv"] = true,
   ["__band"] = true,
   ["__bor"] = true,
   ["__bxor"] = true,
   ["__bnot"] = true,
   ["__shl"] = true,
   ["__shr"] = true,
   ["__concat"] = true,
   ["__len"] = true,
   ["__eq"] = true,
   ["__lt"] = true,
   ["__le"] = true,
   ["__index"] = true,
   ["__newindex"] = true,
   ["__call"] = true,
   ["__tostring"] = true,
   ["__pairs"] = true,
   ["__gc"] = true,
   ["__close"] = true,
   ["__is"] = true,
}

local function parse_macroexp(ps: ParseState, istart: integer, iargs: integer): integer, Node
-- TODO: generic macroexp
--   if ps.tokens[i].tk == "<" then
--      i, node.typeargs = parse_anglebracket_list(ps, i, parse_typearg)
--   end
   local node = new_node(ps.tokens, istart, "macroexp")
   local i: integer
   i, node.args, node.min_arity = parse_argument_list(ps, iargs)
   i, node.rets = parse_return_types(ps, i)
   i = verify_tk(ps, i, "return")
   i, node.exp = parse_expression(ps, i)
   end_at(node, ps.tokens[i])
   i = verify_end(ps, i, istart, node)
   return i, node
end

local function parse_where_clause(ps: ParseState, i: integer): integer, Node
   local node = new_node(ps.tokens, i, "macroexp")

   local selftype = new_type(ps, i, "nominal") as NominalType
   selftype.names = { "@self" }

   node.args = new_node(ps.tokens, i, "argument_list")
   node.args[1] = new_node(ps.tokens, i, "argument")
   node.args[1].tk = "self"
   node.args[1].argtype = selftype
   node.min_arity = 1
   node.rets = new_tuple(ps, i)
   node.rets.tuple[1] = BOOLEAN
   i, node.exp = parse_expression(ps, i)
   end_at(node, ps.tokens[i - 1])
   return i, node
end

parse_interface_name = function(ps: ParseState, i: integer): integer, Type, integer
   local istart = i
   local typ: Type
   i, typ = parse_simple_type_or_nominal(ps, i)
   if not typ is NominalType then
      return fail(ps, istart, "expected an interface")
   end
   return i, typ
end

local function parse_array_interface_type(ps: ParseState, i: integer, def: RecordLikeType): integer, Type
   if def.interface_list then
      local first = def.interface_list[1]
      if first is ArrayType then
         return failskip(ps, i, "duplicated declaration of array element type", parse_type as SkipFunction)
      end
   end
   local t: Type
   i, t = parse_base_type(ps, i)
   if not t then
      return i
   end
   if not t is ArrayType then
      fail(ps, i, "expected an array declaration")
      return i
   end
   def.elements = t.elements
   return i, t
end

parse_record_body = function(ps: ParseState, i: integer, def: RecordLikeType, node: Node): integer, Node
   local istart = i - 1
   def.fields = {}
   def.field_order = {}

   if ps.tokens[i].tk == "<" then
      i, def.typeargs = parse_anglebracket_list(ps, i, parse_typearg)
   end

   if ps.tokens[i].tk == "{" then
      local atype: Type
      i, atype = parse_array_interface_type(ps, i, def)
      if atype then
         def.interface_list = { atype }
      end
   end

   if ps.tokens[i].tk == "is" then
      i = i + 1

      if ps.tokens[i].tk == "{" then
         local atype: Type
         i, atype = parse_array_interface_type(ps, i, def)
         if ps.tokens[i].tk == "," then
            i = i + 1
            i, def.interface_list = parse_trying_list(ps, i, {}, parse_interface_name)
         else
            def.interface_list = {}
         end
         if atype then
            table.insert(def.interface_list, 1, atype)
         end
      else
         i, def.interface_list = parse_trying_list(ps, i, {}, parse_interface_name)
      end
   end

   if ps.tokens[i].tk == "where" then
      local wstart = i
      i = i + 1
      local where_macroexp: Node
      i, where_macroexp = parse_where_clause(ps, i)

      local typ = new_type(ps, wstart, "function") as FunctionType
      typ.is_method = true
      typ.min_arity = 1
      typ.args = a_tuple {
         a_type("nominal", {
            y = typ.y,
            x = typ.x,
            filename = ps.filename,
            names = { "@self" }
         } as NominalType)
      }
      typ.rets = a_tuple { BOOLEAN }
      typ.macroexp = where_macroexp

      def.meta_fields = {}
      def.meta_field_order = {}
      store_field_in_record(ps, i, "__is", typ, def.meta_fields, def.meta_field_order)
   end

   while not (ps.tokens[i].kind == "$EOF$" or ps.tokens[i].tk == "end") do
      local tn = ps.tokens[i].tk as TypeName
      if ps.tokens[i].tk == "userdata" and ps.tokens[i+1].tk ~= ":" then
         if def.is_userdata then
            fail(ps, i, "duplicated 'userdata' declaration")
         else
            def.is_userdata = true
         end
         i = i + 1
      elseif ps.tokens[i].tk == "{" then
         return fail(ps, i, "syntax error: this syntax is no longer valid; declare array interface at the top with 'is {...}'")
      elseif ps.tokens[i].tk == "type" and ps.tokens[i + 1].tk ~= ":" then
         i = i + 1
         local iv = i
         local v: Node
         i, v = verify_kind(ps, i, "identifier", "type_identifier")
         if not v then
            return fail(ps, i, "expected a variable name")
         end
         i = verify_tk(ps, i, "=")
         local nt: Node
         i, nt = parse_newtype(ps, i)
         if not nt or not nt.newtype then
            return fail(ps, i, "expected a type definition")
         end

         local ntt = nt.newtype
         if ntt is TypeAliasType then
            ntt.is_nested_alias = true
         end

         store_field_in_record(ps, iv, v.tk, nt.newtype, def.fields, def.field_order)
      elseif parse_type_body_fns[tn] and ps.tokens[i+1].tk ~= ":" then
         i = parse_nested_type(ps, i, def, tn, parse_type_body_fns[tn])
      else
         local is_metamethod = false
         if ps.tokens[i].tk == "metamethod" and ps.tokens[i+1].tk ~= ":" then
            is_metamethod = true
            i = i + 1
         end

         local v: Node
         if ps.tokens[i].tk == "[" then
            i, v = parse_literal(ps, i+1)
            if v and not v.conststr then
               return fail(ps, i, "expected a string literal")
            end
            i = verify_tk(ps, i, "]")
         else
            i, v = verify_kind(ps, i, "identifier", "variable")
         end
         local iv = i
         if not v then
            return fail(ps, i, "expected a variable name")
         end

         if ps.tokens[i].tk == ":" then
            i = i + 1
            local t: Type
            i, t = parse_type(ps, i)
            if not t then
               return fail(ps, i, "expected a type")
            end

            local field_name = v.conststr or v.tk
            local fields = def.fields
            local field_order = def.field_order
            if is_metamethod then
               if not def.meta_fields then
                  def.meta_fields = {}
                  def.meta_field_order = {}
               end
               fields = def.meta_fields
               field_order = def.meta_field_order
               if not metamethod_names[field_name] then
                  fail(ps, i - 1, "not a valid metamethod: " .. field_name)
               end
            end

            if ps.tokens[i].tk == "=" and ps.tokens[i + 1].tk == "macroexp" then
               if not t is FunctionType then
                  fail(ps, i + 1, "macroexp must have a function type")
               else
                  i, t.macroexp = parse_macroexp(ps, i + 1, i + 2)
               end
            end

            store_field_in_record(ps, iv, field_name, t, fields, field_order)
         elseif ps.tokens[i].tk == "=" then
            local next_word = ps.tokens[i + 1].tk
            if next_word == "record" or next_word == "enum" then
               return fail(ps, i, "syntax error: this syntax is no longer valid; use '" .. next_word .. " " .. v.tk .. "'")
            elseif next_word == "functiontype" then
               return fail(ps, i, "syntax error: this syntax is no longer valid; use 'type " .. v.tk .. " = function('...")
            else
               return fail(ps, i, "syntax error: this syntax is no longer valid; use 'type " .. v.tk .. " = '...")
            end
         else
            fail(ps, i, "syntax error: expected ':' for an attribute or '=' for a nested type")
         end
      end
   end
   i = verify_end(ps, i, istart, node)
   return i, node
end

parse_type_body_fns = {
   ["interface"] = parse_record_body,
   ["record"] = parse_record_body,
   ["enum"] = parse_enum_body,
}

parse_newtype = function(ps: ParseState, i: integer): integer, Node
   local node: Node = new_node(ps.tokens, i, "newtype")
   local def: Type
   local tn = ps.tokens[i].tk as TypeName
   local itype = i
   if parse_type_body_fns[tn] then
      def = new_type(ps, i, tn)
      i = i + 1
      i = parse_type_body_fns[tn](ps, i, def, node)
      if not def then
         return fail(ps, i, "expected a type")
      end

      node.newtype = new_typedecl(ps, itype, def)
      return i, node
   else
      i, def = parse_type(ps, i)
      if not def then
         return fail(ps, i, "expected a type")
      end

      if def is NominalType then
         local typealias = new_type(ps, itype, "typealias") as TypeAliasType
         typealias.alias_to = def
         node.newtype = typealias
      else
         node.newtype = new_typedecl(ps, itype, def)
      end

      return i, node
   end
end

local function parse_assignment_expression_list(ps: ParseState, i: integer, asgn: Node): integer, Node
   asgn.exps = new_node(ps.tokens, i, "expression_list")
   repeat
      i = i + 1
      local val: Node
      i, val = parse_expression(ps, i)
      if not val then
         if #asgn.exps == 0 then
            asgn.exps = nil
         end
         return i
      end
      table.insert(asgn.exps, val)
   until ps.tokens[i].tk ~= ","
   return i, asgn
end

local parse_call_or_assignment: function(ps: ParseState, i: integer): integer, Node
do
   local function is_lvalue(node: Node): boolean
      node.is_lvalue = node.kind == "variable"
                       or (node.kind == "op"
                           and (node.op.op == "@index" or node.op.op == "."))
      return node.is_lvalue
   end

   local function parse_variable(ps: ParseState, i: integer): integer, Node, integer
      local node: Node
      i, node = parse_expression(ps, i)
      if not (node and is_lvalue(node)) then
         return fail(ps, i, "expected a variable")
      end
      return i, node
   end

   parse_call_or_assignment = function(ps: ParseState, i: integer): integer, Node
      local exp: Node
      local istart = i
      i, exp = parse_expression(ps, i)
      if not exp then
         return i
      end

      if (exp.op and exp.op.op == "@funcall") or exp.failstore then
         return i, exp
      end

      if not is_lvalue(exp) then
         return fail(ps, i, "syntax error")
      end

      local asgn: Node = new_node(ps.tokens, istart, "assignment")
      asgn.vars = new_node(ps.tokens, istart, "variable_list")
      asgn.vars[1] = exp
      if ps.tokens[i].tk == "," then
         i = i + 1
         i = parse_trying_list(ps, i, asgn.vars, parse_variable)
         if #asgn.vars < 2 then
            return fail(ps, i, "syntax error")
         end
      end

      if ps.tokens[i].tk ~= "=" then
         verify_tk(ps, i, "=")
         return i
      end

      i, asgn = parse_assignment_expression_list(ps, i, asgn)
      return i, asgn
   end
end

local function parse_variable_declarations(ps: ParseState, i: integer, node_name: NodeKind): integer, Node
   local asgn: Node = new_node(ps.tokens, i, node_name)

   asgn.vars = new_node(ps.tokens, i, "variable_list")
   i = parse_trying_list(ps, i, asgn.vars, parse_variable_name)
   if #asgn.vars == 0 then
      return fail(ps, i, "expected a local variable definition")
   end

   i, asgn.decltuple = parse_type_list(ps, i, "decltuple")

   if ps.tokens[i].tk == "=" then
      -- produce nice error message when using <= 0.7.1 syntax
      local next_word = ps.tokens[i + 1].tk
      local tn = next_word as TypeName
      if parse_type_body_fns[tn] then
         local scope = node_name == "local_declaration" and "local" or "global"
         return failskip(ps, i + 1, "syntax error: this syntax is no longer valid; use '" .. scope .. " " .. next_word .. " " .. asgn.vars[1].tk .. "'", skip_type_body)
      elseif next_word == "functiontype" then
         local scope = node_name == "local_declaration" and "local" or "global"
         return failskip(ps, i + 1, "syntax error: this syntax is no longer valid; use '" .. scope .. " type " .. asgn.vars[1].tk .. " = function('...", parse_function_type as SkipFunction)
      end

      i, asgn = parse_assignment_expression_list(ps, i, asgn)
   end
   return i, asgn
end

local function parse_type_declaration(ps: ParseState, i: integer, node_name: NodeKind): integer, Node
   i = i + 2 -- skip `local` or `global`, and `type`

   local asgn: Node = new_node(ps.tokens, i, node_name)
   i, asgn.var = parse_variable_name(ps, i)
   if not asgn.var then
      return fail(ps, i, "expected a type name")
   end

   if node_name == "global_type" and ps.tokens[i].tk ~= "=" then
      return i, asgn
   end

   i = verify_tk(ps, i, "=")

   if ps.tokens[i].kind == "identifier" and ps.tokens[i].tk == "require" then
      local istart = i
      i, asgn.value = parse_call_or_assignment(ps, i)
      if asgn.value and not node_is_require_call(asgn.value) then
         fail(ps, istart, "require() for type declarations must have a literal argument")
      end
      return i, asgn
   end

   i, asgn.value = parse_newtype(ps, i)
   if not asgn.value then
      return i
   end

   local nt = asgn.value.newtype
   if nt is TypeDeclType then
      local def = nt.def
      if def is RecordLikeType or def is EnumType then
         if not def.declname then
            def.declname = asgn.var.tk
         end
      end
   end

   return i, asgn
end

local function parse_type_constructor(ps: ParseState, i: integer, node_name: NodeKind, type_name: TypeName, parse_body: ParseBody): integer, Node
   local asgn: Node = new_node(ps.tokens, i, node_name)
   local nt: Node = new_node(ps.tokens, i, "newtype")
   asgn.value = nt
   local itype = i
   local def = new_type(ps, i, type_name)

   i = i + 2 -- skip `local` or `global`, and the constructor name

   i, asgn.var = verify_kind(ps, i, "identifier")
   if not asgn.var then
      return fail(ps, i, "expected a type name")
   end

   assert(def is RecordType or def is InterfaceType or def is EnumType)
   def.declname = asgn.var.tk

   i = parse_body(ps, i, def, nt)

   nt.newtype = new_typedecl(ps, itype, def)

   return i, asgn
end

local function skip_type_declaration(ps: ParseState, i: integer): integer, Node
   return parse_type_declaration(ps, i - 1, "local_type")
end

local function parse_local_macroexp(ps: ParseState, i: integer): integer, Node
   local istart = i
   i = i + 2 -- skip `local`
   local node = new_node(ps.tokens, i, "local_macroexp")
   i, node.name = parse_identifier(ps, i)
   i, node.macrodef = parse_macroexp(ps, istart, i)
   end_at(node, ps.tokens[i - 1])
   return i, node
end

local function parse_local(ps: ParseState, i: integer): integer, Node
   local ntk = ps.tokens[i + 1].tk
   local tn = ntk as TypeName
   if ntk == "function" then
      return parse_local_function(ps, i)
   elseif ntk == "type" and ps.tokens[i+2].kind == "identifier" then
      return parse_type_declaration(ps, i, "local_type")
   elseif ntk == "macroexp" and ps.tokens[i+2].kind == "identifier" then
      return parse_local_macroexp(ps, i)
   elseif parse_type_body_fns[tn] and ps.tokens[i+2].kind == "identifier" then
      return parse_type_constructor(ps, i, "local_type", tn, parse_type_body_fns[tn])
   end
   return parse_variable_declarations(ps, i + 1, "local_declaration")
end

local function parse_global(ps: ParseState, i: integer): integer, Node
   local ntk = ps.tokens[i + 1].tk
   local tn = ntk as TypeName
   if ntk == "function" then
      return parse_function(ps, i + 1, "global")
   elseif ntk == "type" and ps.tokens[i+2].kind == "identifier" then
      return parse_type_declaration(ps, i, "global_type")
   elseif parse_type_body_fns[tn] and ps.tokens[i+2].kind == "identifier" then
      return parse_type_constructor(ps, i, "global_type", tn, parse_type_body_fns[tn])
   elseif ps.tokens[i+1].kind == "identifier" then
      return parse_variable_declarations(ps, i + 1, "global_declaration")
   end
   return parse_call_or_assignment(ps, i) -- global is a soft keyword
end

local function parse_record_function(ps: ParseState, i: integer): integer, Node
   return parse_function(ps, i, "record")
end

local parse_statement_fns: {string : function(ParseState, integer):(integer, Node)} = {
   ["::"] = parse_label,
   ["do"] = parse_do,
   ["if"] = parse_if,
   ["for"] = parse_for,
   ["goto"] = parse_goto,
   ["local"] = parse_local,
   ["while"] = parse_while,
   ["break"] = parse_break,
   ["global"] = parse_global,
   ["repeat"] = parse_repeat,
   ["return"] = parse_return,
   ["function"] = parse_record_function,
}

local function type_needs_local_or_global(ps: ParseState, i: integer): integer, Node
   local tk = ps.tokens[i].tk
   return failskip(ps, i, ("%s needs to be declared with 'local %s' or 'global %s'"):format(tk, tk, tk), skip_type_body)
end

local needs_local_or_global: {string : function(ParseState, integer):(integer, Node)} = {
   ["type"] = function(ps: ParseState, i: integer): integer, Node
      return failskip(ps, i, "types need to be declared with 'local type' or 'global type'", skip_type_declaration)
   end,
   ["record"] = type_needs_local_or_global,
   ["enum"] = type_needs_local_or_global,
}

parse_statements = function(ps: ParseState, i: integer, toplevel?: boolean): integer, Node
   local node = new_node(ps.tokens, i, "statements")
   local item: Node
   while true do
      while ps.tokens[i].kind == ";" do
         i = i + 1
         if item then
            item.semicolon = true
         end
      end

      if ps.tokens[i].kind == "$EOF$" then
         break
      end
      local tk = ps.tokens[i].tk
      if (not toplevel) and stop_statement_list[tk] then
         break
      end

      local fn = parse_statement_fns[tk]
      if not fn then
         local skip_fn = needs_local_or_global[tk]
         if skip_fn and ps.tokens[i + 1].kind == "identifier" then
            fn = skip_fn
         else
            fn = parse_call_or_assignment
         end
      end

      i, item = fn(ps, i)

      if item then
         table.insert(node, item)
      elseif i > 1 then
         -- heuristic to resync at the next line after an invalid statement
         local lasty = ps.tokens[i - 1].y
         while ps.tokens[i].kind ~= "$EOF$" and ps.tokens[i].y == lasty do
            i = i + 1
         end
      end
   end

   end_at(node, ps.tokens[i])
   return i, node
end

local function clear_redundant_errors(errors: {Error})
   local redundant: {integer} = {}
   local lastx, lasty = 0, 0
   for i, err in ipairs(errors) do
      err.i = i
   end
   table.sort(errors, function(a: Error, b: Error): boolean
      local af = a.filename or ""
      local bf = b.filename or ""
      return af < bf
             or (af == bf   and (a.y < b.y
             or (a.y == b.y and (a.x < b.x
             or (a.x == b.x and (a.i < b.i))))))
   end)
   for i, err in ipairs(errors) do
      err.i = nil
      if err.x == lastx and err.y == lasty then
         table.insert(redundant, i)
      end
      lastx, lasty = err.x, err.y
   end
   for i = #redundant, 1, -1 do
      table.remove(errors, redundant[i])
   end
end

function parser.parse_program(tokens: {Token}, errs: {Error}, filename: string): Node, {string}
   errs = errs or {}
   local ps: ParseState = {
      tokens = tokens,
      errs = errs,
      filename = filename or "",
      required_modules = {},
   }
   local i = 1
   local hashbang: string
   if ps.tokens[i].kind == "hashbang" then
      hashbang = ps.tokens[i].tk
      i = i + 1
   end
   local _, node = parse_statements(ps, i, true)
   if hashbang then
      node.hashbang = hashbang
   end

   clear_redundant_errors(errs)
   return node, ps.required_modules
end

function parser.parse(input: string, filename: string): Node, {Error}, {string}
   local tokens, errs = tl.lex(input, filename)
   local node, required_modules = tl.parse_program(tokens, errs, filename)
   return node, errs, required_modules
end

