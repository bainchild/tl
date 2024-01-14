
local VERSION = "0.15.3+dev"

local stdlib = require("teal.stdlib")
local parser = require("teal.parser")

local record tl
   enum LoadMode
      "b"
      "t"
      "bt"
      "cb"
      "ct"
      "cbt"
   end
   type LoadFunction = function(...:any): any...

   enum GenCompat
      "off"
      "optional"
      "required"
   end

   enum GenTarget
      "5.1"
      "5.3"
      "5.4"
   end

   enum Feat
      "on"
      "off"
   end

   record PrettyPrintOptions
      preserve_indent: boolean
      preserve_newlines: boolean
      preserve_hashbang: boolean
   end

   record TypeCheckOptions
      feat_lax: Feat
      feat_arity: Feat
      gen_compat: GenCompat
      gen_target: GenTarget
      run_internal_compiler_checks: boolean
   end

   record Env
      globals: {string:Variable}
      modules: {string:Type}
      loaded: {string:Result}
      loaded_order: {string}
      reporter: TypeReporter
      keep_going: boolean
      report_types: boolean
      defaults: TypeCheckOptions
   end

   record Result
      filename: string
      ast: Node
      type: Type
      syntax_errors: {Error}
      type_errors: {Error}
      gen_error: string
      warnings: {Error}
      env: Env
      dependencies: {string:string} -- module name, file found
   end

   record EnvOptions
      defaults: TypeCheckOptions
      predefined_modules: {string}
   end

   load: function(string, string, LoadMode, {any:any}): LoadFunction, string
   process: function(string, Env, string, FILE): (Result, string)
   process_string: function(string, Env, ? string, ? string): Result
   gen: function(string, Env, PrettyPrintOptions): string, Result
   type_check: function(Node, string, string, TypeCheckOptions, ? Env): Result, string
   new_env: function(? EnvOptions): Env, string
   version: function(): string

   -- Backwards compatibility
   init_env: function(? boolean, ? boolean | GenCompat, ? GenTarget, ? {string}): Env, string

   package_loader_env: Env
   load_envs: { {any:any} : Env }
end

local type Env = tl.Env
local type EnvOptions = tl.EnvOptions
local type Error = tl.Error
local type Feat = tl.Feat
local type GenCompat = tl.GenCompat
local type GenTarget = tl.GenTarget
local type LoadFunction = tl.LoadFunction
local type LoadMode = tl.LoadMode
local type PrettyPrintOptions = tl.PrettyPrintOptions
local type Result = tl.Result
local type TypeCheckOptions = tl.TypeCheckOptions
local type TypeInfo = tl.TypeInfo
local type TypeReport = tl.TypeReport
local type WarningKind = tl.WarningKind

local DEFAULT_GEN_COMPAT <const>: GenCompat = "optional"
local DEFAULT_GEN_TARGET <const>: GenTarget = "5.3"

tl.version = function(): string
   return VERSION
end


local enum Narrow
   "narrow"
   "narrowed_declaration"
   "declaration"
end

local record Variable
   t: Type
   attribute: Attribute
   needs_compat: boolean
   narrowed_from: Type
   is_narrowed: Narrow
   declared_at: Node
   is_func_arg: boolean
   used: boolean
   used_as_type: boolean
   aliasing: Variable
   implemented: {string:boolean}
end

--------------------------------------------------------------------------------
-- Compiler debugging
--------------------------------------------------------------------------------

local TL_DEBUG = os.getenv("TL_DEBUG")
local TL_DEBUG_MAXLINE = math.maxinteger

if TL_DEBUG then
   local max <const> = assert(tonumber(TL_DEBUG), "TL_DEBUG was defined, but not a number")
   if max < 0 then
      TL_DEBUG_MAXLINE = math.tointeger(-max)
   elseif max > 1 then
      local count = 0
      local skip: string = nil
      debug.sethook(function(event: debug.HookEvent)
         if event == "call" or event == "tail call" or event == "return" then
            local info <const> = debug.getinfo(2)

            if skip then
               if info.name == skip and event == "return" then
                  skip = nil
               end
               return
            elseif (info.name or "?"):match("^tl_debug_") and event == "call" then
               skip = info.name
               return
            end

            local name = info.name or "<anon>", info.currentline > 0 and "@" .. info.currentline or ""
            io.stderr:write(name, " :: ", event as string, "\n")
            io.stderr:flush()
         else
            count = count + 100
            if count > max then
               error("Too many instructions")
            end
         end
      end, "cr", 100)
   end
end


--------------------------------------------------------------------------------
-- Pretty-print AST
--------------------------------------------------------------------------------

local tight_op: {integer:{string:boolean}} = {
   [1] = {
      ["-"] = true,
      ["~"] = true,
      ["#"] = true,
   },
   [2] = {
      ["."] = true,
      [":"] = true,
   },
}

local spaced_op: {integer:{string:boolean}} = {
   [1] = {
      ["not"] = true,
   },
   [2] = {
      ["or"] = true,
      ["and"] = true,
      ["<"] = true,
      [">"] = true,
      ["<="] = true,
      [">="] = true,
      ["~="] = true,
      ["=="] = true,
      ["|"] = true,
      ["~"] = true,
      ["&"] = true,
      ["<<"] = true,
      [">>"] = true,
      [".."] = true,
      ["+"] = true,
      ["-"] = true,
      ["*"] = true,
      ["/"] = true,
      ["//"] = true,
      ["%"] = true,
      ["^"] = true,
   },
}


local default_pretty_print_ast_opts: PrettyPrintOptions = {
   preserve_indent = true,
   preserve_newlines = true,
   preserve_hashbang = false,
}

local fast_pretty_print_ast_opts: PrettyPrintOptions = {
   preserve_indent = false,
   preserve_newlines = true,
   preserve_hashbang = false,
}

local primitive: {TypeName:string} = {
   ["function"] = "function",
   ["enum"] = "string",
   ["boolean"] = "boolean",
   ["string"] = "string",
   ["nil"] = "nil",
   ["number"] = "number",
   ["integer"] = "number",
   ["thread"] = "thread",
}

function tl.pretty_print_ast(ast: Node, gen_target: GenTarget, mode: boolean | PrettyPrintOptions): string, string
   local err: string
   local indent = 0

   local opts: PrettyPrintOptions
   if mode is PrettyPrintOptions then
      opts = mode
   elseif mode == true then
      opts = fast_pretty_print_ast_opts
   else
      opts = default_pretty_print_ast_opts
   end

   local record Output
      {string}
      y: integer
      h: integer
   end

   local save_indent: {integer} = {}

   local function increment_indent(node: Node)
      local child = node.body or node[1]
      if not child then
         return
      end
      if child.y ~= node.y then
         if indent == 0 and #save_indent > 0 then
            indent = save_indent[#save_indent] + 1
         else
            indent = indent + 1
         end
      else
         table.insert(save_indent, indent)
         indent = 0
      end
   end

   local function decrement_indent(node: Node, child: Node)
      if child.y ~= node.y then
         indent = indent - 1
      else
         indent = table.remove(save_indent)
      end
   end

   if not opts.preserve_indent then
      increment_indent = nil
      decrement_indent = function() end
   end

   local function add_string(out: Output, s: string)
      table.insert(out, s)
      if string.find(s, "\n", 1, true) then
         for _nl in s:gmatch("\n") do
            out.h = out.h + 1
         end
      end
   end

   local function add_child(out: Output, child: Output, space?: string, current_indent?: integer): integer
      if #child == 0 then
         return
      end

      if child.y ~= -1 and child.y < out.y then
         out.y = child.y
      end

      if child.y > out.y + out.h and opts.preserve_newlines then
         local delta = child.y - (out.y + out.h)
         out.h = out.h + delta
         table.insert(out, ("\n"):rep(delta))
      else
         if space then
            if space ~= "" then
               table.insert(out, space)
            end
            current_indent = nil
         end
      end
      if current_indent and opts.preserve_indent then
         table.insert(out, ("   "):rep(current_indent))
      end
      table.insert(out, child as string)
      out.h = out.h + child.h
   end

   local function concat_output(out: Output): string
      for i, s in ipairs(out) do
         if type(s) == "table" then
            out[i] = concat_output(s as Output)
         end
      end
      return table.concat(out)
   end

   local function print_record_def(typ: RecordLikeType): string
      local out: {string} = { "{" }
      for fname, ftype in fields_of(typ) do
         if ftype is TypeDeclType then
            local def = ftype.def
            if def is RecordLikeType then
               table.insert(out, fname)
               table.insert(out, " = ")
               table.insert(out, print_record_def(def))
               table.insert(out, ", ")
            end
         end
      end
      table.insert(out, "}")
      return table.concat(out)
   end

   local visit_node: Visitor<nil, NodeKind, Node, Output> = {}

   local lua_54_attribute <total>: {Attribute:string} = {
      ["const"] = " <const>",
      ["close"] = " <close>",
      ["total"] = " <const>",
   }

   visit_node.cbs = {
      ["statements"] = {
         after = function(_: nil, node: Node, children: {Output}): Output
            local out: Output
            if opts.preserve_hashbang and node.hashbang then
               out = { y = 1, h = 0 }
               table.insert(out, node.hashbang)
            else
               out = { y = node.y, h = 0 }
            end
            local space: string
            for i, child in ipairs(children) do
               add_child(out, child, space, indent)
               if node[i].semicolon then
                  table.insert(out, ";")
                  space = " "
               else
                  space = "; "
               end
            end
            return out
         end
      },
      ["local_declaration"] = {
         after = function(_: nil, node: Node, children: {Output}): Output
            local out: Output = { y = node.y, h = 0 }
            table.insert(out, "local ")
            for i, var in ipairs(node.vars) do
               if i > 1 then
                  add_string(out, ", ")
               end
               add_string(out, var.tk)
               if var.attribute then
                  if gen_target ~= "5.4" and var.attribute == "close" then
                     err = "attempt to emit a <close> attribute for a non 5.4 target"
                  end

                  if gen_target == "5.4" then
                     add_string(out, lua_54_attribute[var.attribute])
                  end
               end
            end
            if children[3] then
               table.insert(out, " =")
               add_child(out, children[3], " ")
            end
            return out
         end,
      },
      ["local_type"] = {
         after = function(_: nil, node: Node, children: {Output}): Output
            local out: Output = { y = node.y, h = 0 }
            if not node.var.elide_type then
               table.insert(out, "local")
               add_child(out, children[1], " ")
               table.insert(out, " =")
               add_child(out, children[2], " ")
            end
            return out
         end,
      },
      ["global_type"] = {
         after = function(_: nil, node: Node, children: {Output}): Output
            local out: Output = { y = node.y, h = 0 }
            if children[2] then
               add_child(out, children[1])
               table.insert(out, " =")
               add_child(out, children[2], " ")
            end
            return out
         end,
      },
      ["global_declaration"] = {
         after = function(_: nil, node: Node, children: {Output}): Output
            local out: Output = { y = node.y, h = 0 }
            if children[3] then
               add_child(out, children[1])
               table.insert(out, " =")
               add_child(out, children[3], " ")
            end
            return out
         end,
      },
      ["assignment"] = {
         after = function(_: nil, node: Node, children: {Output}): Output
            local out: Output = { y = node.y, h = 0 }
            add_child(out, children[1])
            table.insert(out, " =")
            add_child(out, children[3], " ")
            return out
         end,
      },
      ["if"] = {
         after = function(_: nil, node: Node, children: {Output}): Output
            local out: Output = { y = node.y, h = 0 }
            for i, child in ipairs(children) do
               add_child(out, child, i > 1 and " ", child.y ~= node.y and indent)
            end
            add_child(out, { y = node.yend, h = 0, [1] = "end" }, " ", indent)
            return out
         end,
      },
      ["if_block"] = {
         before = increment_indent,
         after = function(_: nil, node: Node, children: {Output}): Output
            local out: Output = { y = node.y, h = 0 }
            if node.if_block_n == 1 then
               table.insert(out, "if")
            elseif not node.exp then
               table.insert(out, "else")
            else
               table.insert(out, "elseif")
            end
            if node.exp then
               add_child(out, children[1], " ")
               table.insert(out, " then")
            end
            add_child(out, children[2], " ")
            decrement_indent(node, node.body)
            return out
         end,
      },
      ["while"] = {
         before = increment_indent,
         after = function(_: nil, node: Node, children: {Output}): Output
            local out: Output = { y = node.y, h = 0 }
            table.insert(out, "while")
            add_child(out, children[1], " ")
            table.insert(out, " do")
            add_child(out, children[2], " ")
            decrement_indent(node, node.body)
            add_child(out, { y = node.yend, h = 0, [1] = "end" }, " ", indent)
            return out
         end,
      },
      ["repeat"] = {
         before = increment_indent,
         after = function(_: nil, node: Node, children: {Output}): Output
            local out: Output = { y = node.y, h = 0 }
            table.insert(out, "repeat")
            add_child(out, children[1], " ")
            decrement_indent(node, node.body)
            add_child(out, { y = node.yend, h = 0, [1] = "until " }, " ", indent)
            add_child(out, children[2])
            return out
         end,
      },
      ["do"] = {
         before = increment_indent,
         after = function(_: nil, node: Node, children: {Output}): Output
            local out: Output = { y = node.y, h = 0 }
            table.insert(out, "do")
            add_child(out, children[1], " ")
            decrement_indent(node, node.body)
            add_child(out, { y = node.yend, h = 0, [1] = "end" }, " ", indent)
            return out
         end,
      },
      ["forin"] = {
         before = increment_indent,
         after = function(_: nil, node: Node, children: {Output}): Output
            local out: Output = { y = node.y, h = 0 }
            table.insert(out, "for")
            add_child(out, children[1], " ")
            table.insert(out, " in")
            add_child(out, children[2], " ")
            table.insert(out, " do")
            add_child(out, children[3], " ")
            decrement_indent(node, node.body)
            add_child(out, { y = node.yend, h = 0, [1] = "end" }, " ", indent)
            return out
         end,
      },
      ["fornum"] = {
         before = increment_indent,
         after = function(_: nil, node: Node, children: {Output}): Output
            local out: Output = { y = node.y, h = 0 }
            table.insert(out, "for")
            add_child(out, children[1], " ")
            table.insert(out, " =")
            add_child(out, children[2], " ")
            table.insert(out, ",")
            add_child(out, children[3], " ")
            if children[4] then
               table.insert(out, ",")
               add_child(out, children[4], " ")
            end
            table.insert(out, " do")
            add_child(out, children[5], " ")
            decrement_indent(node, node.body)
            add_child(out, { y = node.yend, h = 0, [1] = "end" }, " ", indent)
            return out
         end,
      },
      ["return"] = {
         after = function(_: nil, node: Node, children: {Output}): Output
            local out: Output = { y = node.y, h = 0 }
            table.insert(out, "return")
            if #children[1] > 0 then
               add_child(out, children[1], " ")
            end
            return out
         end,
      },
      ["break"] = {
         after = function(_: nil, node: Node, _children: {Output}): Output
            local out: Output = { y = node.y, h = 0 }
            table.insert(out, "break")
            return out
         end,
      },
      ["variable_list"] = {
         after = function(_: nil, node: Node, children: {Output}): Output
            local out: Output = { y = node.y, h = 0 }
            local space: string
            for i, child in ipairs(children) do
               if i > 1 then
                  table.insert(out, ",")
                  space = " "
               end
               add_child(out, child, space, child.y ~= node.y and indent)
            end
            return out
         end,
      },
      ["literal_table"] = {
         before = increment_indent,
         after = function(_: nil, node: Node, children: {Output}): Output
            local out: Output = { y = node.y, h = 0 }
            if #children == 0 then
               table.insert(out, "{}")
               return out
            end
            table.insert(out, "{")
            local n = #children
            for i, child in ipairs(children) do
               add_child(out, child, " ", child.y ~= node.y and indent)
               if i < n or node.yend ~= node.y then
                  table.insert(out, ",")
               end
            end
            decrement_indent(node, node[1])
            add_child(out, { y = node.yend, h = 0, [1] = "}" }, " ", indent)
            return out
         end,
      },
      ["literal_table_item"] = {
         after = function(_: nil, node: Node, children: {Output}): Output
            local out: Output = { y = node.y, h = 0 }
            if node.key_parsed ~= "implicit" then
               if node.key_parsed == "short" then
                  children[1][1] = children[1][1]:sub(2, -2)
                  add_child(out, children[1])
                  table.insert(out, " = ")
               else
                  table.insert(out, "[")
                  if node.key_parsed == "long" and node.key.is_longstring then
                     table.insert(children[1], 1, " ")
                     table.insert(children[1], " ")
                  end
                  add_child(out, children[1])
                  table.insert(out, "] = ")
               end
            end
            add_child(out, children[2])
            return out
         end,
      },
      ["local_macroexp"] = {
         before = increment_indent,
         after = function(_: nil, node: Node, _children: {Output}): Output
            return { y = node.y, h = 0 }
         end,
      },
      ["local_function"] = {
         before = increment_indent,
         after = function(_: nil, node: Node, children: {Output}): Output
            local out: Output = { y = node.y, h = 0 }
            table.insert(out, "local function")
            add_child(out, children[1], " ")
            table.insert(out, "(")
            add_child(out, children[2])
            table.insert(out, ")")
            add_child(out, children[4], " ")
            decrement_indent(node, node.body)
            add_child(out, { y = node.yend, h = 0, [1] = "end" }, " ", indent)
            return out
         end,
      },
      ["global_function"] = {
         before = increment_indent,
         after = function(_: nil, node: Node, children: {Output}): Output
            local out: Output = { y = node.y, h = 0 }
            table.insert(out, "function")
            add_child(out, children[1], " ")
            table.insert(out, "(")
            add_child(out, children[2])
            table.insert(out, ")")
            add_child(out, children[4], " ")
            decrement_indent(node, node.body)
            add_child(out, { y = node.yend, h = 0, [1] = "end" }, " ", indent)
            return out
         end,
      },
      ["record_function"] = {
         before = increment_indent,
         after = function(_: nil, node: Node, children: {Output}): Output
            local out: Output = { y = node.y, h = 0 }
            table.insert(out, "function")
            add_child(out, children[1], " ")
            table.insert(out, node.is_method and ":" or ".")
            add_child(out, children[2])
            table.insert(out, "(")
            if node.is_method then
               -- remove self
               table.remove(children[3], 1)
               if children[3][1] == "," then
                  table.remove(children[3], 1)
                  table.remove(children[3], 1)
               end
            end
            add_child(out, children[3])
            table.insert(out, ")")
            add_child(out, children[5], " ")
            decrement_indent(node, node.body)
            add_child(out, { y = node.yend, h = 0, [1] = "end" }, " ", indent)
            return out
         end,
      },
      ["function"] = {
         before = increment_indent,
         after = function(_: nil, node: Node, children: {Output}): Output
            local out: Output = { y = node.y, h = 0 }
            table.insert(out, "function(")
            add_child(out, children[1])
            table.insert(out, ")")
            add_child(out, children[3], " ")
            decrement_indent(node, node.body)
            add_child(out, { y = node.yend, h = 0, [1] = "end" }, " ", indent)
            return out
         end,
      },
      ["cast"] = {
      },
      ["paren"] = {
         after = function(_: nil, node: Node, children: {Output}): Output
            local out: Output = { y = node.y, h = 0 }
            table.insert(out, "(")
            add_child(out, children[1], "", indent)
            table.insert(out, ")")
            return out
         end,
      },
      ["op"] = {
         after = function(_: nil, node: Node, children: {Output}): Output
            local out: Output = { y = node.y, h = 0 }
            if node.op.op == "@funcall" then
               add_child(out, children[1], "", indent)
               table.insert(out, "(")
               add_child(out, children[3], "", indent)
               table.insert(out, ")")
            elseif node.op.op == "@index" then
               add_child(out, children[1], "", indent)
               table.insert(out, "[")
               if node.e2.is_longstring then
                  table.insert(children[3], 1, " ")
                  table.insert(children[3], " ")
               end
               add_child(out, children[3], "", indent)
               table.insert(out, "]")
            elseif node.op.op == "as" then
               add_child(out, children[1], "", indent)
            elseif node.op.op == "is" then
               if node.e2.casttype.typename == "integer" then
                  table.insert(out, "math.type(")
                  add_child(out, children[1], "", indent)
                  table.insert(out, ") == \"integer\"")
               elseif node.e2.casttype.typename == "nil" then
                  add_child(out, children[1], "", indent)
                  table.insert(out, " == nil")
               else
                  table.insert(out, "type(")
                  add_child(out, children[1], "", indent)
                  table.insert(out, ") == \"")
                  add_child(out, children[3], "", indent)
                  table.insert(out, "\"")
               end
            elseif spaced_op[node.op.arity][node.op.op] or tight_op[node.op.arity][node.op.op] then
               local space = spaced_op[node.op.arity][node.op.op] and " " or ""
               if children[2] and node.op.prec > tonumber(children[2]) then
                  table.insert(children[1], 1, "(")
                  table.insert(children[1], ")")
               end
               if node.op.arity == 1 then
                  table.insert(out, node.op.op)
                  add_child(out, children[1], space, indent)
               elseif node.op.arity == 2 then
                  add_child(out, children[1], "", indent)
                  if space == " " then
                     table.insert(out, " ")
                  end
                  table.insert(out, node.op.op)
                  if children[4] and node.op.prec > tonumber(children[4]) then
                     table.insert(children[3], 1, "(")
                     table.insert(children[3], ")")
                  end
                  add_child(out, children[3], space, indent)
               end
            else
               error("unknown node op " .. node.op.op)
            end
            return out
         end,
      },
      ["variable"] = {
         after = function(_: nil, node: Node, _children: {Output}): Output
            local out: Output = { y = node.y, h = 0 }
            add_string(out, node.tk)
            return out
         end,
      },
      ["newtype"] = {
         after = function(_: nil, node: Node, _children: {Output}): Output
            local out: Output = { y = node.y, h = 0 }
            local nt = node.newtype
            if nt is TypeAliasType then
               table.insert(out, table.concat(nt.alias_to.names, "."))
            elseif nt is TypeDeclType then
               local def = nt.def
               if def is RecordLikeType then
                  table.insert(out, print_record_def(def))
               else
                  table.insert(out, "{}")
               end
            end
            return out
         end,
      },
      ["goto"] = {
         after = function(_: nil, node: Node, _children: {Output}): Output
            local out: Output = { y = node.y, h = 0 }
            table.insert(out, "goto ")
            table.insert(out, node.label)
            return out
         end,
      },
      ["label"] = {
         after = function(_: nil, node: Node, _children: {Output}): Output
            local out: Output = { y = node.y, h = 0 }
            table.insert(out, "::")
            table.insert(out, node.label)
            table.insert(out, "::")
            return out
         end,
      },
   }

   local visit_type: Visitor<nil, TypeName, Type, Output> = {}
   visit_type.cbs = {}
   local default_type_visitor = {
      after = function(_: nil, typ: Type, _children: {Output}): Output
         local out: Output = { y = typ.y or -1, h = 0 }
         local r = typ is NominalType and typ.resolved or typ
         local lua_type = primitive[r.typename] or "table"
         if r is RecordLikeType and r.is_userdata then
            lua_type = "userdata"
         end
         table.insert(out, lua_type)
         return out
      end,
   }

   visit_type.cbs["string"] = default_type_visitor
   visit_type.cbs["typedecl"] = default_type_visitor
   visit_type.cbs["typealias"] = default_type_visitor
   visit_type.cbs["typevar"] = default_type_visitor
   visit_type.cbs["typearg"] = default_type_visitor
   visit_type.cbs["function"] = default_type_visitor
   visit_type.cbs["thread"] = default_type_visitor
   visit_type.cbs["array"] = default_type_visitor
   visit_type.cbs["map"] = default_type_visitor
   visit_type.cbs["tupletable"] = default_type_visitor
   visit_type.cbs["record"] = default_type_visitor
   visit_type.cbs["enum"] = default_type_visitor
   visit_type.cbs["boolean"] = default_type_visitor
   visit_type.cbs["nil"] = default_type_visitor
   visit_type.cbs["number"] = default_type_visitor
   visit_type.cbs["integer"] = default_type_visitor
   visit_type.cbs["union"] = default_type_visitor
   visit_type.cbs["nominal"] = default_type_visitor
   visit_type.cbs["emptytable"] = default_type_visitor
   visit_type.cbs["literal_table_item"] = default_type_visitor
   visit_type.cbs["unresolved_emptytable_value"] = default_type_visitor
   visit_type.cbs["tuple"] = default_type_visitor
   visit_type.cbs["poly"] = default_type_visitor
   visit_type.cbs["any"] = default_type_visitor
   visit_type.cbs["unknown"] = default_type_visitor
   visit_type.cbs["invalid"] = default_type_visitor
   visit_type.cbs["unresolved"] = default_type_visitor
   visit_type.cbs["none"] = default_type_visitor

   visit_node.cbs["expression_list"] = visit_node.cbs["variable_list"]
   visit_node.cbs["argument_list"] = visit_node.cbs["variable_list"]
   visit_node.cbs["identifier"] = visit_node.cbs["variable"]
   visit_node.cbs["number"] = visit_node.cbs["variable"]
   visit_node.cbs["integer"] = visit_node.cbs["variable"]
   visit_node.cbs["string"] = visit_node.cbs["variable"]
   visit_node.cbs["nil"] = visit_node.cbs["variable"]
   visit_node.cbs["boolean"] = visit_node.cbs["variable"]
   visit_node.cbs["..."] = visit_node.cbs["variable"]
   visit_node.cbs["argument"] = visit_node.cbs["variable"]
   visit_node.cbs["type_identifier"] = visit_node.cbs["variable"]

   local out = recurse_node(nil, ast, visit_node, visit_type)
   if err then
      return nil, err
   end

   local code: Output
   if opts.preserve_newlines then
      code = { y = 1, h = 0 }
      add_child(code, out)
   else
      code = out
   end
   return (concat_output(code):gsub(" *\n", "\n"))
end

--------------------------------------------------------------------------------
-- Type collection for report
--------------------------------------------------------------------------------



--------------------------------------------------------------------------------
-- Type check
--------------------------------------------------------------------------------

local NONE = a_type("none", {})
local INVALID = a_type("invalid", {} as InvalidType)
local UNKNOWN = a_type("unknown", {} as UnknownType)
local CIRCULAR_REQUIRE = a_type("circular_require", {})

local FUNCTION = a_fn { args = va_args { ANY }, rets = va_args { ANY } }

--local NOMINAL_FILE = a_type("nominal", { names = {"FILE"} } as NominalType)
local XPCALL_MSGH_FUNCTION = a_fn { args = { ANY }, rets = { } }

--local USERDATA = ANY -- Placeholder for maybe having a userdata "primitive" type

local numeric_binop = {
   ["number"] = {
      ["number"] = NUMBER,
      ["integer"] = NUMBER,
   },
   ["integer"] = {
      ["integer"] = INTEGER,
      ["number"] = NUMBER,
   },
}

local float_binop = {
   ["number"] = {
      ["number"] = NUMBER,
      ["integer"] = NUMBER,
   },
   ["integer"] = {
      ["integer"] = NUMBER,
      ["number"] = NUMBER,
   },
}

local integer_binop = {
   ["number"] = {
      ["number"] = INTEGER,
      ["integer"] = INTEGER,
   },
   ["integer"] = {
      ["integer"] = INTEGER,
      ["number"] = INTEGER,
   },
}

local relational_binop = {
   ["number"] = {
      ["integer"] = BOOLEAN,
      ["number"] = BOOLEAN,
   },
   ["integer"] = {
      ["number"] = BOOLEAN,
      ["integer"] = BOOLEAN,
   },
   ["string"] = {
      ["string"] = BOOLEAN,
   },
   ["boolean"] = {
      ["boolean"] = BOOLEAN,
   },
}

local equality_binop = {
   ["number"] = {
      ["number"] = BOOLEAN,
      ["integer"] = BOOLEAN,
      ["nil"] = BOOLEAN,
   },
   ["integer"] = {
      ["number"] = BOOLEAN,
      ["integer"] = BOOLEAN,
      ["nil"] = BOOLEAN,
   },
   ["string"] = {
      ["string"] = BOOLEAN,
      ["nil"] = BOOLEAN,
   },
   ["boolean"] = {
      ["boolean"] = BOOLEAN,
      ["nil"] = BOOLEAN,
   },
   ["record"] = {
      ["emptytable"] = BOOLEAN,
      ["record"] = BOOLEAN,
      ["nil"] = BOOLEAN,
   },
   ["array"] = {
      ["emptytable"] = BOOLEAN,
      ["array"] = BOOLEAN,
      ["nil"] = BOOLEAN,
   },
   ["map"] = {
      ["emptytable"] = BOOLEAN,
      ["map"] = BOOLEAN,
      ["nil"] = BOOLEAN,
   },
   ["thread"] = {
      ["thread"] = BOOLEAN,
      ["nil"] = BOOLEAN,
   }
}

local unop_types: {string:{string:Type}} = {
   ["#"] = {
      ["string"] = INTEGER,
      ["array"] = INTEGER,
      ["tupletable"] = INTEGER,
      ["map"] = INTEGER,
      ["emptytable"] = INTEGER,
   },
   ["-"] = {
      ["number"] = NUMBER,
      ["integer"] = INTEGER,
   },
   ["~"] = {
      ["number"] = INTEGER,
      ["integer"] = INTEGER,
   },
   ["not"] = {
      ["string"] = BOOLEAN,
      ["number"] = BOOLEAN,
      ["integer"] = BOOLEAN,
      ["boolean"] = BOOLEAN,
      ["record"] = BOOLEAN,
      ["array"] = BOOLEAN,
      ["tupletable"] = BOOLEAN,
      ["map"] = BOOLEAN,
      ["emptytable"] = BOOLEAN,
      ["thread"] = BOOLEAN,
   },
}

local unop_to_metamethod: {string:string} = {
   ["#"] = "__len",
   ["-"] = "__unm",
   ["~"] = "__bnot",
}

local binop_types: {string:{TypeName:{TypeName:Type}}} = {
   ["+"] = numeric_binop,
   ["-"] = numeric_binop,
   ["*"] = numeric_binop,
   ["%"] = numeric_binop,
   ["/"] = float_binop,
   ["//"] = numeric_binop,
   ["^"] = float_binop,
   ["&"] = integer_binop,
   ["|"] = integer_binop,
   ["<<"] = integer_binop,
   [">>"] = integer_binop,
   ["~"] = integer_binop,
   ["=="] = equality_binop,
   ["~="] = equality_binop,
   ["<="] = relational_binop,
   [">="] = relational_binop,
   ["<"] = relational_binop,
   [">"] = relational_binop,
   ["or"] = {
      ["boolean"] = {
         ["boolean"] = BOOLEAN,
         ["function"] = FUNCTION, -- HACK
      },
      ["number"] = {
         ["integer"] = NUMBER,
         ["number"] = NUMBER,
         ["boolean"] = BOOLEAN,
      },
      ["integer"] = {
         ["integer"] = INTEGER,
         ["number"] = NUMBER,
         ["boolean"] = BOOLEAN,
      },
      ["string"] = {
         ["string"] = STRING,
         ["boolean"] = BOOLEAN,
         ["enum"] = STRING,
      },
      ["function"] = {
         ["boolean"] = BOOLEAN,
      },
      ["array"] = {
         ["boolean"] = BOOLEAN,
      },
      ["record"] = {
         ["boolean"] = BOOLEAN,
      },
      ["map"] = {
         ["boolean"] = BOOLEAN,
      },
      ["enum"] = {
         ["string"] = STRING,
      },
      ["thread"] = {
         ["boolean"] = BOOLEAN,
      }
   },
   [".."] = {
      ["string"] = {
         ["string"] = STRING,
         ["enum"] = STRING,
         ["number"] = STRING,
         ["integer"] = STRING,
      },
      ["number"] = {
         ["integer"] = STRING,
         ["number"] = STRING,
         ["string"] = STRING,
         ["enum"] = STRING,
      },
      ["integer"] = {
         ["integer"] = STRING,
         ["number"] = STRING,
         ["string"] = STRING,
         ["enum"] = STRING,
      },
      ["enum"] = {
         ["number"] = STRING,
         ["integer"] = STRING,
         ["string"] = STRING,
         ["enum"] = STRING,
      }
   },
}

local binop_to_metamethod: {string:string} = {
   ["+"] = "__add",
   ["-"] = "__sub",
   ["*"] = "__mul",
   ["/"] = "__div",
   ["%"] = "__mod",
   ["^"] = "__pow",
   ["//"] = "__idiv",
   ["&"] = "__band",
   ["|"] = "__bor",
   ["~"] = "__bxor",
   ["<<"] = "__shl",
   [">>"] = "__shr",
   [".."] = "__concat",
   ["=="] = "__eq",
   ["<"] = "__lt",
   ["<="] = "__le",
   ["@index"] = "__index",
   ["is"] = "__is",
}

local function is_unknown(t: Type): boolean
   return t.typename == "unknown"
       or t.typename == "unresolved_emptytable_value"
end

local function display_typevar(typevar: string): string
   return TL_DEBUG and typevar or (typevar:gsub("@.*", ""))
end

local function show_fields(t: RecordLikeType, show: function(Type):(string)): string
   if t.declname then
      return " " .. t.declname
   end

   local out: {string} = {}
   if t.typeargs then
      table.insert(out, "<")
      local typeargs = {}
      for _, v in ipairs(t.typeargs) do
         table.insert(typeargs, show(v))
      end
      table.insert(out, table.concat(typeargs, ", "))
      table.insert(out, ">")
   end
   table.insert(out, " (")
   if t.elements then
      table.insert(out, "{" .. show(t.elements) .. "}")
   end
   local fs = {}
   for _, k in ipairs(t.field_order) do
      local v = t.fields[k]
      table.insert(fs, k .. ": " .. show(v))
   end
   table.insert(out, table.concat(fs, "; "))
   table.insert(out, ")")
   return table.concat(out)
end

local function show_type_base(t: Type, short: boolean, seen: {Type:string}): string
   -- FIXME this is a control for recursively built types, which should in principle not exist
   if seen[t] then
      return seen[t]
   end
   seen[t] = "..."

   local function show(typ: Type): string
      return show_type(typ, short, seen)
   end

   if t is NominalType then
      if #t.names == 1 and t.names[1] == "@self" then
         return "self"
      end

      if t.typevals then
         local out = { table.concat(t.names, "."), "<" }
         local vals: {string} = {}
         for _, v in ipairs(t.typevals) do
            table.insert(vals, show(v))
         end
         table.insert(out, table.concat(vals, ", "))
         table.insert(out, ">")
         return table.concat(out)
      else
         return table.concat(t.names, ".")
      end
   elseif t is TupleType then
      local out: {string} = {}
      for _, v in ipairs(t.tuple) do
         table.insert(out, show(v))
      end
      local list = table.concat(out, ", ")
      if short then
         return list
      end
      return "(" .. list .. ")"
   elseif t is TupleTableType then
      local out: {string} = {}
      for _, v in ipairs(t.types) do
         table.insert(out, show(v))
      end
      return "{" .. table.concat(out, ", ") .. "}"
   elseif t is PolyType then
      local out: {string} = {}
      for _, v in ipairs(t.types) do
         table.insert(out, show(v))
      end
      return "polymorphic function (with types " .. table.concat(out, " and ") .. ")"
   elseif t is UnionType then
      local out: {string} = {}
      for _, v in ipairs(t.types) do
         table.insert(out, show(v))
      end
      return table.concat(out, " | ")
   elseif t is EmptyTableType then
      return "{}"
   elseif t is MapType then
      return "{" .. show(t.keys) .. " : " .. show(t.values) .. "}"
   elseif t is ArrayType then
      return "{" .. show(t.elements) .. "}"
   elseif t is EnumType then
      return t.declname or "enum"
   elseif t is RecordLikeType then
      return short and t.typename or t.typename .. show_fields(t, show)
   elseif t is FunctionType then
      local out: {string} = {"function"}
      if t.typeargs then
         table.insert(out, "<")
         local typeargs = {}
         for _, v in ipairs(t.typeargs) do
            table.insert(typeargs, show(v))
         end
         table.insert(out, table.concat(typeargs, ", "))
         table.insert(out, ">")
      end
      table.insert(out, "(")
      local args = {}
      if t.is_method then
         table.insert(args, "self")
      end
      for i, v in ipairs(t.args.tuple) do
         if not t.is_method or i > 1 then
            table.insert(args, ((i == #t.args.tuple and t.args.is_va) and "...: "
                               or (i > t.min_arity) and "? "
                               or "") .. show(v))
         end
      end
      table.insert(out, table.concat(args, ", "))
      table.insert(out, ")")
      if t.rets.tuple and #t.rets.tuple > 0 then
         table.insert(out, ": ")
         local rets = {}
         for i, v in ipairs(t.rets.tuple) do
            table.insert(rets, show(v) .. (i == #t.rets.tuple and t.rets.is_va and "..." or ""))
         end
         table.insert(out, table.concat(rets, ", "))
      end
      return table.concat(out)
   elseif t.typename == "number"
       or t.typename == "integer"
       or t.typename == "boolean"
       or t.typename == "thread" then
      return t.typename
   elseif t is StringType then
      if short then
         return "string"
      else
         return t.typename ..
                (t.literal and string.format(" %q", t.literal) or "")
      end
   elseif t is TypeVarType then
      return display_typevar(t.typevar)
   elseif t is TypeArgType then
      return display_typevar(t.typearg)
   elseif t is UnresolvableTypeArgType then
      return display_typevar(t.typearg) .. " (unresolved generic)"
   elseif is_unknown(t) then
      return "<unknown type>"
   elseif t.typename == "invalid" then
      return "<invalid type>"
   elseif t.typename == "any" then
      return "<any type>"
   elseif t.typename == "nil" then
      return "nil"
   elseif t.typename == "none" then
      return ""
   elseif t is TypeAliasType then
      return "type " .. show(t.alias_to)
   elseif t is TypeDeclType then
      return "type " .. show(t.def)
   else
      return "<" .. t.typename .. " " .. tostring(t) .. ">"
   end
end

local function inferred_msg(t: Type): string
   return " (inferred at "..t.inferred_at.filename..":"..t.inferred_at.y..":"..t.inferred_at.x..")"
end

show_type = function(t: Type, short?: boolean, seen?: {Type:string}): string
   seen = seen or {}
   if seen[t] then
      return seen[t]
   end
   local ret = show_type_base(t, short, seen)
   if t.inferred_at then
      ret = ret .. inferred_msg(t)
   end
   seen[t] = ret
   return ret
end

local function search_for(module_name: string, suffix: string, path: string, tried: {string}): string, FILE, {string}
   for entry in path:gmatch("[^;]+") do
      local slash_name = module_name:gsub("%.", "/")
      local filename = entry:gsub("?", slash_name)
      local tl_filename = filename:gsub("%.lua$", suffix)
      local fd = io.open(tl_filename, "rb")
      if fd then
         return tl_filename, fd, tried
      end
      table.insert(tried, "no file '" .. tl_filename .. "'")
   end
   return nil, nil, tried
end

local function filename_to_module_name(filename: string): string
   local path = os.getenv("TL_PATH") or package.path
   for entry in path:gmatch("[^;]+") do
      entry = entry:gsub("%.", "%%.")
      local lua_pat = "^" .. entry:gsub("%?", ".+") .. "$"
      local d_tl_pat = lua_pat:gsub("%%.lua%$", "%%.d%%.tl$")
      local tl_pat = lua_pat:gsub("%%.lua%$", "%%.tl$")

      for _, pat in ipairs({ tl_pat, d_tl_pat, lua_pat }) do
         local cap = filename:match(pat)
         if cap then
            return (cap:gsub("[/\\]", "."))
         end
      end
   end

   -- fallback:
   return (filename:gsub("%.lua$", ""):gsub("%.d%.tl$", ""):gsub("%.tl$", ""):gsub("[/\\]", "."))
end

function tl.search_module(module_name: string, search_dtl: boolean): string, FILE, {string}
   local found: string
   local fd: FILE
   local tried: {string} = {}
   local path = os.getenv("TL_PATH") or package.path
   if search_dtl then
      found, fd, tried = search_for(module_name, ".d.tl", path, tried)
      if found then
         return found, fd
      end
   end
   found, fd, tried = search_for(module_name, ".tl", path, tried)
   if found then
      return found, fd
   end
   found, fd, tried = search_for(module_name, ".lua", path, tried)
   if found then
      return found, fd
   end
   return nil, nil, tried
end

local function require_module(module_name: string, feat_lax: boolean, env: Env): Type, boolean
   local mod = env.modules[module_name]
   if mod then
      return mod, true
   end

   local found, fd = tl.search_module(module_name, true)
   if found and (feat_lax or found:match("tl$") as boolean) then
      local found_result, err: Result, string = tl.process(found, env, module_name, fd)
      assert(found_result, err)

      return found_result.type, true
   elseif fd then
      fd:close()
   end

   return INVALID, found ~= nil
end

local compat_code_cache: {string:Node} = {}

local function add_compat_entries(program: Node, used_set: {string: boolean}, gen_compat: GenCompat)
   if gen_compat == "off" or not next(used_set) then
      return
   end

   local tl_debug = TL_DEBUG
   TL_DEBUG = nil

   local used_list: {string} = sorted_keys(used_set)

   local compat_loaded = false

   local n = 1
   local function load_code(name: string, text: string)
      local code: Node = compat_code_cache[name]
      if not code then
         code = tl.parse(text, "@internal")
         tl.type_check(code, "@internal", "@internal", { feat_lax = "off", gen_compat = "off" })
         compat_code_cache[name] = code
      end
      for _, c in ipairs(code) do
         table.insert(program, n, c)
         n = n + 1
      end
   end

   local function req(m: string): string
      return (gen_compat == "optional")
             and "pcall(require, '" .. m .. "')"
             or  "true, require('" .. m .. "')"
   end

   for _, name in ipairs(used_list) do
      if name == "table.unpack" then
         load_code(name, "local _tl_table_unpack = unpack or table.unpack")
      elseif name == "bit32" then
         load_code(name, "local bit32 = bit32; if not bit32 then local p, m = " .. req("bit32") .. "; if p then bit32 = m end")
      elseif name == "mt" then
         load_code(name, "local _tl_mt = function(m, s, a, b) return (getmetatable(s == 1 and a or b)[m](a, b) end")
      elseif name == "math.maxinteger" then
         load_code(name, "local _tl_math_maxinteger = math.maxinteger or math.pow(2,53)")
      elseif name == "math.mininteger" then
         load_code(name, "local _tl_math_mininteger = math.mininteger or -math.pow(2,53) - 1")
      else
         if not compat_loaded then
            load_code("compat", "local _tl_compat; if (tonumber((_VERSION or ''):match('[%d.]*$')) or 0) < 5.3 then local p, m = " .. req("compat53.module") .. "; if p then _tl_compat = m end")
            compat_loaded = true
         end
         load_code(name, (("local $NAME = _tl_compat and _tl_compat.$NAME or $NAME"):gsub("$NAME", name)))
      end
   end
   program.y = 1

   TL_DEBUG = tl_debug
end

local function get_stdlib_compat(): {string:boolean}
   return {
      ["io"] = true,
      ["math"] = true,
      ["string"] = true,
      ["table"] = true,
      ["utf8"] = true,
      ["coroutine"] = true,
      ["os"] = true,
      ["package"] = true,
      ["debug"] = true,
      ["load"] = true,
      ["loadfile"] = true,
      ["assert"] = true,
      ["pairs"] = true,
      ["ipairs"] = true,
      ["pcall"] = true,
      ["xpcall"] = true,
      ["rawlen"] = true,
   }
end

local bit_operators: {string:string} = {
   ["&"] = "band",
   ["|"] = "bor",
   ["~"] = "bxor",
   [">>"] = "rshift",
   ["<<"] = "lshift",
}

local function convert_node_to_compat_call(node: Node, mod_name: string, fn_name: string, e1: Node, e2?: Node)
   node.op.op = "@funcall"
   node.op.arity = 2
   node.op.prec = 100
   node.e1 = { y = node.y, x = node.x, kind = "op", op = an_operator(node, 2, ".") }
   node.e1.e1 = { y = node.y, x = node.x, kind = "identifier", tk = mod_name }
   node.e1.e2 = { y = node.y, x = node.x, kind = "identifier", tk = fn_name }
   node.e2 = { y = node.y, x = node.x, kind = "expression_list" }
   node.e2[1] = e1
   node.e2[2] = e2
end

local function convert_node_to_compat_mt_call(node: Node, mt_name: string, which_self: integer, e1: Node, e2?: Node)
   node.op.op = "@funcall"
   node.op.arity = 2
   node.op.prec = 100
   node.e1 = { y = node.y, x = node.x, kind = "identifier", tk = "_tl_mt" }
   node.e2 = { y = node.y, x = node.x, kind = "expression_list" }
   node.e2[1] = { y = node.y, x = node.x, kind = "string", tk = "\"" .. mt_name .. "\"" }
   node.e2[2] = { y = node.y, x = node.x, kind = "integer", tk = tostring(which_self) }
   node.e2[3] = e1
   node.e2[4] = e2
end

local stdlib_globals: {string:Variable} = nil
local globals_typeid: integer
local fresh_typevar_ctr = 1

tl.new_env = function(opts?: EnvOptions): Env, string
   opts = opts or {}

   local env: Env = {
      modules = {},
      loaded = {},
      loaded_order = {},
      globals = {},
      defaults = opts.defaults or {},
   }

   if not stdlib_globals then
      local program, syntax_errors = tl.parse(stdlib, "stdlib.d.tl")
      assert(#syntax_errors == 0)
      local result = tl.type_check(program, "@stdlib", "@stdlib", {}, env)
      assert(#result.type_errors == 0)
      stdlib_globals = env.globals;

      -- special cases for compatibility
      local math_t = (stdlib_globals["math"].t as TypeDeclType).def as RecordType
      local table_t = (stdlib_globals["table"].t as TypeDeclType).def as RecordType
      local integer_compat = a_type("integer", { needs_compat = true })
      math_t.fields["maxinteger"] = integer_compat
      math_t.fields["mininteger"] = integer_compat
      table_t.fields["unpack"].needs_compat = true

      -- only global scope and vararg functions accept `...`:
      -- `@is_va` is an internal sentinel value which is
      -- `any` if `...` is accepted in this scope or `nil` if it isn't.
      stdlib_globals["..."] = { t = a_vararg { STRING } }
      stdlib_globals["@is_va"] = { t = ANY }

      env.globals = {}
   end

   local stdlib_compat = get_stdlib_compat()
   for name, var in pairs(stdlib_globals) do
      env.globals[name] = var
      var.needs_compat = stdlib_compat[name]
      local t = var.t
      if t is TypeDeclType then
         -- make standard library tables available as modules for require()
         env.modules[name] = t
      end
   end

   if opts.predefined_modules then
      for _, name in ipairs(opts.predefined_modules) do
         local module_type = require_module(name, env.defaults.feat_lax == "on", env)

         if module_type == INVALID then
            return nil, string.format("Error: could not predefine module '%s'", name)
         end
      end
   end

   return env
end


do
   local type Scope = {string:Variable}
   local type TypeRelations = {TypeName:{TypeName:CompareTypes}}

   local record TypeChecker
      env: Env
      st: {Scope}

      errs: Errors
      module_type: Type

      subtype_relations: TypeRelations
      eqtype_relations: TypeRelations
      type_priorities: {TypeName:integer}

      all_needs_compat: {string:boolean}
      dependencies: {string:string}
      collector: TypeCollector

      gen_compat: GenCompat
      gen_target: GenTarget
      feat_arity: boolean
      feat_lax: boolean

      same_type: function(TypeChecker, Type, Type): boolean, {Error}
      is_a: function(TypeChecker, Type, Type): boolean, {Error}

      get_rets: function(TupleType): TupleType
   end

   local enum VarUse
      "use"
      "lvalue"
      "use_type"
      "check_only"
   end

   function TypeChecker:find_var(name: string, use?: VarUse): Variable, integer, Attribute
      for i = #self.st, 1, -1 do
         local scope = self.st[i]
         local var = scope[name]
         if var then
            if use == "lvalue" and var.is_narrowed then
               if var.narrowed_from then
                  var.used = true
                  return { t = var.narrowed_from, attribute = var.attribute }, i, var.attribute
               end
            else
               if i == 1 and var.needs_compat then
                  self.all_needs_compat[name] = true
               end
               if use == "use_type" then
                  var.used_as_type = true
               elseif use ~= "check_only" then
                  var.used = true
               end
               return var, i, var.attribute
            end
         end
      end
   end

   function TypeChecker:simulate_g(): RecordType, Attribute
      -- this is a static approximation of _G
      local globals: {string:Type} = {}
      for k, v in pairs(self.st[1]) do
         if k:sub(1,1) ~= "@" then
            globals[k] = v.t
         end
      end
      return {
         typeid = globals_typeid,
         typename = "record",
         field_order = sorted_keys(globals),
         fields = globals,
      }, nil
   end

   local type ResolveType = function<S>(S, Type): Type
   local typevar_resolver: function<S>(s: S, typ: Type, fn_var?: ResolveType<S>, fn_arg?: ResolveType<S>): boolean, Type, {Error}

   local function fresh_typevar(_: nil, t: TypeVarType): Type, Type, boolean
      return a_type("typevar", {
         typevar = (t.typevar:gsub("@.*", "")) .. "@" .. fresh_typevar_ctr,
         constraint = t.constraint,
      } as TypeVarType)
   end

   local function fresh_typearg(_: nil, t: TypeArgType): Type
      return a_type("typearg", {
         typearg = (t.typearg:gsub("@.*", "")) .. "@" .. fresh_typevar_ctr,
         constraint = t.constraint,
      } as TypeArgType)
   end

   function TypeChecker:ensure_fresh_typeargs<T is Type>(t: T): T
      if not t is HasTypeArgs then
         return t
      end

      fresh_typevar_ctr = fresh_typevar_ctr + 1
      local ok: boolean
      ok, t = typevar_resolver(nil, t, fresh_typevar, fresh_typearg)
      assert(ok, "Internal Compiler Error: error creating fresh type variables")
      return t
   end

   function TypeChecker:find_var_type(name: string, use?: VarUse): Type, Attribute, Type
      local var = self:find_var(name, use)
      if var then
         local t = var.t
         if t is UnresolvedTypeArgType then
            return nil, nil, t.constraint
         end
         t = self:ensure_fresh_typeargs(t)
         return t, var.attribute
      end
   end

   local function ensure_not_abstract(t: Type): boolean, string
      if t is FunctionType and t.macroexp then
         return nil, "macroexps are abstract; consider using a concrete function"
      elseif t is TypeDeclType then
         local def = t.def
         if def is InterfaceType then
            return nil, "interfaces are abstract; consider using a concrete record"
         end
      end
      return true
   end

   function TypeChecker:find_type(names: {string}, accept_typearg?: boolean): Type
      local typ = self:find_var_type(names[1], "use_type")
      if not typ then
         return nil
      end
      if typ is NominalType and typ.found then
         typ = typ.found
      end
      for i = 2, #names do
         if typ is TypeDeclType then
            typ = typ.def
         end

         local fields = typ is RecordLikeType and typ.fields
         if not fields then
            return nil
         end

         typ = fields[names[i]]
         if typ == nil then
            return nil
         end

         typ = self:ensure_fresh_typeargs(typ)
         if typ is NominalType and typ.found then
            typ = typ.found
         end
      end
      if typ is TypeDeclType or typ is TypeAliasType then
         return typ
      elseif accept_typearg and typ is TypeArgType then
         return typ
      end
   end

   local function type_for_union(t: Type): string, Type
      if t is TypeDeclType then
         return type_for_union(t.def), t.def
      elseif t is TypeAliasType then
         return type_for_union(t.alias_to), t.alias_to
      elseif t is TupleType then
         return type_for_union(t.tuple[1]), t.tuple[1]
      elseif t is NominalType then
         local typedecl = t.found
         if not typedecl then
            return "invalid"
         end
         return type_for_union(typedecl)
      elseif t is RecordLikeType then
         if t.is_userdata then
            return "userdata", t
         end
         return "table", t
      elseif table_types[t.typename] then
         return "table", t
      else
         return t.typename, t
      end
   end

   local function is_valid_union(typ: UnionType): boolean, string
      -- check for limitations in our union support
      -- due to codegen limitations (we only check with type() so far)
      local n_table_types = 0
      local n_table_is_types = 0
      local n_function_types = 0
      local n_userdata_types = 0
      local n_userdata_is_types = 0
      local n_string_enum = 0
      local has_primitive_string_type = false
      for _, t in ipairs(typ.types) do
         local ut, rt = type_for_union(t)
         if ut == "userdata" then -- must be tested before table_types
            assert(rt is RecordLikeType)
            if rt.meta_fields and rt.meta_fields["__is"] then
               n_userdata_is_types = n_userdata_is_types + 1
               if n_userdata_types > 0 then
                  return false, "cannot mix userdata types with and without __is metamethod: %s"
               end
            else
               n_userdata_types = n_userdata_types + 1
               if n_userdata_types > 1 then
                  return false, "cannot discriminate a union between multiple userdata types: %s"
               end
               if n_userdata_is_types > 0 then
                  return false, "cannot mix userdata types with and without __is metamethod: %s"
               end
            end
         elseif ut == "table" then
            if rt is RecordLikeType and rt.meta_fields and rt.meta_fields["__is"] then
               n_table_is_types = n_table_is_types + 1
               if n_table_types > 0 then
                  return false, "cannot mix table types with and without __is metamethod: %s"
               end
            else
               n_table_types = n_table_types + 1
               if n_table_types > 1 then
                  return false, "cannot discriminate a union between multiple table types: %s"
               end
               if n_table_is_types > 0 then
                  return false, "cannot mix table types with and without __is metamethod: %s"
               end
            end
         elseif ut == "function" then
            n_function_types = n_function_types + 1
            if n_function_types > 1 then
               return false, "cannot discriminate a union between multiple function types: %s"
            end
         elseif ut == "enum" or (ut == "string" and not has_primitive_string_type) then
            n_string_enum = n_string_enum + 1
            if n_string_enum > 1 then
               return false, "cannot discriminate a union between multiple string/enum types: %s"
            end
            if ut == "string" then
               has_primitive_string_type = true
            end
         elseif ut == "invalid" then
            return false, nil -- error message comes from invalid type
         end
      end
      return true
   end

   local function show_arity(f: FunctionType): string
      local nfargs = #f.args.tuple
      return f.min_arity < nfargs
             and "at least " .. f.min_arity .. (f.args.is_va and "" or " and at most " .. nfargs)
             or  tostring(nfargs or 0)
   end

   local function resolve_typedecl(t: Type): Type
      if t is TypeDeclType then
         return t.def
      elseif t is TypeAliasType then
         return t.alias_to
      else
         return t
      end
   end

   local no_nested_types: {string:boolean} = {
      ["string"] = true,
      ["number"] = true,
      ["integer"] = true,
      ["boolean"] = true,
      ["thread"] = true,
      ["any"] = true,
      ["enum"] = true,
      ["nil"] = true,
      ["unknown"] = true,
   }

   typevar_resolver = function<S>(self: S, typ: Type, fn_var?: ResolveType<S>, fn_arg?: ResolveType<S>): boolean, Type, {Error}
      local errs: {Error}
      local seen: {Type:Type} = {}
      local resolved: {string:boolean} = {}

      local function resolve<T is Type>(t: T, all_same: boolean): T, boolean
         local same = true

         -- avoid copies of types that do not contain type variables
         if no_nested_types[t.typename] or (t is NominalType and not t.typevals) then
            return t, all_same
         end

         if seen[t] then
            return seen[t], all_same
         end

         local orig_t = t
         if t is TypeVarType then
            local rt = fn_var(self, t)
            if rt then
               resolved[t.typevar] = true
               if no_nested_types[rt.typename] or (rt is NominalType and not rt.typevals) then
                  seen[orig_t] = rt
                  return rt, false
               end
               same = false
               t = rt
            end
         end

         local copy: Type = {}
         seen[orig_t] = copy

         copy.typename = t.typename
         copy.filename = t.filename
         copy.x = t.x
         copy.y = t.y

         if t is ArrayType then
            assert(copy is ArrayType)

            copy.elements, same = resolve(t.elements, same)
            -- inferred_len is not propagated
         elseif t is TypeArgType then
            if fn_arg then
               copy = fn_arg(self, t)
            else
               assert(copy is TypeArgType)
               copy.typearg = t.typearg
               if t.constraint then
                  copy.constraint, same = resolve(t.constraint, same)
               end
            end
         elseif t is UnresolvableTypeArgType then
            assert(copy is UnresolvableTypeArgType)
            copy.typearg = t.typearg
         elseif t is TypeVarType then
            assert(copy is TypeVarType)
            copy.typevar = t.typevar
            if t.constraint then
               copy.constraint, same = resolve(t.constraint, same)
            end
         elseif t is TypeDeclType then
            assert(copy is TypeDeclType)
            copy.def, same = resolve(t.def, same)
         elseif t is TypeAliasType then
            assert(copy is TypeAliasType)
            copy.alias_to, same = resolve(t.alias_to, same)
            copy.is_nested_alias = t.is_nested_alias
         elseif t is NominalType then
            assert(copy is NominalType)
            copy.names = t.names
            copy.typevals = {}
            for i, tf in ipairs(t.typevals) do
               copy.typevals[i], same = resolve(tf, same)
            end
            copy.found = t.found
         elseif t is FunctionType then
            assert(copy is FunctionType)

            if t.typeargs then
               copy.typeargs = {}
               for i, tf in ipairs(t.typeargs) do
                  copy.typeargs[i], same = resolve(tf, same) as (TypeArgType, boolean)
               end
            end

            copy.min_arity = t.min_arity
            copy.is_method = t.is_method
            copy.args, same = resolve(t.args, same) as (TupleType, boolean)
            copy.rets, same = resolve(t.rets, same) as (TupleType, boolean)
         elseif t is RecordLikeType then
            assert(copy is RecordType or copy is InterfaceType)
            copy.declname = t.declname

            if t.typeargs then
               copy.typeargs = {}
               for i, tf in ipairs(t.typeargs) do
                  copy.typeargs[i], same = resolve(tf, same) as (TypeArgType, boolean)
               end
            end

            -- checking array interface
            if t.elements then
               copy.elements, same = resolve(t.elements, same)
            end

            copy.is_userdata = t.is_userdata

            copy.fields = {}
            copy.field_order = {}
            for i, k in ipairs(t.field_order) do
               copy.field_order[i] = k
               copy.fields[k], same = resolve(t.fields[k], same)
            end

            if t.meta_fields then
               copy.meta_fields = {}
               copy.meta_field_order = {}
               for i, k in ipairs(t.meta_field_order) do
                  copy.meta_field_order[i] = k
                  copy.meta_fields[k], same = resolve(t.meta_fields[k], same)
               end
            end
         elseif t is MapType then
            assert(copy is MapType)
            copy.keys, same = resolve(t.keys, same)
            copy.values, same = resolve(t.values, same)
         elseif t is UnionType then
            assert(copy is UnionType)
            copy.types = {}
            for i, tf in ipairs(t.types) do
               copy.types[i], same = resolve(tf, same)
            end

            local _, err = is_valid_union(copy)
            if err then
               errs = errs or {}
               table.insert(errs, Err(t, err, copy))
            end
         elseif t is PolyType then
            assert(copy is PolyType)
            copy.types = {}
            for i, tf in ipairs(t.types) do
               copy.types[i], same = resolve(tf, same) as (FunctionType, boolean)
            end
         elseif t is TupleTableType then
            assert(copy is TupleTableType)
            copy.types = {}
            for i, tf in ipairs(t.types) do
               copy.types[i], same = resolve(tf, same)
            end
         elseif t is TupleType then
            assert(copy is TupleType)
            copy.is_va = t.is_va
            copy.tuple = {}
            for i, tf in ipairs(t.tuple) do
               copy.tuple[i], same = resolve(tf, same)
            end
         end

         copy.typeid = same and orig_t.typeid or new_typeid()
         return copy, same and all_same
      end

      local copy, same = resolve(typ, true)
      if errs then
         return false, INVALID, errs
      end

      if (not same) and
         (copy is FunctionType or copy is RecordLikeType) and
         copy.typeargs
      then
         for i = #copy.typeargs, 1, -1 do
            if resolved[copy.typeargs[i].typearg] then
               table.remove(copy.typeargs, i)
            end
         end
         if not copy.typeargs[1] then
            copy.typeargs = nil
         end
      end
      return true, copy
   end

   local function resolve_typevar(tc: TypeChecker, t: TypeVarType): Type
      local rt = tc:find_var_type(t.typevar)
      if not rt then
         return nil
      elseif rt is StringType then
         -- tk is not propagated
         return STRING
      end
      return rt
   end



   function TypeChecker:infer_emptytable(emptytable: EmptyTableType, fresh_t: Type)
      local is_global = (emptytable.declared_at and emptytable.declared_at.kind == "global_declaration")
      local nst = is_global and 1 or #self.st
      for i = nst, 1, -1 do
         local scope = self.st[i]
         if scope[emptytable.assigned_to] then
            scope[emptytable.assigned_to] = { t = fresh_t }
         end
      end
   end

   local function resolve_tuple(t: Type): Type
      if t is TupleType then
         t = t.tuple[1]
      end
      if t == nil then
         return NIL
      end
      return t
   end


   function TypeChecker:check_if_redeclaration(new_name: string, at: Node)
      local old <const> = self:find_var(new_name, "check_only")
      if old then
         self.errs:redeclaration_warning(at, old)
      end
   end


   local function type_at<T is Type>(w: Where, t: T): T
      t.x = w.x
      t.y = w.y
      t.filename = w.filename
      return t
   end

   function TypeChecker:resolve_typevars_at<T is Type>(where: Where, t: T): T
      assert(where)
      local ok, ret, errs = typevar_resolver(self, t, resolve_typevar)
      if not ok then
         assert(where.y)
         self.errs:add_prefixing(where, errs, "")
      end

      if ret == t or t.typename == "typevar" then
         ret = shallow_copy_table(ret)
      end
      return type_at(where, ret)
   end

   function TypeChecker:infer_at<T is Type>(where: Where, t: T): T
      local ret = self:resolve_typevars_at(where, t)
      if ret.typename == "invalid" then
         ret = t -- errors are produced by resolve_typevars_at
      end

      if ret == t or t.typename == "typevar" then
         ret = shallow_copy_table(ret)
      end
      ret.inferred_at = where
      return ret
   end

   local function drop_constant_value(t: Type): Type
      if t is StringType and t.literal then
         local ret = shallow_copy_table(t)
         ret.literal = nil
         return ret
      end
      return t
   end

   local get_unresolved: function(scope?: Scope): UnresolvedType
   local find_unresolved: function(level?: integer): UnresolvedType

   function TypeChecker:add_to_scope(node: Node, name: string, t: Type, attribute: Attribute, narrow: Narrow, dont_check_redeclaration: boolean): Variable
      local scope <const> = self.st[#self.st]
      local var = scope[name]
      if narrow then
         if var then
            if var.is_narrowed then
               var.t = t
               return var
            end

            var.is_narrowed = narrow
            var.narrowed_from = var.t
            var.t = t
         else
            var = { t = t, attribute = attribute, is_narrowed = narrow, declared_at = node }
            scope[name] = var
         end

         local unresolved = get_unresolved(scope)
         unresolved.narrows[name] = true

         return var
      end

      if not dont_check_redeclaration
         and node
         and name ~= "self"
         and name ~= "..."
         and name:sub(1, 1) ~= "@"
      then
         self:check_if_redeclaration(name, node)
      end

      if var and not var.used then
         -- the old var is removed from the scope and won't be checked when it closes,
         -- so check it here
         self.errs:unused_warning(name, var)
      end

      var = { t = t, attribute = attribute, is_narrowed = nil, declared_at = node }
      scope[name] = var

      return var
   end

   function TypeChecker:add_var(node: Node, name: string, t: Type, attribute?: Attribute, narrow?: Narrow, dont_check_redeclaration?: boolean): Variable
      if self.feat_lax and node and is_unknown(t) and (name ~= "self" and name ~= "...") and not narrow then
         self.errs:add_unknown(node, name)
      end
      if not attribute then
         t = drop_constant_value(t)
      end

      local var = self:add_to_scope(node, name, t, attribute, narrow, dont_check_redeclaration)

      if t is UnresolvedType or t.typename == "none" then
         return var
      end

      if self.collector and node then
         self.collector.add_to_symbol_list(node, name, t)
      end

      return var
   end

   local type CompareTypes = function(TypeChecker, Type, Type): boolean, {Error}

   local enum ArgCheckMode
      "argument"
      "return"
      "self"
   end

   local enum VarianceMode
      "covariant"
      "contravariant"
      "bivariant"
      "invariant"
   end

   function TypeChecker:arg_check(where: Where, all_errs: {Error}, a: Type, b: Type, v: VarianceMode, mode: ArgCheckMode, n?: integer): boolean
      local ok, errs: boolean, {Error}

      if v == "covariant" then
         ok, errs = self:is_a(a, b)
      elseif v == "contravariant" then
         ok, errs = self:is_a(b, a)
      elseif v == "bivariant" then
         ok, errs = self:is_a(a, b)
         if ok then
            return true
         end
         ok = self:is_a(b, a)
         if ok then
            return true
         end
      elseif v == "invariant" then
         ok, errs = self:same_type(a, b)
      end

      if not ok then
         self.errs:add_prefixing(where, errs, mode .. (n and " " .. n or "") .. ": ", all_errs)
         return false
      end
      return true
   end

   function TypeChecker:has_all_types_of(t1s: {Type}, t2s: {Type}): boolean
      for _, t1 in ipairs(t1s) do
         local found = false
         for _, t2 in ipairs(t2s) do
            if self:same_type(t2, t1) then
               found = true
               break
            end
         end
         if not found then
            return false
         end
      end
      return true
   end

   local function any_errors(all_errs: {Error}): boolean, {Error}
      if #all_errs == 0 then
         return true
      else
         return false, all_errs
      end
   end

   local function close_nested_records(t: RecordLikeType)
      for _, ft in pairs(t.fields) do
         if ft is TypeDeclType then
            ft.closed = true
            local def = ft.def
            if def is RecordLikeType then
               close_nested_records(def)
            end
         end
      end
   end

   local function close_types(vars: {string:Variable})
      for _, var in pairs(vars) do
         local t = var.t
         if t is TypeDeclType then
            t.closed = true
            local def = t.def
            if def is RecordLikeType then
               close_nested_records(def)
            end
         end
      end
   end

   function TypeChecker:get_unresolved(scope?: Scope): UnresolvedType
      local unresolved: UnresolvedType
      if scope then
         local unr = scope["@unresolved"]
         unresolved = unr and unr.t as UnresolvedType
      else
         unresolved = self:find_var_type("@unresolved") as UnresolvedType
      end
      if not unresolved then
         unresolved = a_type("unresolved", {
            labels = {},
            nominals = {},
            global_types = {},
            narrows = {},
         } as UnresolvedType)
         self:add_var(nil, "@unresolved", unresolved)
      end
      return unresolved
   end

   function TypeChecker:find_unresolved(level?: integer): UnresolvedType
      local u = self.st[level or #self.st]["@unresolved"]
      if u then
         return u.t as UnresolvedType
      end
   end

   function TypeChecker:begin_scope(node?: Node)
      table.insert(self.st, {})

      if self.collector and node then
         self.collector.begin_symbol_list_scope(node)
      end
   end

   function TypeChecker:end_scope(node?: Node): Type
      local st = self.st
      local scope = st[#st]
      local unresolved = scope["@unresolved"]
      if unresolved then
         local unrt = unresolved.t as UnresolvedType
         local next_scope = st[#st - 1]
         local upper = next_scope["@unresolved"]
         if upper then
            local uppert = upper.t as UnresolvedType
            for name, nodes in pairs(unrt.labels) do
               for _, n in ipairs(nodes) do
                  uppert.labels[name] = uppert.labels[name] or {}
                  table.insert(uppert.labels[name], n)
               end
            end
            for name, types in pairs(unrt.nominals) do
               for _, typ in ipairs(types) do
                  uppert.nominals[name] = uppert.nominals[name] or {}
                  table.insert(uppert.nominals[name], typ)
               end
            end
            for name, _ in pairs(unrt.global_types) do
               uppert.global_types[name] = true
            end
         else
            next_scope["@unresolved"] = unresolved
            unrt.narrows = {}
         end
      end
      close_types(scope)
      self.errs:warn_unused_vars(scope)

      table.remove(st)

      if self.collector and node then
         self.collector.end_symbol_list_scope(node)
      end

      return NONE
   end

   local function end_scope_and_none_type(self: TypeChecker, node: Node, _children: {Type}): Type
      self:end_scope(node)
      return NONE
   end

   do
      local function match_typevals(self: TypeChecker, t: NominalType, def: RecordLikeType | FunctionType): Type
         if t.typevals and def.typeargs then
            if #t.typevals ~= #def.typeargs then
               self.errs:add(t, "mismatch in number of type arguments")
               return nil
            end

            self:begin_scope()
            for i, tt in ipairs(t.typevals) do
               self:add_var(nil, def.typeargs[i].typearg, tt)
            end
            local ret = self:resolve_typevars_at(t, def)
            self:end_scope()
            return ret
         elseif t.typevals then
            self.errs:add(t, "spurious type arguments")
            return nil
         elseif def.typeargs then
            self.errs:add(t, "missing type arguments in %s", def)
            return nil
         else
            return def
         end
      end

      function TypeChecker:resolve_nominal(t: NominalType): Type
         if t.resolved then
            return t.resolved
         end

         local found = t.found or self:find_type(t.names)
         if not found then
            self.errs:add(t, "unknown type %s", t)
            return INVALID
         end

         local resolved: Type

         if found is TypeAliasType then
            found = found.alias_to.found
         end

         if found is TypeDeclType then
            local def = found.def
            if def.typename == "circular_require" then
               -- return, but do not store resolution
               return def
            end

            -- FIXME is this block still needed?
            if def is NominalType then
               found = def.found
               assert(found is TypeDeclType)
               def = found.def
            end
            assert(not def is NominalType)

            resolved = match_typevals(self, t, def)
         else
            self.errs:add(t, table.concat(t.names, ".") .. " is not a type")
            return INVALID
         end

         if not resolved then
            self.errs:add(t, table.concat(t.names, ".") .. " cannot be resolved in scope")
            return INVALID
         end

         if not t.filename then
            t.filename = resolved.filename
            if t.x == nil and t.y == nil then
               t.x = resolved.x
               t.y = resolved.y
            end
         end
         t.found = found
         t.resolved = resolved
         return resolved
      end

      function TypeChecker:resolve_typealias(typealias: TypeAliasType): Type, Variable
         local names = typealias.alias_to.names
         local aliasing = self:find_var(names[1], "use_type")
         if not aliasing then
            return INVALID
         end

         local t = typealias.alias_to
         if t.resolved then
            return t.resolved, aliasing
         end

         local found = t.found or self:find_type(t.names)
         if not found then
            self.errs:add(t, "unknown type %s", t)
            return INVALID
         end

         assert(found is TypeDeclType)

         if t.typevals then
            local resolved = match_typevals(self, t, found.def)
            t.resolved = resolved
            t.found = found
            found = a_typedecl(resolved)
         else
            t.resolved = t
         end

         return found, aliasing
      end
   end

   local function are_same_unresolved_global_type(t1: NominalType, t2: NominalType): boolean
      if t1.names[1] == t2.names[1] then
         local unresolved = get_unresolved()
         if unresolved.global_types[t1.names[1]] then
            return true
         end
      end
      return false
   end

   do
      local function fail_nominals(self: TypeChecker, t1: NominalType, t2: NominalType): boolean, {Error}
         local t1name = show_type(t1)
         local t2name = show_type(t2)
         if t1name == t2name then
            local t1r = self:resolve_nominal(t1)
            if t1r.filename then
               t1name = t1name .. " (defined in " .. t1r.filename .. ":" .. t1r.y .. ")"
            end
            local t2r = self:resolve_nominal(t2)
            if t2r.filename then
               t2name = t2name .. " (defined in " .. t2r.filename .. ":" .. t2r.y .. ")"
            end
         end
         return false, { Err(t1, t1name .. " is not a " .. t2name) }
      end

      function TypeChecker:are_same_nominals(t1: NominalType, t2: NominalType): boolean, {Error}
         local same_names: boolean
         if t1.found and t2.found then
            same_names = t1.found.typeid == t2.found.typeid
         else
            local ft1 = t1.found or self:find_type(t1.names)
            local ft2 = t2.found or self:find_type(t2.names)
            if ft1 and ft2 then
               same_names = ft1.typeid == ft2.typeid
            else
               if are_same_unresolved_global_type(t1, t2) then
                  return true
               end

               if not ft1 then
                  self.errs:add(t1, "unknown type %s", t1)
               end
               if not ft2 then
                  self.errs:add(t2, "unknown type %s", t2)
               end
               return false, {} -- errors were already produced
            end
         end

         if not same_names then
            return fail_nominals(self, t1, t2)
         elseif t1.typevals == nil and t2.typevals == nil then
            return true
         elseif t1.typevals and t2.typevals and #t1.typevals == #t2.typevals then
            local errs = {}
            for i = 1, #t1.typevals do
               local _, typeval_errs = self:same_type(t1.typevals[i], t2.typevals[i])
               self.errs:add_prefixing(t1, typeval_errs, "type parameter <" .. show_type(t2.typevals[i]) .. ">: ", errs)
            end
            return any_errors(errs)
         end
         return true
      end
   end

   local is_lua_table_type: function(t: Type): boolean
   local resolve_tuple_and_nominal: function(t: Type): Type

   local function unite(types: {Type}, flatten_constants?: boolean): Type
      if #types == 1 then
         return types[1]
      end

      local ts: {Type} = {}
      local stack: {Type} = {}

      -- Make things like number | number resolve to number
      local types_seen: {(integer|string):boolean} = {}
      -- but never add nil as a type in the union
      types_seen[NIL.typeid] = true
      types_seen["nil"] = true

      local i = 1
      while types[i] or stack[1] do
         local t: Type
         if stack[1] then
            t = table.remove(stack)
         else
            t = types[i]
            i = i + 1
         end
         t = resolve_tuple(t)
         if t is UnionType then
            for _, s in ipairs(t.types) do
               table.insert(stack, s)
            end
         else
            if primitive[t.typename] and (flatten_constants or (t is StringType and not t.literal)) then
               if not types_seen[t.typename] then
                  types_seen[t.typename] = true
                  table.insert(ts, t)
               end
            else
               local typeid = t.typeid
               if t is NominalType and t.found then
                  typeid = t.found.typeid
               end
               if not types_seen[typeid] then
                  types_seen[typeid] = true
                  table.insert(ts, t)
               end
            end
         end
      end

      if types_seen[INVALID.typeid] then
         return INVALID
      end

      if #ts == 1 then
         return ts[1]
      else
         return a_union(ts)
      end
   end

   function TypeChecker:expand_type(where: Where, old: Type, new: Type): Type
      if not old or old.typename == "nil" then
         return new
      else
         if not self:is_a(new, old) then
            if old is MapType and new is RecordLikeType then
               local old_keys = old.keys
               if old_keys is StringType then
                  for _, ftype in fields_of(new) do
                     old.values = self:expand_type(where, old.values, ftype)
                  end
                  edit_type(old, "map") -- map changed, refresh typeid
               else
                  self.errs:add(where, "cannot determine table literal type")
               end
            elseif old is RecordLikeType and new is RecordLikeType then
               local values: Type
               for _, ftype in fields_of(old) do
                  if not values then
                     values = ftype
                  else
                     values = self:expand_type(where, values, ftype)
                  end
               end
               for _, ftype in fields_of(new) do
                  if not values then
                     values = ftype
                  else
                     values = self:expand_type(where, values, ftype)
                  end
               end
               old.fields = nil
               old.field_order = nil
               old.meta_fields = nil
               old.meta_fields = nil

               edit_type(old, "map")
               assert(old is MapType)
               old.keys = STRING
               old.values = values
            elseif old is UnionType then
               edit_type(old, "union")
               table.insert(old.types, drop_constant_value(new))
            else
               return unite({ old, new }, true)
            end
         end
      end
      return old
   end

   do
      local known_table_types: {TypeName:boolean} = {
         array = true,
         map = true,
         record = true,
         tupletable = true,
         interface = true,
      }

      -- Is the type represented concretely as a Lua table?
      is_lua_table_type = function(t: Type): boolean
         return known_table_types[t.typename]
                and not (t is RecordLikeType and t.is_userdata)
      end
   end

   function TypeChecker:arraytype_from_tuple(where: Where, tupletype: TupleTableType): ArrayType, {Error}
      -- first just try a basic union
      local element_type = unite(tupletype.types, true)
      local valid = (not element_type is UnionType) and true or is_valid_union(element_type)
      if valid then
         return an_array(element_type)
      end

      -- failing a basic union, expand the types
      local arr_type = an_array(tupletype.types[1])
      for i = 2, #tupletype.types do
         local expanded = self:expand_type(where, arr_type, an_array(tupletype.types[i]))
         if not expanded is ArrayType then
            return nil, { Err(tupletype, "unable to convert tuple %s to array", tupletype) }
         end
         arr_type = expanded
      end
      return arr_type
   end

   local function is_self(t: Type): boolean
      return t is NominalType and t.names[1] == "@self"
   end

   local function compare_true(_: TypeChecker, _: Type, _: Type): boolean, {Error}
      return true
   end

   function TypeChecker:subtype_nominal(a: Type, b: Type): boolean, {Error}
      if is_self(a) and is_self(b) then
         return true
      end

      local ra = a is NominalType and self:resolve_nominal(a) or a
      local rb = b is NominalType and self:resolve_nominal(b) or b
      local ok, errs = self:is_a(ra, rb)
      if errs and #errs == 1 and errs[1].msg:match("^got ") then
         return false -- translate to got-expected error with unresolved types
      end
      return ok, errs
   end

   function TypeChecker:subtype_array(a: ArrayLikeType, b: ArrayLikeType): boolean, {Error}
      if (not a.elements) or (not self:is_a(a.elements, b.elements)) then
         return false
      end
      if a.consttypes and #a.consttypes > 1 then
         -- constant array, check elements (useful for array of enums)
         for _, e in ipairs(a.consttypes) do
            if not self:is_a(e, b.elements) then
               return false, { Err(a, "%s is not a member of %s", e, b.elements) }
            end
         end
      end
      return true
   end

   local function find_in_interface_list<T>(a: RecordLikeType, f: function(Type): T): T
      if not a.interface_list then
         return nil
      end

      for _, t in ipairs(a.interface_list) do
         local ret = f(t)
         if ret then
            return ret
         end
      end

      return nil
   end

   function TypeChecker:subtype_record(a: RecordLikeType, b: RecordLikeType): boolean, {Error}
      -- assert(b.typename == "record")
      if a.elements and b.elements then
         if not self:is_a(a.elements, b.elements) then
            return false, { Err(a, "array parts have incompatible element types") }
         end
      end

      if a.is_userdata ~= b.is_userdata then
         return false, { Err(a, a.is_userdata and "userdata is not a record"
                                              or  "record is not a userdata") }
      end

      local errs: {Error} = {}
      for _, k in ipairs(a.field_order) do
         local ak = a.fields[k]
         local bk = b.fields[k]
         if bk then
            local ok, fielderrs = self:is_a(ak, bk)
            if not ok then
               self.errs:add_prefixing(nil, fielderrs, "record field doesn't match: " .. k .. ": ", errs)
            end
         end
      end
      if #errs > 0 then
         for _, err in ipairs(errs) do
            err.msg = show_type(a) .. " is not a " .. show_type(b) .. ": " .. err.msg
         end
         return false, errs
      end

      return true
   end

   function TypeChecker:eqtype_record(a: RecordType, b: RecordType): boolean, {Error}
      -- checking array interface
      if (a.elements ~= nil) ~= (b.elements ~= nil) then
         return false, { Err(a, "types do not have the same array interface") }
      end
      if a.elements then
         local ok, errs = self:same_type(a.elements, b.elements)
         if not ok then
            return ok, errs
         end
      end

      local ok, errs = self:subtype_record(a, b)
      if not ok then
         return ok, errs
      end
      ok, errs = self:subtype_record(b, a)
      if not ok then
         return ok, errs
      end
      return true
   end

   local function compare_map(self: TypeChecker, ak: Type, bk: Type, av: Type, bv: Type, no_hack?: boolean): boolean, {Error}
      local ok1, errs_k = self:same_type(ak, bk)
      local ok2, errs_v = self:same_type(av, bv)

      -- FIXME hack for {any:any}
      if bk.typename == "any" and not no_hack then
         ok1, errs_k = true, nil
      end
      if bv.typename == "any" and not no_hack then
         ok2, errs_v = true, nil
      end

      if ok1 and ok2 then
         return true
      end

      -- combine errs_k and errs_v, prefixing errors
      for i = 1, errs_k and #errs_k or 0 do
         errs_k[i].msg = "in map key: " .. errs_k[i].msg
      end
      for i = 1, errs_v and #errs_v or 0 do
         errs_v[i].msg = "in map value: " .. errs_v[i].msg
      end
      if errs_k and errs_v then
         for i = 1, #errs_v do
            table.insert(errs_k, errs_v[i])
         end
         return false, errs_k
      end
      return false, errs_k or errs_v
   end

   function TypeChecker:compare_or_infer_typevar(typevar: string, a: Type, b: Type, cmp: CompareTypes): boolean, {Error}
      -- assert((a == nil and b ~= nil) or (a ~= nil and b == nil))

      -- does the typevar currently match to a type?
      local vt, _, constraint = self:find_var_type(typevar)
      if vt then
         -- If so, compare it to the other type
         return cmp(self, a or vt, b or vt)
      else
         -- otherwise, infer it to the other type
         local other = a or b

         -- but check interface constraint first if present
         if constraint then
            if not self:is_a(other, constraint) then
               return false, { Err(other, "given type %s does not satisfy %s constraint in type variable " .. display_typevar(typevar), other, constraint) }
            end

            if self:same_type(other, constraint) then
               -- do not infer to some type as constraint right away,
               -- to give a chance to more specific inferences
               -- in other arguments/returns
               return true
            end
         end

         local ok, r, errs = typevar_resolver(self, other, resolve_typevar)
         if not ok then
            return false, errs
         end
         if r is TypeVarType and r.typevar == typevar then
            return true
         end
         self:add_var(nil, typevar, r)
         return true
      end
   end

   -- ∃ x ∈ xs. t <: x
   function TypeChecker:exists_supertype_in(t: Type, xs: AggregateType): Type
      for _, x in ipairs(xs.types) do
         if self:is_a(t, x) then
            return x
         end
      end
   end

   -- emptytable rules are the same in eqtype_relations and subtype_relations
   local emptytable_relations: {TypeName:CompareTypes} = {
      ["array"] = compare_true,
      ["map"] = compare_true,
      ["tupletable"] = compare_true,
      ["interface"] = function(_self: TypeChecker, _a: Type, b: InterfaceType): boolean, {Error}
         return not b.is_userdata
      end,
      ["record"] = function(_self: TypeChecker, _a: Type, b: RecordType): boolean, {Error}
         return not b.is_userdata
      end,
   }

   TypeChecker.eqtype_relations = {
      ["typevar"] = {
         ["typevar"] = function(self: TypeChecker, a: TypeVarType, b: TypeVarType): boolean, {Error}
            if a.typevar == b.typevar then
               return true
            end

            return self:compare_or_infer_typevar(b.typevar, a, nil, self.same_type)
         end,
         ["*"] = function(self: TypeChecker, a: TypeVarType, b: Type): boolean, {Error}
            return self:compare_or_infer_typevar(a.typevar, nil, b, self.same_type)
         end,
      },
      ["emptytable"] = emptytable_relations,
      ["tupletable"] = {
         ["tupletable"] = function(self: TypeChecker, a: TupleTableType, b: TupleTableType): boolean, {Error}
            for i = 1, math.min(#a.types, #b.types) do
               if not self:same_type(a.types[i], b.types[i]) then
                  return false, { Err(a, "in tuple entry " .. tostring(i) .. ": got %s, expected %s", a.types[i], b.types[i]) }
               end
            end
            if #a.types ~= #b.types then
               return false, { Err(a, "tuples have different size", a, b) }
            end
            return true
         end,
      },
      ["array"] = {
         ["array"] = function(self: TypeChecker, a: ArrayType, b: ArrayType): boolean, {Error}
            return self:same_type(a.elements, b.elements)
         end,
      },
      ["map"] = {
         ["map"] = function(self: TypeChecker, a: MapType, b: MapType): boolean, {Error}
            return compare_map(self, a.keys, b.keys, a.values, b.values, true)
         end,
      },
      ["union"] = {
         ["union"] = function(self: TypeChecker, a: UnionType, b: UnionType): boolean, {Error}
            return (self:has_all_types_of(a.types, b.types)
                and self:has_all_types_of(b.types, a.types))
         end,
      },
      ["nominal"] = {
         ["nominal"] = TypeChecker.are_same_nominals,
      },
      ["record"] = {
         ["record"] = TypeChecker.eqtype_record,
      },
      ["function"] = {
         ["function"] = function(self:TypeChecker, a: FunctionType, b: FunctionType): boolean, {Error}
            local argdelta = a.is_method and 1 or 0
            local naargs, nbargs = #a.args.tuple, #b.args.tuple
            if naargs ~= nbargs then
               if (not not a.is_method) ~= (not not b.is_method) then
                  return false, { Err(a, "different number of input arguments: method and non-method are not the same type") }
               end
               return false, { Err(a, "different number of input arguments: got " .. naargs - argdelta .. ", expected " .. nbargs - argdelta) }
            end
            local narets, nbrets = #a.rets.tuple, #b.rets.tuple
            if narets ~= nbrets then
               return false, { Err(a, "different number of return values: got " .. narets .. ", expected " .. nbrets) }
            end
            local errs = {}
            for i = 1, naargs do
               self:arg_check(a, errs, a.args.tuple[i], b.args.tuple[i], "invariant", "argument", i - argdelta)
            end
            for i = 1, narets do
               self:arg_check(a, errs, a.rets.tuple[i], b.rets.tuple[i], "invariant", "return", i)
            end
            return any_errors(errs)
         end,
      },
      ["*"] = {
         ["typevar"] = function(self: TypeChecker, a: Type, b: TypeVarType): boolean, {Error}
            return self:compare_or_infer_typevar(b.typevar, a, nil, self.same_type)
         end,
      },
   }

   TypeChecker.subtype_relations = {
      ["tuple"] = {
         ["tuple"] = function(self: TypeChecker, a: TupleType, b: TupleType): boolean, {Error}  -- ∀ a[i] ∈ a, b[i] ∈ b. a[i] <: b[i]
            local at, bt = a.tuple, b.tuple                                  -- ──────────────────────────────────
            if #at ~= #bt then                                               --        a tuple <: b tuple
               return false
            end
            for i = 1, #at do
               if not self:is_a(at[i], bt[i]) then
                  return false
               end
            end
            return true
         end,
         ["*"] = function(self: TypeChecker, a: Type, b: Type): boolean, {Error}
            return self:is_a(resolve_tuple(a), b)
         end,
      },
      ["typevar"] = {
         ["typevar"] = function(self: TypeChecker, a: TypeVarType, b: TypeVarType): boolean, {Error}
            if a.typevar == b.typevar then
               return true
            end

            return self:compare_or_infer_typevar(b.typevar, a, nil, self.is_a)
         end,
         ["*"] = function(self: TypeChecker, a: TypeVarType, b: Type): boolean, {Error}
            return self:compare_or_infer_typevar(a.typevar, nil, b, self.is_a)
         end,
      },
      ["nil"] = {
         ["*"] = compare_true,
      },
      ["union"] = {
         ["union"] = function(self: TypeChecker, a: UnionType, b: UnionType): boolean, {Error} -- ∀ t ∈ a. ∃ u ∈ b. t <: u
            local used = {}                                                 -- ────────────────────────
            for _, t in ipairs(a.types) do                                  --    a union <: b union
               self:begin_scope()
               local u = self:exists_supertype_in(t, b)
               self:end_scope() -- don't preserve failed inferences
               if not u then
                  return false
               end
               if not used[u] then -- FIXME the order of declared union items affects inference behavior
                  used[u] = t
               end
            end
            for u, t in pairs(used) do
               self:is_a(t, u) -- preserve valid inferences
            end
            return true
         end,
         ["*"] = function(self: TypeChecker, a: UnionType, b: Type): boolean, {Error}   -- ∀ t ∈ a, t <: b
            for _, t in ipairs(a.types) do                                              -- ────────────────
               if not self:is_a(t, b) then                                              --   a union <: b
                  return false
               end
            end
            return true
         end,
      },
      ["poly"] = {
         ["*"] = function(self: TypeChecker, a: Type, b: Type): boolean, {Error}        -- ∃ t ∈ a, t <: b
            if self:exists_supertype_in(b, a) then                                      -- ───────────────
               return true                                                              --   a poly <: b
            end
            return false, { Err(a, "cannot match against any alternatives of the polymorphic type") }
         end,
      },
      ["nominal"] = {
         ["nominal"] = function(self: TypeChecker, a: NominalType, b: NominalType): boolean, {Error}
            local ok, errs = self:are_same_nominals(a, b)
            if ok then
               return true
            end

            local rb = self:resolve_nominal(b)
            if rb is InterfaceType then
               -- match interface subtyping
               return self:is_a(a, rb)
            end

            local ra = self:resolve_nominal(a)
            if ra is UnionType or rb is UnionType then
               -- match unions structurally
               return self:is_a(ra, rb)
            end

            -- all other types nominally
            return ok, errs
         end,
         ["*"] = TypeChecker.subtype_nominal,
      },
      ["enum"] = {
         ["string"] = compare_true,
      },
      ["string"] = {
         ["enum"] = function(_self: TypeChecker, a: StringType, b: EnumType): boolean, {Error}
            if not a.literal then
               return false, { Err(a, "string is not a %s", b) }
            end

            if b.enumset[a.literal] then
               return true
            end

            return false, { Err(a, "%s is not a member of %s", a, b) }
         end,
      },
      ["integer"] = {
         ["number"] = compare_true,
      },
      ["interface"] = {
         ["interface"] = function(self: TypeChecker, a: Type, b: Type): boolean, {Error}
            if find_in_interface_list(a, function(t: Type): boolean return (self:is_a(t, b)) end) then
               return true
            end
            return self:same_type(a, b)
         end,
         ["array"] = TypeChecker.subtype_array,
         ["record"] = TypeChecker.subtype_record,
         ["tupletable"] = function(self: TypeChecker, a: Type, b: Type): boolean, {Error}
            return self.subtype_relations["record"]["tupletable"](self, a, b)
         end,
      },
      ["emptytable"] = emptytable_relations,
      ["tupletable"] = {
         ["tupletable"] = function(self: TypeChecker, a: TupleTableType, b: TupleTableType): boolean, {Error}
            for i = 1, math.min(#a.types, #b.types) do
               if not self:is_a(a.types[i], b.types[i]) then
                  return false, { Err(a, "in tuple entry "
                     .. tostring(i) .. ": got %s, expected %s",
                     a.types[i], b.types[i]) }
               end
            end
            if #a.types > #b.types then
               return false, { Err(a, "tuple %s is too big for tuple %s", a, b) }
            end
            return true
         end,
         ["record"] = function(self: TypeChecker, a: Type, b: RecordType): boolean, {Error}
            if b.elements then
               return self.subtype_relations["tupletable"]["array"](self, a, b)
            end
         end,
         ["array"] = function(self: TypeChecker, a: TupleTableType, b: ArrayType): boolean, {Error}
            if b.inferred_len and b.inferred_len > #a.types then
               return false, { Err(a, "incompatible length, expected maximum length of " .. tostring(#a.types) .. ", got " .. tostring(b.inferred_len)) }
            end
            local aa, err = self:arraytype_from_tuple(a.inferred_at, a)
            if not aa then
               return false, err
            end
            if not self:is_a(aa, b) then
               return false, { Err(a, "got %s (from %s), expected %s", aa, a, b) }
            end
            return true
         end,
         ["map"] = function(self: TypeChecker, a: TupleTableType, b: MapType): boolean, {Error}
            local aa = self:arraytype_from_tuple(a.inferred_at, a)
            if not aa then
               return false, { Err(a, "Unable to convert tuple %s to map", a) }
            end

            return compare_map(self, INTEGER, b.keys, aa.elements, b.values)
         end,
      },
      ["record"] = {
         ["record"] = TypeChecker.subtype_record,
         ["interface"] = function(self: TypeChecker, a: RecordType, b: InterfaceType): boolean, {Error}
            if find_in_interface_list(a, function(t: Type): boolean return (self:is_a(t, b)) end) then
               return true
            end
            if not a.declname then
               -- match inferred table (anonymous record) structurally to interface
               return self:subtype_record(a, b)
            end
         end,
         ["array"] = TypeChecker.subtype_array,
         ["map"] = function(self: TypeChecker, a: RecordType, b: MapType): boolean, {Error}
            if not self:is_a(b.keys, STRING) then
               return false, { Err(a, "can't match a record to a map with non-string keys") }
            end

            for _, k in ipairs(a.field_order) do
               local bk = b.keys
               if bk is EnumType and not bk.enumset[k] then
                  return false, { Err(a, "key is not an enum value: " .. k) }
               end
               if not self:is_a(a.fields[k], b.values) then
                  return false, { Err(a, "record is not a valid map; not all fields have the same type") }
               end
            end

            return true
         end,
         ["tupletable"] = function(self: TypeChecker, a: RecordType, b: Type): boolean, {Error}
            if a.elements then
               return self.subtype_relations["array"]["tupletable"](self, a, b)
            end
         end,
      },
      ["array"] = {
         ["array"] = TypeChecker.subtype_array,
         ["record"] = function(self: TypeChecker, a: ArrayType, b: RecordType): boolean, {Error}
            if b.elements then
               return self:subtype_array(a, b)
            end
         end,
         ["map"] = function(self: TypeChecker, a: ArrayType, b: MapType): boolean, {Error}
            return compare_map(self, INTEGER, b.keys, a.elements, b.values)
         end,
         ["tupletable"] = function(self: TypeChecker, a: ArrayType, b: TupleTableType): boolean, {Error}
            local alen = a.inferred_len or 0
            if alen > #b.types then
               return false, { Err(a, "incompatible length, expected maximum length of " .. tostring(#b.types) .. ", got " .. tostring(alen)) }
            end

            -- for array literals (which is the only case where inferred_len is defined),
            -- only check the entries that are present
            for i = 1, (alen > 0) and alen or #b.types do
               if not self:is_a(a.elements, b.types[i]) then
                  return false, { Err(a, "tuple entry " .. i .. " of type %s does not match type of array elements, which is %s", b.types[i], a.elements) }
               end
            end
            return true
         end,
      },
      ["map"] = {
         ["map"] = function(self: TypeChecker, a: MapType, b: MapType): boolean, {Error}
            return compare_map(self, a.keys, b.keys, a.values, b.values)
         end,
         ["array"] = function(self: TypeChecker, a: MapType, b: ArrayType): boolean, {Error}
            return compare_map(self, a.keys, INTEGER, a.values, b.elements)
         end,
      },
      ["typedecl"] = {
         ["record"] = function(self: TypeChecker, a: TypeDeclType, b: RecordType): boolean, {Error}
            local def = a.def
            if def is RecordLikeType then
               return self:subtype_record(a.def, b) -- record as prototype
            end
         end,
      },
      ["function"] = {
         ["function"] = function(self: TypeChecker, a: FunctionType, b: FunctionType): boolean, {Error}
            local errs = {}

            local aa, ba = a.args.tuple, b.args.tuple
            if (not b.args.is_va) and a.min_arity > b.min_arity then
               table.insert(errs, Err(a, "incompatible number of arguments: got " .. show_arity(a) .. " %s, expected " .. show_arity(b) .. " %s", a.args, b.args))
            else
               for i = ((a.is_method or b.is_method) and 2 or 1), #aa do
                  self:arg_check(nil, errs, aa[i], ba[i] or ba[#ba], "bivariant", "argument", i)
               end
            end

            local ar, br = a.rets.tuple, b.rets.tuple
            local diff_by_va = #br - #ar == 1 and b.rets.is_va
            if #ar < #br and not diff_by_va then
               table.insert(errs, Err(a, "incompatible number of returns: got " .. #ar .. " %s, expected " .. #br .. " %s", a.rets, b.rets))
            else
               local nrets = #br
               if diff_by_va then
                  nrets = nrets - 1
               end
               for i = 1, nrets do
                  self:arg_check(nil, errs, ar[i], br[i], "bivariant", "return", i)
               end
            end

            return any_errors(errs)
         end,
      },
      ["typearg"] = {
         ["typearg"] = function(_self: TypeChecker, a: TypeArgType, b: TypeArgType): boolean, {Error}
            return a.typearg == b.typearg
         end,
         ["*"] = function(self: TypeChecker, a: TypeArgType, b: Type): boolean, {Error}
            if a.constraint then
               return self:is_a(a.constraint, b)
            end
         end,
      },
      ["*"] = {
         ["any"] = compare_true,
         ["tuple"] = function(self: TypeChecker, a: Type, b: Type): boolean, {Error}
            return self:is_a(a_tuple({a}), b)
         end,
         ["typevar"] = function(self: TypeChecker, a: Type, b: TypeVarType): boolean, {Error}
            return self:compare_or_infer_typevar(b.typevar, a, nil, self.is_a)
         end,
         ["typearg"] = function(self: TypeChecker, a: Type, b: TypeArgType): boolean, {Error}
            if b.constraint then
               return self:is_a(a, b.constraint)
            end
         end,
         ["union"] = TypeChecker.exists_supertype_in as CompareTypes,                   -- ∃ t ∈ b, a <: t
                                                                                        -- ───────────────
                                                                                        --  a <: b union
         ["nominal"] = TypeChecker.subtype_nominal,
         ["poly"] = function(self: TypeChecker, a: Type, b: PolyType): boolean, {Error} -- ∀ t ∈ b, a <: t
            for _, t in ipairs(b.types) do                                              -- ───────────────
               if not self:is_a(a, t) then                                              --   a <: b poly
                  return false, { Err(a, "cannot match against all alternatives of the polymorphic type") }
               end
            end
            return true
         end,
      },
   }

   -- evaluation strategy
   TypeChecker.type_priorities = {
      -- types that have catch-all rules evaluate first
      ["tuple"] = 2,
      ["typevar"] = 3,
      ["nil"] = 4,
      ["any"] = 5,
      ["union"] = 6,
      ["poly"] = 7,
      -- then typeargs
      ["typearg"] = 8,
      -- then nominals
      ["nominal"] = 9,
      -- then base types
      ["enum"] = 10,
      ["string"] = 10,
      ["integer"] = 10,
      ["boolean"] = 10,
      -- then interfaces
      ["interface"] = 11,
      -- then special cases of tables
      ["emptytable"] = 12,
      ["tupletable"] = 13,
      -- then other recursive types
      ["record"] = 14,
      ["array"] = 14,
      ["map"] = 14,
      ["function"] = 14,
   }

   local function compare_types(self: TypeChecker, relations: TypeRelations, t1: Type, t2: Type): boolean, {Error}
      if t1.typeid == t2.typeid then
         return true
      end

      local s1 = relations[t1.typename]
      local fn = s1 and s1[t2.typename]
      if not fn then
         local p1 = self.type_priorities[t1.typename] or 999
         local p2 = self.type_priorities[t2.typename] or 999
         fn = (p1 < p2 and (s1 and s1["*"]) or (relations["*"][t2.typename]))
      end

      local ok, err: boolean, {Error}
      if fn then
         if fn == compare_true then
            return true
         end
         ok, err = fn(self, t1, t2)
      else
         ok = t1.typename == t2.typename
      end

      if (not ok) and not err then
         return false, { Err(t1, "got %s, expected %s", t1, t2) }
      end
      return ok, err
   end

   -- subtyping comparison
   function TypeChecker:is_a(t1: Type, t2: Type): boolean, {Error}
      return compare_types(self, self.subtype_relations, t1, t2)
   end

   -- invariant type comparison
   function TypeChecker:same_type(t1: Type, t2: Type): boolean, {Error}
      -- except for error messages, behavior is the same as
      -- `return (is_a(t1, t2) and self:is_a(t2, t1))`
      return compare_types(self, self.eqtype_relations, t1, t2)
   end

   if TL_DEBUG then
      local orig_is_a = TypeChecker.is_a
      TypeChecker.is_a = function(self: TypeChecker, t1: Type, t2: Type): boolean, {Error}
         assert(type(t1) == "table")
         assert(type(t2) == "table")

         if t1.typeid == t2.typeid then
            local st1, st2 = show_type_base(t1, false, {}), show_type_base(t2, false, {})
            assert(st1 == st2, st1 .. " ~= " .. st2)
            return true
         end

         return orig_is_a(self, t1, t2)
      end
   end

   function TypeChecker:assert_is_a(where: Where, t1: Type, t2: Type, context: string, name?: string): boolean
      t1 = resolve_tuple(t1)
      t2 = resolve_tuple(t2)
      if self.feat_lax and (is_unknown(t1) or is_unknown(t2)) then
         return true
      end

      -- some flow-based inference
      if t1.typename == "nil" then
         return true
      elseif t2 is UnresolvedEmptyTableValueType then
         if is_number_type(t2.emptytable_type.keys) then -- ideally integer only
            self:infer_emptytable(t2.emptytable_type, self:infer_at(where, an_array(t1)))
         else
            self:infer_emptytable(t2.emptytable_type, self:infer_at(where, a_map(t2.emptytable_type.keys, t1)))
         end
         return true
      elseif t2 is EmptyTableType then
         if is_lua_table_type(t1) then
            self:infer_emptytable(t2, self:infer_at(where, t1))
         elseif not t1 is EmptyTableType then
            self.errs:add(where, context .. ": " .. (name and (name .. ": ") or "") .. "assigning %s to a variable declared with {}", t1)
            return false
         end
         return true
      end

      local ok, match_errs = self:is_a(t1, t2)
      self.errs:add_prefixing(where, match_errs, context .. ": ".. (name and (name .. ": ") or ""))
      return ok
   end

   local function type_is_closable(t: Type): boolean
      if t is InvalidType then
         return false
      end
      if t.typename == "nil" then
         return true
      end
      if t is NominalType then
         t = assert(t.resolved)
      end
      if t is RecordLikeType then
         return t.meta_fields and t.meta_fields["__close"] ~= nil
      end
   end

   local definitely_not_closable_exprs <const>: {NodeKind:boolean} = {
      ["string"] = true,
      ["number"] = true,
      ["integer"] = true,
      ["boolean"] = true,
      ["literal_table"] = true,
   }
   local function expr_is_definitely_not_closable(e: Node): boolean
      return definitely_not_closable_exprs[e.kind]
   end

   function TypeChecker:same_in_all_union_entries(u: UnionType, check: function(Type): (Type, Type)): Type
      local t1, f = check(u.types[1])
      if not t1 then
         return nil
      end
      for i = 2, #u.types do
         local t2 = check(u.types[i])
         if not t2 or not self:same_type(t1, t2) then
            return nil
         end
      end
      return f or t1
   end

   function TypeChecker:same_call_mt_in_all_union_entries(u: UnionType): Type
      return self:same_in_all_union_entries(u, function(t: Type): (Type, Type)
         t = resolve_tuple_and_nominal(t)
         if t is RecordLikeType then
            local call_mt = t.meta_fields and t.meta_fields["__call"]
            if call_mt is FunctionType then
               local args_tuple = a_tuple({})
               for i = 2, #call_mt.args.tuple do
                  table.insert(args_tuple.tuple, call_mt.args.tuple[i])
               end
               return args_tuple, call_mt
            end
         end
      end)
   end

   function TypeChecker:resolve_for_call(func: Type, args: TupleType, is_method: boolean): Type, boolean
      -- resolve unknown in lax mode, produce a general unknown function
      if self.feat_lax and is_unknown(func) then
         func = a_fn { args = va_args { UNKNOWN }, rets = va_args { UNKNOWN } }
      end
      -- unwrap if tuple, resolve if nominal
      func = resolve_tuple_and_nominal(func)
      if func.typename ~= "function" and func.typename ~= "poly" then
         -- resolve if union
         if func is UnionType then
            local r = self:same_call_mt_in_all_union_entries(func)
            if r then
               table.insert(args.tuple, 1, func.types[1]) -- FIXME: is this right?
               return resolve_tuple_and_nominal(r), true
            end
         end
         -- resolve if prototype
         if func is TypeDeclType then
            local funcdef = func.def
            if funcdef is RecordType then
               func = func.def
            end
         end
         -- resolve if metatable
         if func is RecordLikeType and func.meta_fields and func.meta_fields["__call"] then
            table.insert(args.tuple, 1, func)
            func = func.meta_fields["__call"]
            func = resolve_tuple_and_nominal(func)
            is_method = true
         end
      end
      return func, is_method
   end

   local type OnArgId = function<T>(node: Node, i: integer): T
   local type OnNode = function<S, T>(s: S, node: Node, children: {T}, ret: T): T

   local function traverse_macroexp<T>(macroexp: Node, on_arg_id: OnArgId<T>, on_node: OnNode<nil, T>): T
      local root = macroexp.exp
      local argnames = {}
      for i, a in ipairs(macroexp.args) do
         argnames[a.tk] = i
      end

      local visit_node: Visitor<nil, NodeKind, Node, T> = {
         cbs = {
            ["variable"] = {
               after = function(_: nil, node: Node, _children: {T}): T
                  local i = argnames[node.tk]
                  if not i then
                     return nil
                  end

                  return on_arg_id(node, i)
               end
            }
         },
         after = on_node as VisitorAfter<nil, Node, T>,
      }

      return recurse_node(nil, root, visit_node, {})
   end

   local function expand_macroexp(orignode: Node, args: {Node}, macroexp: Node)
      local on_arg_id = function(_node: Node, i: integer): {Node, Node}
         return { Node, args[i] }
      end

      local on_node = function(node: Node, children: {{Node, Node}}, ret: {Node, Node}): {Node, Node}
         local orig = ret and ret[2] or node

         local out = shallow_copy_table(orig)

         local map = {}
         for _, pair in pairs(children as {integer:{Node, Node}}) do
            if type(pair) == "table" then
               map[pair[1]] = pair[2]
            end
         end

         for k, v in pairs(orig as {any:Node}) do
            if type(v) == "table" and map[v] then
               (out as {any:any})[k] = map[v]
            end
         end

         out.yend = out.yend and (orignode.y + (out.yend - out.y)) or nil
         out.xend = nil
         out.y = orignode.y
         out.x = orignode.x
         return { node, out }
      end

      local p = traverse_macroexp(macroexp, on_arg_id, on_node)
      orignode.expanded = p[2]
   end

   function TypeChecker:check_macroexp_arg_use(macroexp: Node)
      local used: {string:boolean} = {}

      local on_arg_id = function(node: Node, _i: integer): {Node, Node}
         if used[node.tk] then
            self.errs:add(node, "cannot use argument '" .. node.tk .. "' multiple times in macroexp")
         else
            used[node.tk] = true
         end
      end

      traverse_macroexp(macroexp, on_arg_id, nil)
   end

   local function apply_macroexp(orignode: Node)
      local expanded = orignode.expanded
      local saveknown = orignode.known
      orignode.expanded = nil

      for k, _ in pairs(orignode as {any:any}) do
         (orignode as {any:any})[k] = nil
      end
      for k, v in pairs(expanded as {any:any}) do
         (orignode as {any:any})[k] = v
      end
      orignode.known = saveknown
   end

   local type InvalidOrTupleType = InvalidType | TupleType

   do
      local function mark_invalid_typeargs(self: TypeChecker, f: FunctionType)
         if f.typeargs then
            for _, a in ipairs(f.typeargs) do
               if not self:find_var_type(a.typearg) then
                  if a.constraint then
                     self:add_var(nil, a.typearg, a.constraint)
                  else
                     self:add_var(nil, a.typearg, self.feat_lax and UNKNOWN or a_type("unresolvable_typearg", {
                        typearg = a.typearg
                     } as UnresolvableTypeArgType))
                  end
               end
            end
         end
      end

      local function infer_emptytables(self: TypeChecker, where: Where, wheres: {Where}, xs: TupleType, ys: TupleType, delta: integer)
         local xt, yt = xs.tuple, ys.tuple
         local n_xs = #xt
         local n_ys = #yt
         -- resolve inference of emptytables used as arguments or returns
         for i = 1, n_xs do
            local x = xt[i]
            if x is EmptyTableType then
               local y = yt[i] or (ys.is_va and yt[n_ys])
               if y then -- y may not be present when inferring returns
                  local w = wheres and wheres[i + delta] or where -- for self, a + argdelta is 0
                  local inferred_y = self:infer_at(w, y)
                  self:infer_emptytable(x, inferred_y)
                  xt[i] = inferred_y
               end
            end
         end
      end

      local check_args_rets: function(TypeChecker, where: Where, where_args: {Node}, f: FunctionType, args: TupleType, expected_rets: TupleType, argdelta: integer): TupleType, {Error}
      do
         -- check if a tuple `xs` matches tuple `ys`
         local function check_func_type_list(self: TypeChecker, where: Where, wheres: {Where}, xs: TupleType, ys: TupleType, from: integer, delta: integer, v: VarianceMode, mode: ArgCheckMode): boolean, {Error}
            assert(xs.typename == "tuple", xs.typename)
            assert(ys.typename == "tuple", ys.typename)

            local errs = {}
            local xt, yt = xs.tuple, ys.tuple
            local n_xs = #xt
            local n_ys = #yt

            for i = from, math.max(n_xs, n_ys) do
               local pos = i + delta
               local x = xt[i] or (xs.is_va and xt[n_xs]) or NIL
               local y = yt[i] or (ys.is_va and yt[n_ys])
               if y then
                  local w = wheres and wheres[pos] or where
                  if not self:arg_check(w, errs, x, y, v, mode, pos) then
                     return nil, errs
                  end
               end
            end

            return true
         end

         check_args_rets = function(self: TypeChecker, where: Where, where_args: {Node}, f: FunctionType, args: TupleType, expected_rets: TupleType, argdelta: integer): TupleType, {Error}
            local rets_ok = true
            local rets_errs: {Error}
            local args_ok: boolean
            local args_errs: {Error}
            local fargs = f.args.tuple

            local from = 1
            if argdelta == -1 then
               from = 2
               local errs = {}
               if (not is_self(fargs[1])) and not self:arg_check(where, errs, fargs[1], args.tuple[1], "contravariant", "self") then
                  return nil, errs
               end
            end

            if expected_rets then
               expected_rets = self:infer_at(where, expected_rets)
               infer_emptytables(self, where, nil, expected_rets, f.rets, 0)

               rets_ok, rets_errs = check_func_type_list(self, where, nil, f.rets, expected_rets, 1, 0, "covariant", "return")
            end

            args_ok, args_errs = check_func_type_list(self, where, where_args, f.args, args, from, argdelta, "contravariant", "argument")
            if (not args_ok) or (not rets_ok) then
               return nil, args_errs or {}
            end

            -- if we got to this point without returning,
            -- we got a valid function match

            infer_emptytables(self, where, where_args, args, f.args, argdelta)

            mark_invalid_typeargs(self, f)

            return self:resolve_typevars_at(where, f.rets)
         end
      end

      local function push_typeargs(self: TypeChecker, func: FunctionType)
         if func.typeargs then
            for _, fnarg in ipairs(func.typeargs) do
               self:add_var(nil, fnarg.typearg, a_type("unresolved_typearg", {
                  constraint = fnarg.constraint,
               } as UnresolvedTypeArgType))
            end
         end
      end

      local function pop_typeargs(self: TypeChecker, func: FunctionType)
         if func.typeargs then
            for _, fnarg in ipairs(func.typeargs) do
               if self.st[#self.st][fnarg.typearg] then
                  self.st[#self.st][fnarg.typearg] = nil
               end
            end
         end
      end

      local function fail_call(self: TypeChecker, where: Where, func: FunctionType | PolyType, nargs: integer, errs: {Error}): TupleType
         if errs then
            self.errs:collect(errs)
         else
            -- found no arity match to try
            local expects: {string} = {}
            if func is PolyType then
               for _, f in ipairs(func.types) do
                  table.insert(expects, show_arity(f))
               end
               table.sort(expects)
               for i = #expects, 1, -1 do
                  if expects[i] == expects[i+1] then
                     table.remove(expects, i)
                  end
               end
            else
               table.insert(expects, show_arity(func))
            end
            self.errs:add(where, "wrong number of arguments (given " .. nargs .. ", expects " .. table.concat(expects, " or ") .. ")")
         end

         local f = func is PolyType and func.types[1] or func

         mark_invalid_typeargs(self, f)

         return self:resolve_typevars_at(where, f.rets)
      end

      local function check_call(self: TypeChecker, where: Where, where_args: {Node}, func: Type, args: TupleType, expected_rets: TupleType, is_typedecl_funcall: boolean, argdelta: integer): InvalidOrTupleType, FunctionType
         assert(type(func) == "table")
         assert(type(args) == "table")

         local is_method = (argdelta == -1)

         if not (func is FunctionType or func is PolyType) then
            func, is_method = self:resolve_for_call(func, args, is_method)
            if is_method then
               argdelta = -1
            end
            if not (func is FunctionType or func is PolyType) then
               return self.errs:invalid_at(where, "not a function: %s", func)
            end
         end

         if is_method and args.tuple[1] then
            self:add_var(nil, "@self", type_at(where, a_typedecl(args.tuple[1])))
         end

         local passes, n = 1, 1
         if func is PolyType then
            passes, n = 3, #func.types
         end

         local given = #args.tuple
         local tried: {integer:boolean}
         local first_errs: {Error}
         for pass = 1, passes do
            for i = 1, n do
               if (not tried) or not tried[i] then
                  local f = func is PolyType and func.types[i] or func
                  local fargs = f.args.tuple
                  if f.is_method and not is_method then
                     if args.tuple[1] and self:is_a(args.tuple[1], fargs[1]) then
                        -- a non-"@funcall" means a synthesized call, e.g. from a metamethod
                        if not is_typedecl_funcall then
                           self.errs:add_warning("hint", where, "invoked method as a regular function: consider using ':' instead of '.'")
                        end
                     else
                        return self.errs:invalid_at(where, "invoked method as a regular function: use ':' instead of '.'")
                     end
                  end
                  local wanted = #fargs
                  local min_arity = self.feat_arity and f.min_arity or 0

                  -- simple functions:
                  if (passes == 1 and ((given <= wanted and given >= min_arity) or (f.args.is_va and given > wanted) or (self.feat_lax and given <= wanted)))
                  -- poly, pass 1: try exact arity matches first
                  or (passes == 3 and ((pass == 1 and given == wanted)
                  -- poly, pass 2: then try adjusting with nils to missing arguments or using '...'
                                    or (pass == 2 and given < wanted and (self.feat_lax or given >= min_arity))
                  -- poly, pass 3: then finally try vararg functions
                                    or (pass == 3 and f.args.is_va and given > wanted)))
                  then
                     push_typeargs(self, f)

                     local matched, errs = check_args_rets(self, where, where_args, f, args, expected_rets, argdelta)
                     if matched then
                        -- success!
                        return matched, f
                     end
                     first_errs = first_errs or errs

                     if expected_rets then
                        -- revert inferred returns
                        infer_emptytables(self, where, where_args, f.rets, f.rets, argdelta)
                     end

                     if passes == 3 then
                        tried = tried or {}
                        tried[i] = true
                        pop_typeargs(self, f)
                     end
                  end
               end
            end
         end

         return fail_call(self, where, func, given, first_errs)
      end

      function TypeChecker:type_check_function_call(node: Node, func: Type, args: TupleType, argdelta?: integer, e1?: Node, e2?: {Node}): InvalidOrTupleType, FunctionType
         e1 = e1 or node.e1
         e2 = e2 or node.e2

         local expected = node.expected
         local expected_rets: TupleType
         if expected and expected is TupleType then
            expected_rets = expected
         else
            expected_rets = a_tuple { node.expected }
         end

         self:begin_scope()

         local is_typedecl_funcall: boolean
         if node.kind == "op" and node.op.op == "@funcall" and e1 and e1.receiver then
            local receiver = e1.receiver
            if receiver is NominalType then
               local resolved = receiver.resolved
               if resolved and resolved is TypeDeclType then
                  is_typedecl_funcall = true
               end
            end
         end

         local ret, f = check_call(self, node, e2, func, args, expected_rets, is_typedecl_funcall, argdelta or 0)
         ret = self:resolve_typevars_at(node, ret)
         self:end_scope()

         if self.collector then
            self.collector.store_type(e1.y, e1.x, f)
         end

         if f and f.macroexp then
            expand_macroexp(node, e2, f.macroexp)
         end

         return ret, f
      end
   end

   function TypeChecker:check_metamethod(node: Node, method_name: string, a: Type, b: Type, orig_a: Type, orig_b: Type): Type, integer
      if self.feat_lax and ((a and is_unknown(a)) or (b and is_unknown(b))) then
         return UNKNOWN, nil
      end
      local ameta = a is RecordLikeType and a.meta_fields
      local bmeta = b and b is RecordLikeType and b.meta_fields

      if not ameta and not bmeta then
         return nil, nil
      end

      local meta_on_operator = 1
      local metamethod: Type
      if method_name ~= "__is" then
         metamethod = ameta and ameta[method_name or ""]
      end
      if (not metamethod) and b and method_name ~= "__index" then
         metamethod = bmeta and bmeta[method_name or ""]
         meta_on_operator = 2
      end

      if metamethod then
         local e2 = { node.e1 }
         local args = a_tuple { orig_a }
         if b and method_name ~= "__is" then
            e2[2] = node.e2
            args.tuple[2] = orig_b
         end
         return resolve_tuple_and_nominal((self:type_check_function_call(node, metamethod, args, -1, node, e2))), meta_on_operator
      else
         return nil, nil
      end
   end

   function TypeChecker:match_record_key(tbl: Type, rec: Node, key: string): Type, string
      assert(type(tbl) == "table")
      assert(type(rec) == "table")
      assert(type(key) == "string")

      tbl = resolve_tuple_and_nominal(tbl)

      if tbl is StringType or tbl is EnumType then
         tbl = self:find_var_type("string") -- simulate string metatable
      end

      if tbl is TypeDeclType then
         tbl = tbl.def
      elseif tbl is TypeAliasType then
         if tbl.is_nested_alias then
            return nil, "cannot use a nested type alias as a concrete value"
         else
            tbl = self:resolve_nominal(tbl.alias_to)
         end
      end

      if tbl is UnionType then
         local t = self:same_in_all_union_entries(tbl, function(t: Type): (Type, Type)
            return (self:match_record_key(t, rec, key))
         end)

         if t then
            return t
         end
      end

      if (tbl is TypeVarType or tbl is TypeArgType) and tbl.constraint then
         local t = self:match_record_key(tbl.constraint, rec, key)

         if t then
            return t
         end
      end

      if tbl is RecordLikeType then
         assert(tbl.fields, "record has no fields!?")

         if tbl.fields[key] then
            return tbl.fields[key]
         end

         local meta_t = self:check_metamethod(rec, "__index", tbl, STRING, tbl, STRING)
         if meta_t then
            return meta_t
         end

         if rec.kind == "variable" then
            return nil, "invalid key '" .. key .. "' in record '" .. rec.tk .. "' of type %s"
         else
            return nil, "invalid key '" .. key .. "' in type %s"
         end
      elseif tbl is EmptyTableType or is_unknown(tbl) then
         if self.feat_lax then
            return UNKNOWN
         end
         return nil, "cannot index a value of unknown type"
      end

      if rec.kind == "variable" then
         return nil, "cannot index key '" .. key .. "' in " .. tbl.typename .. " '" .. rec.tk .. "' of type %s"
      else
         return nil, "cannot index key '" .. key .. "' in type %s"
      end
   end

   local function widen_in_scope(scope: Scope, var: string): boolean
      assert(scope[var], "no " .. var .. " in scope")
      local narrow_mode = scope[var].is_narrowed
      if narrow_mode and narrow_mode ~= "declaration" then
         if scope[var].narrowed_from then
            scope[var].t = scope[var].narrowed_from
            scope[var].narrowed_from = nil
            scope[var].is_narrowed = nil
         else
            scope[var] = nil
         end

         local unresolved = get_unresolved(scope)
         unresolved.narrows[var] = nil
         return true
      end
      return false
   end

   function TypeChecker:widen_back_var(name: string): boolean
      local widened = false
      for i = #self.st, 1, -1 do
         if self.st[i][name] then
            if widen_in_scope(self.st[i], name) then
               widened = true
            else
               break
            end
         end
      end
      return widened
   end

   local function assigned_anywhere(name: string, root: Node): boolean
      local visit_node: Visitor<nil, NodeKind, Node, boolean> = {
         cbs = {
            ["assignment"] = {
               after = function(_: nil, node: Node, _children: {boolean}): boolean
                  for _, v in ipairs(node.vars) do
                     if v.kind == "variable" and v.tk == name then
                        return true
                     end
                  end
                  return false
               end
            }
         },
         after = function(_: nil, _node: Node, children: {boolean}, ret: boolean): boolean
            ret = ret or false
            for _, c in ipairs(children) do
               local ca = c as any
               if ca is boolean then
                  ret = ret or c
               end
            end
            return ret
         end
      }

      local visit_type: Visitor<nil, TypeName, Type, boolean> = {
         after = function(): boolean
            return false
         end
      }

      return recurse_node(nil, root, visit_node, visit_type)
   end

   function TypeChecker:widen_all_unions(node?: Node)
      for i = #self.st, 1, -1 do
         local scope = self.st[i]
         local unresolved = find_unresolved(i)
         if unresolved and unresolved.narrows then
            for name, _ in pairs(unresolved.narrows) do
               if not node or assigned_anywhere(name, node) then
                  widen_in_scope(scope, name)
               end
            end
         end
      end
   end

   function TypeChecker:add_global(node: Node, varname: string, valtype: Type, is_assigning?: boolean): Variable
      if self.feat_lax and is_unknown(valtype) and (varname ~= "self" and varname ~= "...") then
         self.errs:add_unknown(node, varname)
      end

      local is_const = node.attribute ~= nil
      local existing, scope, existing_attr = self:find_var(varname)
      if existing then
         if scope > 1 then
            self.errs:add(node, "cannot define a global when a local with the same name is in scope")
         elseif is_assigning and existing_attr then
            self.errs:add(node, "cannot reassign to <" .. existing_attr .. "> global: " .. varname)
         elseif existing_attr and not is_const then
            self.errs:add(node, "global was previously declared as <" .. existing_attr .. ">: " .. varname)
         elseif (not existing_attr) and is_const then
            self.errs:add(node, "global was previously declared as not <" .. node.attribute .. ">: " .. varname)
         elseif valtype and not self:same_type(existing.t, valtype) then
            self.errs:add(node, "cannot redeclare global with a different type: previous type of " .. varname .. " is %s", existing.t)
         end
         return nil
      end

      local var = { t = valtype, attribute = is_const and "const" or nil }
      self.st[1][varname] = var

      return var
   end

   function TypeChecker:add_internal_function_variables(node: Node, args: TupleType)
      self:add_var(nil, "@is_va", args.is_va and ANY or NIL)
      self:add_var(nil, "@return", node.rets or a_tuple({}))

      if node.typeargs then
         for _, t in ipairs(node.typeargs) do
            local v = self:find_var(t.typearg, "check_only")
            if not v or not v.used_as_type then
               self.errs:add(t, "type argument '%s' is not used in function signature", t)
            end
         end
      end
   end

   function TypeChecker:add_function_definition_for_recursion(node: Node, fnargs: TupleType)
      self:add_var(nil, node.name.tk, type_at(node, a_function {
         min_arity = node.min_arity,
         typeargs = node.typeargs,
         args = fnargs,
         rets = self.get_rets(node.rets),
      }))
   end

   function TypeChecker:end_function_scope(node: Node)
      self.errs:fail_unresolved(self.st[#self.st])
      self:end_scope(node)
   end

   function TypeChecker:resolve_tuple_and_nominal(t: Type): Type
      t = resolve_tuple(t)
      if t is NominalType then
         t = self:resolve_nominal(t)
      end
      assert(not t is NominalType)
      return t
   end

   local function flatten_tuple(vals: TupleType): TupleType
      local vt = vals.tuple
      local n_vals = #vt
      local ret = a_tuple {}
      local rt = ret.tuple

      if n_vals == 0 then
         return ret
      end

      -- get all arguments except the last...
      for i = 1, n_vals - 1 do
         rt[i] = resolve_tuple(vt[i])
      end

      local last = vt[n_vals]
      if last is TupleType then
         -- ...then unpack the last tuple
         local lt = last.tuple
         for _, v in ipairs(lt) do
            table.insert(rt, v)
         end
         ret.is_va = last.is_va
      else
         rt[n_vals] = vt[n_vals]
         ret.is_va = vals.is_va
      end

      return ret
   end

   local function get_assignment_values(vals: TupleType, wanted: integer): TupleType
      if vals == nil then
         return a_tuple {}
      end

      local ret = flatten_tuple(vals)

      -- ...if the last is vararg, repeat its type until it matches the number of wanted args
      if ret.is_va then
         local rt = ret.tuple
         local n_ret = #rt
         if n_ret > 0 and n_ret < wanted then
            local last = rt[n_ret]
            for _ = n_ret + 1, wanted do
               table.insert(rt, last)
            end
         end
      end
      return ret
   end

   function TypeChecker:match_all_record_field_names(node: Node, a: RecordLikeType, field_names: {string}, errmsg: string): Type
      local t: Type
      for _, k in ipairs(field_names) do
         local f = a.fields[k]
         if not t then
            t = f
         else
            if not self:same_type(f, t) then
               errmsg = errmsg .. string.format(" (types of fields '%s' and '%s' do not match)", field_names[1], k)
               t = nil
               break
            end
         end
      end
      if t then
         return t
      else
         return self.errs:invalid_at(node, errmsg)
      end
   end

   function TypeChecker:type_check_index(anode: Node, bnode: Node, a: Type, b: Type): Type
      local orig_a = a
      local orig_b = b
      a = resolve_typedecl(resolve_tuple_and_nominal(a))
      b = resolve_tuple_and_nominal(b)

      if self.feat_lax and is_unknown(a) then
         return UNKNOWN
      end

      local errm: string
      local erra: Type
      local errb: Type

      if a is TupleTableType and self:is_a(b, INTEGER) then
         if bnode.constnum then
            if bnode.constnum >= 1 and bnode.constnum <= #a.types and bnode.constnum == math.floor(bnode.constnum) then
               return a.types[bnode.constnum as integer]
            end

            errm, erra = "index " .. tostring(bnode.constnum) .. " out of range for tuple %s", a
         else
            local array_type = self:arraytype_from_tuple(bnode, a)
            if array_type then
               return array_type.elements
            end

            errm = "cannot index this tuple with a variable because it would produce a union type that cannot be discriminated at runtime"
         end
      elseif a is ArrayLikeType and self:is_a(b, INTEGER) then
         return a.elements
      elseif a is EmptyTableType then
         if a.keys == nil then
            a.keys = self:infer_at(anode, resolve_tuple(orig_b))
         end

         if self:is_a(orig_b, a.keys) then
            return type_at(anode, a_type("unresolved_emptytable_value", {
               emptytable_type = a
            } as UnresolvedEmptyTableValueType))
         end

         errm, erra, errb = "inconsistent index type: got %s, expected %s (type of keys inferred at "
                            .. a.keys.inferred_at.filename .. ":"
                            .. a.keys.inferred_at.y .. ":"
                            .. a.keys.inferred_at.x .. ": )", orig_b, a.keys
      elseif a is MapType then
         if self:is_a(orig_b, a.keys) then
            return a.values
         end

         errm, erra, errb = "wrong index type: got %s, expected %s", orig_b, a.keys
      elseif b is StringType and b.literal then
         local t, e = self:match_record_key(orig_a, anode, b.literal)
         if t then
            return t
         end

         errm, erra = e, orig_a
      elseif a is RecordLikeType then
         if b is EnumType then
            local field_names: {string} = sorted_keys(b.enumset)
            for _, k in ipairs(field_names) do
               if not a.fields[k] then
                  errm, erra = "enum value '" .. k .. "' is not a field in %s", a
                  break
               end
            end
            if not errm then
               return self:match_all_record_field_names(bnode, a, field_names,
                         "cannot index, not all enum values map to record fields of the same type")
            end
         elseif self:is_a(b, STRING) then
            errm, erra = "cannot index object of type %s with a string, consider using an enum", orig_a
         else
            errm, erra, errb = "cannot index object of type %s with %s", orig_a, orig_b
         end
      else
         errm, erra, errb = "cannot index object of type %s with %s", orig_a, orig_b
      end

      local meta_t = self:check_metamethod(anode, "__index", a, orig_b, orig_a, orig_b)
      if meta_t then
         return meta_t
      end

      return self.errs:invalid_at(bnode, errm, erra, errb)
   end

   function TypeChecker:find_record_to_extend(exp: Node): Type, Variable, string
      -- base
      if exp.kind == "type_identifier" then
         local v = self:find_var(exp.tk)
         if not v then
            return nil, nil, exp.tk
         end

         local t = v.t
         if t is TypeDeclType then
            if t.closed then
               return nil, nil, exp.tk
            end

            return t.def, v, exp.tk
         end

         return t, v, exp.tk
      -- recurse
      elseif exp.kind == "op" then -- assert(exp.op.op == ".")
         local t, v, rname = self:find_record_to_extend(exp.e1)
         local fname = exp.e2.tk
         local dname = rname .. "." .. fname
         if not t then
            return nil, nil, dname
         end
         if not t is RecordLikeType then
            return nil, nil, dname
         end
         t = t.fields[fname]

         if t is TypeDeclType then
            t = t.def
         elseif t is TypeAliasType then
            t = t.alias_to.resolved
         end

         return t, v, dname
      end
   end

   local function typedecl_to_nominal(where: Where, name: string, t: TypeDeclType, resolved?: Type): Type
      local typevals: {Type}
      local def = t.def
      if def is HasTypeArgs then
         typevals = {}
         for _, a in ipairs(def.typeargs) do
            table.insert(typevals, a_type("typevar", {
               typevar = a.typearg,
               constraint = a.constraint,
            } as TypeVarType))
         end
      end
      return type_at(where, a_type("nominal", {
         typevals = typevals,
         names = { name },
         found = t,
         resolved = resolved,
      } as NominalType))
   end

   function TypeChecker:get_self_type(exp: Node): Type
      -- base
      if exp.kind == "type_identifier" then
         local t = self:find_var_type(exp.tk)
         if not t then
            return nil
         end

         if t is TypeDeclType then
            return typedecl_to_nominal(exp, exp.tk, t)
         else
            return t
         end
      -- recurse
      elseif exp.kind == "op" then -- assert(exp.op.op == ".")
         local t = self:get_self_type(exp.e1)
         if not t then
            return nil
         end

         if t is NominalType then
            local found = t.found
            if found then
               if found is TypeDeclType then
                  local def = found.def
                  if def is RecordLikeType and def.fields[exp.e2.tk] then
                     table.insert(t.names, exp.e2.tk)
                     t.found = def.fields[exp.e2.tk]
                  end
               end
            end
         elseif t is RecordLikeType then
            return t.fields and t.fields[exp.e2.tk]
         end
         return t
      end
   end

   -- Inference engine for 'is' operator
   local facts_and: function(where: Where, f1: Fact, f2: Fact): Fact
   local facts_or: function(where: Where, f1: Fact, f2: Fact): Fact
   local facts_not: function(where: Where, f1: Fact): Fact
   local FACT_TRUTHY: Fact
   do
      local IsFact_mt: metatable<IsFact> = {
         __tostring = function(f: IsFact): string
            return ("(%s is %s)"):format(f.var, show_type(f.typ))
         end
      }

      setmetatable(IsFact, {
         __call = function(_: IsFact, fact: Fact): IsFact
            fact.fact = "is"
            return setmetatable(fact as IsFact, IsFact_mt)
         end,
      })

      local EqFact_mt: metatable<EqFact> = {
         __tostring = function(f: EqFact): string
            return ("(%s == %s)"):format(f.var, show_type(f.typ))
         end
      }

      setmetatable(EqFact, {
         __call = function(_: EqFact, fact: Fact): EqFact
            fact.fact = "=="
            return setmetatable(fact as EqFact, EqFact_mt)
         end,
      })

      local TruthyFact_mt: metatable<TruthyFact> = {
         __tostring = function(_f: TruthyFact): string
            return "*"
         end
      }

      setmetatable(TruthyFact, {
         __call = function(_: TruthyFact, fact: Fact): TruthyFact
            fact.fact = "truthy"
            return setmetatable(fact as TruthyFact, TruthyFact_mt)
         end,
      })

      local NotFact_mt: metatable<NotFact> = {
         __tostring = function(f: NotFact): string
            return ("(not %s)"):format(tostring(f.f1))
         end
      }

      setmetatable(NotFact, {
         __call = function(_: NotFact, fact: Fact): NotFact
            fact.fact = "not"
            return setmetatable(fact as NotFact, NotFact_mt)
         end,
      })

      local AndFact_mt: metatable<AndFact> = {
         __tostring = function(f: AndFact): string
            return ("(%s and %s)"):format(tostring(f.f1), tostring(f.f2))
         end
      }

      setmetatable(AndFact, {
         __call = function(_: AndFact, fact: Fact): AndFact
            fact.fact = "and"
            return setmetatable(fact as AndFact, AndFact_mt)
         end,
      })

      local OrFact_mt: metatable<OrFact> = {
         __tostring = function(f: OrFact): string
            return ("(%s or %s)"):format(tostring(f.f1), tostring(f.f2))
         end
      }

      setmetatable(OrFact, {
         __call = function(_: OrFact, fact: Fact): OrFact
            fact.fact = "or"
            return setmetatable(fact as OrFact, OrFact_mt)
         end,
      })

      FACT_TRUTHY = TruthyFact {}

      facts_and = function(where: Where, f1: Fact, f2: Fact): Fact
         return AndFact { f1 = f1, f2 = f2, where = where }
      end

      facts_or = function(where: Where, f1: Fact, f2: Fact): Fact
         if f1 and f2 then
            return OrFact { f1 = f1, f2 = f2, where = where }
         else
            return nil
         end
      end

      facts_not = function(where: Where, f1: Fact): Fact
         if f1 then
            return NotFact { f1 = f1, where = where }
         else
            return nil
         end
      end

      -- t1 ∪ t2
      local function unite_types(t1: Type, t2: Type): Type, string
         return unite({t2, t1})
      end

      -- t1 ∩ t2
      local function intersect_types(self: TypeChecker, t1: Type, t2: Type): Type, string
         if t2 is UnionType then
            t1, t2 = t2, t1
         end
         if t1 is UnionType then
            local out = {}
            for _, t in ipairs(t1.types) do
               if self:is_a(t, t2) then
                  table.insert(out, t)
               end
            end
            return unite(out)
         else
            if self:is_a(t1, t2) then
               return t1
            elseif self:is_a(t2, t1) then
               return t2
            else
               return NIL -- because of implicit nil in all unions
            end
         end
      end

      local function resolve_if_union(t: Type): Type
         local rt = resolve_tuple_and_nominal(t)
         if rt is UnionType then
            return rt
         end
         return t
      end

      -- t1 - t2
      local function subtract_types(self: TypeChecker, t1: Type, t2: Type): Type
         local types: {Type} = {}

         t1 = resolve_if_union(t1)

         -- poly are not first-class, so we don't handle them here
         if not t1 is UnionType then
            return t1
         end

         t2 = resolve_if_union(t2)
         local t2types = t2 is UnionType and t2.types or { t2 }

         for _, at in ipairs(t1.types) do
            local not_present = true
            for _, bt in ipairs(t2types) do
               if self:same_type(at, bt) then
                  not_present = false
                  break
               end
            end
            if not_present then
               table.insert(types, at)
            end
         end

         if #types == 0 then
            return NIL -- because of implicit nil in all unions
         end

         return unite(types)
      end

      local eval_not: function(TypeChecker, f: Fact): {string:IsFact|EqFact}
      local not_facts: function(TypeChecker, fs: {string:IsFact|EqFact}): {string:IsFact|EqFact}
      local or_facts: function(TypeChecker, fs1: {string:IsFact|EqFact}, fs2: {string:IsFact|EqFact}): {string:IsFact|EqFact}
      local and_facts: function(TypeChecker, fs1: {string:IsFact|EqFact}, fs2: {string:IsFact|EqFact}): {string:IsFact|EqFact}
      local eval_fact: function(TypeChecker, f: Fact): {string:IsFact|EqFact}

      local function invalid_from(f: IsFact): IsFact
         return IsFact { fact = "is", var = f.var, typ = INVALID, where = f.where }
      end

      not_facts = function(self: TypeChecker, fs: {string:IsFact|EqFact}): {string:IsFact|EqFact}
         local ret: {string:IsFact|EqFact} = {}
         for var, f in pairs(fs) do
            local typ = self:find_var_type(f.var, "check_only")

            if not typ then
               ret[var] = EqFact { var = var, typ = INVALID, where = f.where }
            elseif f is EqFact then
               -- nothing is known from negation of equality; widen back
               ret[var] = EqFact { var = var, typ = typ }
            elseif typ.typename == "typevar" then
               assert(f.fact == "is")
               -- nothing is known from negation on typeargs; widen back (no 'where')
               ret[var] = EqFact { var = var, typ = typ }
            elseif not self:is_a(f.typ, typ) then
               assert(f.fact == "is")
               self.errs:add_warning("branch", f.where, f.var .. " (of type %s) can never be a %s", show_type(typ), show_type(f.typ))
               ret[var] = EqFact { var = var, typ = INVALID, where = f.where }
            else
               assert(f.fact == "is")
               ret[var] = IsFact { var = var, typ = subtract_types(self, typ, f.typ), where = f.where }
            end
         end
         return ret
      end

      eval_not = function(self: TypeChecker, f: Fact): {string:IsFact|EqFact}
         if not f then
            return {}
         elseif f is IsFact then
            return not_facts(self, {[f.var] = f})
         elseif f is NotFact then
            return eval_fact(self, f.f1)
         elseif f is AndFact and f.f2 and f.f2.fact == "truthy" then
            return eval_not(self, f.f1)
         elseif f is OrFact and f.f2 and f.f2.fact == "truthy" then
            return eval_fact(self, f.f1)
         elseif f is AndFact then
            return or_facts(self, not_facts(self, eval_fact(self, f.f1)), not_facts(self, eval_fact(self, f.f2)))
         elseif f is OrFact then
            return and_facts(self, not_facts(self, eval_fact(self, f.f1)), not_facts(self, eval_fact(self, f.f2)))
         else
            return not_facts(self, eval_fact(self, f))
         end
      end

      or_facts = function(_self: TypeChecker, fs1: {string:IsFact|EqFact}, fs2: {string:IsFact|EqFact}): {string:IsFact|EqFact}
         local ret: {string:IsFact|EqFact} = {}

         for var, f in pairs(fs2) do
            if fs1[var] then
               local united = unite_types(f.typ, fs1[var].typ)
               if fs1[var].fact == "is" and f.fact == "is" then
                  ret[var] = IsFact { var = var, typ = united, where = f.where }
               else
                  ret[var] = EqFact { var = var, typ = united, where = f.where }
               end
            end
         end

         return ret
      end

      and_facts = function(self: TypeChecker, fs1: {string:IsFact|EqFact}, fs2: {string:IsFact|EqFact}): {string:IsFact|EqFact}
         local ret: {string:IsFact|EqFact} = {}
         local has: {FactType:boolean} = {}

         for var, f in pairs(fs1) do
            local rt: Type
            local ctor: IsFact | EqFact = EqFact
            if fs2[var] then
               if fs2[var].fact == "is" and f.fact == "is" then
                  ctor = IsFact
               end
               rt = intersect_types(self, f.typ, fs2[var].typ)
            else
               rt = f.typ
            end
            local ff = ctor { var = var, typ = rt, where = f.where }
            ret[var] = ff
            has[ff.fact] = true
         end

         for var, f in pairs(fs2) do
            if not fs1[var] then
               ret[var] = EqFact { var = var, typ = f.typ, where = f.where }
               has["=="] = true
            end
         end

         if has["is"] and has["=="] then
            for _, f in pairs(ret) do
               f.fact = "=="
            end
         end

         return ret
      end

      eval_fact = function(self: TypeChecker, f: Fact): {string:IsFact|EqFact}
         if not f then
            return {}
         elseif f is IsFact then
            local typ = self:find_var_type(f.var, "check_only")
            if not typ then
               return { [f.var] = invalid_from(f) }
            end
            if typ.typename ~= "typevar" then
               if self:is_a(typ, f.typ) then
                  -- drop this warning because of implicit nil in all unions
                  -- self.errs:add_warning("branch", f.where, f.var .. " (of type %s) is always a %s", show_type(typ), show_type(f.typ))
                  return { [f.var] = f }
               elseif not self:is_a(f.typ, typ) then
                  self.errs:add(f.where, f.var .. " (of type %s) can never be a %s", typ, f.typ)
                  return { [f.var] = invalid_from(f) }
               end
            end
            return { [f.var] = f }
         elseif f is EqFact then
            return { [f.var] = f }
         elseif f is NotFact then
            return eval_not(self, f.f1)
         elseif f is TruthyFact then
            return {}
         elseif f is AndFact and f.f2 and f.f2.fact == "truthy" then
            return eval_fact(self, f.f1)
         elseif f is OrFact and f.f2 and f.f2.fact == "truthy" then
            return eval_not(self, f.f1)
         elseif f is AndFact then
            return and_facts(self, eval_fact(self, f.f1), eval_fact(self, f.f2))
         elseif f is OrFact then
            return or_facts(self, eval_fact(self, f.f1), eval_fact(self, f.f2))
         end
      end

      function TypeChecker:apply_facts(where: Where, known: Fact)
         if not known then
            return
         end

         local facts = eval_fact(self, known)

         for v, f in pairs(facts) do
            if f.typ.typename == "invalid" then
               self.errs:add(where, "cannot resolve a type for " .. v .. " here")
            end
            local t = self:infer_at(where, f.typ)
            if not f.where then
               t.inferred_at = nil
            end
            self:add_var(nil, v, t, "const", "narrow")
         end
      end
   end

   function TypeChecker:dismiss_unresolved(name: string)
      for i = #self.st, 1, -1 do
         local unresolved = find_unresolved(i)
         if unresolved then
            local uses = unresolved.nominals[name]
            if uses then
               for _, t in ipairs(uses) do
                  self:resolve_nominal(t)
               end
               unresolved.nominals[name] = nil
               return
            end
         end
      end
   end

   local type_check_funcall: function(node: Node, a: Type, b: Type, argdelta?: integer): InvalidOrTupleType

   local function special_pcall_xpcall(self: TypeChecker, node: Node, _a: Type, b: TupleType, argdelta: integer): Type
      local base_nargs = (node.e1.tk == "xpcall") and 2 or 1
      if #node.e2 < base_nargs then
         self.errs:add(node, "wrong number of arguments (given " .. #node.e2 .. ", expects at least " .. base_nargs .. ")")
         return a_tuple { BOOLEAN }
      end

      -- The function called by pcall/xpcall is invoked as a regular function,
      -- so we wish to avoid incorrect error messages / unnecessary warning messages
      -- associated with calling methods as functions
      local ftype = table.remove(b.tuple, 1)
      ftype = shallow_copy_new_type(ftype)
      if ftype is FunctionType then
         ftype.is_method = false
      end

      local fe2: Node = {}
      if node.e1.tk == "xpcall" then
         base_nargs = 2
         local msgh = table.remove(b.tuple, 1)
         self:assert_is_a(node.e2[2], msgh, XPCALL_MSGH_FUNCTION, "in message handler")
      end
      for i = base_nargs + 1, #node.e2 do
         table.insert(fe2, node.e2[i])
      end
      local fnode: Node = {
         y = node.y,
         x = node.x,
         kind = "op",
         op = { op = "@funcall" },
         e1 = node.e2[1],
         e2 = fe2,
      }
      local rets = type_check_funcall(fnode, ftype, b, argdelta + base_nargs)
      if rets is InvalidType then
         return rets
      end
      table.insert(rets.tuple, 1, BOOLEAN)
      return rets
   end

   local special_functions: {string : function(TypeChecker, Node,Type,TupleType,integer):InvalidOrTupleType } = {
      ["pairs"] = function(self: TypeChecker, node: Node, a: Type, b: TupleType, argdelta: integer): InvalidOrTupleType
         if not b.tuple[1] then
            return self.errs:invalid_at(node, "pairs requires an argument")
         end
         local t = resolve_tuple_and_nominal(b.tuple[1])
         if t is ArrayLikeType then
            self.errs:add_warning("hint", node, "hint: applying pairs on an array: did you intend to apply ipairs?")
         end

         if t.typename ~= "map" then
            if not (self.feat_lax and is_unknown(t)) then
               if t is RecordLikeType then
                  self:match_all_record_field_names(node.e2, t, t.field_order,
                     "attempting pairs on a record with attributes of different types")
                  local ct = t.typename == "record" and "{string:any}" or "{any:any}"
                  self.errs:add_warning("hint", node.e2, "hint: if you want to iterate over fields of a record, cast it to " .. ct)
               else
                  self.errs:add(node.e2, "cannot apply pairs on values of type: %s", t)
               end
            end
         end

         return (self:type_check_function_call(node, a, b, argdelta))
      end,

      ["ipairs"] = function(self: TypeChecker, node: Node, a: Type, b: TupleType, argdelta: integer): InvalidOrTupleType
         if not b.tuple[1] then
            return self.errs:invalid_at(node, "ipairs requires an argument")
         end
         local orig_t = b.tuple[1]
         local t = resolve_tuple_and_nominal(orig_t)

         if t is TupleTableType then
            local arr_type = self:arraytype_from_tuple(node.e2, t)
            if not arr_type then
               return self.errs:invalid_at(node.e2, "attempting ipairs on tuple that's not a valid array: %s", orig_t)
            end
         elseif not t is ArrayLikeType then
            if not (self.feat_lax and (is_unknown(t) or t is EmptyTableType)) then
               return self.errs:invalid_at(node.e2, "attempting ipairs on something that's not an array: %s", orig_t)
            end
         end

         return (self:type_check_function_call(node, a, b, argdelta))
      end,

      ["rawget"] = function(self: TypeChecker, node: Node, _a: Type, b: TupleType, _argdelta: integer): InvalidOrTupleType
         -- TODO should those offsets be fixed by _argdelta?
         if #b.tuple == 2 then
            return a_tuple({ self:type_check_index(node.e2[1], node.e2[2], b.tuple[1], b.tuple[2]) })
         else
            return self.errs:invalid_at(node, "rawget expects two arguments")
         end
      end,

      ["print_type"] = function(self: TypeChecker, node: Node, _a: Type, b: TupleType, _argdelta: integer): InvalidOrTupleType
         -- TODO should those offsets be fixed by _argdelta?
         if #b.tuple == 0 then
            -- when called with no arguments, print all variables currently in scope and their types.
            print("-----------------------------------------")
            for i, scope in ipairs(self.st) do
               for s, v in pairs(scope) do
                  print(("%2d %-14s %-11s %s"):format(i, s, v.t.typename, show_type(v.t):sub(1, 50)))
               end
            end
            print("-----------------------------------------")
            return a_tuple({})
         else
            local t = show_type(b.tuple[1])
            print(t)
            self.errs:add_warning("debug", node.e2[1], "type is: %s", t)
            return b
         end
      end,

      ["require"] = function(self: TypeChecker, node: Node, _a: Type, b: TupleType, _argdelta: integer): InvalidOrTupleType
         if #b.tuple ~= 1 then
            return self.errs:invalid_at(node, "require expects one literal argument")
         end
         if node.e2[1].kind ~= "string" then
            return self.errs:invalid_at(node, "don't know how to resolve a dynamic require")
         end

         local module_name = assert(node.e2[1].conststr)
         local t, found = require_module(module_name, self.feat_lax, self.env)
         if not found then
            return self.errs:invalid_at(node, "module not found: '" .. module_name .. "'")
         end

         if t.typename == "invalid" then
            if self.feat_lax then
               return a_tuple({ UNKNOWN })
            end
            return self.errs:invalid_at(node, "no type information for required module: '" .. module_name .. "'")
         end

         self.dependencies[module_name] = t.filename
         return type_at(node, a_tuple({ t }))
      end,

      ["pcall"] = special_pcall_xpcall,
      ["xpcall"] = special_pcall_xpcall,

      ["assert"] = function(self: TypeChecker, node: Node, a: Type, b: TupleType, argdelta: integer): InvalidOrTupleType
         node.known = FACT_TRUTHY
         local r = self:type_check_function_call(node, a, b, argdelta)
         self:apply_facts(node, node.e2[1].known)
         return r
      end,
   }

   function TypeChecker:type_check_funcall(node: Node, a: Type, b: TupleType, argdelta?: integer): InvalidOrTupleType
      argdelta = argdelta or 0
      if node.e1.kind == "variable" then
         local special = special_functions[node.e1.tk]
         if special then
            return special(self, node, a, b, argdelta)
         else
            return (self:type_check_function_call(node, a, b, argdelta))
         end
      elseif node.e1.op and node.e1.op.op == ":" then
         table.insert(b.tuple, 1, node.e1.receiver)
         return (self:type_check_function_call(node, a, b, -1))
      else
         return (self:type_check_function_call(node, a, b, argdelta))
      end
   end

   -- is the i-th assignment in a local declaration of the form `x = x` ?
   local function is_localizing_a_variable(node: Node, i: integer): boolean
      return node.exps
         and node.exps[i]
         and node.exps[i].kind == "variable"
         and node.exps[i].tk == node.vars[i].tk
   end

   function TypeChecker:missing_initializer(node: Node, i: integer, name: string): (InvalidType | UnknownType)
      if self.feat_lax then
         return UNKNOWN
      else
         if node.exps then
            return self.errs:invalid_at(node.vars[i], "assignment in declaration did not produce an initial value for variable '" .. name .. "'")
         else
            return self.errs:invalid_at(node.vars[i], "variable '" .. name .. "' has no type or initial value")
         end
      end
   end

   local function set_expected_types_to_decltuple(_: TypeChecker, node: Node, children: {Type})
      local decltuple = node.kind == "assignment" and children[1] or node.decltuple
      assert(decltuple is TupleType)
      local decls = decltuple.tuple
      if decls and node.exps then
         local ndecl = #decls
         local nexps = #node.exps
         for i = 1, nexps do
            local typ: Type
            typ = decls[i]
            if typ then
               if i == nexps and ndecl > nexps then
                  typ = type_at(node, a_tuple {})
                  for a = i, ndecl do
                     table.insert(typ.tuple, decls[a])
                  end
               end
               node.exps[i].expected = typ
               node.exps[i].expected_context = { kind = node.kind, name = node.vars[i].tk }
            end
         end
      end
   end

   local function is_positive_int(n: number): boolean
      return n and n >= 1 and math.floor(n) == n
   end

   local context_name: {NodeKind: string} = {
      ["local_declaration"] = "in local declaration",
      ["global_declaration"] = "in global declaration",
      ["assignment"] = "in assignment",
   }

   local function in_context(ctx: Node.ExpectedContext, msg: string): string
      if not ctx then
         return msg
      end
      local where = context_name[ctx.kind]
      if where then
         return where .. ": " .. (ctx.name and ctx.name .. ": " or "") .. msg
      else
         return msg
      end
   end

   local function infer_table_literal(self: TypeChecker, node: Node, children: {LiteralTableItemType}): Type
      local is_record = false
      local is_array = false
      local is_map = false

      local is_tuple = false
      local is_not_tuple = false

      local last_array_idx = 1
      local largest_array_idx = -1

      local seen_keys: {CheckableKey:Where} = {}

      -- array, tupletable
      local types: {Type}
      -- record
      local fields: {string:Type}
      local field_order: {string}
      -- array, record
      local elements: Type
      -- map
      local keys, values: Type, Type

      for i, child in ipairs(children) do
         local ck = child.kname
         local n = node[i].key.constnum
         local b: boolean = nil
         if child.ktype.typename == "boolean" then
            b = (node[i].key.tk == "true")
         end

         local key: CheckableKey = ck or n or b
         self.errs:check_redeclared_key(node[i], nil, seen_keys, key)

         local uvtype = resolve_tuple(child.vtype)
         if ck then
            is_record = true
            if not fields then
               fields = {}
               field_order = {}
            end
            fields[ck] = uvtype
            table.insert(field_order, ck)
         elseif is_number_type(child.ktype) then
            is_array = true
            if not is_not_tuple then
               is_tuple = true
            end
            if not types then
               types = {}
            end

            if node[i].key_parsed == "implicit" then
               local cv = child.vtype
               if i == #children and cv is TupleType then
                  -- need to expand last item in an array (e.g { 1, 2, 3, f() })
                  for _, c in ipairs(cv.tuple) do
                     elements = self:expand_type(node, elements, c)
                     types[last_array_idx] = resolve_tuple(c)
                     last_array_idx = last_array_idx + 1
                  end
               else
                  types[last_array_idx] = uvtype
                  last_array_idx = last_array_idx + 1
                  elements = self:expand_type(node, elements, uvtype)
               end
            else -- explicit
               if not is_positive_int(n) then
                  elements = self:expand_type(node, elements, uvtype)
                  is_not_tuple = true
               elseif n then
                  types[n as integer] = uvtype
                  if n > largest_array_idx then
                     largest_array_idx = n as integer
                  end
                  elements = self:expand_type(node, elements, uvtype)
               end
            end

            if last_array_idx > largest_array_idx then
               largest_array_idx = last_array_idx
            end
            if not elements then
               is_array = false
            end
         else
            is_map = true
            keys = self:expand_type(node, keys, drop_constant_value(child.ktype))
            values = self:expand_type(node, values, uvtype)
         end
      end

      local t: Type

      if is_array and is_map then
         self.errs:add(node, "cannot determine type of table literal")
         t = a_map(
            self:expand_type(node, keys, INTEGER),
            self:expand_type(node, values, elements)
         )
      elseif is_record and is_array then
         t = a_type("record", {
            fields = fields,
            field_order = field_order,
            elements = elements,
            interface_list = {
               type_at(node, an_array(elements))
            }
         } as RecordType)
         -- TODO adopt logic from self:is_array below when we accept tupletable as an interface
      elseif is_record and is_map then
         if keys is StringType then
            for _, fname in ipairs(field_order) do
               values = self:expand_type(node, values, fields[fname])
            end
            t = a_map(keys, values)
         else
            self.errs:add(node, "cannot determine type of table literal")
         end
      elseif is_array then
         local pure_array = true
         if not is_not_tuple then
            local last_t: Type
            for _, current_t in pairs(types as {integer:Type}) do
               if last_t then
                  if not self:same_type(last_t, current_t) then
                     pure_array = false
                     break
                  end
               end
               last_t = current_t
            end
         end
         if pure_array then
            t = an_array(elements)
            t.consttypes = types
            t.inferred_len = largest_array_idx - 1
         else
            t = a_type("tupletable", {}) as TupleTableType
            t.types = types
         end
      elseif is_record then
         t = a_type("record", {
            fields = fields,
            field_order = field_order,
         } as RecordType)
      elseif is_map then
         t = a_map(keys, values)
      elseif is_tuple then
         t = a_type("tupletable", {}) as TupleTableType
         t.types = types
         if not types or #types == 0 then
            self.errs:add(node, "cannot determine type of tuple elements")
         end
      end

      if not t then
         t = a_type("emptytable", {})
      end

      return type_at(node, t)
   end

   function TypeChecker:infer_negation_of_if_blocks(where: Where, ifnode: Node, n: integer)
      local f = facts_not(where, ifnode.if_blocks[1].exp.known)
      for e = 2, n do
         local b = ifnode.if_blocks[e]
         if b.exp then
            f = facts_and(where, f, facts_not(where, b.exp.known))
         end
      end
      self:apply_facts(where, f)
   end

   function TypeChecker:determine_declaration_type(var: Node, node: Node, infertypes: TupleType, i: integer): boolean, Type, boolean
      local ok = true
      local name = var.tk
      local infertype = infertypes and infertypes.tuple[i]
      if self.feat_lax and infertype and infertype.typename == "nil" then
         infertype = nil
      end

      local decltype = node.decltuple and node.decltuple.tuple[i]
      if decltype then
         if resolve_tuple_and_nominal(decltype) == INVALID then
            decltype = INVALID
         end

         if infertype then
            ok = self:assert_is_a(node.vars[i], infertype, decltype, context_name[node.kind], name)
         end
      else
         if infertype then
            if infertype is UnresolvableTypeArgType then
               self.errs:add(node.vars[i], "cannot infer declaration type; an explicit type annotation is necessary")
               ok = false
               infertype = INVALID
            elseif infertype is FunctionType and infertype.is_method then
               -- If we assign a method to a variable, e.g:
               -- `local myfunc = myobj.dothing`,
               -- the variable should not be treated as a method
               infertype = shallow_copy_new_type(infertype)
               infertype.is_method = false
            end
         end
      end

      if var.attribute == "total" then
         local rd = decltype and resolve_tuple_and_nominal(decltype)
         if rd and (rd.typename ~= "map" and rd.typename ~= "record") then
            self.errs:add(var, "attribute <total> only applies to maps and records")
            ok = false
         elseif not infertype then
            self.errs:add(var, "variable declared <total> does not declare an initialization value")
            ok = false
         elseif not (node.exps[i] and node.exps[i].attribute == "total") then
            local ri = resolve_tuple_and_nominal(infertype)
            if not (ri is MapType or ri is RecordType) then
               self.errs:add(var, "attribute <total> only applies to maps and records")
               ok = false
            elseif not ri.is_total then
               local missing = ""
               if ri.missing then
                  missing = " (missing: " .. table.concat(ri.missing, ", ") .. ")"
               end
               if ri is MapType then
                  self.errs:add(var, "map variable declared <total> does not declare values for all possible keys" .. missing)
                  ok = false
               elseif ri is RecordType then
                  self.errs:add(var, "record variable declared <total> does not declare values for all fields" .. missing)
                  ok = false
               end
               ri.is_total = nil
            end
         end
      end

      local t = decltype or infertype
      if t == nil then
         t = self:missing_initializer(node, i, name)
      elseif t is EmptyTableType then
         t.declared_at = node
         t.assigned_to = name
      elseif t is ArrayLikeType then
         t.inferred_len = nil
      elseif t is NominalType then
         self:resolve_nominal(t)
      end

      return ok, t, infertype ~= nil
   end

   function TypeChecker:get_type_declaration(value: Node): Type, Variable
      if value.kind == "op"
         and value.op.op == "@funcall"
         and value.e1.kind == "variable"
         and value.e1.tk == "require"
      then
         local t = special_functions["require"](self, value, self:find_var_type("require"), a_tuple { STRING }, 0)
         if not t is InvalidType then
            return t.tuple[1]
         end
      else
         local newtype = value.newtype
         if newtype is TypeAliasType then
            return self:resolve_typealias(newtype)
         else
            return value.newtype, nil
         end
      end
   end

   local function total_check_key(key: CheckableKey, seen_keys: {CheckableKey:Where}, is_total: boolean, missing: {string}): boolean, {string}
      if not seen_keys[key] then
         missing = missing or {}
         table.insert(missing, tostring(key))
         return false, missing
      end
      return is_total, missing
   end

   local function total_record_check(t: RecordLikeType, seen_keys: {CheckableKey:Where}): boolean, {string}
      if t.meta_field_order then
         return false
      end

      local is_total = true
      local missing: {string}
      for _, key in ipairs(t.field_order) do
         local ftype = t.fields[key]
         if not (ftype is TypeDeclType or ftype is TypeAliasType) then
            is_total, missing = total_check_key(key, seen_keys, is_total, missing)
         end
      end
      return is_total, missing
   end

   local function total_map_check(t: MapType, seen_keys: {CheckableKey:Where}): boolean, {string}
      local k = resolve_tuple_and_nominal(t.keys)
      local is_total = true
      local missing: {string}
      if k is EnumType then
         for _, key in ipairs(sorted_keys(k.enumset)) do
            is_total, missing = total_check_key(key, seen_keys, is_total, missing)
         end
      elseif k.typename == "boolean" then
         for _, key in ipairs({ true, false }) do
            is_total, missing = total_check_key(key, seen_keys, is_total, missing)
         end
      else
         is_total = false
      end
      return is_total, missing
   end

   local enum MissingError
      "missing"
   end

   function TypeChecker:check_assignment(where: Where, vartype: Type, valtype: Type, varname: string, attr: Attribute): Type, Type, MissingError
      if varname then
         if self:widen_back_var(varname) then
            vartype, attr = self:find_var_type(varname)
            if not vartype then
               self.errs:add(where, "unknown variable")
               return nil
            end
         end
      end
      if attr == "close" or attr == "const" or attr == "total" then
         self.errs:add(where, "cannot assign to <" .. attr .. "> variable")
         return nil
      end

      local var = resolve_tuple_and_nominal(vartype)
      if var is TypeDeclType or var is TypeAliasType then
         self.errs:add(where, "cannot reassign a type")
         return nil
      end

      if not valtype then
         self.errs:add(where, "variable is not being assigned a value")
         return nil, nil, "missing"
      end

      self:assert_is_a(where, valtype, vartype, "in assignment")

      local val = resolve_tuple_and_nominal(valtype)

      return var, val
   end

   local function discard_tuple(node: Node, t: Type, b: Type): Type
      if b.typename == "tuple" then
         node.discarded_tuple = true
      end
      return resolve_tuple(t)
   end

   local visit_node: Visitor<TypeChecker, NodeKind, Node, Type> = {}

   visit_node.cbs = {
      ["statements"] = {
         before = function(self: TypeChecker, node: Node)
            self:begin_scope(node)
         end,
         after = function(self: TypeChecker, node: Node, _children: {Type}): Type
            -- if at the top level
            if #self.st == 2 then
               self.errs:fail_unresolved(self.st[2])
            end

            if not node.is_repeat then
               self:end_scope(node)
            end

            return NONE
         end
      },
      ["local_type"] = {
         before = function(self: TypeChecker, node: Node)
            local name = node.var.tk
            local resolved, aliasing = self:get_type_declaration(node.value)
            local var = self:add_var(node.var, name, resolved, node.var.attribute)
            if aliasing then
               var.aliasing = aliasing
            end
         end,
         after = function(self: TypeChecker, node: Node, _children: {Type}): Type
            self:dismiss_unresolved(node.var.tk)
            return NONE
         end,
      },
      ["global_type"] = {
         before = function(self: TypeChecker, node: Node)
            local name = node.var.tk
            local unresolved = get_unresolved()
            if node.value then
               local resolved, aliasing = self:get_type_declaration(node.value)
               local added = self:add_global(node.var, name, resolved)
               node.value.newtype = resolved
               if aliasing then
                  added.aliasing = aliasing
               end

               if added and unresolved.global_types[name] then
                  unresolved.global_types[name] = nil
               end
            else
               if not self.st[1][name] then
                  unresolved.global_types[name] = true
               end
            end
         end,
         after = function(self: TypeChecker, node: Node, _children: {Type}): Type
            self:dismiss_unresolved(node.var.tk)
            return NONE
         end,
      },
      ["local_declaration"] = {
         before = function(self: TypeChecker, node: Node)
            if self.collector then
               for _, var in ipairs(node.vars) do
                  self.collector.reserve_symbol_list_slot(var)
               end
            end
         end,
         before_exp = set_expected_types_to_decltuple,
         after = function(self: TypeChecker, node: Node, children: {Type}): Type
            local valtuple = children[3] as TupleType -- may be nil

            local encountered_close = false
            local infertypes = get_assignment_values(valtuple, #node.vars)
            for i, var in ipairs(node.vars) do
               if var.attribute == "close" then
                  if self.gen_target == "5.4" then
                     if encountered_close then
                        self.errs:add(var, "only one <close> per declaration is allowed")
                     else
                        encountered_close = true
                     end
                  else
                     self.errs:add(var, "<close> attribute is only valid for Lua 5.4 (current target is " .. tostring(self.gen_target) .. ")")
                  end
               end

               local ok, t = self:determine_declaration_type(var, node, infertypes, i)

               if var.attribute == "close" then
                  if not type_is_closable(t) then
                     self.errs:add(var, "to-be-closed variable " .. var.tk .. " has a non-closable type %s", t)
                  elseif node.exps and node.exps[i] and expr_is_definitely_not_closable(node.exps[i]) then
                     self.errs:add(var, "to-be-closed variable " .. var.tk .. " assigned a non-closable value")
                  end
               end

               assert(var)
               self:add_var(var, var.tk, t, var.attribute, is_localizing_a_variable(node, i) and "declaration")

               local infertype = infertypes.tuple[i]
               if ok and infertype then
                  local where = node.exps[i] or node.exps

                  local rt = resolve_tuple_and_nominal(t)
                  if (not rt is EnumType)
                     and ((not t is NominalType) or (rt is UnionType))
                     and not self:same_type(t, infertype)
                  then
                     t = self:infer_at(where, infertype)
                     self:add_var(where, var.tk, t, "const", "narrowed_declaration")
                  end
               end

               if self.collector then
                  self.collector.store_type(var.y, var.x, t)
               end

               self:dismiss_unresolved(var.tk)
            end
            return NONE
         end,
      },
      ["global_declaration"] = {
         before_exp = set_expected_types_to_decltuple,
         after = function(self: TypeChecker, node: Node, children: {Type}): Type
            local valtuple = children[3] as TupleType -- may be nil

            local infertypes = get_assignment_values(valtuple, #node.vars)
            for i, var in ipairs(node.vars) do
               local _, t, is_inferred = self:determine_declaration_type(var, node, infertypes, i)

               if var.attribute == "close" then
                  self.errs:add(var, "globals may not be <close>")
               end

               self:add_global(var, var.tk, t, is_inferred)

               self:dismiss_unresolved(var.tk)
            end
            return NONE
         end,
      },
      ["assignment"] = {
         before_exp = set_expected_types_to_decltuple,
         after = function(self: TypeChecker, node: Node, children: {Type}): Type
            local vartuple = children[1]
            assert(vartuple is TupleType)
            local vartypes = vartuple.tuple
            local valtuple = children[3]
            assert(valtuple is TupleType)
            local valtypes = get_assignment_values(valtuple, #vartypes)
            for i, vartype in ipairs(vartypes) do
               local varnode = node.vars[i]
               local varname = varnode.tk
               local valtype = valtypes.tuple[i]
               local rvar, rval, err = self:check_assignment(varnode, vartype, valtype, varname, varnode.attribute)
               if err == "missing" then
                  if #node.exps == 1 and node.exps[1].kind == "op" and node.exps[1].op.op == "@funcall" then
                     local msg = #valtuple.tuple == 1
                                 and "only 1 value is returned by the function"
                                 or ("only " .. #valtuple.tuple .. " values are returned by the function")
                     self.errs:add_warning("hint", varnode, msg)
                  end
               end

               if rval and rvar then
                  -- assigning a function
                  if rval is FunctionType then
                     self:widen_all_unions()
                  end

                  if varname and (rvar is UnionType or rvar is InterfaceType) then
                     -- narrow unions and interfaces
                     self:add_var(varnode, varname, rval, nil, "narrow")
                  end

                  if self.collector then
                     self.collector.store_type(varnode.y, varnode.x, valtype)
                  end
               end
            end

            return NONE
         end,
      },
      ["if"] = {
         after = function(self: TypeChecker, node: Node, _children: {Type}): Type
            local all_return = true
            for _, b in ipairs(node.if_blocks) do
               if not b.block_returns then
                  all_return = false
                  break
               end
            end
            if all_return then
               node.block_returns = true
               self:infer_negation_of_if_blocks(node, node, #node.if_blocks)
            end

            return NONE
         end,
      },
      ["if_block"] = {
         before = function(self: TypeChecker, node: Node)
            self:begin_scope(node)
            if node.if_block_n > 1 then
               self:infer_negation_of_if_blocks(node, node.if_parent, node.if_block_n - 1)
            end
         end,
         before_statements = function(self: TypeChecker, node: Node)
            if node.exp then
               self:apply_facts(node.exp, node.exp.known)
            end
         end,
         after = function(self: TypeChecker, node: Node, _children: {Type}): Type
            self:end_scope(node)

            if #node.body > 0 and node.body[#node.body].block_returns then
               node.block_returns = true
            end

            return NONE
         end
      },
      ["while"] = {
         before = function(self: TypeChecker, node: Node)
            -- widen all narrowed variables because we don't calculate a fixpoint yet
            self:widen_all_unions(node)
         end,
         before_statements = function(self: TypeChecker, node: Node)
            self:begin_scope(node)
            self:apply_facts(node.exp, node.exp.known)
         end,
         after = end_scope_and_none_type,
      },
      ["label"] = {
         before = function(self: TypeChecker, node: Node)
            -- widen all narrowed variables because we don't calculate a fixpoint yet
            self:widen_all_unions()
            local label_id = "::" .. node.label .. "::"
            if self.st[#self.st][label_id] then
               self.errs:add(node, "label '" .. node.label .. "' already defined")
            end
            local unresolved = find_unresolved()
            local var = self:add_var(node, label_id, type_at(node, a_type("none", {})))
            if unresolved then
               if unresolved.labels[node.label] then
                  var.used = true
               end
               unresolved.labels[node.label] = nil
            end
         end,
         after = function(): Type
            return NONE
         end
      },
      ["goto"] = {
         after = function(self: TypeChecker, node: Node, _children: {Type}): Type
            if not self:find_var_type("::" .. node.label .. "::") then
               local unresolved = get_unresolved(self.st[#self.st])
               unresolved.labels[node.label] = unresolved.labels[node.label] or {}
               table.insert(unresolved.labels[node.label], node)
            end

            return NONE
         end,
      },
      ["repeat"] = {
         before = function(self: TypeChecker, node: Node)
            -- widen all narrowed variables because we don't calculate a fixpoint yet
            self:widen_all_unions(node)
         end,
         -- only end scope after checking `until`, `statements` in repeat body has is_repeat == true
         after = end_scope_and_none_type,
      },
      ["forin"] = {
         before = function(self: TypeChecker, node: Node)
            self:begin_scope(node)
         end,
         before_statements = function(self: TypeChecker, node: Node, children: {Type})
            local exptuple = children[2]
            assert(exptuple is TupleType)
            local exptypes = exptuple.tuple

            self:widen_all_unions(node)
            local exp1 = node.exps[1]
            local args = a_tuple {
               node.exps[2] and exptypes[2],
               node.exps[3] and exptypes[3]
            }
            local exp1type = self:resolve_for_call(exptypes[1], args, false)

            if exp1type is PolyType then
               local _: Type
               _, exp1type = self:type_check_function_call(exp1, exp1type, args, 0, exp1, {node.exps[2], node.exps[3]})
            end

            if exp1type is FunctionType then
               -- TODO: check that exp1's arguments match with (optional self, explicit iterator, state)
               local last: Type
               local rets = exp1type.rets
               for i, v in ipairs(node.vars) do
                  local r = rets.tuple[i]
                  if not r then
                     if rets.is_va then
                        r = last
                     else
                        r = self.feat_lax and UNKNOWN or INVALID
                     end
                  end
                  self:add_var(v, v.tk, r)

                  if self.collector then
                     self.collector.store_type(v.y, v.x, r)
                  end

                  last = r
               end
               local nrets = #rets.tuple
               if (not self.feat_lax) and (not rets.is_va and #node.vars > nrets) then
                  local at = node.vars[nrets + 1]
                  local n_values = nrets == 1 and "1 value" or tostring(nrets) .. " values"
                  self.errs:add(at, "too many variables for this iterator; it produces " .. n_values)
               end
            else
               if not (self.feat_lax and is_unknown(exp1type)) then
                  self.errs:add(exp1, "expression in for loop does not return an iterator")
               end
            end
         end,
         after = end_scope_and_none_type,
      },
      ["fornum"] = {
         before_statements = function(self: TypeChecker, node: Node, children: {Type})
            self:widen_all_unions(node)
            self:begin_scope(node)
            local from_t = resolve_tuple_and_nominal(children[2])
            local to_t = resolve_tuple_and_nominal(children[3])
            local step_t = children[4] and resolve_tuple_and_nominal(children[4])
            local t = (from_t.typename == "integer" and
                       to_t.typename == "integer" and
                       (not step_t or step_t.typename == "integer"))
                      and INTEGER
                      or  NUMBER
            self:add_var(node.var, node.var.tk, t)
         end,
         after = end_scope_and_none_type,
      },
      ["return"] = {
         before = function(self: TypeChecker, node: Node)
            local rets = self:find_var_type("@return")
            if rets and rets is TupleType then
               for i, exp in ipairs(node.exps) do
                  exp.expected = rets.tuple[i]
               end
            end
         end,
         after = function(self: TypeChecker, node: Node, children: {Type}): Type
            local got = children[1]
            assert(got is TupleType)
            local got_t = got.tuple
            local n_got = #got_t

            node.block_returns = true
            local expected = self:find_var_type("@return") as TupleType
            if not expected then
               -- if at the toplevel
               expected = self:infer_at(node, got)
               self.module_type = drop_constant_value(resolve_tuple_and_nominal(expected))
               self.st[2]["@return"] = { t = expected }
            end
            local expected_t = expected.tuple

            local what = "in return value"
            if expected.inferred_at then
               what = what .. inferred_msg(expected)
            end

            local n_expected = #expected_t
            local vatype: Type
            if n_expected > 0 then
               vatype = expected.is_va and expected.tuple[n_expected]
            end

            if n_got > n_expected and (not self.feat_lax) and not vatype then
               self.errs:add(node, what ..": excess return values, expected " .. n_expected .. " %s, got " .. n_got .. " %s", expected, got)
            end

            if n_expected > 1
            and #node.exps == 1
            and node.exps[1].kind == "op"
            and (node.exps[1].op.op == "and" or node.exps[1].op.op == "or")
            and node.exps[1].discarded_tuple then
               self.errs:add_warning("hint", node.exps[1].e2, "additional return values are being discarded due to '" .. node.exps[1].op.op .. "' expression; suggest parentheses if intentional")
            end

            for i = 1, n_got do
               local e = expected_t[i] or vatype
               if e then
                  e = resolve_tuple(e)
                  local where = (node.exps[i] and node.exps[i].x)
                                and node.exps[i]
                                or  node.exps
                  assert(where and where.x)
                  self:assert_is_a(where, got_t[i], e, what)
               end
            end

            return NONE
         end,
      },
      ["variable_list"] = {
         after = function(self: TypeChecker, node: Node, children: {Type}): Type
            local tuple = a_tuple(children)

            tuple = flatten_tuple(tuple)

            for i, t in ipairs(tuple.tuple) do
               local ok, err = ensure_not_abstract(t)
               if not ok then
                  self.errs:add(node[i], err)
               end
            end

            return tuple
         end,
      },
      ["literal_table"] = {
         before = function(_self: TypeChecker, node: Node)
            if node.expected then
               local decltype = resolve_tuple_and_nominal(node.expected)

               if decltype is TypeVarType and decltype.constraint then
                  decltype = resolve_typedecl(resolve_tuple_and_nominal(decltype.constraint))
               end

               if decltype is TupleTableType then
                  for _, child in ipairs(node) do
                     local n = child.key.constnum
                     if n and is_positive_int(n) then
                        child.value.expected = decltype.types[n as integer]
                     end
                  end
               elseif decltype is ArrayLikeType then
                  for _, child in ipairs(node) do
                     if child.key.constnum then
                        child.value.expected = decltype.elements
                     end
                  end
               elseif decltype is MapType then
                  for _, child in ipairs(node) do
                     child.key.expected = decltype.keys
                     child.value.expected = decltype.values
                  end
               end

               if decltype is RecordLikeType then
                  for _, child in ipairs(node) do
                     if child.key.conststr then
                        child.value.expected = decltype.fields[child.key.conststr]
                     end
                  end
               end
            end
         end,
         after = function(self: TypeChecker, node: Node, children: {LiteralTableItemType}): Type
            node.known = FACT_TRUTHY

            if not node.expected then
               return infer_table_literal(self, node, children)
            end

            local decltype = resolve_tuple_and_nominal(node.expected)

            local constraint: Type
            if decltype is TypeVarType and decltype.constraint then
               constraint = resolve_typedecl(decltype.constraint)
               decltype = resolve_tuple_and_nominal(constraint)
            end

            if decltype is UnionType then
               local single_table_type: Type
               local single_table_rt: Type

               for _, t in ipairs(decltype.types) do
                  local rt = resolve_tuple_and_nominal(t)
                  if is_lua_table_type(rt) then
                     if single_table_type then
                        -- multiple table types in union, give up
                        single_table_type = nil
                        single_table_rt = nil
                        break
                     end

                     single_table_type = t
                     single_table_rt = rt
                  end
               end

               if single_table_type then
                  node.expected = single_table_type
                  decltype = single_table_rt
               end
            end

            if not is_lua_table_type(decltype) then
               return infer_table_literal(self, node, children)
            end

            local force_array: Type = nil

            local seen_keys: {CheckableKey:Where} = {}

            for i, child in ipairs(children) do
               local cvtype = resolve_tuple(child.vtype)
               local ck = child.kname
               local n = node[i].key.constnum
               local b: boolean = nil
               if child.ktype.typename == "boolean" then
                  b = (node[i].key.tk == "true")
               end
               self.errs:check_redeclared_key(node[i], node.expected_context, seen_keys, ck or n or b)
               if decltype is RecordLikeType and ck then
                  local df = decltype.fields[ck]
                  if not df then
                     self.errs:add(node[i], in_context(node.expected_context, "unknown field " .. ck))
                  else
                     if df is TypeDeclType or df is TypeAliasType then
                        self.errs:add(node[i], in_context(node.expected_context, "cannot reassign a type"))
                     else
                        self:assert_is_a(node[i], cvtype, df, "in record field", ck)
                     end
                  end
               elseif decltype is TupleTableType and is_number_type(child.ktype) then
                  local dt = decltype.types[n as integer]
                  if not n then
                     self.errs:add(node[i], in_context(node.expected_context, "unknown index in tuple %s"), decltype)
                  elseif not dt then
                     self.errs:add(node[i], in_context(node.expected_context, "unexpected index " .. n .. " in tuple %s"), decltype)
                  else
                     self:assert_is_a(node[i], cvtype, dt, in_context(node.expected_context, "in tuple"), "at index " .. tostring(n))
                  end
               elseif decltype is ArrayLikeType and is_number_type(child.ktype) then
                  local cv = child.vtype
                  if cv is TupleType and i == #children and node[i].key_parsed == "implicit" then
                     -- need to expand last item in an array (e.g { 1, 2, 3, f() })
                     for ti, tt in ipairs(cv.tuple) do
                        self:assert_is_a(node[i], tt, decltype.elements, in_context(node.expected_context, "expected an array"), "at index " .. tostring(i + ti - 1))
                     end
                  else
                     self:assert_is_a(node[i], cvtype, decltype.elements, in_context(node.expected_context, "expected an array"), "at index " .. tostring(n))
                  end
               elseif node[i].key_parsed == "implicit" then
                  if decltype is MapType then
                     self:assert_is_a(node[i], INTEGER, decltype.keys, in_context(node.expected_context, "in map key"))
                     self:assert_is_a(node[i], cvtype, decltype.values, in_context(node.expected_context, "in map value"))
                  end
                  force_array = self:expand_type(node[i], force_array, child.vtype)
               elseif decltype is MapType then
                  force_array = nil
                  self:assert_is_a(node[i], child.ktype, decltype.keys, in_context(node.expected_context, "in map key"))
                  self:assert_is_a(node[i], cvtype, decltype.values, in_context(node.expected_context, "in map value"))
               else
                  self.errs:add(node[i], in_context(node.expected_context, "unexpected key of type %s in table of type %s"), child.ktype, decltype)
               end
            end

            local t: Type
            if force_array then
               t = self:infer_at(node, an_array(force_array))
            else
               t = self:resolve_typevars_at(node, node.expected)
               if node.expected == t and t is NominalType then
                  t = a_type("nominal", {
                     names = t.names,
                     found = t.found,
                     resolved = t.resolved,
                  } as NominalType)
               end
            end

            if decltype is RecordType then
               local rt = resolve_tuple_and_nominal(t)
               if rt is RecordType then
                  rt.is_total, rt.missing = total_record_check(decltype, seen_keys)
               end
            elseif decltype is MapType then
               local rt = resolve_tuple_and_nominal(t)
               if rt is MapType then
                  rt.is_total, rt.missing = total_map_check(decltype, seen_keys)
               end
            end

            if constraint then
               return constraint
            end

            return t
         end,
      },
      ["literal_table_item"] = {
         after = function(self: TypeChecker, node: Node, children: {Type}): Type
            local kname = node.key.conststr
            local ktype = children[1]
            local vtype = children[2]
            if node.itemtype then
               vtype = node.itemtype
               self:assert_is_a(node.value, children[2], node.itemtype, "in table item")
            end
            if vtype is FunctionType and vtype.is_method then
               -- If we assign a method to a table item, e.g.
               -- `local a = { myfunc = myobj.dothing }`
               -- the table item should not be treated as a method
               vtype = shallow_copy_new_type(vtype)
               vtype.is_method = false
            end
            return type_at(node, a_type("literal_table_item", {
               kname = kname,
               ktype = ktype,
               vtype = vtype,
            } as LiteralTableItemType))
         end,
      },
      ["local_function"] = {
         before = function(self: TypeChecker, node: Node)
            self:widen_all_unions()
            if self.collector then
               self.collector.reserve_symbol_list_slot(node)
            end
            self:begin_scope(node)
         end,
         before_statements = function(self: TypeChecker, node: Node, children: {Type})
            local args = children[2]
            assert(args is TupleType)

            self:add_internal_function_variables(node, args)
            self:add_function_definition_for_recursion(node, args)
         end,
         after = function(self: TypeChecker, node: Node, children: {Type}): Type
            local args = children[2]
            assert(args is TupleType)
            local rets = children[3]
            assert(rets is TupleType)

            self:end_function_scope(node)

            local t = type_at(node, self:ensure_fresh_typeargs(a_function {
               min_arity = node.min_arity,
               typeargs = node.typeargs,
               args = args,
               rets = self.get_rets(rets),
            }))

            self:add_var(node, node.name.tk, t)
            return t
         end,
      },
      ["local_macroexp"] = {
         before = function(self: TypeChecker, node: Node)
            self:widen_all_unions()
            if self.collector then
               self.collector.reserve_symbol_list_slot(node)
            end
            self:begin_scope(node)
         end,
         after = function(self: TypeChecker, node: Node, children: {Type}): Type
            local args = children[2]
            assert(args is TupleType)
            local rets = children[3]
            assert(rets is TupleType)

            self:end_function_scope(node)

            self:check_macroexp_arg_use(node.macrodef)

            local t = type_at(node, self:ensure_fresh_typeargs(a_function {
               min_arity = node.macrodef.min_arity,
               typeargs = node.typeargs,
               args = args,
               rets = self.get_rets(rets),
               macroexp = node.macrodef,
            }))

            self:add_var(node, node.name.tk, t)
            return t
         end,
      },
      ["global_function"] = {
         before = function(self: TypeChecker, node: Node)
            self:widen_all_unions()
            self:begin_scope(node)
            if node.implicit_global_function then
               local typ = self:find_var_type(node.name.tk)
               if typ then
                  if typ is FunctionType then
                     node.is_predeclared_local_function = true
                  elseif not self.feat_lax then
                     self.errs:add(node, "cannot declare function: type of " .. node.name.tk .. " is %s", typ)
                  end
               elseif not self.feat_lax then
                  self.errs:add(node, "functions need an explicit 'local' or 'global' annotation")
               end
            end
         end,
         before_statements = function(self: TypeChecker, node: Node, children: {Type})
            local args = children[2]
            assert(args is TupleType)

            self:add_internal_function_variables(node, args)
            self:add_function_definition_for_recursion(node, args)
         end,
         after = function(self: TypeChecker, node: Node, children: {Type}): Type
            local args = children[2]
            assert(args is TupleType)
            local rets = children[3]
            assert(rets is TupleType)

            self:end_function_scope(node)
            if node.is_predeclared_local_function then
               return NONE
            end

            self:add_global(node, node.name.tk, type_at(node, self:ensure_fresh_typeargs(a_function {
               min_arity = node.min_arity,
               typeargs = node.typeargs,
               args = args,
               rets = self.get_rets(rets),
            })))

            return NONE
         end,
      },
      ["record_function"] = {
         before = function(self: TypeChecker, node: Node)
            self:widen_all_unions()
            self:begin_scope(node)
         end,
         before_arguments = function(self: TypeChecker, _node: Node, children: {Type})
            local rtype = resolve_tuple_and_nominal(resolve_typedecl(children[1]))

            -- add type arguments from the record implicitly
            if rtype is RecordLikeType and rtype.typeargs then
               for _, typ in ipairs(rtype.typeargs) do
                  self:add_var(nil, typ.typearg, type_at(typ, a_type("typearg", {
                     typearg = typ.typearg,
                     constraint = typ.constraint,
                  } as TypeArgType)))
               end
            end
         end,
         before_statements = function(self: TypeChecker, node: Node, children: {Type})
            local args = children[3]
            assert(args is TupleType)
            local rets = children[4]
            assert(rets is TupleType)

            local rtype = resolve_tuple_and_nominal(resolve_typedecl(children[1]))

            if self.feat_lax and rtype is UnknownType then
               return
            end

            if rtype is EmptyTableType then
               edit_type(rtype, "record")
               local r = rtype as RecordType
               r.fields = {}
               r.field_order = {}
            end

            if not rtype is RecordLikeType then
               self.errs:add(node, "not a record: %s", rtype)
               return
            end

            local selftype = self:get_self_type(node.fn_owner)
            if node.is_method then
               if not selftype then
                  self.errs:add(node, "could not resolve type of self")
                  return
               end
               args.tuple[1] = selftype
               self:add_var(nil, "self", selftype)
            end

            local fn_type = type_at(node, self:ensure_fresh_typeargs(a_function {
               min_arity = node.min_arity,
               is_method = node.is_method,
               typeargs = node.typeargs,
               args = args,
               rets = self.get_rets(rets),
            }))

            local open_t, open_v, owner_name = self:find_record_to_extend(node.fn_owner)
            local open_k = owner_name .. "." .. node.name.tk
            local rfieldtype = rtype.fields[node.name.tk]
            if rfieldtype then
               rfieldtype = resolve_tuple_and_nominal(rfieldtype)

               if open_v and open_v.implemented and open_v.implemented[open_k] then
                  self.errs:redeclaration_warning(node)
               end

               local ok, err = self:same_type(fn_type, rfieldtype)
               if not ok then
                  if rfieldtype is PolyType then
                     self.errs:add_prefixing(node, err, "type signature does not match declaration: field has multiple function definitions (such polymorphic declarations are intended for Lua module interoperability)")
                     return
                  end

                  local shortname = selftype and show_type(selftype) or owner_name
                  local msg = "type signature of '" .. node.name.tk .. "' does not match its declaration in " .. shortname .. ": "
                  self.errs:add_prefixing(node, err, msg)
                  return
               end
            else
               if self.feat_lax or rtype == open_t then
                  rtype.fields[node.name.tk] = fn_type
                  table.insert(rtype.field_order, node.name.tk)
               else
                  self.errs:add(node, "cannot add undeclared function '" .. node.name.tk .. "' outside of the scope where '" .. owner_name .. "' was originally declared")
                  return
               end

            end

            if open_v then
               if not open_v.implemented then
                  open_v.implemented = {}
               end
               open_v.implemented[open_k] = true
            end

            self:add_internal_function_variables(node, args)
         end,
         after = function(self: TypeChecker, node: Node, _children: {Type}): Type
            self:end_function_scope(node)
            return NONE
         end,
      },
      ["function"] = {
         before = function(self: TypeChecker, node: Node)
            self:widen_all_unions(node)
            self:begin_scope(node)
         end,
         before_statements = function(self: TypeChecker, node: Node, children: {Type})
            local args = children[1]
            assert(args is TupleType)

            self:add_internal_function_variables(node, args)
         end,
         after = function(self: TypeChecker, node: Node, children: {Type}): Type
            local args = children[1]
            assert(args is TupleType)
            local rets = children[2]
            assert(rets is TupleType)

            self:end_function_scope(node)
            return type_at(node, self:ensure_fresh_typeargs(a_function {
               min_arity = node.min_arity,
               typeargs = node.typeargs,
               args = args,
               rets = rets,
            }))
         end,
      },
      ["macroexp"] = {
         before = function(self: TypeChecker, node: Node)
            self:widen_all_unions(node)
            self:begin_scope(node)
         end,
         before_exp = function(self: TypeChecker, node: Node, children: {Type})
            local args = children[1]
            assert(args is TupleType)

            self:add_internal_function_variables(node, args)
         end,
         after = function(self: TypeChecker, node: Node, children: {Type}): Type
            local args = children[1]
            assert(args is TupleType)
            local rets = children[2]
            assert(rets is TupleType)

            self:end_function_scope(node)
            return type_at(node, self:ensure_fresh_typeargs(a_function {
               min_arity = node.min_arity,
               typeargs = node.typeargs,
               args = args,
               rets = rets,
            }))
         end,
      },
      ["cast"] = {
         after = function(_self: TypeChecker, node: Node, _children: {Type}): Type
            return node.casttype
         end
      },
      ["paren"] = {
         before = function(_self: TypeChecker, node: Node)
            node.e1.expected = node.expected
         end,
         after = function(_self: TypeChecker, node: Node, children: {Type}): Type
            node.known = node.e1 and node.e1.known
            return resolve_tuple(children[1])
         end,
      },
      ["op"] = {
         before = function(self: TypeChecker, node: Node)
            self:begin_scope()
            if node.expected then
               if node.op.op == "and" then
                  node.e2.expected = node.expected
               elseif node.op.op == "or" then
                  node.e1.expected = node.expected
                  if not (node.e2.kind == "literal_table" and #node.e2 == 0) then
                     node.e2.expected = node.expected
                  end
               end
            end
         end,
         before_e2 = function(self: TypeChecker, node: Node, children: {Type})
            local e1type = children[1]

            if node.op.op == "and" then
               self:apply_facts(node, node.e1.known)
            elseif node.op.op == "or" then
               self:apply_facts(node, facts_not(node, node.e1.known))
            elseif node.op.op == "@funcall" then
               if e1type is FunctionType then
                  local argdelta = (node.e1.op and node.e1.op.op == ":") and -1 or 0
                  if node.expected then
                     self:is_a(e1type.rets, node.expected)
                  end
                  local e1args = e1type.args.tuple
                  local at = argdelta
                  for _, typ in ipairs(e1args) do
                     at = at + 1
                     if node.e2[at] then
                        node.e2[at].expected = typ
                     end
                  end
                  if e1type.args.is_va then
                     local typ = e1args[#e1args]
                     for i = at + 1, #node.e2 do
                        node.e2[i].expected = typ
                     end
                  end
               end
            elseif node.op.op == "@index" then
               if e1type is MapType then
                  node.e2.expected = e1type.keys
               end
            end
         end,
         after = function(self: TypeChecker, node: Node, children: {Type}): Type
            self:end_scope()

            local a: Type = children[1]
            local b: Type = children[3]

            local orig_a = a
            local orig_b = b
            local ra = a and resolve_tuple_and_nominal(a)
            local rb = b and resolve_tuple_and_nominal(b)

            local expected = node.expected and resolve_tuple_and_nominal(node.expected)

            if ra.typename == "circular_require" or (ra is TypeDeclType and ra.def and ra.def.typename == "circular_require") then
               return self.errs:invalid_at(node, "cannot dereference a type from a circular require")
            end

            if node.op.op == "@funcall" then
               if self.feat_lax and is_unknown(a) then
                  if node.e1.op and node.e1.op.op == ":" and node.e1.e1.kind == "variable" then
                     self.errs:add_unknown_dot(node, node.e1.e1.tk .. "." .. node.e1.e2.tk)
                  end
               end
               local t = type_check_funcall(node, a, b)
               return t
            end

            local ok, err = ensure_not_abstract(ra)
            if not ok then
               self.errs:add(node.e1, err)
            end
            if ra is TypeDeclType and ra.def.typename == "record" then
               ra = ra.def
            end
            if rb then
               ok, err = ensure_not_abstract(rb)
               if not ok then
                  self.errs:add(node.e2, err)
               end
               if rb is TypeDeclType and rb.def.typename == "record" then
                  rb = rb.def
               end
            end

            if node.op.op == "." then
               node.receiver = a

               assert(node.e2.kind == "identifier")
               local bnode: Node = {
                  y = node.e2.y,
                  x = node.e2.x,
                  tk = node.e2.tk,
                  kind = "string",
               }
               local btype = type_at(node.e2, a_type("string", { literal = node.e2.tk } as StringType))
               local t = self:type_check_index(node.e1, bnode, orig_a, btype)

               if t.needs_compat and self.gen_compat ~= "off" then
                  -- only apply to a literal use, not a propagated type
                  if node.e1.kind == "variable" and node.e2.kind == "identifier" then
                     local key = node.e1.tk .. "." .. node.e2.tk
                     node.kind = "variable"
                     node.tk = "_tl_" .. node.e1.tk .. "_" .. node.e2.tk
                     self.all_needs_compat[key] = true
                  end
               end

               return t
            end

            if node.op.op == "@index" then
               return self:type_check_index(node.e1, node.e2, a, b)
            end

            if node.op.op == "as" then
               return b
            end

            if node.op.op == "is" then
               if rb.typename == "integer" then
                  self.all_needs_compat["math"] = true
               end
               if ra is TypeDeclType then
                  self.errs:add(node, "can only use 'is' on variables, not types")
               elseif node.e1.kind == "variable" then
                  self:check_metamethod(node, "__is", ra, resolve_typedecl(rb), orig_a, orig_b)
                  node.known = IsFact { var = node.e1.tk, typ = b, where = node }
               else
                  self.errs:add(node, "can only use 'is' on variables")
               end
               return BOOLEAN
            end

            if node.op.op == ":" then
               node.receiver = a

               -- we handle ':' separately from '.' because ':' is specific to records,
               -- so we produce different error messages
               if self.feat_lax and (is_unknown(a) or a.typename == "typevar") then
                  if node.e1.kind == "variable" then
                     self.errs:add_unknown_dot(node.e1, node.e1.tk .. "." .. node.e2.tk)
                  end
                  return UNKNOWN
               end

               local t, e = self:match_record_key(a, node.e1, node.e2.conststr or node.e2.tk)
               if not t then
                  return self.errs:invalid_at(node.e2, e, resolve_tuple(orig_a))
               end

               return t
            end

            if node.op.op == "not" then
               node.known = facts_not(node, node.e1.known)
               return BOOLEAN
            end

            if node.op.op == "and" then
               node.known = facts_and(node, node.e1.known, node.e2.known)
               return discard_tuple(node, b, b)
            end

            if node.op.op == "or" then
               local t: Type
               if b.typename == "nil" then
                  node.known = nil
                  t = a

               elseif is_lua_table_type(ra) and b is EmptyTableType then
                  node.known = nil
                  t = a

               elseif ((ra is EnumType and rb is StringType and self:is_a(rb, ra))
                  or (ra is StringType and rb is EnumType and self:is_a(ra, rb))) then
                  node.known = nil
                  t = (ra is EnumType and ra or rb)

               elseif expected and expected is UnionType then
                  -- must be checked after string/enum above
                  node.known = facts_or(node, node.e1.known, node.e2.known)
                  local u = unite({ra, rb}, true)
                  if u is UnionType then
                     ok, err = is_valid_union(u)
                     if not ok then
                        u = err and self.errs:invalid_at(node, err, u) or INVALID
                     end
                  end
                  t = u

               elseif self:is_a(rb, ra) then
                  node.known = facts_or(node, node.e1.known, node.e2.known)
                  if expected then
                     local a_is = self:is_a(a, node.expected)
                     local b_is = self:is_a(b, node.expected)
                     if a_is and b_is then
                        t = self:resolve_typevars_at(node, node.expected)
                     elseif a_is then
                        t = resolve_tuple(b)
                     else
                        t = resolve_tuple(a)
                     end
                  else
                     t = resolve_tuple(a)
                  end
                  t = drop_constant_value(t)
               end

               if t then
                  return discard_tuple(node, t, b)
               end
               -- else fallthrough to general binop handler
            end

            if node.op.op == "==" or node.op.op == "~=" then
--               if is_lua_table_type(ra) and is_lua_table_type(rb) then
--                  self:check_metamethod(node, binop_to_metamethod[node.op.op], ra, rb)
--               end

               if ra is EnumType and rb is StringType then
                  if not (rb.literal and ra.enumset[rb.literal]) then
                     return self.errs:invalid_at(node, "%s is not a member of %s", b, a)
                  end
               elseif ra is TupleTableType and rb is TupleTableType and #ra.types ~= #rb.types then
                  return self.errs:invalid_at(node, "tuples are not the same size")
               elseif self:is_a(b, a) or a.typename == "typevar" then
                  if node.op.op == "==" and node.e1.kind == "variable" then
                     node.known = EqFact { var = node.e1.tk, typ = b, where = node }
                  end
               elseif self:is_a(a, b) or b.typename == "typevar" then
                  if node.op.op == "==" and node.e2.kind == "variable" then
                     node.known = EqFact { var = node.e2.tk, typ = a, where = node }
                  end
               elseif self.feat_lax and (is_unknown(a) or is_unknown(b)) then
                  return UNKNOWN
               else
                  return self.errs:invalid_at(node, "types are not comparable for equality: %s and %s", a, b)
               end

               return BOOLEAN
            end

            if node.op.arity == 1 and unop_types[node.op.op] then
               a = ra
               if a is UnionType then
                  a = unite(a.types, true) -- squash unions of string constants
               end

               local types_op = unop_types[node.op.op]

               local t = types_op[a.typename]

               if not t then
                  t = find_in_interface_list(a, function(ty: Type): Type
                     return types_op[ty.typename]
                  end)
               end

               local meta_on_operator: integer
               if not t then
                  local mt_name = unop_to_metamethod[node.op.op]
                  if mt_name then
                     t, meta_on_operator = self:check_metamethod(node, mt_name, a, nil, orig_a, nil)
                  end
                  if not t then
                     self.errs:add(node, "cannot use operator '" .. node.op.op:gsub("%%", "%%%%") .. "' on type %s", resolve_tuple(orig_a))
                     t = INVALID
                  end
               end

               if a is MapType then
                  if a.keys.typename == "number" or a.keys.typename == "integer" then
                      self.errs:add_warning("hint", node, "using the '#' operator on a map with numeric key type may produce unexpected results")
                  else
                      self.errs:add(node, "using the '#' operator on this map will always return 0")
                  end
               end

               if t.typename ~= "boolean" and not is_unknown(t) then
                  node.known = FACT_TRUTHY
               end

               if node.op.op == "~" and self.gen_target == "5.1" then
                  if meta_on_operator then
                     self.all_needs_compat["mt"] = true
                     convert_node_to_compat_mt_call(node, unop_to_metamethod[node.op.op], 1, node.e1)
                  else
                     self.all_needs_compat["bit32"] = true
                     convert_node_to_compat_call(node, "bit32", "bnot", node.e1)
                  end
               end

               return t
            end

            if node.op.arity == 2 and binop_types[node.op.op] then
               if node.op.op == "or" then
                  node.known = facts_or(node, node.e1.known, node.e2.known)
               end

               a = ra
               b = rb

               if a is UnionType then
                  a = unite(a.types, true) -- squash unions of string constants
               end
               if b is UnionType then
                  b = unite(b.types, true) -- squash unions of string constants
               end

               local types_op = binop_types[node.op.op]

               local t = types_op[a.typename] and types_op[a.typename][b.typename]

               local meta_on_operator: integer
               if not t then
                  local mt_name = binop_to_metamethod[node.op.op]
                  if mt_name then
                     t, meta_on_operator = self:check_metamethod(node, mt_name, a, b, orig_a, orig_b)
                  end
                  if not t then
                     self.errs:add(node, "cannot use operator '" .. node.op.op:gsub("%%", "%%%%") .. "' for types %s and %s", resolve_tuple(orig_a), resolve_tuple(orig_b))
                     t = INVALID
                     if node.op.op == "or" then
                        local u = unite({orig_a, orig_b})
                        if u is UnionType and is_valid_union(u) then
                           self.errs:add_warning("hint", node, "if a union type was intended, consider declaring it explicitly")
                        end
                     end
                  end
               end

               if orig_a is NominalType and orig_b is NominalType and not meta_on_operator then
                  if self:is_a(orig_a, orig_b) then
                     t = resolve_tuple(orig_a)
                  else
                     self.errs:add(node, "cannot use operator '" .. node.op.op:gsub("%%", "%%%%") .. "' for distinct nominal types %s and %s", resolve_tuple(orig_a), resolve_tuple(orig_b))
                  end
               end

               if types_op == numeric_binop or node.op.op == ".." then
                  node.known = FACT_TRUTHY
               end

               if node.op.op == "//" and self.gen_target == "5.1" then
                  if meta_on_operator then
                     self.all_needs_compat["mt"] = true
                     convert_node_to_compat_mt_call(node, "__idiv", meta_on_operator, node.e1, node.e2)
                  else
                     local div: Node = { y = node.y, x = node.x, kind = "op", op = an_operator(node, 2, "/"), e1 = node.e1, e2 = node.e2 }
                     convert_node_to_compat_call(node, "math", "floor", div)
                  end
               elseif bit_operators[node.op.op] and self.gen_target == "5.1" then
                  if meta_on_operator then
                     self.all_needs_compat["mt"] = true
                     convert_node_to_compat_mt_call(node, binop_to_metamethod[node.op.op], meta_on_operator, node.e1, node.e2)
                  else
                     self.all_needs_compat["bit32"] = true
                     convert_node_to_compat_call(node, "bit32", bit_operators[node.op.op], node.e1, node.e2)
                  end
               end

               return t
            end

            error("unknown node op " .. node.op.op)
         end,
      },
      ["variable"] = {
         after = function(self: TypeChecker, node: Node, _children: {Type}): Type
            if node.tk == "..." then
               local va_sentinel = self:find_var_type("@is_va")
               if not va_sentinel or va_sentinel.typename == "nil" then
                  return self.errs:invalid_at(node, "cannot use '...' outside a vararg function")
               end
            end

            local t: Type
            if node.tk == "_G" then
               t, node.attribute = self:simulate_g()
            else
               local use: VarUse = node.is_lvalue and "lvalue" or "use"
               t, node.attribute = self:find_var_type(node.tk, use)
            end
            if not t then
               if self.feat_lax then
                  self.errs:add_unknown(node, node.tk)
                  return UNKNOWN
               end

               return self.errs:invalid_at(node, "unknown variable: " .. node.tk)
            end

            if t is TypeDeclType then
               t = typedecl_to_nominal(node, node.tk, t, t)
            end

            return t
         end,
      },
      ["type_identifier"] = {
         after = function(self: TypeChecker, node: Node, _children: {Type}): Type
            local typ, attr = self:find_var_type(node.tk)
            node.attribute = attr
            if typ then
               return typ
            end

            if self.feat_lax then
               self.errs:add_unknown(node, node.tk)
               return UNKNOWN
            end

            return self.errs:invalid_at(node, "unknown variable: " .. node.tk)
         end,
      },
      ["argument"] = {
         after = function(self: TypeChecker, node: Node, children: {Type}): Type
            local t = children[1]
            if not t then
               t = UNKNOWN
            end
            if node.tk == "..." then
               t = a_vararg { t }
            end
            self:add_var(node, node.tk, t).is_func_arg = true
            return t
         end,
      },
      ["identifier"] = {
         after = function(_self: TypeChecker, _node: Node, _children: {Type}): Type
            return NONE -- type is resolved elsewhere
         end,
      },
      ["newtype"] = {
         after = function(_self: TypeChecker, node: Node, _children: {Type}): Type
            return node.newtype
         end,
      },
      ["error_node"] = {
         after = function(_self: TypeChecker, _node: Node, _children: {Type}): Type
            return INVALID
         end,
      }
   }

   visit_node.cbs["break"] = {
      after = function(_self: TypeChecker, _node: Node, _children: {Type}): Type
         return NONE
      end,
   }
   visit_node.cbs["do"] = visit_node.cbs["break"]

   local function after_literal(_self: TypeChecker, node: Node): Type
      node.known = FACT_TRUTHY
      return type_at(node, a_type(node.kind as TypeName, {}))
   end

   visit_node.cbs["string"] = {
      after = function(self: TypeChecker, node: Node, _children: {Type}): Type
         local t = after_literal(self, node) as StringType
         t.literal = node.conststr

         local expected = node.expected
         if expected and expected is EnumType and self:is_a(t, expected) then
            return node.expected
         end

         return t
      end,
   }
   visit_node.cbs["number"] = { after = after_literal }
   visit_node.cbs["integer"] = { after = after_literal }

   visit_node.cbs["boolean"] = {
      after = function(self: TypeChecker, node: Node, _children: {Type}): Type
         local t = after_literal(self, node)
         node.known = (node.tk == "true") and FACT_TRUTHY or nil
         return t
      end,
   }
   visit_node.cbs["nil"] = visit_node.cbs["boolean"]

   visit_node.cbs["..."] = visit_node.cbs["variable"]
   visit_node.cbs["argument_list"] = visit_node.cbs["variable_list"]
   visit_node.cbs["expression_list"] = visit_node.cbs["variable_list"]

   visit_node.after = function(_self: TypeChecker, node: Node, _children: {Type}, t: Type): Type
      if node.expanded then
         apply_macroexp(node)
      end

      return t
   end

   local expand_interfaces: function(Type)
   do
      local function add_interface_fields(self: TypeChecker, what: string, fields: {string:Type}, field_order: {string}, resolved: RecordLikeType, named: NominalType, list?: MetaMode)
         for fname, ftype in fields_of(resolved, list) do
            if fields[fname] then
               if not self:is_a(fields[fname], ftype) then
                  self.errs:add(fields[fname], what .." '" .. fname .. "' does not match definition in interface %s", named)
               end
            else
               table.insert(field_order, fname)
               fields[fname] = ftype
            end
         end
      end

      local function collect_interfaces(self: TypeChecker, list: {ArrayType | NominalType}, t: RecordLikeType, seen:{Type:boolean}): {ArrayType | NominalType}
         if t.interface_list then
            for _, iface in ipairs(t.interface_list) do
               if iface is NominalType then
                  local ri = self:resolve_nominal(iface)
                  if not (ri.typename == "invalid") then
                     assert(ri is InterfaceType, "nominal resolved to " .. ri.typename)
                     if not ri.interfaces_expanded and not seen[ri] then
                        seen[ri] = true
                        collect_interfaces(self, list, ri, seen)
                     end
                     table.insert(list, iface)
                  end
               else
                  if not seen[iface] then
                     seen[iface] = true
                     table.insert(list, iface)
                  end
               end
            end
         end
         return list
      end

      function TypeChecker:expand_interfaces(t: RecordLikeType)
         if t.interfaces_expanded then
            return
         end
         t.interfaces_expanded = true

         t.interface_list = collect_interfaces(self, {}, t, {})

         for _, iface in ipairs(t.interface_list) do
            if iface is NominalType then
               local ri = self:resolve_nominal(iface)
               assert(ri is InterfaceType)
               add_interface_fields(self, "field", t.fields, t.field_order, ri, iface)
               if ri.meta_fields then
                  t.meta_fields = t.meta_fields or {}
                  t.meta_field_order = t.meta_field_order or {}
                  add_interface_fields(self, "metamethod", t.meta_fields, t.meta_field_order, ri, iface, "meta")
               end
            else
               if not t.elements then
                  t.elements = iface
               else
                  if not self:same_type(iface.elements, t.elements) then
                     self.errs:add(t, "incompatible array interfaces")
                  end
               end
            end
         end
      end
   end

   local visit_type: Visitor<TypeChecker, TypeName,Type,Type>
   visit_type = {
      cbs = {
         ["function"] = {
            before = function(self: TypeChecker, _typ: Type)
               self:begin_scope()
            end,
            after = function(self: TypeChecker, typ: Type, _children: {Type}): Type
               self:end_scope()
               return self:ensure_fresh_typeargs(typ)
            end,
         },
         ["record"] = {
            before = function(self: TypeChecker, typ: Type)
               self:begin_scope()
               self:add_var(nil, "@self", type_at(typ, a_typedecl(typ)))

               for fname, ftype in fields_of(typ) do
                  if ftype is TypeAliasType then
                     self:resolve_nominal(ftype.alias_to)
                     self:add_var(nil, fname, ftype)
                  elseif ftype is TypeDeclType then
                     self:add_var(nil, fname, ftype)
                  end
               end
            end,
            after = function(self: TypeChecker, typ: RecordType, children: {Type}): Type
               local i = 1
               if typ.typeargs then
                  for _, _ in ipairs(typ.typeargs) do
                     typ.typeargs[i] = children[i] as TypeArgType
                     i = i + 1
                  end
               end
               if typ.interface_list then
                  for j, _ in ipairs(typ.interface_list) do
                     local iface = children[i]
                     if iface is ArrayType then
                        typ.interface_list[j] = iface
                     elseif iface is NominalType then
                        local ri = self:resolve_nominal(iface)
                        if ri is InterfaceType then
                           typ.interface_list[j] = iface
                        else
                           self.errs:add(children[i], "%s is not an interface", children[i])
                        end
                     end
                     i = i + 1
                  end
               end
               if typ.elements then
                  typ.elements = children[i]
                  i = i + 1
               end
               local fmacros: {FunctionType}
               for name, _ in fields_of(typ) do
                  local ftype = children[i]
                  if ftype is FunctionType then
                     if ftype.macroexp then
                        fmacros = fmacros or {}
                        table.insert(fmacros, ftype)
                     end

                     if ftype.is_method then
                        local fargs = ftype.args.tuple
                        if fargs[1] then
                           local record_name = typ.declname
                           if record_name then
                              local selfarg = fargs[1] as NominalType
                              if selfarg.names[1] ~= record_name or (typ.typeargs and not selfarg.typevals) then
                                 ftype.is_method = false
                              elseif typ.typeargs then
                                 for j=1,#typ.typeargs do
                                    local tv = selfarg.typevals[j]
                                    if not (tv and tv is TypeVarType and tv.typevar == typ.typeargs[j].typearg) then
                                       ftype.is_method = false
                                       break
                                    end
                                 end
                              end
                           end
                        end
                     end
                  end

                  typ.fields[name] = ftype
                  i = i + 1
               end
               for name, _ in fields_of(typ, "meta") do
                  local ftype = children[i]
                  if ftype is FunctionType then
                     if ftype.macroexp then
                        fmacros = fmacros or {}
                        table.insert(fmacros, ftype)
                     end
                  end
                  typ.meta_fields[name] = ftype
                  i = i + 1
               end

               if typ.interface_list then
                  expand_interfaces(typ)
               end

               if fmacros then
                  for _, t in ipairs(fmacros) do
                     local macroexp_type = recurse_node(self, t.macroexp, visit_node, visit_type)

                     self:check_macroexp_arg_use(t.macroexp)

                     if not self:is_a(macroexp_type, t) then
                        self.errs:add(macroexp_type, "macroexp type does not match declaration")
                     end
                  end
               end

               self:end_scope()

               return typ
            end,
         },
         ["typearg"] = {
            after = function(self: TypeChecker, typ: TypeArgType, _children: {Type}): Type
               self:add_var(nil, typ.typearg, type_at(typ, a_type("typearg", {
                  typearg = typ.typearg,
                  constraint = typ.constraint,
               } as TypeArgType)))
               return typ
            end,
         },
         ["typevar"] = {
            after = function(self: TypeChecker, typ: TypeVarType, _children: {Type}): Type
               if not self:find_var_type(typ.typevar) then
                  self.errs:add(typ, "undefined type variable " .. typ.typevar)
               end
               return typ
            end,
         },
         ["nominal"] = {
            after = function(self: TypeChecker, typ: NominalType, _children: {Type}): Type
               if typ.found then
                  return typ
               end

               local t = self:find_type(typ.names, true)
               if t then
                  if t is TypeArgType then
                     -- convert nominal into a typevar
                     typ.names = nil
                     edit_type(typ, "typevar")
                     local tv = typ as TypeVarType
                     tv.typevar = t.typearg
                     tv.constraint = t.constraint
                  elseif t is TypeDeclType then
                     if t.def.typename ~= "circular_require" then
                        typ.found = t
                     end
                  end
               else
                  local name = typ.names[1]
                  local unresolved = get_unresolved()
                  unresolved.nominals[name] = unresolved.nominals[name] or {}
                  table.insert(unresolved.nominals[name], typ)
               end
               return typ
            end,
         },
         ["union"] = {
            after = function(self: TypeChecker, typ: UnionType, _children: {Type}): Type
               local ok, err = is_valid_union(typ)
               if not ok then
                  return err and self.errs:invalid_at(typ, err, typ) or INVALID
               end
               return typ
            end
         },
      },
   }

   local default_type_visitor = {
      after = function(_self: TypeChecker, typ: Type, _children: {Type}): Type
         return typ
      end,
   }

   visit_type.cbs["interface"] = visit_type.cbs["record"]

   visit_type.cbs["string"] = default_type_visitor
   visit_type.cbs["tupletable"] = default_type_visitor
   visit_type.cbs["typedecl"] = default_type_visitor
   visit_type.cbs["typealias"] = default_type_visitor
   visit_type.cbs["array"] = default_type_visitor
   visit_type.cbs["map"] = default_type_visitor
   visit_type.cbs["enum"] = default_type_visitor
   visit_type.cbs["boolean"] = default_type_visitor
   visit_type.cbs["nil"] = default_type_visitor
   visit_type.cbs["number"] = default_type_visitor
   visit_type.cbs["integer"] = default_type_visitor
   visit_type.cbs["thread"] = default_type_visitor
   visit_type.cbs["emptytable"] = default_type_visitor
   visit_type.cbs["literal_table_item"] = default_type_visitor
   visit_type.cbs["unresolved_emptytable_value"] = default_type_visitor
   visit_type.cbs["tuple"] = default_type_visitor
   visit_type.cbs["poly"] = default_type_visitor
   visit_type.cbs["any"] = default_type_visitor
   visit_type.cbs["unknown"] = default_type_visitor
   visit_type.cbs["invalid"] = default_type_visitor
   visit_type.cbs["unresolved"] = default_type_visitor
   visit_type.cbs["none"] = default_type_visitor

   local type VisitorAfterPatcher = function<S, N, T>(VisitorAfter<S, N, T>): VisitorAfter<S, N, T>

   local function internal_compiler_check<S, N>(fn: VisitorAfter<S, N, Type>): VisitorAfter<S, N, Type>
      return function(s: S, n: N, children: {Type}, t: Type): Type
         t = fn and fn(s, n, children, t) or t

         if type(t) ~= "table" then
            error(((n as Node).kind or (n as Type).typename) .. " did not produce a type")
         end
         if type(t.typename) ~= "string" then
            error(((n as Node).kind or (n as Type).typename) .. " type does not have a typename")
         end

         return t
      end
   end

   local function store_type_after<N>(fn: VisitorAfter<TypeChecker, N, Type>): VisitorAfter<TypeChecker, N, Type>
      return function(self: TypeChecker, n: N, children: {Type}, t: Type): Type
         t = fn and fn(self, n, children, t) or t

         local where = n as Where

         if where.y then
            self.collector.store_type(where.y, where.x, t)
         end

         return t
      end
   end

   local function debug_type_after<S>(fn: VisitorAfter<S, Node, Type>): VisitorAfter<S, Node, Type>
      return function(s: S, node: Node, children: {Type}, t: Type): Type
         t = fn and fn(s, node, children, t) or t

         node.debug_type = t
         return t
      end
   end

   local function patch_visitors(my_visit_node: Visitor<TypeChecker, NodeKind, Node, Type>,
                                 after_node: VisitorAfterPatcher<TypeChecker, Node, Type>,
                                 my_visit_type?: Visitor<TypeChecker, TypeName, Type, Type>,
                                 after_type?: VisitorAfterPatcher<TypeChecker, Type, Type>):
                                 Visitor<TypeChecker, NodeKind, Node, Type>,
                                 Visitor<TypeChecker, TypeName, Type, Type>
      if my_visit_node == visit_node then
         my_visit_node = shallow_copy_table(my_visit_node)
      end
      my_visit_node.after = after_node(my_visit_node.after)
      if my_visit_type then
         if my_visit_type == visit_type then
            my_visit_type = shallow_copy_table(my_visit_type)
         end
         my_visit_type.after = after_type(my_visit_type.after)
      else
         my_visit_type = visit_type
      end
   end

   local function set_feat(feat: Feat, default: boolean): boolean
      if feat then
         return (feat == "on")
      else
         return default
      end
   end

   tl.type_check = function(ast: Node, filename: string, module_name: string, opts: TypeCheckOptions, env?: Env): Result, string
      filename = filename or "?"
      module_name = module_name or "?"

      opts = opts or {}

      if not env then
         local err: string
         env, err = tl.new_env({ defaults = opts })
         if err then
            return nil, err
         end
      end

      env.modules[module_name] = a_typedecl(CIRCULAR_REQUIRE)

      local module_type: Type

      local self: TypeChecker = {
         env = env,
         st = { env.globals },
         errs = Errors.new(),
         all_needs_compat = {},
         dependencies = {},
         subtype_relations = TypeChecker.subtype_relations,
         eqtype_relations = TypeChecker.eqtype_relations,
         type_priorities = TypeChecker.type_priorities,
      }

      setmetatable(self, { __index = TypeChecker })

      self.feat_lax   = set_feat(opts.feat_lax   or env.defaults.feat_lax,   false)
      self.feat_arity = set_feat(opts.feat_arity or env.defaults.feat_arity, true)
      self.gen_compat = opts.gen_compat or env.defaults.gen_compat or DEFAULT_GEN_COMPAT
      self.gen_target = opts.gen_target or env.defaults.gen_target or DEFAULT_GEN_TARGET

      if self.gen_target == "5.4" and self.gen_compat ~= "off" then
         return nil, "gen-compat must be explicitly 'off' when gen-target is '5.4'"
      end

      if self.feat_lax then
         self.type_priorities = shallow_copy_table(self.type_priorities)
         self.type_priorities["unknown"] = 0

         self.subtype_relations = shallow_copy_table(self.subtype_relations)

         self.subtype_relations["unknown"] = {}
         self.subtype_relations["unknown"]["*"] = compare_true

         self.subtype_relations["*"] = shallow_copy_table(self.subtype_relations["*"])
         self.subtype_relations["*"]["unknown"] = compare_true
         -- in .lua files, all values can be used in a boolean context
         self.subtype_relations["*"]["boolean"] = compare_true

         self.get_rets = function(rets: TupleType): TupleType
            if #rets.tuple == 0 then
               return a_vararg { UNKNOWN }
            end
            return rets
         end
      else
         self.get_rets = function(rets: TupleType): TupleType
            return rets
         end
      end

      if env.report_types then
         env.reporter = env.reporter or tl.new_type_reporter()
         self.collector = env.reporter:get_collector(filename)
      end

      local visit_node, visit_type = visit_node, visit_type
      if opts.run_internal_compiler_checks then
         visit_node, visit_type = patch_visitors(
            visit_node, internal_compiler_check,
            visit_type, internal_compiler_check
         )
      end
      if self.collector then
         visit_node, visit_type = patch_visitors(
            visit_node, store_type_after,
            visit_type, store_type_after
         )
      end
      if TL_DEBUG then
         visit_node, visit_type = patch_visitors(
            visit_node, debug_type_after
         )
      end

      assert(ast.kind == "statements")
      recurse_node(self, ast, visit_node, visit_type)

      local global_scope = self.st[1]
      close_types(global_scope)
      self.errs:warn_unused_vars(global_scope, true)

      clear_redundant_errors(self.errs.errors)

      add_compat_entries(ast, self.all_needs_compat, self.gen_compat)

      local result = {
         ast = ast,
         env = env,
         type = module_type or BOOLEAN,
         filename = filename,
         warnings = self.errs.warnings,
         type_errors = self.errs.errors,
         dependencies = self.dependencies,
      }

      env.loaded[filename] = result
      table.insert(env.loaded_order, filename or "")

      env.modules[module_name] = result.type

      if self.collector then
         env.reporter:store_result(self.collector, env.globals)
      end

      return result
   end
end

--------------------------------------------------------------------------------
-- High-level API
--------------------------------------------------------------------------------

local function read_full_file(fd: FILE): string, string
   local bom <const> = "\xEF\xBB\xBF"
   local content, err = fd:read("*a")
   if content:sub(1, bom:len()) == bom then
      content = content:sub(bom:len() + 1)
   end
   return content, err
end

local function feat_lax_heuristic(filename?: string, input?: string): Feat
   if filename then
      local _, extension = filename:match("(.*)%.([a-z]+)$")
      extension = extension and extension:lower()

      if extension == "tl" then
         return "off"
      elseif extension == "lua" then
         return "on"
      end
   end
   if input then
      return (input:match("^#![^\n]*lua[^\n]*\n")) and "on" or "off"
   end
   return "off"
end

tl.process = function(filename: string, env: Env, module_name: string, fd: FILE): Result, string
   if env and env.loaded and env.loaded[filename] then
      return env.loaded[filename]
   end

   local input, err: string, string

   if not fd then
      fd, err = io.open(filename, "rb")
      if not fd then
         return nil, "could not open " .. filename .. ": " .. err
      end
   end

   input, err = read_full_file(fd)
   fd:close()
   if not input then
      return nil, "could not read " .. filename .. ": " .. err
   end

   return tl.process_string(input, env, filename, module_name)
end

function tl.target_from_lua_version(str: string): GenTarget
   if str == "Lua 5.1"
      or str == "Lua 5.2" then
      return "5.1"
   elseif str == "Lua 5.3" then
      return "5.3"
   elseif str == "Lua 5.4" then
      return "5.4"
   end
end

local function default_env_opts(runtime: boolean, filename?: string, input?: string): EnvOptions
   local gen_target = runtime and tl.target_from_lua_version(_VERSION) or DEFAULT_GEN_TARGET
   local gen_compat: GenCompat = (gen_target == "5.4") and "off" or DEFAULT_GEN_COMPAT
   return {
      defaults = {
         feat_lax = feat_lax_heuristic(filename, input),
         gen_target = gen_target,
         gen_compat = gen_compat,
         run_internal_compiler_checks = false,
      }
   }
end

function tl.process_string(input: string, env?: Env, filename?: string, module_name?: string): Result
   if filename and not module_name then
      module_name = filename_to_module_name(filename)
   end

   local opts = default_env_opts(false, filename, input)
   env = env or tl.new_env(opts)

   if env.loaded and env.loaded[filename] then
      return env.loaded[filename]
   end
   filename = filename or ""

   local program, syntax_errors = tl.parse(input, filename)

   if (not env.keep_going) and #syntax_errors > 0 then
      local result = {
         ok = false,
         filename = filename,
         module_name = module_name,
         type = BOOLEAN,
         type_errors = {},
         syntax_errors = syntax_errors,
         env = env,
      }
      env.loaded[filename] = result
      table.insert(env.loaded_order, filename)
      return result
   end

   local result = tl.type_check(program, filename, module_name, opts.defaults, env)

   result.syntax_errors = syntax_errors

   return result
end

tl.gen = function(input: string, env: Env, pp: PrettyPrintOptions): string, Result
   env = env or assert(tl.new_env(default_env_opts(false, nil, input)), "Default environment initialization failed")
   local result = tl.process_string(input, env)

   if (not result.ast) or #result.syntax_errors > 0 then
      return nil, result
   end

   local code: string
   code, result.gen_error = tl.pretty_print_ast(result.ast, env.defaults.gen_target, pp)
   return code, result
end

local function tl_package_loader(module_name: string): any, any
   local found_filename, fd, tried = tl.search_module(module_name, false)
   if found_filename then
      local input = read_full_file(fd)
      if not input then
         return table.concat(tried, "\n\t")
      end
      fd:close()
      local program, errs = tl.parse(input, found_filename)
      if #errs > 0 then
         error(found_filename .. ":" .. errs[1].y .. ":" .. errs[1].x .. ": " .. errs[1].msg)
      end

      local env = tl.package_loader_env
      if not env then
         tl.package_loader_env = assert(tl.new_env(), "Default environment initialization failed")
         env = tl.package_loader_env
      end

      local opts = default_env_opts(true, found_filename)

      tl.type_check(program, found_filename, module_name, opts.defaults, env)

      -- TODO: should this be a hard error? this seems analogous to
      -- finding a lua file with a syntax error in it
      local code = assert(tl.pretty_print_ast(program, opts.defaults.gen_target, true))
      local chunk, err = load(code, "@" .. found_filename, "t")
      if chunk then
         return function(modname: string, loader_data: string): any
            if loader_data == nil then
               loader_data = found_filename
            end
            local ret = chunk(modname, loader_data)
            package.loaded[module_name] = ret
            return ret
         end, found_filename
      else
         error("Internal Compiler Error: Teal generator produced invalid Lua. Please report a bug at https://github.com/teal-language/tl\n\n" .. err)
      end
   end
   return table.concat(tried, "\n\t")
end

function tl.loader()
   if package.searchers then
      table.insert(package.searchers, 2, tl_package_loader)
   else
      table.insert(package.loaders, 2, tl_package_loader)
   end
end

local function env_for(opts: EnvOptions, env_tbl: {any:any}): Env
   if not env_tbl then
      if not tl.package_loader_env then
         tl.package_loader_env = tl.new_env(opts)
      end
      return tl.package_loader_env
   end

   if not tl.load_envs then
      tl.load_envs = setmetatable({}, { __mode = "k" })
   end

   tl.load_envs[env_tbl] = tl.load_envs[env_tbl] or tl.new_env(opts)
   return tl.load_envs[env_tbl]
end

tl.load = function(input: string, chunkname: string, mode: LoadMode, ...: {any:any}): LoadFunction, string
   local program, errs = tl.parse(input, chunkname)
   if #errs > 0 then
      return nil, (chunkname or "") .. ":" .. errs[1].y .. ":" .. errs[1].x .. ": " .. errs[1].msg
   end

   local opts = default_env_opts(true, chunkname)

   if not tl.package_loader_env then
      tl.package_loader_env = tl.new_env(opts)
   end

   local filename = chunkname or ("string \"" .. input:sub(45) .. (#input > 45 and "..." or "") .. "\"")
   local result = tl.type_check(program, filename, "?", opts.defaults, env_for(opts, ...))

   if mode and mode:match("c") then
      if #result.type_errors > 0 then
         local errout = {}
         for _, err in ipairs(result.type_errors) do
            table.insert(errout, err.filename .. ":" .. err.y .. ":" .. err.x .. ": " .. (err.msg or ""))
         end
         return nil, table.concat(errout, "\n")
      end

      mode = mode:gsub("c", "") as LoadMode
   end

   local code, err = tl.pretty_print_ast(program, opts.defaults.gen_target, true)
   if not code then
      return nil, err
   end

   return load(code, chunkname, mode, ...)
end

--------------------------------------------------------------------------------
-- Backwards compatibility
--------------------------------------------------------------------------------

function tl.get_types(result: Result): TypeReport, TypeReporter
   return result.env.reporter:get_report(), result.env.reporter
end

tl.init_env = function(lax?: boolean, gen_compat?: boolean | GenCompat, gen_target?: GenTarget, predefined?: {string}): Env, string
   local opts = {
      defaults = {
         feat_lax = (lax and "on" or "off") as Feat,
         gen_compat = ((gen_compat is GenCompat) and gen_compat) or
                       (gen_compat == false and "off") or
                       (gen_compat == true or gen_compat == nil) and "optional",
         gen_target = gen_target or
                      ((_VERSION == "Lua 5.1" or _VERSION == "Lua 5.2") and "5.1") or
                      "5.3",
      },
      predefined_modules = predefined,
   }

   return tl.new_env(opts)
end

return tl
