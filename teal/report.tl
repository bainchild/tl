-- Implementation rationale:
-- * bit 31: (MSB) special ("any", "unknown", "invalid")
--   * "any" satisfies all Lua masks
-- * bits 30-27: if valid: other Teal types ("nominal", "poly", "union", "typevar")
-- * bits 24-26: reserved
-- * bits 20-23: abstract types ("interface")
-- * bits 16-19: if valid: Teal types ("array", "record", "map", "tuple", "enum") that map to a Lua type ("table", "string")
-- * bit 15: if not valid: value is unknown
-- * bits 8-14: reserved
-- * bits 0-7: (LSB) Lua types, one bit for each ("nil", "number", "boolean", "string", table, "function", "userdata", "thread")
--   * every valid value has a Lua type bit set
tl.typecodes = {
   -- Lua types
   NIL                    = 0x00000001,
   NUMBER                 = 0x00000002,
   BOOLEAN                = 0x00000004,
   STRING                 = 0x00000008,
   TABLE                  = 0x00000010,
   FUNCTION               = 0x00000020,
   USERDATA               = 0x00000040,
   THREAD                 = 0x00000080,
   -- Teal types
   INTEGER                = 0x00010002,
   ENUM                   = 0x00010004,
   EMPTY_TABLE            = 0x00000008,
   ARRAY                  = 0x00010008,
   RECORD                 = 0x00020008,
   MAP                    = 0x00040008,
   TUPLE                  = 0x00080008,
   INTERFACE              = 0x00100008,
   POLY                   = 0x20000020,
   UNION                  = 0x40000000,
   -- Indirect types
   NOMINAL                = 0x10000000,
   TYPE_VARIABLE          = 0x08000000,
   -- Special types
   ANY                    = 0xffffffff,
   UNKNOWN                = 0x80008000,
   INVALID                = 0x80000000,
}

   typecodes: {string:integer}

   record TypeInfo
      t: integer

      str: string
      file: string
      x: integer
      y: integer
      ref: integer -- NOMINAL
      fields: {string: integer} -- RECORD
      enums: {string} -- ENUM
      args: {{integer, string}} -- FUNCTION
      rets: {{integer, string}} -- FUNCTION
      vararg: boolean -- FUNCTION
      varret: boolean -- FUNCTION
      types: {integer} -- UNION, POLY, TUPLE
      keys: integer -- MAP
      values: integer -- MAP
      elements: integer -- ARRAY
   end

   record TypeReport
      by_pos: {string: {integer: {integer: integer}}}
      types: {integer: TypeInfo}
      symbols: {{integer, integer, string, integer}}
      globals: {string: integer}
   end

local record TypeReporter
   typeid_to_num: {integer: integer}
   next_num: integer
   tr: TypeReport

   get_typenum: function(TypeReporter, Type): integer
end

local typename_to_typecode <total>: {TypeName:integer} = {
   ["typevar"] = tl.typecodes.TYPE_VARIABLE,
   ["typearg"] = tl.typecodes.TYPE_VARIABLE,
   ["unresolved_typearg"] = tl.typecodes.TYPE_VARIABLE,
   ["unresolvable_typearg"] = tl.typecodes.TYPE_VARIABLE,
   ["function"] = tl.typecodes.FUNCTION,
   ["array"] = tl.typecodes.ARRAY,
   ["map"] = tl.typecodes.MAP,
   ["tupletable"] = tl.typecodes.TUPLE,
   ["interface"] = tl.typecodes.INTERFACE,
   ["record"] = tl.typecodes.RECORD,
   ["enum"] = tl.typecodes.ENUM,
   ["boolean"] = tl.typecodes.BOOLEAN,
   ["string"] = tl.typecodes.STRING,
   ["nil"] = tl.typecodes.NIL,
   ["thread"] = tl.typecodes.THREAD,
   ["number"] = tl.typecodes.NUMBER,
   ["integer"] = tl.typecodes.INTEGER,
   ["union"] = tl.typecodes.UNION,
   ["nominal"] = tl.typecodes.NOMINAL,
   ["circular_require"] = tl.typecodes.NOMINAL,
   ["emptytable"] = tl.typecodes.EMPTY_TABLE,
   ["unresolved_emptytable_value"] = tl.typecodes.EMPTY_TABLE,
   ["poly"] = tl.typecodes.POLY,
   ["any"] = tl.typecodes.ANY,
   ["unknown"] = tl.typecodes.UNKNOWN,
   ["invalid"] = tl.typecodes.INVALID,
   -- types that should be skipped or not present:
   ["none"] = tl.typecodes.UNKNOWN,
   ["tuple"] = tl.typecodes.UNKNOWN,
   ["literal_table_item"] = tl.typecodes.UNKNOWN,
   ["unresolved"] = tl.typecodes.UNKNOWN,
   ["typedecl"] = tl.typecodes.UNKNOWN,
   ["typealias"] = tl.typecodes.UNKNOWN,
   ["*"] = tl.typecodes.UNKNOWN,
}

local skip_types: {TypeName: boolean} = {
   ["none"] = true,
   ["literal_table_item"] = true,
   ["unresolved"] = true,
}

local function sorted_keys<A,B>(m: {A:B}):{A}
   local keys = {}
   for k, _ in pairs(m) do
      table.insert(keys, k)
   end
   table.sort(keys)
   return keys
end

-- mark array for JSON-encoded reports in `tl types`
local function mark_array<T>(x: T): T
   local arr = x as {boolean}
   arr[0] = false
   return x
end

function tl.new_type_reporter(): TypeReporter
   local self: TypeReporter = {
      next_num = 1,
      typeid_to_num = {},
      tr = {
         by_pos = {},
         types = {},
         symbols = mark_array {},
         globals = {},
      },
   }
   return setmetatable(self, { __index = TypeReporter })
end

function TypeReporter:store_function(ti: TypeInfo, rt: FunctionType)
   local args: {{integer, string}} = {}
   for _, fnarg in ipairs(rt.args.tuple) do
      table.insert(args, mark_array { self:get_typenum(fnarg), nil })
   end
   ti.args = mark_array(args)
   local rets: {{integer, string}} = {}
   for _, fnarg in ipairs(rt.rets.tuple) do
      table.insert(rets, mark_array { self:get_typenum(fnarg), nil })
   end
   ti.rets = mark_array(rets)
   ti.vararg = not not rt.args.is_va
   ti.varret = not not rt.rets.is_va
end

function TypeReporter:get_typenum(t: Type): integer
   assert(t.typeid)
   -- try by typeid
   local n = self.typeid_to_num[t.typeid]
   if n then
      return n
   end

   local tr = self.tr

   -- it's a new entry: store and increment
   n = self.next_num

   local rt = t
   if rt is TupleType and #rt.tuple == 1 then
      rt = rt.tuple[1]
   end

   if rt is TypeDeclType then
      rt = rt.def
   elseif rt is TypeAliasType then
      rt = rt.alias_to
   end

   local ti: TypeInfo = {
      t = assert(typename_to_typecode[rt.typename]),
      str = show_type(t, true),
      file = t.filename,
      y = t.y,
      x = t.x,
   }
   tr.types[n] = ti
   self.typeid_to_num[t.typeid] = n
   self.next_num = self.next_num + 1

   if t is NominalType then
      if t.found then
         ti.ref = self:get_typenum(t.found)
      end
      if t.resolved then
         rt = t
      end
   end
   assert(not (rt is TypeDeclType or rt is TypeAliasType))

   if rt is RecordLikeType then
      -- store record field info
      local r = {}
      for _, k in ipairs(rt.field_order) do
         local v = rt.fields[k]
         r[k] = self:get_typenum(v)
      end
      ti.fields = r
   end

   if rt is ArrayLikeType then
      ti.elements = self:get_typenum(rt.elements)
   end

   if rt is MapType then
      ti.keys = self:get_typenum(rt.keys)
      ti.values = self:get_typenum(rt.values)
   elseif rt is EnumType then
      ti.enums = mark_array(sorted_keys(rt.enumset))
   elseif rt is FunctionType then
      self:store_function(ti, rt)
   elseif rt is AggregateType then
      local tis = {}
      for _, pt in ipairs(rt.types) do
         table.insert(tis, self:get_typenum(pt))
      end
      ti.types = mark_array(tis)
   end

   return n
end

local record TypeCollector
   record Symbol
      x: integer
      y: integer
      name: string
      typ: Type
      skip: boolean
   end

   filename: string
   symbol_list: {Symbol}

   store_type: function(y: integer, x: integer, typ: Type)
   reserve_symbol_list_slot: function(Node)
   add_to_symbol_list: function(node: Node, name: string, t: Type)
   begin_symbol_list_scope: function(node: Node)
   end_symbol_list_scope: function(node: Node)
end

function TypeReporter:get_collector(filename: string): TypeCollector
   local collector: TypeCollector = {
      filename = filename,
      symbol_list = {},
   }

   local ft: {integer:{integer:integer}} = {}
   self.tr.by_pos[filename] = ft

   local symbol_list = collector.symbol_list
   local symbol_list_n = 0

   collector.store_type = function(y: integer, x: integer, typ: Type)
      if not typ or skip_types[typ.typename] then
         return
      end

      local yt = ft[y]
      if not yt then
         yt = {}
         ft[y] = yt
      end

      yt[x] = self:get_typenum(typ)
   end

   collector.reserve_symbol_list_slot = function(node: Node)
      symbol_list_n = symbol_list_n + 1
      node.symbol_list_slot = symbol_list_n
   end

   collector.add_to_symbol_list = function(node: Node, name: string, t: Type)
      if not node then
         return
      end
      local slot: integer
      if node.symbol_list_slot then
         slot = node.symbol_list_slot
      else
         symbol_list_n = symbol_list_n + 1
         slot = symbol_list_n
      end
      symbol_list[slot] = { y = node.y, x = node.x, name = name, typ = t }
   end

   collector.begin_symbol_list_scope = function(node: Node)
      symbol_list_n = symbol_list_n + 1
      symbol_list[symbol_list_n] = { y = node.y, x = node.x, name = "@{" }
   end

   collector.end_symbol_list_scope = function(node: Node)
      if symbol_list[symbol_list_n].name == "@{" then
         symbol_list[symbol_list_n] = nil
         symbol_list_n = symbol_list_n - 1
      else
         symbol_list_n = symbol_list_n + 1
         symbol_list[symbol_list_n] = { y = assert(node.yend), x = assert(node.xend), name = "@}" }
      end
   end

   return collector
end

function TypeReporter:store_result(collector: TypeCollector, globals: {string:Variable})
   local tr = self.tr

   local filename = collector.filename
   local symbol_list = collector.symbol_list

   tr.by_pos[filename][0] = nil

   -- mark unneeded scope blocks to be skipped
   do
      local n = 0 -- number of symbols in current scope
      local p = 0 -- opening position of current scope block
      local n_stack, p_stack = {}, {}
      local level = 0
      for i, s in ipairs(symbol_list) do
         if s.typ then
            n = n + 1
         elseif s.name == "@{" then
            level = level + 1
            n_stack[level], p_stack[level] = n, p -- push current scope
            n, p = 0, i -- begin new scope
         else
            if n == 0 then -- nothing declared in this scope
               symbol_list[p].skip = true -- skip @{
               s.skip = true -- skip @}
            end
            n, p = n_stack[level], p_stack[level] -- pop previous scope
            level = level - 1
         end
      end
   end

   -- resolve scope cross references, skipping unneeded scope blocks
   do
      local stack = {}
      local level = 0
      local i = 0
      for _, s in ipairs(symbol_list) do
         if not s.skip then
            i = i + 1
            local id: integer
            if s.typ then
               id = self:get_typenum(s.typ)
            elseif s.name == "@{" then
               level = level + 1
               stack[level] = i
               id = -1 -- will be overwritten
            else
               local other = stack[level]
               level = level - 1
               tr.symbols[other][4] = i -- overwrite id from @{
               id = other - 1
            end
            local sym = mark_array({ s.y, s.x, s.name, id })
            table.insert(tr.symbols, sym)
         end
      end
   end

   local gkeys = sorted_keys(globals)
   for _, name in ipairs(gkeys) do
      if name:sub(1, 1) ~= "@" then
         local var = globals[name]
         tr.globals[name] = self:get_typenum(var.t)
      end
   end
end

function TypeReporter:get_report(): TypeReport
   return self.tr
end


--------------------------------------------------------------------------------
-- Report types
--------------------------------------------------------------------------------

function tl.symbols_in_scope(tr: TypeReport, y: integer, x: integer): {string:integer}
   local function find(symbols: {{integer, integer, string, integer}}, at_y: integer, at_x: integer): integer
      local function le(a: {integer, integer}, b: {integer, integer}): boolean
         return a[1] < b[1]
            or (a[1] == b[1] and a[2] <= b[2])
      end
      return binary_search(symbols, {at_y, at_x}, le) or 0
   end

   local ret: {string:integer} = {}

   -- local a, b = 0, 0
   -- for i, s in ipairs(tr.symbols) do
   --    print("["..i.."]", (a < s[1] or (a == s[1] and b <= s[2])) and " " or "x", s[1], s[2], s[3], s[4])
   --    a, b = s[1], s[2]
   -- end
   -- print()

   local n = find(tr.symbols, y, x)

   local symbols = tr.symbols
   while n >= 1 do
      local s = symbols[n]
      if s[3] == "@{" then
         n = n - 1
      elseif s[3] == "@}" then
         n = s[4]
      else
         ret[s[3]] = s[4]
         n = n - 1
      end
   end

   return ret
end
