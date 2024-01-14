local types = require("teal.types")
local type Type = types.Type
local type Where = types.Where

local record Errors
   errors: {errors.Error}
   warnings: {errors.Error}
   unknown_dots: {string:boolean}
end

local record errors
   enum WarningKind
      "unknown"
      "unused"
      "redeclaration"
      "branch"
      "hint"
      "debug"
   end
   warning_kinds: {WarningKind:boolean}

   record Error
      y: integer
      x: integer
      msg: string
      filename: string

      tag: WarningKind

      -- used temporarily for stable-sorting
      i: integer
   end

   type Errors = Errors
end

local type Error = errors.Error

local wk <total>: {errors.WarningKind:boolean} = {
   ["unknown"] = true,
   ["unused"] = true,
   ["redeclaration"] = true,
   ["branch"] = true,
   ["hint"] = true,
   ["debug"] = true,
}
errors.warning_kinds = wk

function Errors.new(): Errors
   local self = {
      errors = {},
      warnings = {},
      unknown_dots = {},
   }
   return setmetatable(self, { __index = Errors })
end

local function Err(where: Where, msg: string, ...: Type): Error
   local n = select("#", ...)
   if n > 0 then
      local showt = {}
      for i = 1, n do
         local t = select(i, ...)
         if t then
            if t.typename == "invalid" then
               return nil
            end
            showt[i] = show_type(t)
         end
      end
      msg = msg:format(table.unpack(showt))
   end

   if TL_DEBUG then
      io.stderr:write("ERROR:" .. (where.y or -1) .. ":" .. (where.x or -1) .. ": " .. msg .. "\n")
   end

   return {
      y = where.y,
      x = where.x,
      msg = msg,
      filename = where.filename,
   }
end

function Errors:add(w: Where, msg: string, ...:Type)
   assert(w.y)

   local e = Err(w, msg, ...)
   if e then
      table.insert(self.errors, e)
   end
end

function Errors:collect(errs: {Error})
   for _, err in ipairs(errs) do
      table.insert(self.errors, err)
   end
end

function Errors:add_warning(tag: WarningKind, where: Where, fmt: string, ...: any)
   table.insert(self.warnings, {
      y = where.y,
      x = where.x,
      msg = fmt:format(...),
      filename = assert(where.filename),
      tag = tag,
   })
end

function Errors:invalid_at(where: Where, msg: string, ...:Type): InvalidType
   self:add(where, msg, ...)
   return INVALID
end

function Errors:add_unknown(node: Node, name: string)
   self:add_warning("unknown", node, "unknown variable: %s", name)
end

function Errors:redeclaration_warning(node: Node, old_var?: Variable)
   if node.tk:sub(1, 1) == "_" then return end

   local var_kind = "variable"
   local var_name = node.tk
   if node.kind == "local_function" or node.kind == "record_function" then
      var_kind = "function"
      var_name = node.name.tk
   end

   local short_error = "redeclaration of " .. var_kind .. " '%s'"
   if old_var and old_var.declared_at then
      self:add_warning("redeclaration", node, short_error .. " (originally declared at %d:%d)", var_name, old_var.declared_at.y, old_var.declared_at.x)
   else
      self:add_warning("redeclaration", node, short_error, var_name)
   end
end

function Errors:unused_warning(name: string, var: Variable)
   local prefix <const> = name:sub(1,1)
   if var.declared_at
      and var.is_narrowed ~= "narrow"
      and prefix ~= "_"
      and prefix ~= "@"
   then
      if name:sub(1, 2) == "::" then
         self:add_warning("unused", var.declared_at, "unused label %s", name)
      else
         local t = var.t
         self:add_warning(
            "unused",
            var.declared_at,
            "unused %s %s: %s",
            var.is_func_arg and "argument"
               or t is FunctionType and "function"
               or t is TypeDeclType and "type"
               or t is TypeAliasType and "type"
               or "variable",
            name,
            show_type(var.t)
         )
      end
   end
end

function Errors:add_prefixing(where: Where, src: {Error}, prefix: string, dst?: {Error})
   if not src then
      return
   end
   dst = dst or self.errors

   for _, err in ipairs(src) do
      err.msg = prefix .. err.msg

      -- where.y may be nil because primitive types don't have locations
      if where and where.y and (
         (err.filename ~= where.filename)
         or (not err.y)
         or (where.y > err.y or (where.y == err.y and where.x > err.x))
      ) then
         err.y = where.y
         err.x = where.x
         err.filename = where.filename
      end

      table.insert(dst, err)
   end
end

local record Unused
   y: integer
   x: integer
   name: string
   var: Variable
end

local function check_for_unused_vars(vars: {string:Variable}, is_global?: boolean): {Unused}
   if not next(vars) then
      return
   end
   local list: {Unused}
   for name, var in pairs(vars) do
      local t = var.t
      if var.declared_at and not var.used then
         if var.used_as_type then
            var.declared_at.elide_type = true
         else
            if (t is TypeDeclType or t is TypeAliasType) and not is_global then
               var.declared_at.elide_type = true
            end
            list = list or {}
            table.insert(list, { y = var.declared_at.y, x = var.declared_at.x, name = name, var = var })
         end
      elseif var.used and (t is TypeDeclType or t is TypeAliasType) and var.aliasing then
         var.aliasing.used = true
         var.aliasing.declared_at.elide_type = false
      end
   end
   if list then
      table.sort(list, function(a: Unused, b: Unused): boolean
         return a.y < b.y or (a.y == b.y and a.x < b.x)
      end)
   end
   return list
end

function Errors:warn_unused_vars(scope: Scope, is_global?: boolean)
   local unused = check_for_unused_vars(scope, is_global)
   if unused then
      for _, u in ipairs(unused) do
         self:unused_warning(u.name, u.var)
      end
   end
end

function Errors:add_unknown_dot(node: Node, name: string)
   if not unknown_dots[name] then
      self.unknown_dots[name] = true
      self:add_unknown(node, name)
   end
end

function Errors:fail_unresolved(scope: Scope)
   local unresolved = scope["@unresolved"]
   if unresolved then
      scope["@unresolved"] = nil
      local unrt = unresolved.t as UnresolvedType
      for name, nodes in pairs(unrt.labels) do
         for _, node in ipairs(nodes) do
            self:add(node, "no visible label '" .. name .. "' for goto")
         end
      end
      for name, types in pairs(unrt.nominals) do
         if not unrt.global_types[name] then
            for _, typ in ipairs(types) do
               assert(typ.x)
               assert(typ.y)
               self:add(typ, "unknown type %s", typ)
            end
         end
      end
   end
end

local type CheckableKey = string | number | boolean

function Errors:check_redeclared_key(where: Where, ctx: Node.ExpectedContext, seen_keys: {CheckableKey:Where}, key: CheckableKey)
   if key ~= nil then
      local s = seen_keys[key]
      if s then
         self:add(where, in_context(ctx, "redeclared key " .. tostring(key) .. " (previously declared at " .. s.filename .. ":" .. s.y .. ":" .. s.x .. ")"))
      else
         seen_keys[key] = where
      end
   end
end

return errors
