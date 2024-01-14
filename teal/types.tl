local last_typeid = 0

local function new_typeid(): integer
   last_typeid = last_typeid + 1
   return last_typeid
end

local interface Where
   y: integer
   x: integer
   filename: string
end

local record types
   type Where = Where

   enum TypeName
      "typedecl"
      "typealias"
      "typevar"
      "typearg"
      "function"
      "array"
      "map"
      "tupletable"
      "record"
      "interface"
      "enum"
      "boolean"
      "string"
      "nil"
      "thread"
      "number"
      "integer"
      "union"
      "nominal"
      "emptytable"
      "literal_table_item"
      "unresolved_emptytable_value"
      "unresolved_typearg"
      "unresolvable_typearg"
      "circular_require"
      "tuple"
      "poly" -- intersection types, currently restricted to polymorphic functions defined inside records
      "any"
      "unknown" -- to be used in lax mode only
      "invalid" -- producing a new value of this type (not propagating) must always produce a type error
      "unresolved"
      "none"
      "*"
   end

   interface Type
      is Where
      where self.typename

      typename: TypeName    -- discriminator
      typeid: integer       -- unique identifier
      inferred_at: Where    -- for error messages
      needs_compat: boolean -- for Lua compatibilty
   end

   record StringType
      is Type
      where self.typename == "string"

      literal: string
   end

   record TypeDeclType
      is Type
      where self.typename == "typedecl"

      def: Type
      closed: boolean
   end

   record TypeAliasType
      is Type
      where self.typename == "typealias"

      alias_to: NominalType
      is_nested_alias: boolean
   end

   record LiteralTableItemType
      is Type
      where self.typename == "literal_table_item"

      -- table items
      kname: string
      ktype: Type
      vtype: Type
   end

   record UnresolvedType
      is Type
      where self.typename == "unresolved"

      labels: {string:{Node}}
      nominals: {string:{NominalType}}
      global_types: {string:boolean}
      narrows: {string:boolean}
   end

   interface HasTypeArgs
      where self.typeargs

      typeargs: {TypeArgType}
   end

   interface HasDeclName
      declname: string
   end

   interface HasIsTotal
      is_total: boolean
      missing: {string}
   end

   record NominalType
      is Type
      where self.typename == "nominal"

      names: {string}
      typevals: {Type}
      found: Type    -- type is found but typeargs are not resolved
      resolved: Type -- type is found and typeargs are resolved
   end

   interface ArrayLikeType
      is Type
      where self.elements

      elements: Type
      consttypes: {Type}
      inferred_len: integer
   end

   interface RecordLikeType
      is Type, HasTypeArgs, HasDeclName, ArrayLikeType
      where self.fields

      interface_list: {ArrayType | NominalType}
      interfaces_expanded: boolean
      fields: {string: Type}
      field_order: {string}
      meta_fields: {string: Type}
      meta_field_order: {string}
      is_userdata: boolean
   end

   record ArrayType
      is ArrayLikeType
      where self.typename == "array"
   end

   record RecordType
      is RecordLikeType, HasIsTotal
      where self.typename == "record"
   end

   record InterfaceType
      is RecordLikeType
      where self.typename == "interface"
   end

   record InvalidType
      is Type
      where self.typename == "invalid"
   end

   record UnknownType
      is Type
      where self.typename == "unknown"
   end

   record TupleType
      is Type
      where self.typename == "tuple"

      is_va: boolean
      tuple: {Type}
   end

   record TypeArgType
      is Type
      where self.typename == "typearg"

      typearg: string
      constraint: Type
   end

   record UnresolvedTypeArgType
      is Type
      where self.typename == "unresolved_typearg"

      typearg: string
      constraint: Type
   end

   record UnresolvableTypeArgType
      is Type
      where self.typename == "unresolvable_typearg"

      typearg: string
   end

   record TypeVarType
      is Type
      where self.typename == "typevar"

      typevar: string
      constraint: Type
   end

   record MapType
      is Type, HasIsTotal
      where self.typename == "map"

      keys: Type
      values: Type
   end

   record EmptyTableType
      is Type
      where self.typename == "emptytable"

      declared_at: Node
      assigned_to: string
      keys: Type
   end

   record UnresolvedEmptyTableValueType
      is Type
      where self.typename == "unresolved_emptytable_value"

      emptytable_type: EmptyTableType
   end

   record FunctionType
      is Type, HasTypeArgs
      where self.typename == "function"

      is_method: boolean
      min_arity: integer
      args: TupleType
      rets: TupleType
      macroexp: Node
   end

   interface AggregateType
      is Type
      where self.types

      types: {Type}
   end

   record UnionType
      is AggregateType
      where self.typename == "union"
   end

   record TupleTableType
      is AggregateType
      where self.typename == "tupletable"
   end

   record PolyType
      is AggregateType
      where self.typename == "poly"

      types: {FunctionType}
   end

   record EnumType
      is Type, HasDeclName
      where self.typename == "enum"

      enumset: {string:boolean}
   end

   table_types: {TypeName:boolean}
end

local table_types <total>: {types.TypeName:boolean} = {
   ["array"] = true,
   ["map"] = true,
   ["record"] = true,
   ["interface"] = true,
   ["emptytable"] = true,
   ["tupletable"] = true,

   ["typedecl"] = false,
   ["typealias"] = false,
   ["typevar"] = false,
   ["typearg"] = false,
   ["function"] = false,
   ["enum"] = false,
   ["boolean"] = false,
   ["string"] = false,
   ["nil"] = false,
   ["thread"] = false,
   ["number"] = false,
   ["integer"] = false,
   ["union"] = false,
   ["nominal"] = false,
   ["literal_table_item"] = false,
   ["unresolved_emptytable_value"] = false,
   ["unresolved_typearg"] = false,
   ["unresolvable_typearg"] = false,
   ["circular_require"] = false,
   ["tuple"] = false,
   ["poly"] = false,
   ["any"] = false,
   ["unknown"] = false,
   ["invalid"] = false,
   ["unresolved"] = false,
   ["none"] = false,
   ["*"] = false,
}
types.table_types = table_types

return types
