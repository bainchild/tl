util = require("spec.util")

describe("function calls", function()
   it("does not crash attempting to infer an emptytable when there's no return type", util.check_type_error([[
      local function f()
      end

      local x = {}

      x = f()
   ]], {
      { y = 6, msg = "variable is not being assigned a value" },
   }))

   describe("check the arity of functions:", function()
      it("when excessive", util.check_type_error([[
         local function f(n: number, m: number): number
            return n + m
         end

         local x = f(1, 2, 3)
      ]], {
         { y = 5, msg = "wrong number of arguments (given 3, expects 2)" },
      }))

      it("when insufficient", util.check_type_error([[
         local function f(n: number, m: number): number
            return n + m
         end

         local x = f(1)
      ]], {
         { y = 5, msg = "wrong number of arguments (given 1, expects 2)" },
      }))

      it("when using optional", util.check([[
         local function f(n: number, m?: number): number
            return n + (m or 0)
         end

         local x = f(1)
      ]]))

      it("when insufficient with optionals", util.check_type_error([[
         local function f(n: number, m?: number): number
            return n + (m or 0)
         end

         local x = f()
      ]], {
         { y = 5, msg = "wrong number of arguments (given 0, expects at least 1 and at most 2)" },
      }))

      it("when using all optionals", util.check([[
         local function f(n?: number, m?: number): number
            return (n or 0) + (m or 0)
         end

         local x = f()
      ]]))

      it("when using all optionals", util.check([[
         local function f(n?: number, m?: number): number
            return (n or 0) + (m or 0)
         end

         local x = f(1, 2)
      ]]))

      it("when excessive with optionals", util.check_type_error([[
         local function f(n: number, m?: number): number
            return (n or 0) + (m or 0)
         end

         local x = f(1, 2, 3)
      ]], {
         { y = 5, msg = "wrong number of arguments (given 3, expects at least 1 and at most 2)" },
      }))
   end)
end)
