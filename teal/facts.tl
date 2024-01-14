local type Where = require("teal.Where")
local type types = require("teal.types")
local type Type = types.Type

local enum FactType
   "is"     -- type-based type judgement (its negation implies the subtracted type)
   "=="     -- value-based type judgement (its negation does not imply a subtracted type negated)
   "not"    -- negation: type-based judgements subtract, value-based judgements prove nothing
   "and"    -- conjunction: type-based judgements intersect, any value-based judgement downgrades all
   "or"     -- disjunction: type-based judgements unite, any value-based judgement downgrades all
   "truthy" -- expression that is either truthy or a runtime error
end

local interface Fact
   where self.fact

   fact: FactType
   where: Where
end

local record TruthyFact
   is Fact
   where self.fact == "truthy"

   metamethod __call: function(Fact, Fact): TruthyFact
end

local record NotFact
   is Fact
   where self.fact == "not"

   f1: Fact

   metamethod __call: function(Fact, Fact): NotFact
end

local record AndFact
   is Fact
   where self.fact == "and"

   f1: Fact
   f2: Fact

   metamethod __call: function(Fact, Fact): AndFact
end

local record OrFact
   is Fact
   where self.fact == "or"

   f1: Fact
   f2: Fact

   metamethod __call: function(Fact, Fact): OrFact
end

local record EqFact
   is Fact
   where self.fact == "=="

   var: string
   typ: Type

   metamethod __call: function(Fact, Fact): EqFact
end

local record IsFact
   is Fact
   where self.fact == "is"

   var: string
   typ: Type

   metamethod __call: function(Fact, Fact): IsFact
end

local record facts
   type Fact = Fact
end

return facts
