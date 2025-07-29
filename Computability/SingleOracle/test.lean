import Computability.SingleOracle.Jump

#eval Encodable.encode (Option.none : Option ℕ)
#eval Encodable.encode (Option.some 1 : Option ℕ)
#eval Encodable.encode (Option.some 2 : Option ℕ)
