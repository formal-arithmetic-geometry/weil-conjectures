class ISFOrder where
  value : Nat

instance second : ISFOrder := ⟨2⟩
instance first : ISFOrder := ⟨1⟩

set_option trace.Meta.synthInstance true in
example : ISFOrder := inferInstance

