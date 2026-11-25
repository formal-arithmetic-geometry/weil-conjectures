class ISFOrder where
  value : Nat

instance first : ISFOrder := ⟨1⟩
instance second : ISFOrder := ⟨2⟩

set_option trace.Meta.synthInstance true in
example : ISFOrder := inferInstance

attribute [-instance] first second
attribute [instance] second first

set_option trace.Meta.synthInstance true in
example : ISFOrder := inferInstance

