/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Pasting exchange transformations of left adjoints through their conjugates

Consider three "stages" `A`, `B`, `C`, each over two "bases" `X`, `Y`, with base change functors
`u_A : A_X ⥤ A_Y`, `u_B`, `u_C` and change of stage functors `T : A ⥤ B`, `P : B ⥤ C`,
`Q : A ⥤ C` over each base, all of them left adjoints. Exchange transformations
`s_T : T_X ⋙ u_B ⟶ u_A ⋙ T_Y` (and `s_P`, `s_Q`) and comparisons `a : Q ⟶ T ⋙ P` satisfy the
pasting identity

```
u_C (Q_X M) ⟶ u_C (P_X (T_X M)) ⟶ P_Y (u_B (T_X M)) ⟶ P_Y (T_Y (u_A M))
  = u_C (Q_X M) ⟶ Q_Y (u_A M) ⟶ P_Y (T_Y (u_A M))
```

as soon as their conjugates, transformations between the right adjoints, satisfy the
corresponding identity (`CategoryTheory.conjugateEquiv_paste`). In applications the right
adjoints are restrictions of scalars and pushforwards, whose exchange transformations are
identities on the underlying objects, so that the identity between the conjugates is
immediate.
-/

@[expose] public section

namespace CategoryTheory

open CategoryTheory.Functor

variable {A₁ A₂ B₁ B₂ C₁ C₂ : Type*} [Category A₁] [Category A₂] [Category B₁] [Category B₂]
  [Category C₁] [Category C₂]

variable {uA : A₁ ⥤ A₂} {dA : A₂ ⥤ A₁} {uB : B₁ ⥤ B₂} {dB : B₂ ⥤ B₁} {uC : C₁ ⥤ C₂}
  {dC : C₂ ⥤ C₁} (gA : uA ⊣ dA) (gB : uB ⊣ dB) (gC : uC ⊣ dC)
  {T₁ : A₁ ⥤ B₁} {RT₁ : B₁ ⥤ A₁} {T₂ : A₂ ⥤ B₂} {RT₂ : B₂ ⥤ A₂}
  {P₁ : B₁ ⥤ C₁} {RP₁ : C₁ ⥤ B₁} {P₂ : B₂ ⥤ C₂} {RP₂ : C₂ ⥤ B₂}
  {Q₁ : A₁ ⥤ C₁} {RQ₁ : C₁ ⥤ A₁} {Q₂ : A₂ ⥤ C₂} {RQ₂ : C₂ ⥤ A₂}
  (t₁ : T₁ ⊣ RT₁) (t₂ : T₂ ⊣ RT₂) (p₁ : P₁ ⊣ RP₁) (p₂ : P₂ ⊣ RP₂) (q₁ : Q₁ ⊣ RQ₁)
  (q₂ : Q₂ ⊣ RQ₂)

section Cocycle

variable {A₃ A₄ : Type*} [Category A₃] [Category A₄]
  {L₁₂ : A₁ ⥤ A₂} {R₂₁ : A₂ ⥤ A₁} {L₂₃ : A₂ ⥤ A₃} {R₃₂ : A₃ ⥤ A₂} {L₃₄ : A₃ ⥤ A₄}
  {R₄₃ : A₄ ⥤ A₃} {L₁₃ : A₁ ⥤ A₃} {R₃₁ : A₃ ⥤ A₁} {L₂₄ : A₂ ⥤ A₄} {R₄₂ : A₄ ⥤ A₂}
  {L₁₄ : A₁ ⥤ A₄} {R₄₁ : A₄ ⥤ A₁} (t₁₂ : L₁₂ ⊣ R₂₁) (t₂₃ : L₂₃ ⊣ R₃₂) (t₃₄ : L₃₄ ⊣ R₄₃)
  (t₁₃ : L₁₃ ⊣ R₃₁) (t₂₄ : L₂₄ ⊣ R₄₂) (t₁₄ : L₁₄ ⊣ R₄₁)

end Cocycle

end CategoryTheory
