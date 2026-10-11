/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Diagonal counit identity for a flat proper morphism

Source: literature/stacks-project/duality.tex, Equation 48.12.8.1
(Tag 0E2P), used in Tag 0E2Q
(blueprint: lem-sc-smooth-proper-diagonal-pushforward-structure).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry

/-- For a flat proper morphism, the diagonal right-adjoint counit identifies the
structure sheaf with the pullback of the right adjoint of the original morphism.
Source: Stacks Project, Tag 0E2Q (blueprint: lem-sc-smooth-proper-diagonal-pushforward-structure).

The preservation proofs `hRf`, `hRΔ`, and `hLpr₁` lift the shared derived
functors to the full quasi-coherent subcategories. The proofs `hOX` and `hOS`
place the structure sheaves in those subcategories. These are typing witnesses,
not additional geometric conditions. `adjA` and `adjC` specify the two actual
adjunctions. The isomorphism is obtained by the adjunction and proper flat
base-change identifications in the proof below.

Proof:
1. Form `P = X ×_S X` (`def-pc-base-change`), with `pr₂` the base change of `f`.
   Properness is preserved by base change (`lem-weil-pbc-proper-base-change`).
   Thus `P` is of finite type over the Noetherian scheme `X`, and is Noetherian
   (`lem-weil-pbc-finite-type-over-noetherian`). The theorem
   `lem-pc-noetherian-derived-direct-image-right-adjoint` supplies `b`, right
   adjoint to `R(pr₂)_*` on the quasi-coherent derived categories.
2. Properness makes `f` separated, so its diagonal is a closed immersion and
   proper (Stacks Tags 01KH, 01W6). Since `Δ ≫ pr₂ = 𝟙 X`, composition of proper
   derived direct images (`lem-pc-proper-derived-direct-image-composition`)
   identifies `RΔ_* ⋙ R(pr₂)_*` with the identity. Pasting the adjunctions and
   uniqueness of right adjoints (`lem-cat-right-adjoint-composition`) identify
   `b ⋙ c` with the identity. Evaluate at `𝒪_X` to get `𝒪_X ≅ c(b(𝒪_X))`.
3. Properness implies finite type. Over Noetherian `S` this implies finite
   presentation (Stacks Tag 01TX). The proper flat right-adjoint base-change
   formula (`lem-sc-smooth-proper-diagonal-basechange-upper-shriek`) identifies
   `b(𝒪_X)` with `L pr₁^* a(𝒪_S)`. Apply `c` and compose with step 2.
The degree-zero objects and functors are those of `def-pc-derived-category`,
`def-pc-derived-direct-image`, and the shared `def-pc-derived-pullback`. -/
theorem diagonal_counit_identity
    {X S : Scheme.{u}} [IsNoetherian X] [IsNoetherian S]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    (f : X ⟶ S) [Flat f] [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings (Limits.pullback f f).toRingedSpace))]
    (hRf : ∀ E : schemeDerivedQCohCategory X,
      schemeDerivedQCohProperty S ((schemeDerivedDirectImage f).obj E.obj))
    (hRΔ : ∀ E : schemeDerivedQCohCategory X,
      schemeDerivedQCohProperty (Limits.pullback f f)
        ((schemeDerivedDirectImage (pullback.diagonal f)).obj E.obj))
    (hLpr₁ : ∀ E : schemeDerivedQCohCategory X,
      schemeDerivedQCohProperty (Limits.pullback f f)
        ((derivedPullback (pullback.fst f f)).obj E.obj))
    (hOX : schemeDerivedQCohProperty X
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj
        (SheafOfModules.unit (moduleRings X.toRingedSpace))))
    (hOS : schemeDerivedQCohProperty S
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).obj
        (SheafOfModules.unit (moduleRings S.toRingedSpace))))
    (a : schemeDerivedQCohCategory S ⥤ schemeDerivedQCohCategory X)
    (adjA : (schemeDerivedQCohProperty S).lift
      ((schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f) hRf ⊣ a)
    (c : schemeDerivedQCohCategory (Limits.pullback f f) ⥤ schemeDerivedQCohCategory X)
    (adjC : (schemeDerivedQCohProperty (Limits.pullback f f)).lift
      ((schemeDerivedQCohProperty X).ι ⋙
        schemeDerivedDirectImage (pullback.diagonal f)) hRΔ ⊣ c) :
    Nonempty
      ((⟨(DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj
          (SheafOfModules.unit (moduleRings X.toRingedSpace)), hOX⟩ :
          schemeDerivedQCohCategory X) ≅
        c.obj (((schemeDerivedQCohProperty (Limits.pullback f f)).lift
          ((schemeDerivedQCohProperty X).ι ⋙ derivedPullback (pullback.fst f f))
          hLpr₁).obj (a.obj
            ⟨(DerivedCategory.singleFunctor
              (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).obj
              (SheafOfModules.unit (moduleRings S.toRingedSpace)), hOS⟩))) := by
  sorry

end AlgebraicGeometry
