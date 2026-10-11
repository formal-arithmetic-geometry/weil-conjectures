/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
import Sheaf.AlgebraicGeometry.BaseChangeConventions
import Sheaf.AlgebraicGeometry.DerivedPullback
import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Base change of a right adjoint on the self-product

Source: Stacks Project, Tag 0E2P, proof of Lemma 48.12.8, third equality,
using Lemma 48.12.4 (Tag 0AAB)
(blueprint: lem-sc-smooth-proper-diagonal-basechange-upper-shriek).
-/

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- For a proper flat morphism of finite presentation, the right adjoint to the second
projection, evaluated at `𝒪_X`, is canonically isomorphic to `L pr₁^* a(𝒪_S)`.
Source: Stacks Project, Tag 0E2P, third equality in the proof of Lemma 48.12.8,
using Tag 0AAB (blueprint: lem-sc-smooth-proper-diagonal-basechange-upper-shriek).

The witnesses `hRf`, `hRpr₂`, and `hLpr₁` restrict the shared derived functors to
`D_QCoh`. The witnesses `hOX` and `hOS` place the actual structure sheaves, in degree
zero, in those full subcategories. The adjunctions specify the chosen right adjoints.
The isomorphism is the right-adjoint base-change isomorphism at `𝒪_S`,
transported along the canonical identification `Lf^* 𝒪_S ≅ 𝒪_X`.

Proof:
1. Apply `lem-sc-proper-flat-right-adjoint-basechange` with the original map `f`,
   base-change scheme `X`, and base-change map `f`. The cartesian square has upper
   left corner `pullback f f`, horizontal map `pullback.fst f f = pr₁`, and vertical
   map `pullback.snd f f = pr₂` (`def-pc-base-change`). Noetherian schemes are
   quasi-compact and quasi-separated, so the general theorem applies.
2. Its two right adjoints are `a` and `b`. Evaluate the base-change isomorphism at
   `𝒪_S`. The canonical structure-sheaf pullback identification
   (`lem-weil-pbc-module-pullback-structure-sheaf`), computed on the flat structure
   sheaf in degree zero, gives `Lf^* 𝒪_S ≅ 𝒪_X`. Transport through `b` and invert
   the comparison to obtain `b(𝒪_X) ≅ L pr₁^* a(𝒪_S)` in `D_QCoh(𝒪_P)`. -/
theorem diagonal_baseChange_upperShriek
    {X S : Scheme.{u}} [IsNoetherian X] [IsNoetherian S]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (f : X ⟶ S) [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (hRf : ∀ E : schemeDerivedQCohCategory X,
      schemeDerivedQCohProperty S ((schemeDerivedDirectImage f).obj E.obj))
    (hRpr₂ : ∀ E : schemeDerivedQCohCategory (Limits.pullback f f),
      schemeDerivedQCohProperty X
        ((schemeDerivedDirectImage (pullback.snd f f)).obj E.obj))
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
    (b : schemeDerivedQCohCategory X ⥤ schemeDerivedQCohCategory (Limits.pullback f f))
    (adjA : (schemeDerivedQCohProperty S).lift
      ((schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f) hRf ⊣ a)
    (adjB : (schemeDerivedQCohProperty X).lift
      ((schemeDerivedQCohProperty (Limits.pullback f f)).ι ⋙
        schemeDerivedDirectImage (pullback.snd f f)) hRpr₂ ⊣ b) :
    Nonempty
      (b.obj ⟨(DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj
          (SheafOfModules.unit (moduleRings X.toRingedSpace)), hOX⟩ ≅
        ((schemeDerivedQCohProperty (Limits.pullback f f)).lift
          ((schemeDerivedQCohProperty X).ι ⋙ derivedPullback (pullback.fst f f))
          hLpr₁).obj (a.obj
            ⟨(DerivedCategory.singleFunctor
              (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).obj
              (SheafOfModules.unit (moduleRings S.toRingedSpace)), hOS⟩)) := by
  sorry

end AlgebraicGeometry
