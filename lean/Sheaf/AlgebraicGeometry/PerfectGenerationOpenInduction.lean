/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
import Sheaf.AlgebraicGeometry.PerfectComplex
import Sheaf.AlgebraicGeometry.DerivedCategory
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Topology.QuasiSeparated

/-! # Extending perfect generators across an affine open

Source: Stacks Project, Tag 09IS, induction step using Tags 09IQ and 09IR
(blueprint: lem-pc-perfect-generation-open-induction-step).
-/

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option backward.isDefEq.respectTransparency false in
/-- A perfect generator on a quasi-compact open extends as a summand of a perfect object;
a second perfect object supported on the affine complement makes their sum a generator.
Source: Stacks Project, Tag 09IS, induction step
(blueprint: lem-pc-perfect-generation-open-induction-step).

Proof:
1. Apply lem-sc-perfect-support-map-lift with T = X, E = 0 and the zero map from P.
   It gives a perfect Q whose restriction to U contains P as a direct summand (Tag 09IQ).
2. Write V = Spec A. Quasi-separatedness makes U intersect V quasi-compact, so its
   complement Z is V(f_1,...,f_r). The Koszul complex K is perfect and supported on Z.
   By lem-pc-supported-open-pushforward its derived pushforward K' is perfect on X
   and is also its extension by zero (Tags 08DP and 09IR).
3. If all shifted maps from Q plus K' to a quasi-coherent E vanish, extension-by-zero
   adjunction and lem-pc-perfect-generation-koszul-orthogonal identify E on V with the
   derived pushforward from U intersect V. By lem-pc-restrict-derived-direct-image-open,
   the unit E to Rj_*(E on U) is an isomorphism on U and V, hence globally: its cone's
   cohomology vanishes on the open cover.
4. Adjunction now identifies maps from shifts of Q to E with maps from shifts of Q on U
   to E on U. Since P is a summand, maps from shifts of P also vanish. The generator
   hypothesis (def-pc-generators) gives E on U = 0, and thus E = Rj_*0 = 0.
-/
theorem exists_perfect_generator_of_open_union_affine
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (U V : X.Opens) (hU : IsCompact (U : Set X)) (hV : IsAffineOpen V)
    (hcover : U ⊔ V = ⊤)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ W : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over W))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [∀ W : U.toScheme.Opens,
      HasDerivedCategory.{w}
        (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over W))]
    (P : schemeDerivedQCohCategory U.toScheme)
    (hP : IsPerfect U.toScheme P.obj)
    (hgen : ∀ E : schemeDerivedQCohCategory U.toScheme,
      IsZero E.obj ↔ ∀ n : ℤ, Subsingleton (P.obj⟦n⟧ ⟶ E.obj)) :
    ∃ Q K' : schemeDerivedCategory X,
      IsPerfect X Q ∧ IsPerfect X K' ∧
      (∃ (ι : P.obj ⟶
          ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
            Equivalence.functor
              (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
              (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
              (Modules.overEquiv U)).mapDerivedCategory.obj Q)
        (π : ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
            Equivalence.functor
              (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
              (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
              (Modules.overEquiv U)).mapDerivedCategory.obj Q ⟶ P.obj),
        ι ≫ π = 𝟙 P.obj) ∧
      (∀ (n : ℤ) (x : X), x ∉ (V : Set X) \ (U : Set X) →
        Subsingleton ↑(TopCat.Presheaf.stalk
          ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj K').val.presheaf x)) ∧
      schemeDerivedQCohProperty X (Q ⊞ K') ∧
      ∀ E : schemeDerivedQCohCategory X,
        IsZero E.obj ↔ ∀ n : ℤ, Subsingleton ((Q ⊞ K')⟦n⟧ ⟶ E.obj) := by
  sorry

end AlgebraicGeometry.Scheme
