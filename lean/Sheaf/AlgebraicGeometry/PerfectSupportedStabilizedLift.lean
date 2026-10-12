/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E3
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
import Sheaf.AlgebraicGeometry.AffinePerfectMapLift
import Sheaf.AlgebraicGeometry.AffinePerfectSupportExtension
import Sheaf.AlgebraicGeometry.DerivedOpenGluing

/-! # The finite stabilization construction for supported map lifting

Source: Stacks Project, Tag 09IM, proof of Lemma 36.13.11.
(blueprint: lem-sc-perfect-supported-stabilized-lift).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option backward.isDefEq.respectTransparency false in
/-- The affine-cover construction extends one finite stabilization of the given map.
This records the actual iterated object and its first-projection map.
Source: Stacks Project, Tag 09IM, proof of Lemma 36.13.11 and Remark 36.13.12.
(blueprint: lem-sc-perfect-supported-stabilized-lift).

Proof: Choose finitely many affine opens whose union with U is X, and attach them
one at a time. Start with S 0 and a 0 on U. At an attachment V, the intersection
with the previously attached union is quasi-compact by quasi-separatedness.
The complement of T on V is quasi-compact for the same reason. Apply the affine
supported extension lemma to the current perfect object on that intersection;
it extends that object plus its shift to a perfect object Q on V supported on T.
Compose the overlap identification with the first projection and the current map.
Apply affine perfect map lifting to Q; its tensor augmentation is invertible on
the overlap, and its source remains perfect and supported on T. Glue the resulting
map on V to the first-projection map on the previous union by derived open gluing.
The two maps agree by the affine lifting equation. Perfectness and support are
local, so the glued source has both properties. On U the source and map have
changed from S k and a k to S (k+1) and a (k+1), using hS and ha. The canonical
comparison isomorphisms for iterated restriction transport these identifications.
Induction on the finite cover gives n, R, beta and the stated isomorphism and
map equation. No retraction or direct-summand assertion is used in this construction.
For an empty added cover use n=0; empty support or a zero source causes no change
in the construction. -/
theorem exists_perfect_supported_stabilized_lift
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (U : X.Opens) (hU : IsCompact (U : Set X))
    (T : Set X) (hT : IsClosed T) (hTc : IsCompact Tᶜ)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ V : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [∀ V : U.toScheme.Opens,
      HasDerivedCategory.{w}
        (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over V))]
    (E : schemeDerivedQCohCategory X)
    (S : ℕ → schemeDerivedCategory U.toScheme)
    (hS : ∀ n : ℕ, S (n + 1) ≅ S n ⊞ (S n)⟦(1 : ℤ)⟧)
    (hP : IsPerfect U.toScheme (S 0))
    (hPT : ∀ (n : ℤ) (x : U.toScheme), x.val ∉ T →
      Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) n).obj
          (S 0)).val.presheaf x)))
    (a : ∀ n : ℕ, S n ⟶ ((SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) U) ⋙ Equivalence.functor
          (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
          (Modules.overEquiv U)).mapDerivedCategory.obj E.obj)
    (ha : ∀ n : ℕ, a (n + 1) = (hS n).hom ≫ biprod.fst ≫ a n) :
    ∃ (n : ℕ) (R : schemeDerivedCategory X) (β : R ⟶ E.obj),
      IsPerfect X R ∧
      (∀ (i : ℤ) (x : X), x ∉ T →
        Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj R).val.presheaf x))) ∧
      ∃ e : ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory.obj R ≅ S n,
        ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory.map β = e.hom ≫ a n := by sorry

end AlgebraicGeometry.Scheme
