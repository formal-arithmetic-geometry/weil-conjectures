/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero
public import Sheaf.AlgebraicGeometry.ProEtaleOpenProperClopenWitness

public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-! # Boundary restriction of the higher direct image

Source: the proof plan of `isZero_higherDirectImage_open_injective_of_proper`
in `Sheaf.AlgebraicGeometry.ProEtaleOpenInjectiveProperAcyclic`.
(blueprint: lem-sp-proetale-open-injective-proper-acyclic-boundary-restriction)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Vanishing on the boundary part of the base open-closed decomposition.

Source: the recorded compactification-independence proof plan in
`Sheaf.AlgebraicGeometry.ProEtaleOpenInjectiveProperAcyclic`, steps
4--7. Stacks Tag 0F7B is its etale analogue only.

Proof: Write F = k_!J and G = H^q(Rp_*F[0]). Cover affine pro-etale test
objects by w-contractible affines. For the pullback of E, choose finitely many
principal opens and closed-localize at its complementary ideal. These opens
and the closed localization cover the affine. The principal opens miss the
closed boundary. On the remaining localization every point specializes to the
closed complement; after proper base change the extension has zero closed
restriction. The boundary cohomology argument gives vanishing of its positive
cohomology there. Restriction along the weakly etale projections preserves
injectivity of J, and exact evaluation identifies these cohomology groups with
the sections of G. Sheaf locality gives zero closed restriction of G.
This step is for arbitrary injective J; an etale-origin-only boundary theorem
is insufficient to perform it.
(blueprint: lem-sp-proetale-open-injective-proper-acyclic-boundary-restriction)
-/
theorem isZero_boundaryRestriction_higherDirectImage_open_injective_of_proper
    (A : Type u) [CommRing A] [Finite A]
    {B D C E : Scheme.{u}} (p : B ⟶ D) (r : C ⟶ E)
    (k : C ⟶ B) (i : E ⟶ D)
    [IsProper p] [IsProper r]
    [IsOpenImmersion k] [QuasiCompact k]
    [IsOpenImmersion i] [QuasiCompact i]
    (hcomm : k ≫ p = r ≫ i)
    (J : proEtaleRingModules C (proEtaleConstantRing C A)) [Injective J]
    (w : OpenProperClopenWitness p r k i)
    (q : ℕ) (hq : 0 < q) :
    IsZero ((proEtaleConstantRingPullback A i.closedComplement).obj
      ((DerivedCategory.homologyFunctor
        (proEtaleRingModules D (proEtaleConstantRing D A)) (q : ℤ)).obj
        ((proEtaleConstantDerivedDirectImage p A).obj
          ((DerivedCategory.singleFunctor
            (proEtaleRingModules B (proEtaleConstantRing B A)) 0).obj
            ((sfIntrinsicExtensionByZero k A).obj J))))) := by
  sorry

end AlgebraicGeometry.Scheme
