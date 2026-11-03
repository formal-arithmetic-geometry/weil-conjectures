/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FiniteFieldDualizingPullbackCore
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DetSfCompBaseChangeDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.DetPropSfCbc
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients

/-!
# Normalization of the finite geometric dualizing isomorphism

Source: latest blueprint,
`part-six-operations/sec-six-functors/sec-the-remaining-operations/`
`sk-thm-sf-ctf-stability/det-prop-sf-biduality-general.proof.md`, opening locality/restriction step
(blueprint: lem-sfb-finite-geometric-verdier-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The dualizing isomorphism for any two constructible representing pairs is normalized
by the actual compact-support exchange and their given counits.
Source: latest blueprint `sec-six-functors-basics/sk-thm-sf-ctf-stability/`
`det-prop-sf-biduality-general.proof.md`, geometric restriction argument.

Proof: take the directed tower of finite separable subextensions of a separable closure
inside kbar. At each finite stage, etale sum functors are left adjoint to pullback and
agree with compact support. Compose these adjunction bijections with the given
representing bijection for W and compact-support composition. This represents the
finite-stage compact-support Hom functor by the pullback of W. The etale-horizontal
support mate identifies its counit with the inverse of the specified exchange.
Exchange pasting makes these finite-stage identifications compatible along the tower.

Constructible finite-Tor descent and Hom continuity pass these compatible bijections
and equalities to the separable closure; compact support preserves the required
constructible finite-Tor category. If a purely inseparable step remains, topological
invariance and its monoidal equivalence transport the representing functor, preserving
both constructibility and the Tor condition. Thus G W and Wbar represent the same Hom
functor on the geometric constructible finite-Tor category. Apply the two representing
bijections to identities to construct inverse maps. At the original-stage presentation
of W its identity corresponds to the given counit. The support-mate identity, continuity
of equalities and exchange pasting therefore give exactly the displayed normalization
for this isomorphism, with the given counitBar and coefficient unit identification.
No biduality or internal-Hom invertibility is used. For an algebraically closed base
the tower is trivial and Yoneda gives the same normalized equivalence. The representing
bijections handle zero coefficients and the empty scheme without extra assumptions.
(blueprint: new-lem-sfb-finite-geometric-verdier-normalization) -/
theorem finite_geometric_dualizing_normalization
    (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hple : p ≠ ell)
    (k : Type u) [Field k] [CharP k p]
    (hk : Finite k ∨ IsAlgClosed k)
    (A : Type u) [CommRing A] [Finite A]
    (hA : ∃ r : ℕ, (ell : A) ^ r = 0)
    (kbar : Type u) [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar]
    (X : Scheme.{u}) (a : X ⟶ Spec (.of k))
    [LocallyOfFiniteType a] [QuasiCompact a] [IsSeparated a]
    (c : Compactification a) :
    let Λ := cartesianFinitePointRing A
    let h := Spec.map (CommRingCat.ofHom (algebraMap k kbar))
    let G := detSfDerivedPullback Λ (pullback.fst a h)
    let H := detSfDerivedPullback Λ h
    let C := finiteFieldModuleDerived (CommMon.mk Λ) X
    let D := finiteFieldModuleDerived (CommMon.mk Λ) (pullback a h)
    let S := constantModelBoundedConstructible Λ X ⊓ DerivedCategory.finiteTorAmplitude _
    let Sbar := constantModelBoundedConstructible Λ (pullback a h) ⊓
      DerivedCategory.finiteTorAmplitude _
    let R := detSfCompactSupport Λ c
    let Rbar := detSfCompactSupport Λ (c.baseChange h)
    let alpha := detSfCompactSupportBaseChangeComposite Λ a h c
      (compactSupportOpenBaseChangeIso Λ a h c)
    ∀ (W : C) (Wbar : D) (counit : R.obj W ⟶ 𝟙_ _)
      (counitBar : Rbar.obj Wbar ⟶ 𝟙_ _),
      S W → Sbar Wbar →
      (∀ P : S.FullSubcategory,
        Function.Bijective (fun f : P.obj ⟶ W ↦ R.map f ≫ counit)) →
      (∀ P : Sbar.FullSubcategory,
        Function.Bijective (fun f : P.obj ⟶ Wbar ↦ Rbar.map f ≫ counitBar)) →
      ∃ w : G.obj W ≅ Wbar,
        alpha.app W ≫ Rbar.map w.hom ≫ counitBar =
          H.map counit ≫ (leftDerivedUpperStarUnitIso Λ h).hom := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
