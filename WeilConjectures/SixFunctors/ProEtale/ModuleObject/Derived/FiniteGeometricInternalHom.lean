/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DetSfCompBaseChangeDefs
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.WeaklyEtaleIhom
import WeilConjectures.SixFunctors.ProEtale.GenericPoint

/-!
# Finite-coefficient geometric internal-Hom invertibility

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

/-- Invertibility of the evaluation-transpose internal-Hom map after geometric pullback.
Source: latest blueprint `sec-six-functors-basics/sk-thm-sf-ctf-stability/`
`det-prop-sf-biduality-general.proof.md`, geometric restriction of duality.

Proof: finite and algebraically closed fields are perfect. Thus the algebraic extension
kbar/k is separable, hence ind-etale: every finitely generated subalgebra is a finite
separable field extension and is etale. The spectrum map is weakly etale, and base change
makes the geometric projection weakly etale as well. Apply the adopted native theorem
isIso_ihomComparison_leftDerivedUpperStar_of_weaklyEtale to the actual pulled-back
coefficient ring and K. Its derived pullback is definitionally detSfDerivedPullback.
The source theorem uses localization of the pro-etale site and the exact left adjoint
g_! with its projection formula, so it concerns precisely the canonical evaluation
transpose of the specified monoidal tensorator. Its component at W is invertible.
This proof works for all objects, without needing their constructibility or Tor bounds,
and uses no exceptional adjunction or biduality. The algebraically closed case and the
zero-coefficient or empty-scheme cases are included in the same argument.
(blueprint: new-lem-sfb-finite-geometric-internal-hom) -/
theorem finite_geometric_internalHom_comparison
    (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (_hple : p ≠ ell)
    (k : Type u) [Field k] [CharP k p]
    (hk : Finite k ∨ IsAlgClosed k)
    (A : Type u) [CommRing A] [Finite A]
    (_hA : ∃ r : ℕ, (ell : A) ^ r = 0)
    (kbar : Type u) [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar]
    (X : Scheme.{u}) (a : X ⟶ Spec (.of k))
    [LocallyOfFiniteType a] [QuasiCompact a] [IsSeparated a]
    (K W : (constantModelBoundedConstructible (cartesianFinitePointRing A) X ⊓
      DerivedCategory.finiteTorAmplitude _).FullSubcategory) :
    IsIso ((Functor.LaxMonoidal.ihomComparison
      (detSfDerivedPullback (cartesianFinitePointRing A)
        (pullback.fst a (Spec.map (CommRingCat.ofHom (algebraMap k kbar)))))
      K.obj).natTrans.app W.obj) := by
  have : PerfectField k := by
    rcases hk with h | h
    · have : Finite k := h
      infer_instance
    · have : IsAlgClosed k := h
      infer_instance
  have : Algebra.IndEtale k kbar := Algebra.IndEtale.of_isSeparable k kbar
  have : IsIso (Functor.LaxMonoidal.ihomComparison
      (detSfDerivedPullback (cartesianFinitePointRing A)
        (pullback.fst a (Spec.map (CommRingCat.ofHom (algebraMap k kbar)))))
      K.obj).natTrans :=
    isIso_ihomComparison_leftDerivedUpperStar_of_weaklyEtale
      (cartesianFinitePointRing A) _ K.obj
  infer_instance

end AlgebraicGeometry.ProEtale.CondensedRing
