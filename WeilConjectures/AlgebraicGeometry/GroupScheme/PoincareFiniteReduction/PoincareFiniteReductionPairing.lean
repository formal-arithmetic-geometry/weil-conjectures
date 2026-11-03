/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.PoincareFiniteReduction.PoincareFiniteReductionData

/-! # Finite Poincare coefficient comparisons

Source: latest blueprint sec-six-functors/sk-thm-sf-package/
thm-pod-finite-reduction.proof.md (blueprint: lem-pod-finite-reduction-pairing-identity).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.PurityTransport
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace WeilConjectures.PoincareFiniteReduction

/-- The cup/evaluation/trace square in generic coefficient coordinates.
Source: the pairing square in thm-pod-finite-reduction.proof.md
(blueprint: lem-pod-finite-reduction-pairing-identity). -/
def ScalarPairingCompatibility (ell : ℕ) [Fact ell.Prime] (D : FiniteFieldDatum.{u})
    (hEll : ell ≠ D.p) (cn cm : Coefficient ell)
    (a : cn.bundled.{u} ell ⟶ cm.bundled ell)
    (φ : condensedScalarRing (cn.obj ell) →+* condensedScalarRing (cm.obj ell))
    (X : Over (Spec (.of D.k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom] (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] (cf : Compactification X.hom)
    (K : ConstantModelConstructibleFiniteTor (cn.obj ell) X.left)
    (hK : IsPerfectOnCoefficientSite (cn.obj ell) X.left K.obj) : Prop :=
  letI : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  ∀ (hKm : constantModelBoundedConstructible (cm.obj ell) X.left
      ((scalarSixChange a X.left).obj K.obj) ∧
      DerivedCategory.finiteTorAmplitude _ ((scalarSixChange a X.left).obj K.obj))
    (hPKm : IsPerfectOnCoefficientSite (cm.obj ell) X.left
      ((scalarSixChange a X.left).obj K.obj))
    (σ : RestrictionSquare a D.k φ),
  (∀ (M : ModuleRingedComparison.internalModules (cm.obj ell) (Spec (.of D.k)))
    (x : (CohomologyTransport.sections (cm.obj ell) (Spec (.of D.k))).obj M),
    (σ.hom.app M).hom x = x) →
  ∀ (ha : cn.integralMap ell ≫ a.hom.hom = cm.integralMap ell)
    (p : ScalarLineCoordinates ell a ha X.left),
  let T := ModuleCat.ordinaryDerivedExtendScalars φ
  let u := compactComparison a D.k φ σ cf K.obj
  let v := ordinaryTwistedComparison ell a D.k φ σ X.hom d ha p K.obj
  let βn := derivedPoincarePairing ell D hEll (cn.bundled ell) cn (Iso.refl _)
    X d cf K hK
  let βm := derivedPoincarePairing ell D hEll (cm.bundled ell) cm (Iso.refl _)
    X d cf ⟨(scalarSixChange a X.left).obj K.obj, hKm⟩ hPKm
  Functor.LaxMonoidal.μ T _ _ ≫ T.map βn ≫ Functor.OplaxMonoidal.η T =
    (u ⊗ₘ v) ≫ βm

set_option maxHeartbeats 2000000 in
-- Matching the finite coefficient presentation needs extra elaboration work.
/-- Scalar extension preserves the canonical cup/evaluation/trace pairing through
the specified ordinary and compact-support comparisons. The ordinary comparison
is not assumed invertible here.

Source: thm-pod-finite-reduction.proof.md, paragraph 1, composing the cup,
evaluation and normalized trace squares
(blueprint: lem-pod-finite-reduction-pairing-identity).

Proof in words. Apply finite mixed-support cup compatibility to K and its
coefficient dual tensored with the positive Tate line. The scalar tensor and
site-perfect internal-Hom comparisons preserve evaluation. The normalized root
line coordinates preserve the positive Tate line, including its tensor unit in
dimension zero. Finite reduction of smooth purity identifies the reduced smooth
trace with the trace composed with the compact-support comparison and this line
map. Apply exact point sections. Naturality of the unit-adjunct pointComparison
moves it past the trace, and its coefficient-unit normalization identifies the
last map with the ordinary scalar-extension unit comparison. Paste the cup,
evaluation and trace identities, using naturality of the scalar tensorator and
its shift comparison. The resulting composite is exactly derivedPoincarePairing,
with compactComparison on its first factor and ordinaryTwistedComparison on its
second factor, yielding the displayed equality. All changes are derived.
-/
theorem finiteReduction_pairing_identity
    (P : CondensedPoincareDualityConventions.{u})
    (n m : ℕ) (h : m ≤ n)
    (K : ConstantModelConstructibleFiniteTor ((coefficient P n).obj P.ell) P.X)
    (hK : IsPerfectOnCoefficientSite ((coefficient P n).obj P.ell) P.X K.obj) :
    letI : SmoothOfRelativeDimension P.dimension P.smoothIndex.X.hom := P.smoothIndex.smooth
    ScalarPairingCompatibility P.ell P.datum P.different (coefficient P n) (coefficient P m)
      (change P h) (scalarMap P h) P.smoothIndex.X P.dimension P.compactification K hK := by
  sorry

end WeilConjectures.PoincareFiniteReduction
