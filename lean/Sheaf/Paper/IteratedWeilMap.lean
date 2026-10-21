/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NS
-/
module

public import Sheaf.Paper.TraceFormulaStrictWeilComplex
public import Sheaf.SixFunctors.SelectedSchemeGaloisComparison
public import Sheaf.Paper.IntegralFinitePullbackComposition
public import Sheaf.TraceFormula.PointTransportComposition

/-!
# Iterated Weil isomorphisms and scheme-Frobenius maps

Source: main-20261015 blueprint, sec-trace-formula/sk-d-weil,
def-trf-iterated-weil-map.md, order 2639 (blueprint: def-trf-iterated-weil-map).

All maps are composites of actual isomorphisms. Pullback presentation changes preserve
the adjunction unit. The recursion starts at exponent one, so it requires no auxiliary
zero-iterate choice. The cocycle identity belongs to its separate DAG node.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.TraceFormulaCoefficientConventions

/-- Specialize the existing unit-normalized `pointPowerPullbackModel` to the
coefficient convention's positive level; no second presentation comparison is constructed.
Source: main-20261015 blueprint, order 2639, pullback conventions
(blueprint: def-trf-iterated-weil-map). -/
def iteratedWeilPullbackModel (T : TraceFormulaCoefficientConventions.{u})
    {Y Z : Scheme.{u}} (f : Y ⟶ Z) :
    T.derivedPullback f ≅ proEtaleConstantRingDerivedPullback T.coefficientRing f := by
  rcases T with ⟨D, C, E, n, hn, X, hft, hqc, hsep⟩
  cases n with
  | zero => omega
  | succ n =>
    let F := AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar E
    exact pointPowerPullbackModel C.l F n f


/-- The finite composite of pulled-back copies of an isomorphism, using the canonical
scheme-pullback composition comparison rather than identifying functor powers by fiat.
Source: main-20261015 blueprint, order 2639, first display
(blueprint: def-trf-iterated-weil-map). -/
def iteratedWeilPullbackIso {X : Scheme.{u}} (A : Type u) [CommRing A]
    (g : End X) (K : proEtaleDerivedCategory X A)
    (phi : (proEtaleConstantRingDerivedPullback A g).obj K ≅ K) : (n : ℕ) →
    (proEtaleConstantRingDerivedPullback A (g ^ (n + 1))).obj K ≅ K
  | 0 => eqToIso (congrArg
      (fun f => (proEtaleConstantRingDerivedPullback A f).obj K) (pow_one g)) ≪≫ phi
  | n + 1 => eqToIso (congrArg
      (fun f => (proEtaleConstantRingDerivedPullback A f).obj K) (pow_succ g (n + 1))) ≪≫
    (proEtaleConstantRingPullbackComposition g (g ^ (n + 1)) A).symm.app K ≪≫
    (proEtaleConstantRingDerivedPullback A g).mapIso (iteratedWeilPullbackIso A g K phi n) ≪≫
    phi

/-- The positive-exponent recursion phi_[n+1], specialized to the recorded strict
Weil structure and its unit-normalized change of presentation.
Source: main-20261015 blueprint, order 2639, first display
(blueprint: def-trf-iterated-weil-map). -/
def iteratedWeilIsomorphismSucc (T : TraceFormulaCoefficientConventions.{u})
    (K : T.strictWeilComplex) (n : ℕ) :
    (proEtaleConstantRingDerivedPullback T.coefficientRing
      ((End.of (T.datum.geometricGaloisFrobenius T.X₀)) ^ (n + 1))).obj K.obj.carrier ≅
      K.obj.carrier :=
  iteratedWeilPullbackIso T.coefficientRing (T.datum.geometricGaloisFrobenius T.X₀)
    K.obj.carrier
    ((T.iteratedWeilPullbackModel
      (T.datum.geometricGaloisFrobenius T.X₀)).symm.app K.obj.carrier ≪≫
        T.strictWeilFrobenius K) n

/-- The specified iterated Weil isomorphism phi^[m] for every positive m.
Source: main-20261015 blueprint, order 2639, first display
(blueprint: def-trf-iterated-weil-map). -/
def iteratedWeilIsomorphism (T : TraceFormulaCoefficientConventions.{u})
    (K : T.strictWeilComplex) (m : ℕ) (hm : 1 ≤ m) :
    (proEtaleConstantRingDerivedPullback T.coefficientRing
      ((End.of (T.datum.geometricGaloisFrobenius T.X₀)) ^ m)).obj K.obj.carrier ≅ K.obj.carrier :=
  eqToIso (congrArg (fun n => (proEtaleConstantRingDerivedPullback T.coefficientRing
      ((End.of (T.datum.geometricGaloisFrobenius T.X₀)) ^ n)).obj K.obj.carrier)
    (Nat.sub_add_cancel hm).symm) ≪≫ T.iteratedWeilIsomorphismSucc K (m - 1)

/-- The scheme-Frobenius isomorphism u_m = phi^[m] composed with kappa^(m)_K.
The Weil structure is transported by its canonical tensor-unit-preserving comparison.
Source: main-20261015 blueprint, order 2639, second display
(blueprint: def-trf-iterated-weil-map). -/
def iteratedWeilSchemeFrobenius (T : TraceFormulaCoefficientConventions.{u})
    (K : T.strictWeilComplex) (m : ℕ) (hm : 1 ≤ m) :
    (proEtaleConstantRingDerivedPullback T.coefficientRing
      (T.datum.schemeFrobeniusIterate T.X₀ m)).obj K.obj.carrier ≅ K.obj.carrier :=
  (T.selectedSchemeGaloisComparison T.X₀ m hm).app K.obj.carrier ≪≫
    T.iteratedWeilIsomorphism K m hm

end WeilConjectures.TraceFormulaCoefficientConventions
