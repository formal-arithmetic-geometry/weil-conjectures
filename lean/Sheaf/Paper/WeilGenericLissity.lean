/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N0
-/
module

public import Sheaf.Paper.WeilIndSheafCategory
public import Sheaf.Paper.CommonStageLisse
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties

public import Sheaf.Paper.LisseIntegralSmallCoefficients
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.Topology.NoetherianSpace
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
import Sheaf.Paper.SfConstructibleHeart
import Sheaf.Paper.DerivedPullbackTensorHom
import Sheaf.Paper.FiniteFieldFiber
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Sheaf.AlgebraicGeometry.FrobeniusDetailed
public import Sheaf.Paper.SfWeilSheafComplex
import Sheaf.Paper.RationalCoefficientCategoryComparison
import Sheaf.AlgebraicGeometry.GeometricReducedFiniteTypePerfectField
import Sheaf.Paper.AdicHeartIntrinsicFibres
import Sheaf.Paper.LisseCompletedSystemComparison
import Sheaf.Paper.IntegralPullbackComposition
import WeilConjectures.AlgebraicGeometry.EtaleLocallyConstantOpenPullback

/-! # Generic lissity over the finite-field model

Source: blueprint main-20261015, thm-zl-relative-line-stratification, proof paragraphs 1
and 4; Deligne, Weil II (1.1.1), pp. 146--147
(blueprint: lem-zl-weil-generic-lissity).

Restriction uses the recorded common-stage Weil heart and its normalized Frobenius
pullback square. Lissity is the existing integral lisse-lattice realization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u})

/-- An open of the finite-field model, with its induced structure map.
Source: stratification proof, paragraph 4 (blueprint: lem-zl-weil-generic-lissity). -/
def zlGenericOpenModel (X₀ : Over (Spec (.of D.k₀))) (U₀ : X₀.left.Opens) :
    Over (Spec (.of D.k₀)) := Over.mk (U₀.ι ≫ X₀.hom)

/-- The canonical inclusion is a morphism over the finite field.
Source: stratification proof, paragraph 4 (blueprint: lem-zl-weil-generic-lissity). -/
def zlGenericOpenInclusion (X₀ : Over (Spec (.of D.k₀))) (U₀ : X₀.left.Opens) :
    zlGenericOpenModel D X₀ U₀ ⟶ X₀ := Over.homMk U₀.ι

/-- Local finite type is inherited by an open subscheme.
Source: stratification proof, paragraph 4 (blueprint: lem-zl-weil-generic-lissity). -/
instance zlGenericOpenModel_locallyOfFiniteType (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] (U₀ : X₀.left.Opens) :
    LocallyOfFiniteType (zlGenericOpenModel D X₀ U₀).hom :=
  inferInstanceAs (LocallyOfFiniteType (U₀.ι ≫ X₀.hom))

/-- The open is quasi-compact over the field because its finite-type model is noetherian.
Source: stratification proof, paragraph 4 (blueprint: lem-zl-weil-generic-lissity). -/
instance zlGenericOpenModel_quasiCompact (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] (U₀ : X₀.left.Opens) :
    QuasiCompact (zlGenericOpenModel D X₀ U₀).hom :=
  letI : IsLocallyNoetherian X₀.left := LocallyOfFiniteType.isLocallyNoetherian X₀.hom
  letI : CompactSpace X₀.left := QuasiCompact.compactSpace_of_compactSpace X₀.hom
  letI : IsNoetherian X₀.left := ⟨⟩
  inferInstanceAs (QuasiCompact (U₀.ι ≫ X₀.hom))

/-- A constructible common-stage Weil sheaf is lisse on a dense open defined over k₀.
The restriction is the canonical Weil-heart inverse image, so its Frobenius structure
is the pulled-back original structure composed with the normalized pullback square.
The top-open clause records the specified choice on the empty scheme.
Source: stratification proof, paragraphs 1 and 4; Weil II (1.1.1), pp. 146--147
(blueprint: lem-zl-weil-generic-lissity).

Proof (the six steps of the DAG node):
1. On the empty scheme take the top open. The zero integral system is lisse and
represents the unique heart object; restrict the Frobenius isomorphism and its inverse.
2. Finite-type base change is separated and noetherian. Perfectness of k₀ makes its
reduced model geometrically reduced. The identity-induced rational coefficient
comparison identifies the constructible hearts. The adic-heart theorem gives a finite
lisse stratification. On each irreducible component choose an open around its generic
point avoiding the other components and contained in its stratum. Reducedness makes
the stratum immersion an isomorphism there. The finite disjoint union W is lisse;
put the finitely many integral models over their common finite coefficient extension.
3. The geometric projection p is integral by integral base change along k/k₀, hence
closed. The complement of p(X minus W) is an open U₀ whose inverse image lies in W.
4. Every point above a component generic point of X₀ is generic in X: a component
generic point generalizing it has the same image, and integral incomparability makes
them equal. Thus U₀ contains all component generic points and is dense.
5. Restrict the finite-level locally constant integral systems to p inverse U₀.
Their quotient-transition isomorphisms restrict as well. Rationalization and the
completed-system comparison identify this lisse model with the actual heart pullback.
6. Since U₀ is defined over k₀, geometric Galois Frobenius commutes with its inclusion.
The integral composition comparison, rationalized and passed to common stages,
composed with the pulled-back theta gives the restricted Weil isomorphism. Its inverse
comes from the pulled-back inverse. This is exactly zlWeilPull, with no assertion that
geometric Frobenius is k-linear. -/
theorem weil_exists_dense_open_lisse
    (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [IsSeparated X₀.hom] [IsReduced X₀.left]
    (F : sfCommonStageWeilSheaf D l hl X₀ Ω) :
    ∃ U₀ : X₀.left.Opens, Dense (U₀ : Set X₀.left) ∧
      (IsEmpty X₀.left → U₀ = ⊤) ∧
      HasCommonStageLisseLattice l Ω (D.geometricFiber (zlGenericOpenModel D X₀ U₀)).left
        (((zlWeilPull D l hl Ω (zlGenericOpenInclusion D X₀ U₀)).obj F).obj.carrier) := by
  sorry

end WeilConjectures
