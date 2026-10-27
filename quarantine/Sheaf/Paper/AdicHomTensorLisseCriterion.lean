/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q30
-/
module

public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.IntrinsicQbarCategory
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.LisseRationalRealization
public import Sheaf.Paper.DerivedAutomorphismHomEvaluation
public import Sheaf.Paper.ConstructibleTruncations

import Sheaf.Paper.CompletedTensorHomTranspose
import Sheaf.Paper.FiniteStagePairCategory
import Sheaf.Paper.RationalCoefficientCategoryComparison
import Sheaf.Paper.RationalRealizationTensorComparison
import Sheaf.Paper.ContinuousRationalDerivedRealization
import Sheaf.Topology.ProfiniteCondensedRing
import Sheaf.Paper.TAdmissibleDualizableTruncations
import Sheaf.AlgebraicGeometry.FiniteTypeNoetherianSpectrum
import Mathlib.Topology.NoetherianSpace
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # The adic tensor--Hom criterion for lisse cohomology

Source: Hemo--Richarz--Scholbach, Definition 3.3, Theorem 6.2(2), Corollaries 6.3
and 6.11, Theorem 7.7 and Lemma 7.9; Bhatt--Scholze, Proposition 6.8.14(2)
(blueprint: lem-zl-adic-hom-tensor-lisse-criterion).

The two comparisons below are the actual evaluation transposes, in the raw rational
category and its common-finite-stage category. No integral lisse lattice is input.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
namespace WeilConjectures

section Finite
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (X : Scheme.{u}) [∀ x : X, Invertible (l : X.residueField x)]

/-- The canonical comparison is the transpose of evaluation after interchanging N and K.
The two proof arguments express exactly the permitted internal-Hom pairs of the recorded
operations; the dual object is defined to be RHom(K, unit).
Source: Hemo--Richarz--Scholbach, Definition 3.3, closed-monoidal duality criterion
(blueprint: lem-zl-adic-hom-tensor-lisse-criterion). -/
def rationalAdicHomTensorComparison (K N : sfRationalConstructibleCategory l E X)
    (hdual : constructibleRationalHomPairs l E X
      (op K, pullbackTensorRationalUnit l E X))
    (hN : constructibleRationalHomPairs l E X (op K, N)) :
    (rationalDerivedTensor l E X).obj
        ((rationalDerivedInternalHom l E X).obj
          ⟨(op K, pullbackTensorRationalUnit l E X), hdual⟩, N) ⟶
      (rationalDerivedInternalHom l E X).obj ⟨(op K, N), hN⟩ :=
  let P : (constructibleRationalHomPairs l E X).FullSubcategory :=
    ⟨(op K, pullbackTensorRationalUnit l E X), hdual⟩
  let dual := (rationalDerivedInternalHom l E X).obj P
  let T := rationalDerivedTensor l E X
  (podRationalClosed l E X).transpose (T.obj (dual, N)) ⟨(op K, N), hN⟩
    ((pullbackTensorRationalAssociator l E X dual N K).hom ≫
      T.map (Prod.mkHom (𝟙 dual) (pullbackTensorRationalBraiding l E X N K).hom) ≫
      (pullbackTensorRationalAssociator l E X dual K N).inv ≫
      T.map (Prod.mkHom ((podRationalClosed l E X).evaluation P) (𝟙 N)) ≫
      (pullbackTensorRationalLeftUnitor l E X N).hom)
end Finite

section Common
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (X : Scheme.{u}) [∀ x : X, Invertible (l : X.residueField x)]

/-- The same evaluation transpose on actual common-stage objects and morphism classes.
Its associator, symmetry, evaluation and transpose are the recorded finite-stage maps
transported to a common coefficient field, independently of the representative.
Source: Hemo--Richarz--Scholbach, Definition 3.3 and Lemma 7.9
(blueprint: lem-zl-adic-hom-tensor-lisse-criterion). -/
def commonAdicHomTensorComparison
    (K N : generalAlgebraicallyClosedConstructibleCategory l Ω X)
    (hdual : commonStageHomPairs l Ω X (op K, pullbackTensorCommonUnit l Ω X))
    (hN : commonStageHomPairs l Ω X (op K, N)) :
    (commonStageDerivedTensor l Ω X).obj
        ((commonStageDerivedInternalHom l Ω X).obj
          ⟨(op K, pullbackTensorCommonUnit l Ω X), hdual⟩, N) ⟶
      (commonStageDerivedInternalHom l Ω X).obj ⟨(op K, N), hN⟩ :=
  let P : (commonStageHomPairs l Ω X).FullSubcategory :=
    ⟨(op K, pullbackTensorCommonUnit l Ω X), hdual⟩
  let dual := (commonStageDerivedInternalHom l Ω X).obj P
  let T := commonStageDerivedTensor l Ω X
  (podCommonClosed l Ω X).transpose (T.obj (dual, N)) ⟨(op K, N), hN⟩
    ((pullbackTensorCommonAssociator l Ω X dual N K).hom ≫
      T.map (Prod.mkHom (𝟙 dual) (pullbackTensorCommonBraiding l Ω X N K).hom) ≫
      (pullbackTensorCommonAssociator l Ω X dual K N).inv ≫
      T.map (Prod.mkHom ((podCommonClosed l Ω X).evaluation P) (𝟙 N)) ≫
      (pullbackTensorCommonLeftUnitor l Ω X N).hom)
end Common

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (X : LisseRealization.Base D l hl)
  [hsep : IsSeparated (X.scheme ↘ Spec (.of D.k))]

include hsep

/-- The finite-field-stage criterion, with no global integral lisse lattice assumption.
The existential hN merely types the canonical comparison on the dependency's permitted
Hom pairs; it does not choose a comparison arrow.

Source: Hemo--Richarz--Scholbach, Definition 3.3, Theorem 6.2(2), Corollaries 6.3
and 6.11, Theorem 7.7; Bhatt--Scholze, Proposition 6.8.14(2)
(blueprint: lem-zl-adic-hom-tensor-lisse-criterion).

Proof plan:
1. Set dual = RHom(K, unit). Use the canonical comparison and completed tensor--Hom
transposition to identify Hom(A, N tensor dual) with Hom(A tensor K, N). The inverse
image of id_K gives coevaluation. Its defining equation is the first triangle identity;
for r = (evaluation tensor id_dual)(id_dual tensor coevaluation), interchange of the
evaluations gives evaluation(r tensor id_K) = evaluation. Injectivity of transposition
then gives r = id_dual, the second triangle.
This uses lem-coef-completed-tensor-hom-transpose and the recorded tensor/Hom operations.
2. At this finite stage retain that dual pair. The identity-on-integral-objects equivalence
of lem-fd-rational-coefficient-category-comparison identifies the raw coefficient models.
3. Apply lem-per-continuous-rational-derived-realization and the tensor/unit comparisons
of lem-zl-rational-realization-tensor-comparison. Their associator and unitor coherence
carries both triangle identities to the ambient continuous-coefficient derived category.
4. The condensed field is t-admissible: finitely presented vector spaces are finite free,
and every vector space is flat. Finite type over a field makes X noetherian, hence it has
finitely many irreducible components. Apply lem-zl-t-admissible-dualizable-truncations.
Every realized cohomology sheaf is locally finite free, allowing rank zero and a different
rank on each cover member. The noetherian inputs are lem-sfb-finite-type-noetherian-spectrum
and lem-sc-noetherian-finite-irreducible-components.
5. The realization is t-exact. Its full faithfulness and the local finite free essential
image in lem-tw-lisse-rational-realization identify each standard cohomology object with
a lisse heart object. None of these steps chooses a globally lisse integral lattice. -/
theorem rationalAdicHomTensor_lisse_cohomology
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (K : sfRationalConstructibleCategory l E X.scheme)
    (hdual : constructibleRationalHomPairs l E X.scheme
      (op K, pullbackTensorRationalUnit l E X.scheme))
    (hcomparison : ∀ N : sfRationalConstructibleCategory l E X.scheme,
      ∃ hN : constructibleRationalHomPairs l E X.scheme (op K, N),
        IsIso (rationalAdicHomTensorComparison l E X.scheme K N hdual hN)) :
    ∀ j : ℤ, IsRationalLisse l E X.scheme
      ((constructibleTruncationCohomology
        (sfRationalStandardTStructure l E X.scheme D hl) j).obj K) := by
  sorry

/-- The common-finite-stage criterion, including all integer cohomological degrees.
Source: Hemo--Richarz--Scholbach, Definition 3.3, Theorem 6.2(2), Corollaries 6.3
and 6.11, Theorem 7.7 and Lemma 7.9; Bhatt--Scholze, Proposition 6.8.14(2)
(blueprint: lem-zl-adic-hom-tensor-lisse-criterion).

Proof plan:
1. Use the evaluation transpose and assumed invertible canonical comparisons to construct
a dual pair, by the two triangle calculations in the finite-stage theorem above. At the
common stage the tensor--Hom bijections are the filtered colimits of the rational ones.
2. Represent K, its dual, evaluation and coevaluation at one finite coefficient field.
The pair-category equality relation makes each triangle identity hold after a further
finite extension. Take the compositum of those two extensions. Both identities now hold
at that stage; no universally quantified comparison hypothesis is descended. This uses
def-weil-pbc-finite-stage-pair-category and def-weil-derived-pullback-tensor-hom.
3. Identify the raw rational coefficient models by the identity comparison, then realize
the finite-stage dual pair using lem-zl-rational-realization-tensor-comparison and
lem-per-continuous-rational-derived-realization, preserving both triangles.
4. Apply lem-zl-t-admissible-dualizable-truncations to the condensed finite coefficient
field on the noetherian finite-type scheme. Its cohomology is locally finite free.
5. By t-exactness and lem-tw-lisse-rational-realization the finite-stage cohomology is
lisse. The common-stage truncations of prop-constructible-truncations commute with
finite coefficient extension. Their images are therefore the common-stage cohomology,
and the common-stage clause of lisse realization preserves each local finite basis.
Ranks may be zero and may vary locally. No global integral lisse lattice is assumed. -/
theorem commonAdicHomTensor_lisse_cohomology
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω X.scheme)
    (hdual : commonStageHomPairs l Ω X.scheme
      (op K, pullbackTensorCommonUnit l Ω X.scheme))
    (hcomparison : ∀ N : generalAlgebraicallyClosedConstructibleCategory l Ω X.scheme,
      ∃ hN : commonStageHomPairs l Ω X.scheme (op K, N),
        IsIso (commonAdicHomTensorComparison l Ω X.scheme K N hdual hN)) :
    ∀ j : ℤ, IsCommonStageLisse l Ω X.scheme
      ((constructibleTruncationCohomology
        (sfCommonStageStandardTStructure l X.scheme Ω D hl) j).obj K) := by
  sorry

end WeilConjectures
