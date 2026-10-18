/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.IntegralScalarExtensionUniverses
public import Sheaf.Paper.IntegralOperationsScalarComparisons
public import Sheaf.Paper.CompletedPullbackTensorComparison
public import Sheaf.Paper.SfScalarExtensionComposition
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.Paper.ConstantCompletionEquivalence
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
import Sheaf.Paper.WeilCompletedTensorReflector
import Sheaf.Paper.IntegralDerivedOperationsOnSlices
import Sheaf.AlgebraicGeometry.DiscreteNoetherianConstructibleSerre
import Sheaf.Paper.FiniteRingConstructibleDerivedOrigin
import Sheaf.Paper.IntegralOperationsPreserveConstructible
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import Sheaf.Algebra.Homology.RingedInternalHomSignedCalculus
import Sheaf.Algebra.Homology.RingedInternalHomExactRestriction
import Sheaf.Paper.CoefficientRingedTensorHomModel
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Paper.CoefficientHomRepresentativeEvaluation
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
import Sheaf.CategoryTheory.RingedSiteDualityMaps
import Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses
import Sheaf.Paper.FiniteFreeCompletedScalarComparison
import Sheaf.SixFunctors.RingedFiniteFreeHomBaseChange
import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
import Sheaf.Algebra.Homology.KFlat
import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.CategoryTheory.SiteCoveringAxioms
import Sheaf.Paper.IntegralScalarExtensionConstructibleIntrinsic
import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# Closed tensor structure on integral constructible adic complexes

Source: Bhatt--Scholze, The pro-etale topology for schemes, Definition 3.4.10,
Lemma 3.4.11 and Lemmas 6.7.12--6.7.13 (blueprint: lem-per-adic-closed-constructible).

The ambient category is that of modules over the completed coefficient sheaf.
The full-subcategory predicate, completed tensor, ambient internal Hom, completion
unit and scalar comparisons use the published constructions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace WeilConjectures.AdicClosed

variable (l : ℕ) [Fact l.Prime] (k : Type u) [Field k] [hk : Fact (IsUnit (l : k))]
  (T : Scheme.{u}) [hOver : T.Over (Spec (.of k))]

/-- The base-field unit maps to a unit in each residue field. This is the actual
mapped inverse, without an extra geometric hypothesis.
Source: Bhatt--Scholze, Section 6.7, ell-coprime convention
(blueprint: lem-per-adic-closed-constructible). -/
@[instance_reducible]
def residueInvertible : ∀ x : T, Invertible (l : T.residueField x) := fun x ↦ by
  let φ : k →+* T.residueField x :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (T ↘ Spec (.of k)).appTop ≫ T.Γevaluation x).hom
  exact (map_natCast φ l ▸ (Fact.out : IsUnit (l : k)).map φ).invertible

variable [hft : LocallyOfFiniteType (T ↘ Spec (.of k))]
  [hqc : QuasiCompact (T ↘ Spec (.of k))] [hsep : IsSeparated (T ↘ Spec (.of k))]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

include hk hOver hft hqc hsep in
/-- Ambient internal Hom of any two integral constructible objects is constructible.
Source: Bhatt--Scholze, Lemma 6.7.13 (blueprint: lem-per-adic-closed-constructible).
Proof: (1) R is a Noetherian DVR with finite residue field; the completed coefficient
sheaf is flat with the expected quotients. Finite type over k makes T Noetherian and
finite dimensional. (2) The strict balanced-tensor formula identifies completed tensor
with the quotient-completion reflector. (3) Integral Hom reduction gives completeness
and identifies each reduced Hom with the finite-coefficient internal Hom.
(4) At the residue field the reductions have finite Tor amplitude; apply
lem-per-finite-tor-internal-hom-any-field to get a bounded constructible residue Hom.
(5) For n>1 use 0 -> R/t -> R/t^n -> R/t^(n-1) -> 0. Its tensor triangle and the
cohomology long exact sequence keep the same finite interval at every n. The weak
Serre property gives constructibility, with affine partitions combined using a finite
affine cover of the Noetherian scheme. Finite-ring derived origin gives etale origin.
Completeness and these uniformly bounded constructible reductions are exactly the
recorded integral predicate. These are DAG proof steps 1--5, using respectively
lem-weil-l-adic-extension-integers-dvr, lem-weil-pbc-constant-completion-equivalence,
lem-weil-pbc-finite-type-over-noetherian, lem-kun-dimension-finite-type,
lem-weil-pbc-integral-stratified-perfect-characterization,
lem-weil-pbc-ringed-koszul-completion-reflector, lem-coef-integral-hom-reduction,
lem-per-finite-tor-internal-hom-any-field, lem-sf-derived-ses-triangle,
lem-sf-derived-homology-long-exact, lem-sfb-discrete-noetherian-constructible-serre,
def-weil-finite-torsion-constructibility and lem-weil-pbc-finite-ring-constructible-derived-origin.
-/
theorem hom_constructible (P Q : sfIntegralConstructibleCategory l E T) :
    sfIntegralConstructible l E T
      ((integralDerivedInternalHom l E T).obj (op P.obj, Q.obj)) := by
  sorry

/-- The published tensor, with the actual base-field inverse passed explicitly.
Source: Bhatt--Scholze, Lemma 6.7.12 (blueprint: lem-per-adic-closed-constructible). -/
abbrev tensor :=
  @constructibleIntegralTensor l _ E _ _ _ T (residueInvertible l k T)

/-- The restriction of the existing ambient internal-Hom functor to all pairs.
Source: Bhatt--Scholze, Lemma 6.7.13 (blueprint: lem-per-adic-closed-constructible). -/
def hom : (sfIntegralConstructibleCategory l E T)ᵒᵖ ×
    sfIntegralConstructibleCategory l E T ⥤ sfIntegralConstructibleCategory l E T :=
  (sfIntegralConstructible l E T).lift
    (((sfIntegralConstructible l E T).ι.op.prod (sfIntegralConstructible l E T).ι) ⋙
      integralDerivedInternalHom l E T)
    (fun PQ ↦ hom_constructible l k T E PQ.1.unop PQ.2)

include hk hOver hft hqc hsep in
/-- The completed tensor-Hom bijection is uniquely fixed by ordinary transposition
and the actual completion unit. The latter is the reduction adjunction unit,
followed by the tensor comparison and inverse normalized Roos realization.
Source: Bhatt--Scholze, Definition 3.4.10 and Lemma 3.4.11
(blueprint: lem-per-adic-closed-constructible).
Proof: DAG steps 2 and 6 identify the displayed unit with the Koszul completion
reflector unit, by the strict balanced tensor formula on simultaneous K-flat
representatives. Maps into the complete target Q are therefore bijective after
precomposition with this very unit. Compose that bijection with the ordinary
ringed-site transpose. Every f has the prescribed image, so the resulting
bijection is unique. The inputs are lem-weil-pbc-ringed-koszul-completion-reflector,
lem-weil-pbc-constant-completion-equivalence,
lem-weil-pbc-ringed-internal-hom-exact-restriction and lem-pur-rhom-global-sections. -/
theorem transpose_existsUnique (M P Q : sfIntegralConstructibleCategory l E T) :
    ∃! τ : ((integralCompletedTensor l E T).obj (M.obj, P.obj) ⟶ Q.obj) ≃
        (M.obj ⟶ (integralDerivedInternalHom l E T).obj (op P.obj, Q.obj)),
      ∀ f, τ f = (pullbackTensorCalculus l E T).integralClosed.transpose M.obj P.obj Q.obj
        ((pullbackTensorCalculus l E T).adjunction.unit.app _ ≫
          (coefficientSequenceLimit l E T).map
            ((pullbackTensorCalculus l E T).reductionTensor.hom.app (M.obj, P.obj)) ≫
          (pullbackTensorIntegralTensorModel l E T).inv.app (M.obj, P.obj) ≫ f) := by
  sorry

/-- The unique completed transpose with the preceding completion-unit normalization.
Source: Bhatt--Scholze, Lemma 3.4.11 (blueprint: lem-per-adic-closed-constructible). -/
def transpose (M P Q : sfIntegralConstructibleCategory l E T) :=
  (transpose_existsUnique l k T E M P Q).exists.choose

/-- The actual completed evaluation, the inverse transpose of the identity.
Source: Bhatt--Scholze, Lemma 3.4.11 (blueprint: lem-per-adic-closed-constructible). -/
def evaluation (P Q : sfIntegralConstructibleCategory l E T) :
    (integralCompletedTensor l E T).obj
        ((integralDerivedInternalHom l E T).obj (op P.obj, Q.obj), P.obj) ⟶ Q.obj :=
  (transpose l k T E ((hom l k T E).obj (op P, Q)) P Q).symm (𝟙 _)

/-- Closed symmetric monoidal structure with exactly the recorded tensor, ambient
internal Hom and completed coefficient-ring unit. The transpose equality pins its
adjunction to ambient evaluation after the canonical ordinary-to-completed unit.
Source: Bhatt--Scholze, Definition 3.4.10, Lemmas 3.4.11, 6.7.12--6.7.13
(blueprint: lem-per-adic-closed-constructible).
Proof: DAG step 1 gives the one-stratum rank-one unit. Steps 2 and 6 identify maps
out of completed tensor into a complete target with maps out of ordinary tensor,
then apply the ambient ringed-site adjunction. Fullness and hom_constructible put
the Hom in the integral category. This is precisely the completion-unit-normalized transpose.
For step 7, currying into complete test objects shows C(CA tensor D) = C(A tensor D).
Hence both triple bracketings identify with C(M tensor P tensor Q). Ordinary
rebracketing, unit multiplication and signed symmetry induce the constraints.
The pentagon, triangle and symmetry identities follow from the ordinary identities
by the reflector's bijection. Tensor closure is
lem-pur-integral-operations-preserve-constructible; the other inputs are
lem-weil-pbc-ringed-koszul-completion-reflector,
lem-weil-pbc-ringed-internal-hom-exact-restriction and lem-pur-rhom-global-sections. -/
theorem closed_symmetric_monoidal :
    ∃ S : CoefficientClosedStructure (hom l k T E),
      Nonempty (@SymmetricCategory _ _ S.monoidal) ∧
      ∃ hTensor : S.tensor = tensor l k T E,
        S.monoidal.tensorUnit.obj =
          (DerivedCategory.singleFunctor (integralTowerModules l E T) 0).obj
            (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E T)) ∧
        ∀ (M P Q : sfIntegralConstructibleCategory l E T)
          (f : (tensor l k T E).obj (M, P) ⟶ Q),
          (S.transpose M P Q
            (eqToHom (congrArg (fun F ↦ F.obj (M, P)) hTensor) ≫ f)).hom =
            transpose l k T E M P Q f.hom := by
  sorry

variable (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- Abbreviation for the already recorded scalar functor on the integral category;
the auxiliary p=0 in its interface adds no hypothesis, since l is prime.
Source: blueprint integral scalar extension; Bhatt--Scholze, Section 6.7
(blueprint: lem-per-adic-closed-constructible). -/
abbrev extend : sfIntegralConstructibleCategory l E T ⥤ sfIntegralConstructibleCategory l L T :=
  sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι T

/-- The evaluation-defined completed Hom comparison from the dependency, including
its inverse. Its ordinary model is the transpose of extended ordinary evaluation;
scalarCompletionIso supplies the canonical completion identifications.
Source: Bhatt--Scholze, Sections 3.4 and 6.7; Stacks 08J9
(blueprint: lem-per-adic-closed-constructible). -/
abbrev homScalar (P Q : sfIntegralConstructibleCategory l E T) :=
  scalarHomCompleteInputs l E L ι T P.obj Q.obj P.property.1 Q.property.1

/-- Naturality, evaluation normalization and compatibility of every adjunction
bijection with integral scalar extension. In particular the specified transpose of
extended completed evaluation is the recorded isomorphism, not an arbitrary map.
Source: Bhatt--Scholze, Section 6.7; Stacks 08J9
(blueprint: lem-per-adic-closed-constructible).
Proof: DAG step 8 applies finite-free completed scalar comparison to P,Q and their
complete Hom. Ringed finite-free Hom base change is evaluation-transposed and
invertible. On K-flat representatives the scalar tensor map sends
(x tensor s) tensor (y tensor t) to (x tensor y) tensor st. Reduction and Roos
realization give scalarTensorCompleted. The reflector's uniqueness therefore
identifies the displayed transposes. For step 9, uncurry: both sides evaluate u(m)
on p and multiply the two new coefficients. This proves naturality in both
variables, the evaluation equation (u=identity), and every transpose equation.
Inputs: lem-weil-finite-free-completed-scalar-comparison,
lem-sf-ringed-finite-free-hom-base-change, lem-weil-integral-scalar-extension-constructible,
lem-pur-integral-operations-scalar-extension and the closed adjunction of step 6. -/
theorem scalar_laws :
    (∀ (P Q P' Q' : sfIntegralConstructibleCategory l E T) (a : P' ⟶ P) (b : Q ⟶ Q'),
      (integralScalarExtension l E L ι T).map
          ((integralDerivedInternalHom l E T).map (Prod.mkHom a.hom.op b.hom)) ≫
        (homScalar l T E L ι P' Q').hom =
      (homScalar l T E L ι P Q).hom ≫
        (integralDerivedInternalHom l L T).map (Prod.mkHom
          ((integralScalarExtension l E L ι T).map a.hom).op
          ((integralScalarExtension l E L ι T).map b.hom))) ∧
    (∀ P Q : sfIntegralConstructibleCategory l E T,
      (homScalar l T E L ι P Q).hom =
        transpose l k T L
          ((extend l T E L ι).obj ((hom l k T E).obj (op P, Q)))
          ((extend l T E L ι).obj P) ((extend l T E L ι).obj Q)
          ((scalarTensorCompleted l E L ι T
            ((integralDerivedInternalHom l E T).obj (op P.obj, Q.obj)) P.obj
            (hom_constructible l k T E P Q).1 P.property.1
            ((tensor l k T E).obj
              ((hom l k T E).obj (op P, Q), P)).property.1).inv ≫
            (integralScalarExtension l E L ι T).map (evaluation l k T E P Q))) ∧
    (∀ (M P Q : sfIntegralConstructibleCategory l E T)
      (f : (integralCompletedTensor l E T).obj (M.obj, P.obj) ⟶ Q.obj),
      (integralScalarExtension l E L ι T).map (transpose l k T E M P Q f) ≫
          (homScalar l T E L ι P Q).hom =
        transpose l k T L ((extend l T E L ι).obj M)
          ((extend l T E L ι).obj P) ((extend l T E L ι).obj Q)
          ((scalarTensorCompleted l E L ι T M.obj P.obj M.property.1 P.property.1
            ((tensor l k T E).obj (M, P)).property.1).inv ≫
            (integralScalarExtension l E L ι T).map f)) := by
  sorry

/-- Identity normalization and the tower square for precisely the published
composition isomorphisms of integral scalar extension.
Source: Bhatt--Scholze, Section 6.7; Stacks 08J9
(blueprint: lem-per-adic-closed-constructible).
Proof: DAG step 9 uncurry the identity and tower composites. On simultaneous
representatives both tower maps send (h tensor s tensor s', p tensor u') to
h(p) tensor ss'u'. Scalar multiplication is associative; the degree-zero
coefficients introduce no signs. Balancing, quotient transitions and Roos
realization preserve this equality. Normalized ordinary-to-completed comparisons
cancel in the two composites, giving exactly sfIntegralScalarComp. For the
identity extension the formula is ordinary evaluation and sfIntegralScalarUnit
is the completion-unit identification. The closed transpose is injective, so
the two displayed identities follow. Inputs are
lem-sf-ringed-finite-free-hom-base-change,
lem-weil-finite-free-completed-scalar-comparison,
lem-pur-integral-operations-scalar-extension and lem-weil-scalar-extension-composition. -/
theorem scalar_coherence (P Q : sfIntegralConstructibleCategory l E T) :
    (((sfIntegralScalarUnit l E T 0 (Nat.Prime.ne_zero (Fact.out : l.Prime))).inv.app
        ((hom l k T E).obj (op P, Q))).hom ≫
      (homScalar l T E E (AlgHom.id ℚ_[l] E) P Q).hom ≫
      (integralDerivedInternalHom l E T).map (Prod.mkHom
        (((sfIntegralScalarUnit l E T 0 (Nat.Prime.ne_zero (Fact.out : l.Prime))).inv.app
          P).hom.op)
        (((sfIntegralScalarUnit l E T 0 (Nat.Prime.ne_zero (Fact.out : l.Prime))).hom.app
          Q).hom)) = 𝟙 _) ∧
    (∀ (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
      (j : L →ₐ[ℚ_[l]] F),
      (integralScalarExtension l L F j T).map (homScalar l T E L ι P Q).hom ≫
        (homScalar l T L F j ((extend l T E L ι).obj P)
          ((extend l T E L ι).obj Q)).hom ≫
        (integralDerivedInternalHom l F T).map (Prod.mkHom
          (((sfIntegralScalarComp l E L ι T 0 (Nat.Prime.ne_zero (Fact.out : l.Prime))
            F j).inv.app P).hom.op)
          (((sfIntegralScalarComp l E L ι T 0 (Nat.Prime.ne_zero (Fact.out : l.Prime))
            F j).hom.app Q).hom)) =
        ((sfIntegralScalarComp l E L ι T 0 (Nat.Prime.ne_zero (Fact.out : l.Prime))
          F j).hom.app ((hom l k T E).obj (op P, Q))).hom ≫
          (homScalar l T E F (j.comp ι) P Q).hom) := by
  sorry

end WeilConjectures.AdicClosed
