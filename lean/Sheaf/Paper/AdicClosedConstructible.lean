/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.IntegralScalarExtensionUniverses
public import Sheaf.Paper.IntegralOperationsScalarComparisons
public import Sheaf.Paper.SfScalarExtensionComposition
public import Sheaf.Paper.CompletedPullbackTensorComparison
public import Sheaf.Paper.CoefficientRingedTensorHomModel
public import Sheaf.Paper.IntegralScalarExtensionConstructibleIntrinsic
public import WeilConjectures.ZetaSeries
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.Paper.ConstantCompletionCore
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
import Sheaf.Paper.WeilCompletedTensorReflector
import Sheaf.Paper.IntegralDerivedOperationsOnSlices
import Sheaf.Paper.IntegralHomReduction
import Sheaf.Paper.FiniteTorInternalHomAnyField
import Sheaf.AlgebraicGeometry.DiscreteNoetherianConstructibleSerre
import Sheaf.Paper.FiniteRingConstructibleDerivedOrigin
import Sheaf.Paper.IntegralOperationsPreserveConstructible
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses
import Sheaf.Paper.FiniteFreeCompletedScalarComparison
import Sheaf.SixFunctors.RingedFiniteFreeHomBaseChange
import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-! # Closed structure on integral constructible adic complexes

Source: Bhatt--Scholze, Sections 3.4, 6.5 and 6.7, especially Lemmas 3.4.11,
6.7.12 and 6.7.13 (blueprint: lem-per-adic-closed-constructible).
The scalar comparisons are transposes of evaluation through the recorded completed
tensor comparison. Coefficients are modules over the completed ring sheaf.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicClosed

/-- Transport the inverse of ell along the structural residue-field map.
Source: Bhatt--Scholze, the ell-coprime hypothesis in Section 6.7
(blueprint: lem-per-adic-closed-constructible). -/
@[instance_reducible] def residueInvertible (l : ℕ) (k : Type u) [Field k] (hl : IsUnit (l : k))
    (W : Scheme.{u}) [W.Over (Spec (.of k))] (w : W) :
    Invertible (l : W.residueField w) :=
  (map_natCast ((W ↘ Spec (.of k)).residueFieldAlgebraMap w) l) ▸
    (hl.map ((W ↘ Spec (.of k)).residueFieldAlgebraMap w)).invertible

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (k : Type u) [Field k] (hl : IsUnit (l : k))
  (W : Scheme.{u}) [hW : W.Over (Spec (.of k))]
  [hft : LocallyOfFiniteType (W ↘ Spec (.of k))]
  [hqc : QuasiCompact (W ↘ Spec (.of k))]
  [hsep : IsSeparated (W ↘ Spec (.of k))]

include hl hW hft hqc hsep in
/-- Ambient internal Hom preserves the intrinsic integral constructible predicate.
Source: Bhatt--Scholze, Lemma 6.7.13
(blueprint: lem-per-adic-closed-constructible).

Proof: (1) the completed coefficient ring is flat over the DVR, has the specified
finite reductions, and its degree-zero unit is stratified perfect. Finite type over
k makes W Noetherian and finite-dimensional. (2) identify the strict finite-tensor
Roos tower with completion of ordinary tensor on flat-term K-flat representatives.
(3) integral Hom reduction gives completeness and evaluation-defined reduction
isomorphisms. At the residue field, both inputs have finite Tor amplitude.
(4) lem-per-finite-tor-internal-hom-any-field gives bounded constructibility of
that residue Hom. (5) the coefficient exact sequences A_1 -> A_n -> A_(n-1)
give triangles after derived tensor. Induction and the cohomology long exact
sequence keep the same interval; the weak Serre property preserves constructibility.
Affine-local and finite global stratifications agree on the Noetherian W, and
finite-ring derived origin gives the required pro-etale reductions. Together with
completeness these are precisely sfIntegralConstructible. -/
theorem hom_constructible (P Q : sfIntegralConstructibleCategory l E W) :
    sfIntegralConstructible l E W
      ((integralDerivedInternalHom l E W).obj (op P.obj, Q.obj)) := by
  sorry

/-- The full internal-Hom functor is the restriction of the recorded ambient functor.
Only its constructibility proof is postponed; its object and arrow maps are real.
Source: Bhatt--Scholze, Lemma 6.7.13
(blueprint: lem-per-adic-closed-constructible). -/
def hom : (sfIntegralConstructibleCategory l E W)ᵒᵖ ×
    sfIntegralConstructibleCategory l E W ⥤ sfIntegralConstructibleCategory l E W :=
  (sfIntegralConstructible l E W).lift
    (((sfIntegralConstructible l E W).ι.op.prod (sfIntegralConstructible l E W).ι) ⋙
      integralDerivedInternalHom l E W)
    (fun P ↦ hom_constructible l E k hl W P.1.unop P.2)

/-- The recorded completed tensor with residue invertibility derived from the base.
Source: Bhatt--Scholze, Lemma 6.7.12
(blueprint: lem-per-adic-closed-constructible). -/
abbrev tensor := @constructibleIntegralTensor l _ E _ _ _ W (residueInvertible l k hl W)

/-- The completed adjunction is uniquely fixed by the ambient transpose after the
actual reduction/limit unit and the prescribed Roos tensor realization.
Source: Bhatt--Scholze, Lemma 3.4.11; node proof Steps 2 and 6
(blueprint: lem-per-adic-closed-constructible).

Proof: the displayed composite is the ordinary-to-completed tensor map. On good
representatives it is the quotient augmentation into the finite tensor Roos tower.
The Koszul completion reflector identifies precomposition by this map with a
bijection for every complete target Q. Compose with ambient tensor-Hom transposition.
Both bijections are additive, so this is an additive equivalence. Its displayed
value on every arrow determines the equivalence uniquely. -/
theorem transpose_existsUnique (M P Q : sfIntegralConstructibleCategory l E W) :
    ∃! e : ((tensor l E k hl W).obj (M, P) ⟶ Q) ≃+
        (M ⟶ (hom l E k hl W).obj (op P, Q)),
      ∀ f : (tensor l E k hl W).obj (M, P) ⟶ Q,
        HEq ((e f).hom)
          ((pullbackTensorCalculus l E W).integralClosed.transpose M.obj P.obj Q.obj
            ((pullbackTensorCalculus l E W).adjunction.unit.app
                ((pullbackTensorCalculus l E W).integralClosed.tensor.obj (M.obj, P.obj)) ≫
              (coefficientSequenceLimit l E W).map
                ((pullbackTensorCalculus l E W).reductionTensor.hom.app (M.obj, P.obj)) ≫
              (pullbackTensorIntegralTensorModel l E W).inv.app (M.obj, P.obj) ≫ f.hom)) := by
  sorry

/-- The full completed transpose with its unique ambient normalization.
Source: Bhatt--Scholze, Lemma 3.4.11; node proof Step 6
(blueprint: lem-per-adic-closed-constructible). -/
def transpose (M P Q : sfIntegralConstructibleCategory l E W) :
    ((tensor l E k hl W).obj (M, P) ⟶ Q) ≃+
      (M ⟶ (hom l E k hl W).obj (op P, Q)) :=
  (transpose_existsUnique l E k hl W M P Q).exists.choose

/-- The restricted ambient evaluation, equivalently the inverse transpose of identity.
Source: Bhatt--Scholze, Lemma 3.4.11, and node proof Step 6
(blueprint: lem-per-adic-closed-constructible). -/
def evaluation (P Q : sfIntegralConstructibleCategory l E W) :
    (tensor l E k hl W).obj ((hom l E k hl W).obj (op P, Q), P) ⟶ Q :=
  (transpose l E k hl W _ P Q).symm (𝟙 _)

/-- The closed symmetric monoidal structure has the recorded completed tensor,
the degree-zero completed coefficient unit, and precisely the ambient transposes.
Source: Bhatt--Scholze, Lemmas 3.4.11 and 6.7.12--13
(blueprint: lem-per-adic-closed-constructible).

Proof: Steps 1--5 give Hom closure and the coefficient unit. Step 6 uses the
completion reflector to identify maps out of completed tensor into a complete
target with maps out of ordinary tensor, then applies ambient tensor-Hom adjunction.
Fullness identifies these with the subcategory Hom groups. Step 7 reflects the
ordinary associator, unitors and symmetry: completion of CA tensor D equals
completion of A tensor D, by testing maps into complete targets and currying.
Both triple bracketings identify with completion of ordinary triple tensor.
Pentagon, triangle and symmetry follow from their ordinary total-tensor identities.
The normalization in transpose_existsUnique fixes exactly these transposes. -/
theorem closed_symmetric_monoidal :
    ∃ S : CoefficientClosedStructure (hom l E k hl W),
      ∃ ht : S.tensor = tensor l E k hl W,
        Nonempty (@SymmetricCategory _ _ S.monoidal) ∧
        S.monoidal.tensorUnit.obj =
          (DerivedCategory.singleFunctor (integralTowerModules l E W) 0).obj
            (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E W)) ∧
        ∀ (M P Q : sfIntegralConstructibleCategory l E W)
          (f : (tensor l E k hl W).obj (M, P) ⟶ Q),
          S.transpose M P Q (eqToHom (congrArg (fun T ↦ T.obj (M, P)) ht) ≫ f) =
            transpose l E k hl W M P Q f := by
  sorry

section Scalar
variable (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- The scalar comparison is the target transpose of extended evaluation after the
inverse of the recorded completed tensor comparison, on every constructible pair.
Source: node proof Step 8; Stacks 08J9, 08JA
(blueprint: lem-per-adic-closed-constructible). -/
def scalarHom (P Q : sfIntegralConstructibleCategory l E W) :
    (sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
      E L ι W).obj ((hom l E k hl W).obj (op P, Q)) ⟶
      (hom l L k hl W).obj
        (op ((sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).obj P),
          (sfConstructibleIntegralScalarExtension 0 l
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).obj Q) :=
  transpose l L k hl W _ _ _
    ((@integralTensorScalarComparison l _ E _ _ _ L _ _ _ ι W
      (residueInvertible l k hl W) ((hom l E k hl W).obj (op P, Q)) P).inv ≫
        (sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).map
          (evaluation l E k hl W P Q))

/-- Finite scalar extension makes the evaluation-defined comparison invertible.
Source: node proof Step 8; Stacks 08J9, 08JA
(blueprint: lem-per-adic-closed-constructible).

Proof: completed scalar extension equals ordinary finite-free change of rings on
complete objects, including the ambient Hom. Finite-free Hom base change is an
isomorphism, transposed from ordinary extended evaluation. On K-flat representatives
the scalar tensor comparison multiplies the coefficients. Reduction and Roos limit
preserve this formula. Precomposition by the completion unit identifies completed
and ordinary evaluation, so uniqueness of transposition identifies this isomorphism
with scalarHom. No perfect-first-input hypothesis is required. -/
theorem scalarHom_isIso (P Q : sfIntegralConstructibleCategory l E W) :
    IsIso (scalarHom l E k hl W L ι P Q) := by
  sorry

/-- Naturality of the same comparison in both constructible inputs.
Source: node proof Step 9; Stacks 08J9
(blueprint: lem-per-adic-closed-constructible).

Proof: uncurry both routes. Tensor-comparison naturality and evaluation naturality
identify their values with extended evaluation after the given input arrows.
Injectivity of the normalized target transpose gives the displayed equality. -/
theorem scalarHom_naturality (P Q P' Q' : sfIntegralConstructibleCategory l E W)
    (a : P' ⟶ P) (b : Q ⟶ Q') :
    (sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
      E L ι W).map ((hom l E k hl W).map (Prod.mkHom a.op b)) ≫
        scalarHom l E k hl W L ι P' Q' =
      scalarHom l E k hl W L ι P Q ≫
        (hom l L k hl W).map (Prod.mkHom
          (((sfConstructibleIntegralScalarExtension 0 l
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).map a).op)
          ((sfConstructibleIntegralScalarExtension 0 l
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).map b)) := by
  sorry

/-- Scalar extension carries the restricted ambient evaluation to evaluation.
Source: node proof Steps 8--9; Stacks 08J9
(blueprint: lem-per-adic-closed-constructible).

Proof: the defining transpose of scalarHom has inverse transpose equal to extended
evaluation after the inverse tensor comparison. Compose with the tensor comparison
and use the tensor-Hom counit identity to obtain the displayed evaluation square. -/
theorem scalarHom_evaluation (P Q : sfIntegralConstructibleCategory l E W) :
    (@integralTensorScalarComparison l _ E _ _ _ L _ _ _ ι W
      (residueInvertible l k hl W) ((hom l E k hl W).obj (op P, Q)) P).hom ≫
      (tensor l L k hl W).map (Prod.mkHom (scalarHom l E k hl W L ι P Q) (𝟙 _)) ≫
        evaluation l L k hl W
          ((sfConstructibleIntegralScalarExtension 0 l
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).obj P)
          ((sfConstructibleIntegralScalarExtension 0 l
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).obj Q) =
      (sfConstructibleIntegralScalarExtension 0 l
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).map
          (evaluation l E k hl W P Q) := by
  sorry

/-- Scalar extension carries every tensor-Hom transpose to the target transpose.
Source: node proof Step 9; Stacks 08J9
(blueprint: lem-per-adic-closed-constructible).

Proof: write an inverse transpose as evaluation after tensoring its transpose with
the identity of P. Apply scalar extension. The evaluation square and naturality of
the completed tensor comparison give the target inverse transpose; transpose back. -/
theorem scalarHom_transpose (M P Q : sfIntegralConstructibleCategory l E W)
    (f : (tensor l E k hl W).obj (M, P) ⟶ Q) :
    transpose l L k hl W _ _ _
        ((@integralTensorScalarComparison l _ E _ _ _ L _ _ _ ι W
          (residueInvertible l k hl W) M P).inv ≫
            (sfConstructibleIntegralScalarExtension 0 l
              (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).map f) =
      (sfConstructibleIntegralScalarExtension 0 l
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).map
          (transpose l E k hl W M P Q f) ≫ scalarHom l E k hl W L ι P Q := by
  sorry

/-- The identity comparison is the canonical scalar unit on Hom.
Source: node proof Step 9; Stacks 08J9
(blueprint: lem-per-adic-closed-constructible).

Proof: uncurry after the scalar unit identifications. On representatives both maps
send (h,p) to h(p). The normalized tensor comparison and completion preserve this
identity, so injectivity of transposition proves the equation. -/
theorem scalar_identity (P Q : sfIntegralConstructibleCategory l E W) :
    scalarHom l E k hl W E (AlgHom.id ℚ_[l] E) P Q ≫
      (hom l E k hl W).map (Prod.mkHom
        (((sfIntegralScalarUnit l E W 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime))).inv.app P).op)
        ((sfIntegralScalarUnit l E W 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime))).hom.app Q)) =
      (sfIntegralScalarUnit l E W 0 (Nat.Prime.ne_zero (Fact.out : l.Prime))).hom.app
        ((hom l E k hl W).obj (op P, Q)) := by
  sorry

/-- Composition uses the canonical scalar associators and the contravariant inverse.
Source: node proof Step 9; Stacks 08J9
(blueprint: lem-per-adic-closed-constructible).

Proof: uncurry both routes through the completed tensor adjunction. For a tower
E -> L -> F both maps send (h tensor s tensor t, p tensor u) to h(p) tensor s*t*u.
Associativity of coefficient multiplication proves equality on K-flat representatives,
compatible with differentials, reductions and completion. Injectivity of the target
transpose proves the equation with the normalized scalar composition isomorphisms. -/
theorem scalar_tower (F : Type u) [Field F] [Algebra ℚ_[l] F]
    [FiniteDimensional ℚ_[l] F] (j : L →ₐ[ℚ_[l]] F)
    (P Q : sfIntegralConstructibleCategory l E W) :
    (sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
      L F j W).map (scalarHom l E k hl W L ι P Q) ≫
      scalarHom l L k hl W F j
        ((sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).obj P)
        ((sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).obj Q) ≫
      (hom l F k hl W).map (Prod.mkHom
        (((sfIntegralScalarComp l E L ι W 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) F j).inv.app P).op)
        ((sfIntegralScalarComp l E L ι W 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) F j).hom.app Q)) =
      (sfIntegralScalarComp l E L ι W 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) F j).hom.app
          ((hom l E k hl W).obj (op P, Q)) ≫
        scalarHom l E k hl W F (j.comp ι) P Q := by
  sorry

end Scalar
end WeilConjectures.AdicClosed
