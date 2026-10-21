/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Sheaf.Algebra.Homology.FiniteFreeCompletionExchange
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import Sheaf.CategoryTheory.StrictRoosComparison
public import Sheaf.CategoryTheory.CompactSupportRoosCofinality
public import Sheaf.CategoryTheory.StrictRoosAdditiveComparison
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.CategoryTheory.StrictRoosModel

/-! # Coherence of finite free completion exchange

Source: Stacks Project, sites-cohomology.tex, Tag 0941, and the coefficient-tower
and identity refinement in the DAG proof, steps 1--10.
(blueprint: lem-pur-finite-free-completion-exchange-coherence).

The ordinary associator is fixed on sheafified tensor generators, and the derived
associator is fixed by the recorded cochain counits. Exchanges retain the existing
representative specification, including both actual Roos coordinates.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v r wR wS wV x y xA xB xD yA yB yD
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.StrictTowerArithmetic
open scoped ChangeOfRings

namespace CategoryTheory.PrincipalQuotientCompletion

/-- The actual arithmetic Roos map from selection and finite-block summation.
This is the already defined map of the corresponding commuting square.
Source: Stacks 0H9K, DAG proof steps 6--7
(blueprint: lem-pur-finite-free-completion-exchange-coherence). -/
noncomputable def arithmeticRoosMap
    {A : Type x} [Category.{y} A] [Abelian A] [HasCountableProducts A]
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (e : ℕ) (he : 1 ≤ e) :
    roosF.obj X ⟶ roosF.obj ((complexRestriction A e).obj X) :=
  strictRoosMapOfSquare (selection e X.asFunctor) (block e X.asFunctor)
    (strictRoosBlock_comm X e he)

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [HasSheafify J AddCommGrpCat.{r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  {R S V : Sheaf J CommRingCat.{r}} {a : R ⟶ S} {b : S ⟶ V}
  [HasDerivedCategory.{wR}
    (ringedSiteModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J R))]
  [HasDerivedCategory.{wS}
    (ringedSiteModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J S))]
  [HasDerivedCategory.{wV}
    (ringedSiteModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J V))]

/-- A sheafified pure tensor, transported through the model's prescribed object equality.
Source: Stacks 03EK, balanced formula in DAG proof step 1
(blueprint: lem-pur-finite-free-completion-exchange-coherence). -/
noncomputable def scalarTensorSection
    (F : SheafOfModules.DerivedChangeOfRingsCochainModel a)
    (M : ringedSiteModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J R))
    (U : Cᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) : (F.E.obj M).val.obj U :=
  (eqToHom (F.obj_eq M).symm).val.app U
    ((toSheafify J (SheafOfModules.changeOfRingsPresheaf a M).presheaf).app U
      (s ⊗ₜ[R.obj.obj U, (a.hom.app U).hom] x))

/-- Normalization of the balanced scalar associator at ordinary and derived levels.
The derived formula uses K-flat representatives and the specified cochain counits.
Source: Stacks 03EK, 06YT and 06YY, DAG proof step 1
(blueprint: lem-pur-finite-free-completion-exchange-coherence). -/
structure BalancedScalarAssociator
    (Fa : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} a)
    (Fb : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, r, wS, wV} b)
    (Fba : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, r, wR, wV} (a ≫ b)) where
  /-- The ordinary, sheafified balanced associator. -/
  ordinary : Fa.E ⋙ Fb.E ≅ Fba.E
  /-- Its precise formula on local tensor generators. -/
  balanced : ∀ M (U : Cᵒᵖ) (s : S.obj.obj U) (q : V.obj.obj U) (x : M.val.obj U),
    (ordinary.hom.app M).val.app U
      (scalarTensorSection Fb (Fa.E.obj M) U q (scalarTensorSection Fa M U s x)) =
        scalarTensorSection Fba M U (b.hom.app U s * q) x
  /-- The natural associator on the unbounded derived categories. -/
  derived : Fa.T ⋙ Fb.T ≅ Fba.T
  /-- Its normalization through the canonical K-flat computation maps. -/
  computes : ∀ P, CochainComplex.IsKFlatIndependentCoefficients (R := R) P →
    derived.hom.app (DerivedCategory.Q.obj P) ≫ Fba.ε.app P =
      Fb.T.map (Fa.ε.app P) ≫ Fb.ε.app ((extendedComplex Fa).obj P) ≫
        DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso ordinary (.up ℤ)).hom.app P)

/-- The scalar multiplication identification for identity extension, with its derived
normalization. Source: Stacks 03EK and 06YY, DAG proof step 9
(blueprint: lem-pur-finite-free-completion-exchange-coherence). -/
structure BalancedScalarUnit
    (F : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, r, wR, wR} (𝟙 R)) where
  /-- Ordinary multiplication. -/
  ordinary : F.E ≅ 𝟭 _
  /-- Multiplication on every sheafified tensor generator. -/
  balanced : ∀ M (U : Cᵒᵖ) (s : R.obj.obj U) (x : M.val.obj U),
    (ordinary.hom.app M).val.app U (scalarTensorSection F M U s x) = s • x
  /-- The induced derived multiplication identification. -/
  derived : F.T ≅ 𝟭 _
  /-- Its canonical K-flat normalization. -/
  computes : ∀ P, CochainComplex.IsKFlatIndependentCoefficients (R := R) P →
    derived.hom.app (DerivedCategory.Q.obj P) =
      F.ε.app P ≫ DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app P)

/-- Strict coordinate coherence before inverting arithmetic restriction.
`restricted` is the second scalar comparison on the first arithmetic subsequence;
its finite-stage maps are precisely the selected finite-stage maps of `rb`.
The last two fields give the arithmetic square and weighted-block composition.
Source: Stacks 0941 and 0H9K, DAG proof steps 3--8
(blueprint: lem-pur-finite-free-completion-exchange-coherence). -/
structure RepresentativeComposition
    {A : Type xA} [Category.{yA} A] [Abelian A] [HasCountableProducts A]
    {B : Type xB} [Category.{yB} B] [Abelian B] [HasCountableProducts B]
    {D : Type xD} [Category.{yD} D] [Abelian D] [HasCountableProducts D]
    {E : A ⥤ B} [E.Additive] {F : B ⥤ D} [F.Additive] {G : A ⥤ D} [G.Additive]
    (α : E ⋙ F ≅ G)
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (Y : CochainComplex (ℕᵒᵖ ⥤ B) ℤ)
    (Z W : CochainComplex (ℕᵒᵖ ⥤ D) ℤ) (m : Z ⟶ W)
    (e f : ℕ) (he : 1 ≤ e)
    (ra : RepresentativeRoosComparison E X Y e)
    (rb : RepresentativeRoosComparison F Y Z f)
    (rba : RepresentativeRoosComparison G X W (e * f)) where
  /-- The second tensor/product comparison on the restricted source tower. -/
  restricted : RepresentativeRoosComparison F ((complexRestriction B e).obj Y) Z (e * f)
  /-- Reindexing selects the original quotient maps without a new unit multiplier. -/
  selected_quotients : ∀ n : ℕ,
    HEq (restricted.β.hom.app (op n)) (rb.β.hom.app ((index e).obj (op n)))
  /-- Equality of the actual chain maps, hence of both signed Roos product coordinates. -/
  coordinates :
    (F.mapHomologicalComplex (.up ℤ)).map ra.δ.hom ≫ restricted.δ.hom ≫
      roosF.map ((complexRestriction D (e * f)).map m) =
    (Functor.mapHomologicalComplexCompIso α (.up ℤ)).hom.app (roosF.obj X) ≫ rba.δ.hom
  /-- Arithmetic restriction of the second comparison's target. -/
  arithmetic : roosF.obj ((complexRestriction D f).obj Z) ⟶
    roosF.obj ((complexRestriction D (e * f)).obj Z)
  /-- Both coordinates use selection and the weighted finite-block sum. -/
  arithmetic_coordinates : HEq arithmetic
    (arithmeticRoosMap ((complexRestriction D f).obj Z) e he)
  /-- Additive scalar extension commutes with the specified arithmetic map. -/
  arithmetic_square :
    (F.mapHomologicalComplex (.up ℤ)).map ra.a ≫ restricted.δ.hom = rb.δ.hom ≫ arithmetic
  /-- Weighted blocks compose in exactly the order used by the coefficient tower. -/
  arithmetic_composition : rb.a ≫ arithmetic = restricted.a

/-- The specified completion exchanges compose with balanced scalar reassociation,
including their quotient units, actual Roos coordinates and normalized limit transport.

Source: Stacks Project, sites-cohomology.tex, Tag 0941, agent-formulated coefficient-tower
refinement, DAG proof steps 1--10
(blueprint: lem-pur-finite-free-completion-exchange-coherence).

Proof plan:
1. Resolve by an unbounded K-flat complex P using lem-pc-kflat-resolution.
lem-pur-derived-change-of-rings computes both extensions, and extension preserves
K-flatness by restriction of acyclic test complexes. Balanced scalar multiplication
and insertion of 1 give inverse chain associators and their natural derived descent.
2. Finite freeness makes scalar extension exact and identifies its product comparison
with the canonical map to finite tuples; rank zero gives the zero functor. Composed
bases show V is finite free over R. Only invertibility uses bases.
3. Use lem-pur-finite-free-completion-exchange to express each exchange as its actual
Roos tensor/product comparison followed by inverse arithmetic restriction.
4. The equal ideals a(t^n)S=(v^(en)) and b(v^m)V=(w^(fm)) identify the quotient maps.
Both balanced routes send ((rbar tensor s) tensor q) to (ba)(r)b(s)q modulo w^(efn).
Units affect the equality of ideals, never the residue formula or its transitions.
5. Project each tensor/product map to its nth factor. Naturality of the balanced
associator gives the same map; product universality proves equality on both signed
Roos coordinates. This yields RepresentativeComposition.coordinates.
6. Apply lem-pur-roos-additive-comparison: selection commutes with extension and the
weighted block map commutes because extension carries each finite sum and transition
to the corresponding one. This gives the arithmetic square for nonconstant rings.
7. Expanding the e blocks of length f gives the interval of length ef. Transition
composition and finite sum regrouping prove the arithmetic composition equation.
8. Multiply both derived routes by this specified arithmetic quasi-isomorphism.
Steps 5--7 identify them, and cancellation gives the displayed derived equation.
9. The quotient unit has coordinates (0, quotient family). Every preceding map
preserves these coordinates. All formulas commute with chain maps and descend
naturally along K-flat resolutions, so the equality holds for every Q in D(R).
10. lem-weil-strict-roos-comparison replaces each Roos vertex by its normalized
strict derived limit. Naturality moves these comparisons past the maps and the
intermediate inverse pairs cancel. The transport clause applies in particular to
these normalized identifications. No bound, completeness or perfectness is used. -/
theorem finiteFreeCompletionExchangeCoherence
    (Fa : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} a)
    (Fb : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, r, wS, wV} b)
    (Fba : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, r, wR, wV} (a ≫ b))
    (_hfreeS : ∃ d : ℕ, Nonempty
      ((SheafOfModules.restrictScalars
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map a)).obj
          (SheafOfModules.unit (SheafOfModules.derivedChangeRingIndependentCoefficients J S)) ≅
        ∐ (fun _ : Fin d ↦ SheafOfModules.unit
          (SheafOfModules.derivedChangeRingIndependentCoefficients J R))))
    (_hfreeV : ∃ d : ℕ, Nonempty
      ((SheafOfModules.restrictScalars
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map b)).obj
          (SheafOfModules.unit (SheafOfModules.derivedChangeRingIndependentCoefficients J V)) ≅
        ∐ (fun _ : Fin d ↦ SheafOfModules.unit
          (SheafOfModules.derivedChangeRingIndependentCoefficients J S))))
    (t : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)).sections)
    (vS : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J S)).sections)
    (w : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J V)).sections)
    (_ht : Mono (globalSectionMultiplication R t))
    (_hv : Mono (globalSectionMultiplication S vS))
    (_hw : Mono (globalSectionMultiplication V w))
    (uS : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J S)).sections)
    (z : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J V)).sections)
    (_hu : ∀ U : Cᵒᵖ, IsUnit (@id (S.obj.obj U) (uS.val U)))
    (_hz : ∀ U : Cᵒᵖ, IsUnit (@id (V.obj.obj U) (z.val U)))
    (e f : ℕ) (_he : 1 ≤ e) (_hf : 1 ≤ f)
    (_ha : ∀ U : Cᵒᵖ, a.hom.app U (@id (R.obj.obj U) (t.val U)) =
      (@id (S.obj.obj U) (uS.val U)) * (@id (S.obj.obj U) (vS.val U)) ^ e)
    (_hb : ∀ U : Cᵒᵖ, b.hom.app U (@id (S.obj.obj U) (vS.val U)) =
      (@id (V.obj.obj U) (z.val U)) * (@id (V.obj.obj U) (w.val U)) ^ f)
    [HasExactLimitsOfShape (Discrete ℕ)
      (ringedSiteModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J R))]
    [HasExactLimitsOfShape (Discrete ℕ)
      (ringedSiteModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J S))]
    [HasExactLimitsOfShape (Discrete ℕ)
      (ringedSiteModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J V))]
    [HasExactLimitsOfShape (Discrete ℕ) (Sheaf J AddCommGrpCat.{r})] :
    ∃ α : BalancedScalarAssociator Fa Fb Fba,
      ∀ (CR : Model R t) (CS : Model S vS) (CV : Model V w)
        (εa : CR.completion ⋙ Fa.T ≅ Fa.T ⋙ CS.completion)
        (εb : CS.completion ⋙ Fb.T ≅ Fb.T ⋙ CV.completion)
        (εba : CR.completion ⋙ Fba.T ≅ Fba.T ⋙ CV.completion),
      (∀ P, CochainComplex.IsKFlatIndependentCoefficients (R := R) P →
        Nonempty (RepresentativeComparison Fa t vS e CR CS εa P)) →
      (∀ P, CochainComplex.IsKFlatIndependentCoefficients (R := S) P →
        Nonempty (RepresentativeComparison Fb vS w f CS CV εb P)) →
      (∀ P, CochainComplex.IsKFlatIndependentCoefficients (R := R) P →
        Nonempty (RepresentativeComparison Fba t w (e * f) CR CV εba P)) →
      (∀ Q, Fb.T.map (εa.hom.app Q) ≫ εb.hom.app (Fa.T.obj Q) ≫
        CV.completion.map (α.derived.hom.app Q) =
          α.derived.hom.app (CR.completion.obj Q) ≫ εba.hom.app Q) ∧
      (∀ Q, Fa.T.map (CR.unit.app Q) ≫ εa.hom.app Q = CS.unit.app (Fa.T.obj Q)) ∧
      (∀ Q, Fb.T.map (CS.unit.app Q) ≫ εb.hom.app Q = CV.unit.app (Fb.T.obj Q)) ∧
      (∀ Q, Fba.T.map (CR.unit.app Q) ≫ εba.hom.app Q = CV.unit.app (Fba.T.obj Q)) ∧
      (∀ P, CochainComplex.IsKFlatIndependentCoefficients (R := R) P →
        ∃ (ra : RepresentativeComparison Fa t vS e CR CS εa P)
          (rb : RepresentativeComparison Fb vS w f CS CV εb ((extendedComplex Fa).obj P))
          (rba : RepresentativeComparison Fba t w (e * f) CR CV εba P),
          Nonempty (RepresentativeComposition α.ordinary
            (sourceTower t P) (targetTower Fa vS P)
            (targetTower Fb w ((extendedComplex Fa).obj P)) (targetTower Fba w P)
            ((quotientTower V w).map
              ((Functor.mapHomologicalComplexCompIso α.ordinary (.up ℤ)).hom.app P))
            e f _he ra.val rb.val rba.val)) ∧
      (∀ (D : DerivedCategory.{wV} (ringedSiteModules.{r}
          (SheafOfModules.derivedChangeRingIndependentCoefficients J V)) ⥤
          DerivedCategory.{wV} (ringedSiteModules.{r}
          (SheafOfModules.derivedChangeRingIndependentCoefficients J V)))
        (ρ : CV.completion ≅ D) Q,
        Fb.T.map (εa.hom.app Q) ≫ εb.hom.app (Fa.T.obj Q) ≫
          CV.completion.map (α.derived.hom.app Q) ≫ ρ.hom.app (Fba.T.obj Q) =
        α.derived.hom.app (CR.completion.obj Q) ≫ εba.hom.app Q ≫
          ρ.hom.app (Fba.T.obj Q)) := by
  sorry

/-- For identity coefficients and exponent one the specified exchange is identity
under scalar multiplication; its quotient augmentation is the same strict quotient unit.

Source: Stacks 03EK, 0941 and 0H9K, DAG proof steps 7 and 9
(blueprint: lem-pur-finite-free-completion-exchange-coherence).

Proof: Multiplication s tensor x to sx and x to 1 tensor x give inverse ordinary
identity-extension maps; they commute with all module maps and differentials.
K-flat computation descends them to the normalized derived unit. The canonical
product comparison and quotient maps become identities under multiplication.
For exponent one selection is identity and each weighted block has the single
identity-transition term. Thus both actual Roos coordinates of the exchange are
identity. Its quotient augmentation is (0, quotient family), so the unit equation
also holds. Localizing and using the normalized strict-Roos comparison preserves
these equations. This works for all unbounded Q and includes zero rings. -/
theorem finiteFreeCompletionExchangeIdentity
    (F : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, r, wR, wR} (𝟙 R))
    (t : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)).sections)
    (_ht : Mono (globalSectionMultiplication R t))
    [HasExactLimitsOfShape (Discrete ℕ)
      (ringedSiteModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J R))]
    [HasExactLimitsOfShape (Discrete ℕ) (Sheaf J AddCommGrpCat.{r})] :
    ∃ ι : BalancedScalarUnit F, ∀ (CR : Model R t)
      (ε : CR.completion ⋙ F.T ≅ F.T ⋙ CR.completion),
      (∀ P, CochainComplex.IsKFlatIndependentCoefficients (R := R) P →
        Nonempty (RepresentativeComparison F t t 1 CR CR ε P)) →
      (∀ Q, ε.hom.app Q ≫ CR.completion.map (ι.derived.hom.app Q) =
        ι.derived.hom.app (CR.completion.obj Q)) ∧
      (∀ Q, F.T.map (CR.unit.app Q) ≫ ε.hom.app Q = CR.unit.app (F.T.obj Q)) := by
  sorry

end CategoryTheory.PrincipalQuotientCompletion
