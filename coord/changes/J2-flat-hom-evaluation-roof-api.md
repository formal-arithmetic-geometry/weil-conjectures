# CategoryTheory.SfbFlatHom.EvaluationRoof

## Reason

The full proof repeatedly elaborates the same large tensor comparison and roof
conditions. Keep those conditions in named definitions, and use their types for
the structure fields and the private proofs. All seven definitions contain exactly
the original predicates. The field names and generated structure declarations
remain available. The comparison type abbreviations are transparent.

Give `sourceMap`, `targetMap`, `denominator`, `numerator`, and `denominatorInverse`
explicit result types. Change `scalarTensor`, `denominator`, and `numerator` from
abbreviations to ordinary definitions with their original bodies. Local
reducibility attributes provide the proof API; none is exported. These changes
reduce repeated unfolding without changing any map or object.

The private proof uses a proved equation for total-tensor generators before hiding
that construction locally. It reuses the library's proved tensor-map factorization
and total-pure extensionality lemmas. Explicit universe arguments and explicit
unfolding at the scalar-comparison step keep those definitions behind their API.
The private isomorphism definitions need no exported implementation bodies. The original
public imports and the target theorem's signature are unchanged.

The private inclusion API names the homogeneous summand inclusions of the total
tensor and proves their naturality. Generator mapping then uses that square
and the existing pure-tensor map formula, keeping the colimit construction
out of subsequent elaboration. This adds only proved private helpers.

A proved private evaluation-transport lemma matches the two chain evaluations on
homogeneous tensor generators. Its interface states only the needed normalization
law, so the final roof calculation does not repeatedly unfold the representative data.


For the semantic acceptance check, unfolding the named conditions recovers all
original binders and conclusions verbatim. There is no new mathematical premise,
choice of data, weaker conclusion, or change to a target of `Challenge.lean`.

Any target whose statement uses these definitions is submitted for the standard
semantic review again. The original field expressions and the reflexivity checks
provide the comparison for that review.

## Old

In the file's original surrounding namespace and variables:

```lean
/-- The already recorded strict tensor functor with the restricted regular S-module.
This abbreviation uses restriction of scalars and the actual single-zero total tensor.
Source: Stacks 03CZ, 06YN (blueprint: lem-sfb-hom-flat-evaluation-roof). -/
noncomputable abbrev scalarTensor {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S) :=
  Prod.sectR ((scalarRestriction a).obj (SheafOfModules.unit
    ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj S)))
    (CochainComplex (scalarModules J R) ℤ) ⋙ tensor.{c, v, r} J R

variable (M : ScalarHomModels.{c, v, r, w} J)
  (μ : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S),
    ScalarHomTensorComparison M a)
  (α : ScalarInternalHomAdjunction M μ)
  {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)

/-- The canonical map c is the transpose of scalar-extended evaluation, with the
inverse strong tensor comparison in front of it. It is defined for all derived inputs.
Source: Stacks 08J9, 07A4 (blueprint: lem-sfb-hom-flat-evaluation-roof). -/
noncomputable def comparison (K L : DerivedCategory (scalarModules J R)) :
    (M.scalar a).derived.obj
        ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op K, L)) ⟶
      (derivedInternalHomOfUniverses.{c, v, r, w} J S).obj
        (op ((M.scalar a).derived.obj K), (M.scalar a).derived.obj L) :=
  (M.closed S).transpose _ _ _
    ((μ a).iso.inv.app
        ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op K, L), K) ≫
      (M.scalar a).derived.map ((M.closed R).evaluation K L))

/-- The precise map Theta U(c), using the recorded normalized scalar adjunction.
Source: Stacks 08J9, 03CZ (blueprint: lem-sfb-hom-flat-evaluation-roof). -/
noncomputable def restrictedComparison (K L : DerivedCategory (scalarModules J R)) :
    (scalarDerivedRestriction a).obj ((M.scalar a).derived.obj
        ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op K, L))) ⟶
      (derivedInternalHomOfUniverses.{c, v, r, w} J R).obj
        (op K, (scalarDerivedRestriction a).obj ((M.scalar a).derived.obj L)) :=
  (scalarDerivedRestriction a).map (comparison M μ a K L) ≫
    (α.iso a).hom.app (op K, (M.scalar a).derived.obj L)

/-- The exact-extension representative map, using the universal derived counit and
termwise restriction comparison. Its invertibility under exactness is asserted below.
Source: Stacks 06YY, 07A6 (blueprint: lem-sfb-hom-flat-evaluation-roof). -/
noncomputable def representative
    (ν : scalarTensor.{c, v, r} a ≅
      scalarComplex (M.scalar a).extension (M.scalar a).extension_additive ⋙
        (scalarRestriction a).mapHomologicalComplex (.up ℤ))
    (B : CochainComplex (scalarModules J R) ℤ) :
    (scalarDerivedRestriction a).obj ((M.scalar a).derived.obj (DerivedCategory.Q.obj B)) ⟶
      DerivedCategory.Q.obj ((scalarTensor.{c, v, r} a).obj B) :=
  (scalarDerivedRestriction a).map
      (scalarPairComplexComparison (M.scalar a).extension (M.scalar a).extension_additive
        (M.scalar a).derived (M.scalar a).counit B) ≫
    (scalarRestrictionComparison a).hom.app
      ((scalarComplex (M.scalar a).extension (M.scalar a).extension_additive).obj B) ≫
    DerivedCategory.Q.map (ν.inv.app B)

/-- The source identification U E^L H_R(QP,QC) to Q(S tensor Hom(P,I(C))).
Source: Stacks 0A95, 06YY (blueprint: lem-sfb-hom-flat-evaluation-roof). -/
noncomputable def sourceMap
    (ν : scalarTensor.{c, v, r} a ≅
      scalarComplex (M.scalar a).extension (M.scalar a).extension_additive ⋙
        (scalarRestriction a).mapHomologicalComplex (.up ℤ))
    (P L : CochainComplex (scalarModules J R) ℤ) :=
  (scalarDerivedRestriction a).map ((M.scalar a).derived.map
      (coefficientHomResolutionIso.{r, c, v, w} J R P L).hom) ≫
    representative M a ν ((homFixed.{c, v, r} J R P).obj L)

/-- The target identification H_R(QP,U E^L QC) to Q(Hom(P,I(S tensor C))).
Source: Stacks 0A95, 06YY (blueprint: lem-sfb-hom-flat-evaluation-roof). -/
noncomputable def targetMap
    (ν : scalarTensor.{c, v, r} a ≅
      scalarComplex (M.scalar a).extension (M.scalar a).extension_additive ⋙
        (scalarRestriction a).mapHomologicalComplex (.up ℤ))
    (P L : CochainComplex (scalarModules J R) ℤ) :=
  (derivedInternalHomOfUniverses.{c, v, r, w} J R).map
      (Prod.mkHom (𝟙 (op (DerivedCategory.Q.obj P))) (representative M a ν L)) ≫
    (coefficientHomResolutionIso.{r, c, v, w} J R P ((scalarTensor.{c, v, r} a).obj L)).hom

/-- The strict denominator v_S = Hom(P,I(S tensor eta_C)), without changing models.
Source: Stacks 0A95 (blueprint: lem-sfb-hom-flat-evaluation-roof). -/
noncomputable abbrev denominator
    (P L : CochainComplex (scalarModules J R) ℤ) :=
  roofDenominator.{c, v, r} J R P L
    ((scalarRestriction a).obj (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj S)))

/-- The strict numerator a_S is the component of the unique normalized comparison.
Source: Stacks 08J9, 03CZ (blueprint: lem-sfb-hom-flat-evaluation-roof). -/
noncomputable abbrev numerator
    (P L : CochainComplex (scalarModules J R) ℤ) :=
  (WeilConjectures.SfbHomFilteredColimit.comparison.{c, v, r} J R P L).app
    ((scalarRestriction a).obj (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj S)))

/-- Inverting precisely the localized denominator; the argument supplies only its proof
of being a quasi-isomorphism, with no choice of any map or object.
Source: Stacks 0A95 (blueprint: lem-sfb-hom-flat-evaluation-roof). -/
noncomputable def denominatorInverse
    (P L : CochainComplex (scalarModules J R) ℤ) (hv : QuasiIso (denominator.{c, v, r} a P L)) :=
  letI := hv
  inv (DerivedCategory.Q.map (denominator.{c, v, r} a P L))

/-- The full flat evaluation-roof assertion, simultaneously for every coefficient map.
The natural isomorphism nu is fixed by its actual pure-tensor formula. The remaining
fields are propositions about the recorded models and explicitly defined maps.
Coefficient composition includes identity maps and, by the two paths in a commutative
square, arbitrary compatible coefficient maps.
Source: Stacks 08J9, 0A95, 03CZ and the node's evaluation-roof refinement
(blueprint: lem-sfb-hom-flat-evaluation-roof). -/
structure EvaluationRoof where
  /-- The canonical tensor/restricted-extension identification, before localization. -/
  tensorIso : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S),
    scalarTensor.{c, v, r} a ≅
      scalarComplex (M.scalar a).extension (M.scalar a).extension_additive ⋙
        (scalarRestriction a).mapHomologicalComplex (.up ℤ)
  /-- On actual sheafified generators, nu sends s tensor x to s tensor x. -/
  tensorIso_normalized : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)
    (B : CochainComplex (scalarModules J R) ℤ) (n : ℤ) (V : Cᵒᵖ)
    (s : S.obj.obj V) (x : (B.X n).val.obj V),
    (((tensorIso a).hom.app B).f n).val.app V
        (tensorGenerator.{c, v, r} J R _ B n V s x) =
      ((eqToHom ((M.scalar a).extension_obj (B.X n)).symm).val.app V)
        ((toSheafify J (changeOfRingsPresheaf a (B.X n)).presheaf).app V
          (s ⊗ₜ[R.obj.obj V, (a.hom.app V).hom] x))
  /-- Exact ordinary extension computes derived extension on every complex. -/
  exact_computes : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S),
    PreservesFiniteLimits (M.scalar a).extension →
    ∀ B : CochainComplex (scalarModules J R) ℤ,
      IsIso (scalarPairComplexComparison (M.scalar a).extension (M.scalar a).extension_additive
        (M.scalar a).derived (M.scalar a).counit B)
  /-- No boundedness or continuity is needed for the strict denominator. -/
  denominator_quasiIso : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S),
    PreservesFiniteLimits (M.scalar a).extension →
    ∀ (P L : CochainComplex (scalarModules J R) ℤ),
      CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P →
      (∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (P.X n)) →
      QuasiIso (denominator.{c, v, r} a P L)
  /-- The equation [v_S] Theta U(c) = [a_S], with both representative transports. -/
  equation : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S),
    PreservesFiniteLimits (M.scalar a).extension →
    ∀ (P L : CochainComplex (scalarModules J R) ℤ),
      CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P →
      (∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (P.X n)) →
      restrictedComparison M μ α a (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj L) ≫
          targetMap M a (tensorIso a) P L ≫ DerivedCategory.Q.map (denominator.{c, v, r} a P L) =
        sourceMap M a (tensorIso a) P L ≫ DerivedCategory.Q.map (numerator.{c, v, r} a P L)
  /-- Equivalently Theta U(c) is the numerator followed by the inverse denominator. -/
  roof : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S),
    PreservesFiniteLimits (M.scalar a).extension →
    ∀ (P L : CochainComplex (scalarModules J R) ℤ),
      CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P →
      (∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (P.X n)) →
      ∀ hv : QuasiIso (denominator.{c, v, r} a P L),
        restrictedComparison M μ α a (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj L) ≫
            targetMap M a (tensorIso a) P L =
          sourceMap M a (tensorIso a) P L ≫ DerivedCategory.Q.map (numerator.{c, v, r} a P L) ≫
            denominatorInverse.{c, v, r, w} a P L hv
  /-- Naturality in both derived inputs, including maps represented by inverse quasi-isos. -/
  naturality : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)
    (K K' L L' : DerivedCategory (scalarModules J R)) (f : K' ⟶ K) (g : L ⟶ L'),
    (scalarDerivedRestriction a).map ((M.scalar a).derived.map
        ((derivedInternalHomOfUniverses.{c, v, r, w} J R).map (Prod.mkHom f.op g))) ≫
        restrictedComparison M μ α a K' L' =
      restrictedComparison M μ α a K L ≫
        (derivedInternalHomOfUniverses.{c, v, r, w} J R).map
          (Prod.mkHom f.op ((scalarDerivedRestriction a).map ((M.scalar a).derived.map g)))
  /-- Coefficient compatibility, with the unit-normalized scalar composition transports. -/
  coefficients : ∀ {R S T : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S) (b : S ⟶ T)
    (K L : DerivedCategory (scalarModules J R)),
    comparison M μ (a ≫ b) K L =
      (scalarHomExtensionComp M a b).inv.app
          ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op K, L)) ≫
        (M.scalar b).derived.map (comparison M μ a K L) ≫
          comparison M μ b ((M.scalar a).derived.obj K) ((M.scalar a).derived.obj L) ≫
            (derivedInternalHomOfUniverses.{c, v, r, w} J T).map
              (Prod.mkHom ((scalarHomExtensionComp M a b).inv.app K).op
                ((scalarHomExtensionComp M a b).hom.app L))
```

## New

In the same surrounding namespace and variables:

```lean
/-- The already recorded strict tensor functor with the restricted regular S-module.
This abbreviation uses restriction of scalars and the actual single-zero total tensor.
Source: Stacks 03CZ, 06YN (blueprint: lem-sfb-hom-flat-evaluation-roof). -/
noncomputable def scalarTensor {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S) :
    CochainComplex (scalarModules J R) ℤ ⥤ CochainComplex (scalarModules J R) ℤ :=
  Prod.sectR ((scalarRestriction a).obj (SheafOfModules.unit
    ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj S)))
    (CochainComplex (scalarModules J R) ℤ) ⋙ tensor.{c, v, r} J R

variable (M : ScalarHomModels.{c, v, r, w} J)
  (μ : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S),
    ScalarHomTensorComparison M a)
  (α : ScalarInternalHomAdjunction M μ)
  {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)

/-- The fixed strict tensor comparison type, shared without changing its functors.
(blueprint: lem-sfb-hom-flat-evaluation-roof). -/
abbrev ScalarTensorIdentification :=
  scalarTensor.{c, v, r} a ≅
    scalarComplex (M.scalar a).extension (M.scalar a).extension_additive ⋙
      (scalarRestriction a).mapHomologicalComplex (.up ℤ)

/-- The family of the fixed strict tensor comparisons.
(blueprint: lem-sfb-hom-flat-evaluation-roof). -/
abbrev ScalarTensorComparisons :=
  ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S),
    ScalarTensorIdentification M a

/-- The canonical map c is the transpose of scalar-extended evaluation, with the
inverse strong tensor comparison in front of it. It is defined for all derived inputs.
Source: Stacks 08J9, 07A4 (blueprint: lem-sfb-hom-flat-evaluation-roof). -/
noncomputable def comparison (K L : DerivedCategory (scalarModules J R)) :
    (M.scalar a).derived.obj
        ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op K, L)) ⟶
      (derivedInternalHomOfUniverses.{c, v, r, w} J S).obj
        (op ((M.scalar a).derived.obj K), (M.scalar a).derived.obj L) :=
  (M.closed S).transpose _ _ _
    ((μ a).iso.inv.app
        ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op K, L), K) ≫
      (M.scalar a).derived.map ((M.closed R).evaluation K L))

/-- The precise map Theta U(c), using the recorded normalized scalar adjunction.
Source: Stacks 08J9, 03CZ (blueprint: lem-sfb-hom-flat-evaluation-roof). -/
noncomputable def restrictedComparison (K L : DerivedCategory (scalarModules J R)) :
    (scalarDerivedRestriction a).obj ((M.scalar a).derived.obj
        ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op K, L))) ⟶
      (derivedInternalHomOfUniverses.{c, v, r, w} J R).obj
        (op K, (scalarDerivedRestriction a).obj ((M.scalar a).derived.obj L)) :=
  (scalarDerivedRestriction a).map (comparison M μ a K L) ≫
    (α.iso a).hom.app (op K, (M.scalar a).derived.obj L)

/-- The exact-extension representative map, using the universal derived counit and
termwise restriction comparison. Its invertibility under exactness is asserted below.
Source: Stacks 06YY, 07A6 (blueprint: lem-sfb-hom-flat-evaluation-roof). -/
noncomputable def representative
    (ν : ScalarTensorIdentification M a)
    (B : CochainComplex (scalarModules J R) ℤ) :
    (scalarDerivedRestriction a).obj ((M.scalar a).derived.obj (DerivedCategory.Q.obj B)) ⟶
      DerivedCategory.Q.obj ((scalarTensor.{c, v, r} a).obj B) :=
  (scalarDerivedRestriction a).map
      (scalarPairComplexComparison (M.scalar a).extension (M.scalar a).extension_additive
        (M.scalar a).derived (M.scalar a).counit B) ≫
    (scalarRestrictionComparison a).hom.app
      ((scalarComplex (M.scalar a).extension (M.scalar a).extension_additive).obj B) ≫
    DerivedCategory.Q.map (ν.inv.app B)

/-- The source identification U E^L H_R(QP,QC) to Q(S tensor Hom(P,I(C))).
Source: Stacks 0A95, 06YY (blueprint: lem-sfb-hom-flat-evaluation-roof). -/
noncomputable def sourceMap
    (ν : ScalarTensorIdentification M a)
    (P L : CochainComplex (scalarModules J R) ℤ) :
    (scalarDerivedRestriction a).obj ((M.scalar a).derived.obj
      ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj
        (op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj L))) ⟶
      DerivedCategory.Q.obj ((scalarTensor.{c, v, r} a).obj
        ((homFixed.{c, v, r} J R P).obj L)) :=
  (scalarDerivedRestriction a).map ((M.scalar a).derived.map
      (coefficientHomResolutionIso.{r, c, v, w} J R P L).hom) ≫
    representative M a ν ((homFixed.{c, v, r} J R P).obj L)

/-- The target identification H_R(QP,U E^L QC) to Q(Hom(P,I(S tensor C))).
Source: Stacks 0A95, 06YY (blueprint: lem-sfb-hom-flat-evaluation-roof). -/
noncomputable def targetMap
    (ν : ScalarTensorIdentification M a)
    (P L : CochainComplex (scalarModules J R) ℤ) :
    (derivedInternalHomOfUniverses.{c, v, r, w} J R).obj
      (op (DerivedCategory.Q.obj P),
        (scalarDerivedRestriction a).obj ((M.scalar a).derived.obj (DerivedCategory.Q.obj L))) ⟶
      DerivedCategory.Q.obj ((homFixed.{c, v, r} J R P).obj
        ((scalarTensor.{c, v, r} a).obj L)) :=
  (derivedInternalHomOfUniverses.{c, v, r, w} J R).map
      (Prod.mkHom (𝟙 (op (DerivedCategory.Q.obj P))) (representative M a ν L)) ≫
    (coefficientHomResolutionIso.{r, c, v, w} J R P ((scalarTensor.{c, v, r} a).obj L)).hom

/-- The strict denominator v_S = Hom(P,I(S tensor eta_C)), without changing models.
Source: Stacks 0A95 (blueprint: lem-sfb-hom-flat-evaluation-roof). -/
noncomputable def denominator
    (P L : CochainComplex (scalarModules J R) ℤ) :
    (homFixed.{c, v, r} J R P).obj ((scalarTensor.{c, v, r} a).obj L) ⟶
      (homFixed.{c, v, r} J R P).obj ((scalarTensor.{c, v, r} a).obj
        ((coefficientHomResolution.{r, c, v} J R).obj L)) :=
  roofDenominator.{c, v, r} J R P L
    ((scalarRestriction a).obj (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj S)))

/-- The strict numerator a_S is the component of the unique normalized comparison.
Source: Stacks 08J9, 03CZ (blueprint: lem-sfb-hom-flat-evaluation-roof). -/
noncomputable def numerator
    (P L : CochainComplex (scalarModules J R) ℤ) :
    (scalarTensor.{c, v, r} a).obj ((homFixed.{c, v, r} J R P).obj L) ⟶
      (homFixed.{c, v, r} J R P).obj ((scalarTensor.{c, v, r} a).obj
        ((coefficientHomResolution.{r, c, v} J R).obj L)) :=
  (WeilConjectures.SfbHomFilteredColimit.comparison.{c, v, r} J R P L).app
    ((scalarRestriction a).obj (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj S)))

/-- Inverting precisely the localized denominator; the argument supplies only its proof
of being a quasi-isomorphism, with no choice of any map or object.
Source: Stacks 0A95 (blueprint: lem-sfb-hom-flat-evaluation-roof). -/
noncomputable def denominatorInverse
    (P L : CochainComplex (scalarModules J R) ℤ) (hv : QuasiIso (denominator.{c, v, r} a P L)) :
    DerivedCategory.Q.obj ((homFixed.{c, v, r} J R P).obj
      ((scalarTensor.{c, v, r} a).obj ((coefficientHomResolution.{r, c, v} J R).obj L))) ⟶
    DerivedCategory.Q.obj ((homFixed.{c, v, r} J R P).obj
      ((scalarTensor.{c, v, r} a).obj L)) :=
  letI := hv
  inv (DerivedCategory.Q.map (denominator.{c, v, r} a P L))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The unchanged `tensorIso_normalized` condition, shared by the roof declarations.
(blueprint: lem-sfb-hom-flat-evaluation-roof). -/
def RoofTensorNormalized (ν : ScalarTensorComparisons M) : Prop :=
  ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)
  (B : CochainComplex (scalarModules J R) ℤ) (n : ℤ) (V : Cᵒᵖ)
  (s : S.obj.obj V) (x : (B.X n).val.obj V),
  (((ν a).hom.app B).f n).val.app V
      (tensorGenerator.{c, v, r} J R _ B n V s x) =
    ((eqToHom ((M.scalar a).extension_obj (B.X n)).symm).val.app V)
      ((toSheafify J (changeOfRingsPresheaf a (B.X n)).presheaf).app V
        (s ⊗ₜ[R.obj.obj V, (a.hom.app V).hom] x))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The unchanged `exact_computes` condition, shared by the roof declarations.
(blueprint: lem-sfb-hom-flat-evaluation-roof). -/
def RoofExactComputes : Prop :=
  ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S),
  PreservesFiniteLimits (M.scalar a).extension →
  ∀ B : CochainComplex (scalarModules J R) ℤ,
    IsIso (scalarPairComplexComparison (M.scalar a).extension (M.scalar a).extension_additive
      (M.scalar a).derived (M.scalar a).counit B)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The unchanged `denominator_quasiIso` condition, shared by the roof declarations.
(blueprint: lem-sfb-hom-flat-evaluation-roof). -/
def RoofDenominatorQuasiIso : Prop :=
  ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S),
  PreservesFiniteLimits (M.scalar a).extension →
  ∀ (P L : CochainComplex (scalarModules J R) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P →
    (∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (P.X n)) →
    QuasiIso (denominator.{c, v, r} a P L)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The unchanged `equation` condition, shared by the roof declarations.
(blueprint: lem-sfb-hom-flat-evaluation-roof). -/
def RoofEquation (ν : ScalarTensorComparisons M) : Prop :=
  ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S),
  PreservesFiniteLimits (M.scalar a).extension →
  ∀ (P L : CochainComplex (scalarModules J R) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P →
    (∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (P.X n)) →
    restrictedComparison M μ α a (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj L) ≫
        targetMap M a (ν a) P L ≫ DerivedCategory.Q.map (denominator.{c, v, r} a P L) =
      sourceMap M a (ν a) P L ≫ DerivedCategory.Q.map (numerator.{c, v, r} a P L)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The unchanged `roof` condition, shared by the roof declarations.
(blueprint: lem-sfb-hom-flat-evaluation-roof). -/
def RoofFormula (ν : ScalarTensorComparisons M) : Prop :=
  ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S),
  PreservesFiniteLimits (M.scalar a).extension →
  ∀ (P L : CochainComplex (scalarModules J R) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P →
    (∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (P.X n)) →
    ∀ hv : QuasiIso (denominator.{c, v, r} a P L),
      restrictedComparison M μ α a (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj L) ≫
          targetMap M a (ν a) P L =
        sourceMap M a (ν a) P L ≫ DerivedCategory.Q.map (numerator.{c, v, r} a P L) ≫
          denominatorInverse.{c, v, r, w} a P L hv

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The unchanged `naturality` condition, shared by the roof declarations.
(blueprint: lem-sfb-hom-flat-evaluation-roof). -/
def RoofNaturality : Prop :=
  ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)
  (K K' L L' : DerivedCategory (scalarModules J R)) (f : K' ⟶ K) (g : L ⟶ L'),
  (scalarDerivedRestriction a).map ((M.scalar a).derived.map
      ((derivedInternalHomOfUniverses.{c, v, r, w} J R).map (Prod.mkHom f.op g))) ≫
      restrictedComparison M μ α a K' L' =
    restrictedComparison M μ α a K L ≫
      (derivedInternalHomOfUniverses.{c, v, r, w} J R).map
        (Prod.mkHom f.op ((scalarDerivedRestriction a).map ((M.scalar a).derived.map g)))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The unchanged `coefficients` condition, shared by the roof declarations.
(blueprint: lem-sfb-hom-flat-evaluation-roof). -/
def RoofCoefficients : Prop :=
  ∀ {R S T : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S) (b : S ⟶ T)
  (K L : DerivedCategory (scalarModules J R)),
  comparison M μ (a ≫ b) K L =
    (scalarHomExtensionComp M a b).inv.app
        ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op K, L)) ≫
      (M.scalar b).derived.map (comparison M μ a K L) ≫
        comparison M μ b ((M.scalar a).derived.obj K) ((M.scalar a).derived.obj L) ≫
          (derivedInternalHomOfUniverses.{c, v, r, w} J T).map
            (Prod.mkHom ((scalarHomExtensionComp M a b).inv.app K).op
              ((scalarHomExtensionComp M a b).hom.app L))

section RoofStructure

attribute [local irreducible] RoofTensorNormalized RoofExactComputes
  RoofDenominatorQuasiIso RoofEquation RoofFormula RoofNaturality RoofCoefficients

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The full flat evaluation-roof assertion, simultaneously for every coefficient map.
The natural isomorphism nu is fixed by its actual pure-tensor formula. The remaining
fields are propositions about the recorded models and explicitly defined maps.
Coefficient composition includes identity maps and, by the two paths in a commutative
square, arbitrary compatible coefficient maps.
Source: Stacks 08J9, 0A95, 03CZ and the node's evaluation-roof refinement
(blueprint: lem-sfb-hom-flat-evaluation-roof). -/
structure EvaluationRoof where
  /-- The canonical tensor/restricted-extension identification, before localization. -/
  tensorIso : ScalarTensorComparisons M
  /-- On actual sheafified generators, nu sends s tensor x to s tensor x. -/
  tensorIso_normalized : RoofTensorNormalized M tensorIso
  /-- Exact ordinary extension computes derived extension on every complex. -/
  exact_computes : RoofExactComputes M
  /-- No boundedness or continuity is needed for the strict denominator. -/
  denominator_quasiIso : RoofDenominatorQuasiIso M
  /-- The equation [v_S] Theta U(c) = [a_S], with both representative transports. -/
  equation : RoofEquation M μ α tensorIso
  /-- Equivalently Theta U(c) is the numerator followed by the inverse denominator. -/
  roof : RoofFormula M μ α tensorIso
  /-- Naturality in both derived inputs, including maps represented by inverse quasi-isos. -/
  naturality : RoofNaturality M μ α
  /-- Coefficient compatibility, with the unit-normalized scalar composition transports. -/
  coefficients : RoofCoefficients M μ

end RoofStructure
```


The private proof tests triple tensors through sheafification's universal property and
reuses the existing proved resolution-comparison naturality helper. Opacity for the
section formulas starts after their normalization proof. No additional public statement
or consumer adaptation is introduced by these proof changes.

## Users

`tools/downstream.py` lists one downstream module. Textual use searches for all
changed declarations find only the item itself, and `EvaluationRoof` in that
consumer. The consumer uses the type in a `Nonempty` assertion; it does not unfold
its fields or any changed map definition. No source adaptation is necessary.
The temporary interface check compares every named condition with the original
field expression by reflexivity. Its independent `lcompile.py` check passed for
all seven predicates. A full `lcompile.py --all` run then compiled the item
(54.5 s), the interface check (7.7 s), and the unchanged consumer (39.7 s).
Both temporary check files were removed from the packet before delivery.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Algebra.Homology.FlatInternalHomEvaluationRoof` | J2 | Original constructions and field conditions; complete private proofs use the named API. |
| `Sheaf.Paper.QlbarInternalHomCoefficientComparison` | unclaimed at inspection | Same `EvaluationRoof` and `comparison` uses; no source changes. |

## Status

landed 20261022T013420-L-3569107 2026-10-22 (merge of deliver/J2/Sheaf.Algebra.Homology.FlatInternalHomEvaluationRoof)
