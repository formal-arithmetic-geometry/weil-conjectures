# WeilConjectures.RamifiedPullback tower interfaces

## Reason

The coefficient comparison and the geometric pullback comparison are separate source
lemmas. They need the existing interfaces without importing the theorem that combines
them. Move the declarations verbatim into RamifiedPullbackTowerData and publicly import
that module from the original item. No definition, signature, visibility, or target meaning changes.

## Old

In lean/Sheaf/Paper/RamifiedPullbackTowerIdentification.lean:

```lean
/-- The existing ring-sheaf forgetful operation at the actual site sizes.
Source: Stacks 03EK (blueprint: lem-weil-ramified-pullback-tower-identification). -/
abbrev ring {W : Scheme.{t}} (R : Sheaf (Scheme.ProEt.topology W)
    CommRingCat.{max u (t + 1)}) :=
  (sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R

/-- Module sheaves in the common coefficient universe; the site is unchanged.
Source: Stacks 03EK (blueprint: lem-weil-ramified-pullback-tower-identification). -/
abbrev Mod {W : Scheme.{t}} (R : Sheaf (Scheme.ProEt.topology W)
    CommRingCat.{max u (t + 1)}) := SheafOfModules.{max u (t + 1)} (ring.{t, u} R)

set_option linter.defProp false in
/-- The existing canonical tensor witness, with standard derived localizations.
Only its ordinary functor is used here.
Source: Stacks 03EK (blueprint: lem-weil-ramified-pullback-tower-identification). -/
def scalarWitness {W : Scheme.{t}}
    {R S : Sheaf (Scheme.ProEt.topology W) CommRingCat.{max u (t + 1)}} (c : R ⟶ S) :=
  letI := HasDerivedCategory.standard (Mod.{t, u} R)
  letI := HasDerivedCategory.standard (Mod.{t, u} S)
  SheafOfModules.derivedChangeOfRingsIndependentCoefficients.{_, max u (t + 1), t + 1, t} c

/-- Ordinary scalar extension, with exactly the existing tensor objects and maps.
Source: Stacks 03EK (blueprint: lem-weil-ramified-pullback-tower-identification). -/
def scalar {W : Scheme.{t}}
    {R S : Sheaf (Scheme.ProEt.topology W) CommRingCat.{max u (t + 1)}} (c : R ⟶ S) :
    Mod.{t, u} R ⥤ Mod.{t, u} S := (scalarWitness.{t, u} c).choose

/-- Additivity from the existing tensor witness.
Source: Stacks 03EK (blueprint: lem-weil-ramified-pullback-tower-identification). -/
instance scalar_additive {W : Scheme.{t}}
    {R S : Sheaf (Scheme.ProEt.topology W) CommRingCat.{max u (t + 1)}} (c : R ⟶ S) :
    (scalar.{t, u} c).Additive :=
  (scalarWitness.{t, u} c).choose_spec.choose_spec.choose_spec.choose

/-- Termwise ordinary scalar extension on all cochain complexes.
Source: Stacks 03EK (blueprint: lem-weil-ramified-pullback-tower-identification). -/
abbrev scalarCx {W : Scheme.{t}}
    {R S : Sheaf (Scheme.ProEt.topology W) CommRingCat.{max u (t + 1)}} (c : R ⟶ S) :=
  (scalar.{t, u} c).mapHomologicalComplex (.up ℤ)

/-- The local tensor s⊗x, with the target scalar written first as in Mathlib.
Source: Stacks 03EK (blueprint: lem-weil-ramified-pullback-tower-identification). -/
def tensor {W : Scheme.{t}}
    {R S : Sheaf (Scheme.ProEt.topology W) CommRingCat.{max u (t + 1)}} (c : R ⟶ S)
    (M : Mod.{t, u} R) (U : W.ProEtᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    ((scalar.{t, u} c).obj M).val.obj U :=
  (eqToHom ((scalarWitness.{t, u} c).choose_spec.choose M).symm).val.app U
    ((toSheafify (Scheme.ProEt.topology W)
      (SheafOfModules.changeOfRingsPresheaf.{t, t + 1, max u (t + 1)} c M).presheaf).app U
        (s ⊗ₜ[R.obj.obj U, (c.hom.app U).hom] x))

/-- Constant sheafification of a quotient coefficient homomorphism.
Source: Stacks 03EK (blueprint: lem-weil-ramified-pullback-tower-identification). -/
def constantMap (W : Scheme.{t}) {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) :
    (constantSheaf (Scheme.ProEt.topology W) CommRingCat.{max u (t + 1)}).obj
        (CommRingCat.of (ULift.{t + 1} A)) ⟶
      (constantSheaf (Scheme.ProEt.topology W) CommRingCat.{max u (t + 1)}).obj
        (CommRingCat.of (ULift.{t + 1} B)) :=
  (constantSheaf (Scheme.ProEt.topology W) CommRingCat.{max u (t + 1)}).map
    (CommRingCat.ofHom ((ULift.ringEquiv : ULift.{t + 1} B ≃+* B).symm.toRingHom.comp
      (f.comp (ULift.ringEquiv : ULift.{t + 1} A ≃+* A).toRingHom)))

/-- The zero-based index of the e-subsequence.
Source: Stacks 03EK (blueprint: lem-weil-ramified-pullback-tower-identification). -/
def index (e n : ℕ) : ℕ := e * (n + 1) - 1

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- A finite coefficient sheaf as a module over its actual completed ring.
Source: Stacks 093M (blueprint: lem-weil-ramified-pullback-tower-identification). -/
abbrev coefficientModule (W : Scheme.{t}) (n : ℕ) :
    integralTowerModules l E W :=
  (SheafOfModules.restrictScalars
    ((sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
      (completedIntegralCommRingProjectionUnrestricted l E W n))).obj
        (SheafOfModules.unit (ring (integralCoefficientCommRingSheaf l E W n)))

/-- Composite transition in the specified pullback tower, including equal indices.
Source: Stacks 03EK (blueprint: lem-weil-ramified-pullback-tower-identification). -/
def transition {X Y : Scheme.{t}} (g : X ⟶ Y) (a b : ℕ) (h : a ≤ b)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :
    (integralOperationsPullbackLevel l E g b).obj P ⟶
      (integralOperationsPullbackLevel l E g a).obj P :=
  ((integralOperationsPullbackTowerFunctor l E g).obj P).map (homOfLE h).op

/-- The local section ((g⁻¹(p⊗a))⊗b), using the actual pullback adjunction unit.
Source: Stacks 03EL (blueprint: lem-weil-ramified-pullback-tower-identification). -/
def pullTensor {X Y : Scheme.{t}} (g : X ⟶ Y) (n : ℕ)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) (i : ℤ) (V : Y.ProEt)
    (a : (integralCoefficientCommRingSheaf l E Y n).obj.obj (op V))
    (b : (integralCoefficientCommRingSheaf l E X n).obj.obj
      (op ((Scheme.proEtaleBaseChange g).obj V))) (p : (P.X i).val.obj (op V)) :
    (((integralOperationsPullbackLevel l E g n).obj P).X i).val.obj
      (op ((Scheme.proEtaleBaseChange g).obj V)) :=
  b • @id (((integralOperationsLevelPullback l E g n).obj
      (((unrestrictedIntegralFiniteComplex l E Y n).obj P).X i)).val.obj
        (op ((Scheme.proEtaleBaseChange g).obj V)))
    (integralOperationsPullbackGenerator l E g n
      (((unrestrictedIntegralFiniteComplex l E Y n).obj P).X i) V
        (unrestrictedIntegralTensorSection l E Y n (P.X i) (op V) a p))

variable (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- The ramified quotient map on the already recorded coefficient sheaves.
Source: Stacks 03EK (blueprint: lem-weil-ramified-pullback-tower-identification). -/
def ramifiedMap (W : Scheme.{t}) (e n : ℕ)
    (j : Padic.coefficientExtensionRing l E (n + 1) →+*
      Padic.coefficientExtensionRing l L (index e n + 1)) :
    integralCoefficientCommRingSheaf l E W n ⟶
      integralCoefficientCommRingSheaf l L W (index e n) := constantMap W j

/-- Normalized coefficient identification on one of the two small pro-etale sites.
The maps are fixed by inclusion, the actual completed projections, and pure tensors.
Source: Stacks 093M and 03EK
(blueprint: lem-weil-ramified-pullback-tower-identification). -/
structure Coefficients (e : ℕ)
    (j : ∀ n : ℕ, Padic.coefficientExtensionRing l E (n + 1) →+*
      Padic.coefficientExtensionRing l L (index e n + 1)) (W : Scheme.{t}) where
  completedMap : completedIntegralCommRingSheafUnrestricted l E W ⟶
    completedIntegralCommRingSheafUnrestricted l L W
  projection : ∀ n : ℕ,
    completedMap ≫ completedIntegralCommRingProjectionUnrestricted l L W n =
      integralScalarRho l E L ι W n
  ramified_projection : ∀ n : ℕ,
    completedMap ≫ completedIntegralCommRingProjectionUnrestricted l L W (index e n) =
      completedIntegralCommRingProjectionUnrestricted l E W n ≫ ramifiedMap l E L W e n (j n)
  coefficientIso : ∀ n : ℕ,
    (scalar.{t, u} completedMap).obj (coefficientModule l E W n) ≅
      coefficientModule l L W (index e n)
  coefficient_formula : ∀ (n : ℕ) (U : W.ProEtᵒᵖ)
    (a : (integralCoefficientCommRingSheaf l E W n).obj.obj U)
    (s : (completedIntegralCommRingSheafUnrestricted l L W).obj.obj U),
    (coefficientIso n).hom.val.app U
      (tensor completedMap (coefficientModule l E W n) U s a) =
        (ramifiedMap l E L W e n (j n)).hom.app U a *
          (completedIntegralCommRingProjectionUnrestricted l L W (index e n)).hom.app U s
  coefficient_transitions : ∀ (a b : ℕ) (h : a ≤ b) (h' : index e a ≤ index e b)
    (U : W.ProEtᵒᵖ)
    (x : (integralCoefficientCommRingSheaf l E W b).obj.obj U)
    (s : (completedIntegralCommRingSheafUnrestricted l L W).obj.obj U),
    (coefficientIso a).hom.val.app U
      (tensor completedMap (coefficientModule l E W a) U s
        ((((integralCoefficientSheafSystem l E W).map (homOfLE h).op).hom.app U) x)) =
      (((integralCoefficientSheafSystem l L W).map (homOfLE h').op).hom.app U)
        ((coefficientIso b).hom.val.app U
          (tensor completedMap (coefficientModule l E W b) U s x))

/-- The entire ramified identification, including its specified same-index map.
No auxiliary unit occurs in these data; all maps have their normalized formulas.
Source: Stacks 093M, 03EK and 03EL; Bhatt--Scholze 6.8.2(1)
(blueprint: lem-weil-ramified-pullback-tower-identification). -/
structure Identification {X Y : Scheme.{t}} (g : X ⟶ Y) where
  e : ℕ
  positive : 1 ≤ e
  ideal : Ideal.span ({integralScalarIntegerInclusion l E L ι
    (Padic.coefficientExtensionUniformizer l E)} : Set (Padic.coefficientExtensionIntegers l L)) =
      Ideal.span {Padic.coefficientExtensionUniformizer l L ^ e}
  unique_index : ∀ k : ℕ, 1 ≤ k →
    Ideal.span ({integralScalarIntegerInclusion l E L ι
      (Padic.coefficientExtensionUniformizer l E)} :
        Set (Padic.coefficientExtensionIntegers l L)) =
      Ideal.span {Padic.coefficientExtensionUniformizer l L ^ k} → k = e
  exponent : ∀ n : ℕ, index e n + 1 = e * (n + 1)
  monotone : Monotone (index e)
  same_le : ∀ n : ℕ, n ≤ index e n
  quotientMap : ∀ n : ℕ, Padic.coefficientExtensionRing l E (n + 1) →+*
    Padic.coefficientExtensionRing l L (index e n + 1)
  quotient_formula : ∀ (n : ℕ) (a : Padic.coefficientExtensionIntegers l E),
    quotientMap n (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) a) =
      Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l L (index e n + 1))
        (integralScalarIntegerInclusion l E L ι a)
  source : Coefficients l E L ι e quotientMap Y
  target : Coefficients l E L ι e quotientMap X
  levelIso : ∀ n : ℕ,
    integralOperationsPullbackLevel l E g n ⋙ scalarCx.{t, u} target.completedMap ≅
      scalarCx.{t, u} source.completedMap ⋙
        integralOperationsPullbackLevel l L g (index e n)
  pullback_formula : ∀ (n : ℕ) (P : CochainComplex (integralTowerModules l E Y) ℤ)
    (i : ℤ) (V : Y.ProEt)
    (a : (integralCoefficientCommRingSheaf l E Y n).obj.obj (op V))
    (b : (integralCoefficientCommRingSheaf l E X n).obj.obj
      (op ((Scheme.proEtaleBaseChange g).obj V)))
    (s : (completedIntegralCommRingSheafUnrestricted l L X).obj.obj
      (op ((Scheme.proEtaleBaseChange g).obj V))) (p : (P.X i).val.obj (op V)),
    (((levelIso n).hom.app P).f i).val.app _
      (tensor target.completedMap (((integralOperationsPullbackLevel l E g n).obj P).X i)
        _ s (pullTensor l E g n P i V a b p)) =
      pullTensor l L g (index e n) ((scalarCx.{t, u} source.completedMap).obj P) i V
        ((ramifiedMap l E L Y e n (quotientMap n)).hom.app (op V) a)
        ((ramifiedMap l E L X e n (quotientMap n)).hom.app _ b *
          (completedIntegralCommRingProjectionUnrestricted l L X (index e n)).hom.app _ s)
        (tensor source.completedMap (P.X i) (op V) 1 p)
  transitions : ∀ (n : ℕ) (P : CochainComplex (integralTowerModules l E Y) ℤ),
    (scalarCx.{t, u} target.completedMap).map
        ((integralOperationsPullbackTransition l E g n).app P) ≫
          (levelIso n).hom.app P =
      (levelIso (n + 1)).hom.app P ≫
        transition l L g (index e n) (index e (n + 1)) (monotone (Nat.le_succ n))
          ((scalarCx.{t, u} source.completedMap).obj P)
  sameIndex : ∀ n : ℕ,
    integralOperationsPullbackLevel l E g n ⋙ scalarCx.{t, u} target.completedMap ⟶
      scalarCx.{t, u} source.completedMap ⋙ integralOperationsPullbackLevel l L g n
  same_formula : ∀ (n : ℕ) (P : CochainComplex (integralTowerModules l E Y) ℤ)
    (i : ℤ) (V : Y.ProEt)
    (a : (integralCoefficientCommRingSheaf l E Y n).obj.obj (op V))
    (b : (integralCoefficientCommRingSheaf l E X n).obj.obj
      (op ((Scheme.proEtaleBaseChange g).obj V)))
    (s : (completedIntegralCommRingSheafUnrestricted l L X).obj.obj
      (op ((Scheme.proEtaleBaseChange g).obj V))) (p : (P.X i).val.obj (op V)),
    (((sameIndex n).app P).f i).val.app _
      (tensor target.completedMap (((integralOperationsPullbackLevel l E g n).obj P).X i)
        _ s (pullTensor l E g n P i V a b p)) =
      pullTensor l L g n ((scalarCx.{t, u} source.completedMap).obj P) i V
        ((integralScalarQuotientSheafMap l E L ι Y n).hom.app (op V) a)
        ((integralScalarQuotientSheafMap l E L ι X n).hom.app _ b *
          (completedIntegralCommRingProjectionUnrestricted l L X n).hom.app _ s)
        (tensor source.completedMap (P.X i) (op V) 1 p)
  factorization : ∀ (n : ℕ) (P : CochainComplex (integralTowerModules l E Y) ℤ),
    (sameIndex n).app P = (levelIso n).hom.app P ≫
      transition l L g n (index e n) (same_le n)
        ((scalarCx.{t, u} source.completedMap).obj P)
```

## New

The exact block above now lives in lean/Sheaf/Paper/RamifiedPullbackTowerData.lean.
The original item publicly imports Sheaf.Paper.RamifiedPullbackTowerData.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.RamifiedPullbackTowerIdentification | H3 | Same declarations re-exported; proof assembled from separate coefficient and geometric lemmas. |

The required downstream.py --uses check reports zero downstream modules for the item
and only the item itself using Identification. A repository-wide search finds no other
RamifiedPullback namespace consumers. Existing DAG parents retain their dependency on
the original item, which is preserved. No forced adaptation and no target statement change.

## Status

landed 20261021T174242-L-3772858 2026-10-21 (merge of deliver/H3/Sheaf.Paper.RamifiedPullbackTowerIdentification)
