# AlgebraicGeometry.ProEtale.siteHomTensorParameterShift and site Hom assertion reduction controls

## Reason

The native signed exactness intermediate must use the existing canonical source shifts.
Keeping their definitions in the item module would create a circular import. Move the
three construction bodies verbatim to the new lower module
`Sheaf.CategoryTheory.NativeDerivedHomSignedExact`, and publicly import that module
from the original module. No construction, signature, visibility or normalization changes. The reduction controls
listed below bound expansion without changing any object.
This is an interface relocation, not a mathematical statement change.

## Old

In `Sheaf.AlgebraicGeometry.SiteHomComparisonThick`:

```lean
section Shift
variable {D : Type d} [Category.{v} D] [Preadditive D] [HasShift D ℤ]
  [MonoidalCategory D] [MonoidalClosed D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [(curriedTensor D).CommShift₂Int]

/-- The existing tensor shift in its parameter, assembled as a natural isomorphism.
Source: Stacks 08JC, total-tensor signs
(blueprint: lem-sf-site-hom-comparison-thick). -/
def siteHomTensorParameterShift (K : D) (n : ℤ) :
    tensorLeft (K⟦n⟧) ≅ tensorLeft K ⋙ shiftFunctor D n :=
  NatIso.ofComponents (fun M ↦ (((curriedTensor D).flip.obj M).commShiftIso n).app K)
    (fun f ↦ (NatTrans.shift_app_comm ((curriedTensor D).flip.map f) n K).symm)

/-- The canonical source-Hom shift, as the right-adjoint mate of total-tensor shift.
This is the fixed-coefficient counterpart of the recorded ringed source shift, with
orientation H(K[n],-) → H(K,-)[-n]. Its opposite exact structure includes the correction
(-1)^(n(n+1)/2), prescribed below, rather than treating the raw shifts as coherent.
Source: Stacks 0A8X, 08JC (blueprint: lem-sf-site-hom-comparison-thick). -/
def siteHomSourceShift (K : D) (n : ℤ) :
    ihom (K⟦n⟧) ≅ ihom K ⋙ shiftFunctor D (-n) :=
  (ihom.adjunction (K⟦n⟧)).rightAdjointUniq
    (((shiftEquiv D n).toAdjunction.comp (ihom.adjunction K)).ofNatIsoLeft
      ((tensorLeft K).commShiftIso n ≪≫ (siteHomTensorParameterShift K n).symm))
/-- The same canonical source shift with the opposite-category integer parameter.
The equality transport records -(-n)=n explicitly. Source: Stacks 08JC
(blueprint: lem-sf-site-hom-comparison-thick). -/
def siteHomOppositeSourceShift (K : D) (n : ℤ) :
    ihom (K⟦-n⟧) ≅ ihom K ⋙ shiftFunctor D n :=
  siteHomSourceShift K (-n) ≪≫
    Functor.isoWhiskerLeft (ihom K) (eqToIso (congrArg (shiftFunctor D) (neg_neg n)))

end Shift
```

The additional existing definitions before their reduction attributes were added:

```lean
def siteHomExactThickAssertion
    {C : Type d} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [MonoidalCategory C] [MonoidalClosed C] [(curriedTensor C).CommShift₂Int]
    {D : Type e} [Category.{v} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    [MonoidalCategory D] [MonoidalClosed D] [(curriedTensor D).CommShift₂Int]
    (F : C ⥤ D) [F.CommShift ℤ]
    (b : ∀ K M : C, F.obj ((ihom K).obj M) ⟶ (ihom (F.obj K)).obj (F.obj M))
    (M : C) : Prop :=
  let B := MonoidalClosed.internalHom.flip.obj M ⋙ F
  let E := F.op ⋙ MonoidalClosed.internalHom.flip.obj (F.obj M)
  let P : ObjectProperty C := fun K ↦ IsIso (b K M)
  ∃ (sB : B.CommShift ℤ) (sE : E.CommShift ℤ) (β : B ⟶ E),
    (∀ K : C, β.app (op K) = b K M) ∧
    (fun [_sB : B.CommShift ℤ] [_sE : E.CommShift ℤ] ↦
      B.IsTriangulated ∧ E.IsTriangulated ∧ NatTrans.CommShift β ℤ ∧
      (∀ (K : C) (n : ℤ), (B.commShiftIso n).hom.app (op K) =
        (n * (n + 1) / 2).negOnePow •
          (F.map ((siteHomOppositeSourceShift K n).hom.app M) ≫
            (F.commShiftIso n).hom.app ((ihom K).obj M))) ∧
      (∀ (K : C) (n : ℤ), (E.commShiftIso n).hom.app (op K) =
        (n * (n + 1) / 2).negOnePow •
          ((MonoidalClosed.internalHom.map ((F.commShiftIso (-n)).inv.app K).op).app
              (F.obj M) ≫
            (siteHomOppositeSourceShift (F.obj K) n).hom.app (F.obj M))) ∧
      (∀ T : Triangle C, T ∈ distTriang C →
        ∃ φ : B.mapTriangle.obj ((triangleOpEquivalence C).functor.obj (op T)) ⟶
          E.mapTriangle.obj ((triangleOpEquivalence C).functor.obj (op T)),
          φ.hom₁ = β.app (op T.obj₃) ∧ φ.hom₂ = β.app (op T.obj₂) ∧
            φ.hom₃ = β.app (op T.obj₁))) (_sB := sB) (_sE := sE) ∧
    P.IsTriangulated ∧ P.IsStableUnderRetracts

def siteHomSiteExactThick
    (B : Type (u + 2)) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B]
    [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B]
    (X : Scheme.{u}) [(comparisonUpperStar B X).PreservesFlat]
    (M : DerivedCategory (Sheaf X.smallEtaleTopology B)) : Prop :=
  siteHomExactThickAssertion (comparisonUpperStar B X).mapDerivedCategory
    (siteComparisonEvaluationHom B X) M

def siteHomRestrictionSquareFor
    (B : Type (u + 2)) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B]
    [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B]
    {Y X : Scheme.{u}} (f : Y ⟶ X) :
    (Etale.upperStar B f).mapDerivedCategory ⋙
        (comparisonUpperStar B Y).mapDerivedCategory ≅
      (comparisonUpperStar B X).mapDerivedCategory ⋙
        (upperStar B f).mapDerivedCategory :=
  let e : Etale.upperStar B f ⋙
      comparisonUpperStar B Y ≅
    comparisonUpperStar B X ⋙
      upperStar B f :=
    supportSiteComparisonCoefficientPullbackIso B f
  (Functor.mapDerivedCategoryCompIso
      (Etale.upperStar B f)
      (comparisonUpperStar B Y)).symm ≪≫
    Functor.mapDerivedCategoryNatIso e ≪≫
    Functor.mapDerivedCategoryCompIso
      (comparisonUpperStar B X)
      (upperStar B f)

def siteHomRestrictionSquareAssertion
    {C : Type d} [Category.{v} C] {C₁ : Type d₁} [Category.{v} C₁]
    {D : Type e} [Category.{v} D] {D₁ : Type e₁} [Category.{v} D₁]
    (H : Cᵒᵖ ⥤ C ⥤ C) (H₁ : C₁ᵒᵖ ⥤ C₁ ⥤ C₁)
    (G : Dᵒᵖ ⥤ D ⥤ D) (G₁ : D₁ᵒᵖ ⥤ D₁ ⥤ D₁)
    (F : C ⥤ D) (F₁ : C₁ ⥤ D₁) (r_e : C ⥤ C₁) (r_p : D ⥤ D₁)
    (θ : r_e ⋙ F₁ ≅ F ⋙ r_p)
    (b : ∀ K M : C, F.obj ((H.obj (op K)).obj M) ⟶
      (G.obj (op (F.obj K))).obj (F.obj M))
    (b₁ : ∀ K M : C₁, F₁.obj ((H₁.obj (op K)).obj M) ⟶
      (G₁.obj (op (F₁.obj K))).obj (F₁.obj M))
    (h_e : ∀ K M : C, r_e.obj ((H.obj (op K)).obj M) ⟶
      (H₁.obj (op (r_e.obj K))).obj (r_e.obj M))
    (h_p : ∀ K M : D, r_p.obj ((G.obj (op K)).obj M) ⟶
      (G₁.obj (op (r_p.obj K))).obj (r_p.obj M)) (K M : C) : Prop :=
  IsIso (h_e K M) ∧ IsIso (h_p (F.obj K) (F.obj M)) ∧
    F₁.map (h_e K M) ≫ b₁ (r_e.obj K) (r_e.obj M) ≫
      (G₁.map (θ.inv.app K).op).app (F₁.obj (r_e.obj M)) ≫
      (G₁.obj (op (r_p.obj (F.obj K)))).map (θ.hom.app M) =
    θ.hom.app ((H.obj (op K)).obj M) ≫ r_p.map (b K M) ≫ h_p (F.obj K) (F.obj M)

def siteHomRestrictionAssertion
    (B : Type (u + 2)) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B]
    [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B]
    {Y X : Scheme.{u}} (f : Y ⟶ X)
    [(comparisonUpperStar B X).PreservesFlat]
    [(comparisonUpperStar B Y).PreservesFlat]
    (m_e : (Etale.upperStar B f).mapDerivedCategory.Monoidal)
    (m_p : (upperStar B f).mapDerivedCategory.Monoidal)
    (K M : DerivedCategory (Sheaf X.smallEtaleTopology B)) : Prop :=
  siteHomRestrictionSquareAssertion
    (Etale.derivedHom B X) (Etale.derivedHom B Y)
    (derivedHom B X) (derivedHom B Y)
    (comparisonUpperStar B X).mapDerivedCategory
    (comparisonUpperStar B Y).mapDerivedCategory
    (Etale.upperStar B f).mapDerivedCategory (upperStar B f).mapDerivedCategory
    (siteHomRestrictionSquareFor B f)
    (siteComparisonEvaluationHom B X) (siteComparisonEvaluationHom B Y)
    (siteHomEtaleRestrictionEvaluation B f m_e)
    (siteHomProEtaleRestrictionEvaluation B f m_p) K M

private theorem etaleRestriction_isIso
    (B : Type (u + 2)) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B]
    [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B]
    {Y X : Scheme.{u}} (f : Y ⟶ X) [Etale f] [(Etale.upperStar B f).PreservesFlat]
    (K M : DerivedCategory (Sheaf X.smallEtaleTopology B)) :
    IsIso (siteHomEtaleRestrictionEvaluation B f
      (siteHomExactDerivedMonoidal (Etale.upperStar B f)) K M) := by
  let L := Etale.etaleLowerShriek B f inferInstance
  let a : L ⊣ Etale.upperStar B f :=
    Etale.etaleLowerShriekUpperStarAdjunction B f inferInstance
  have : PreservesFiniteLimits L :=
    Etale.preservesFiniteLimits_etaleLowerShriek_of_hasSmallSiteSheafify B f inferInstance
  have : L.Additive := a.left_adjoint_additive
  have := a.leftAdjoint_preservesColimits
  have : PreservesFiniteColimits L :=
    PreservesColimitsOfSize.preservesFiniteColimits.{u + 1, u + 1} L
  have (P : Sheaf X.smallEtaleTopology B) :
      IsIso (Functor.LaxMonoidal.ihomComparison (Etale.upperStar B f) P).natTrans :=
    Etale.isIso_ihomComparison_upperStar B f P
  unfold siteHomEtaleRestrictionEvaluation
  exact isIso_exactDerivedHom (Etale.upperStar B f) a K M

private theorem proetaleRestriction_isIso
    (B : Type (u + 2)) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B]
    [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B]
    {Y X : Scheme.{u}} (f : Y ⟶ X) [WeaklyEtale f] [(upperStar B f).PreservesFlat]
    (K M : DerivedCategory (Sheaf (Scheme.ProEt.topology X) B)) :
    IsIso (siteHomProEtaleRestrictionEvaluation B f
      (siteHomExactDerivedMonoidal (upperStar B f)) K M) := by
  have (P : Sheaf (Scheme.ProEt.topology X) B) :
      IsIso (Functor.LaxMonoidal.ihomComparison (upperStar B f) P).natTrans :=
    ProEtale.isIso_ihomComparison_upperStar B f P
  unfold siteHomProEtaleRestrictionEvaluation
  exact isIso_exactDerivedHom (upperStar B f) (weaklyEtaleLowerShriekAdjunction B f) K M

section RestrictionSquare
variable (B : Type (u + 2)) [Category.{u + 1} B] [Abelian B]
  [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B]
  [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
  [Abelian.HasFunctorialFlatResolution B]

private theorem comparisonMonoidal_eq (X : Scheme.{u})
    [(comparisonUpperStar B X).PreservesFlat] :
    siteComparisonMonoidal B X = monoidal_comparisonUpperStar B X := by
  apply monoidal_eq_of_delta
  intro K M
  unfold siteComparisonMonoidal monoidal_comparisonUpperStar
  rfl

private theorem comparisonDerivedMonoidal_eq (X : Scheme.{u})
    [(comparisonUpperStar B X).PreservesFlat] :
    letI : (comparisonUpperStar B X).Monoidal := siteComparisonMonoidal B X
    siteComparisonDerivedMonoidal B X =
      siteHomExactDerivedMonoidal (comparisonUpperStar B X) := by
  letI : (comparisonUpperStar B X).Monoidal := siteComparisonMonoidal B X
  unfold siteHomExactDerivedMonoidal
  exact Functor.exactDerivedMonoidal_eq_of_delta (comparisonUpperStar B X)
    (siteComparisonDerivedMonoidal B X) (siteComparisonDerivedMonoidal_δ B X)
private theorem ordinaryRestrictionSquare_eq {Y X : Scheme.{u}} (f : Y ⟶ X) :
    supportSiteComparisonCoefficientPullbackIso B f =
      (comparisonUpperStarCompUpperStarIso B f).symm := by
  rfl

private theorem ordinaryRestrictionSquare_monoidal {Y X : Scheme.{u}} (f : Y ⟶ X) :
    NatTrans.IsMonoidal (comparisonUpperStarCompUpperStarIso B f).inv := by
  haveI := isMonoidal_comparisonUpperStarCompUpperStarIso_hom (A := B) f
  infer_instance

private theorem restrictionSquare_monoidal {Y X : Scheme.{u}} (f : Y ⟶ X)
    [(comparisonUpperStar B X).PreservesFlat]
    [(comparisonUpperStar B Y).PreservesFlat]
    [(Etale.upperStar B f).PreservesFlat] [(upperStar B f).PreservesFlat] :
    letI : (comparisonUpperStar B X).mapDerivedCategory.Monoidal :=
    siteComparisonDerivedMonoidal B X
    letI : (comparisonUpperStar B Y).mapDerivedCategory.Monoidal :=
    siteComparisonDerivedMonoidal B Y
    letI := siteHomExactDerivedMonoidal (Etale.upperStar B f)
    letI := siteHomExactDerivedMonoidal (upperStar B f)
    NatTrans.IsMonoidal (siteHomRestrictionSquareFor B f).hom := by
  letI mX : (comparisonUpperStar B X).Monoidal := siteComparisonMonoidal B X
  letI mY : (comparisonUpperStar B Y).Monoidal := siteComparisonMonoidal B Y
  let e : Etale.upperStar B f ⋙ comparisonUpperStar B Y ≅
      comparisonUpperStar B X ⋙ upperStar B f :=
    supportSiteComparisonCoefficientPullbackIso B f
  have he : e = (comparisonUpperStarCompUpperStarIso B f).symm :=
    ordinaryRestrictionSquare_eq B f
  let P (a : (comparisonUpperStar B X).Monoidal)
      (b : (comparisonUpperStar B Y).Monoidal) : Prop :=
    letI := a
    letI := b
    NatTrans.IsMonoidal e.hom
  have h₀ : P (monoidal_comparisonUpperStar B X)
      (monoidal_comparisonUpperStar B Y) := by
    dsimp only [P]
    rw [he]
    exact ordinaryRestrictionSquare_monoidal B f
  haveI h : NatTrans.IsMonoidal e.hom :=
    Eq.mpr (congrArg₂ P (comparisonMonoidal_eq B X) (comparisonMonoidal_eq B Y)) h₀
  rw [comparisonDerivedMonoidal_eq B X, comparisonDerivedMonoidal_eq B Y]
  unfold siteHomExactDerivedMonoidal
    siteHomRestrictionSquareFor
  exact Functor.exactDerivedSquare_monoidal (comparisonUpperStar B X) (upperStar B f)
    (Etale.upperStar B f) (comparisonUpperStar B Y)
    e

private theorem siteComparisonEvaluationHom_eq_closedComparison (X : Scheme.{u})
    [(comparisonUpperStar B X).PreservesFlat]
    (K M : DerivedCategory (Sheaf X.smallEtaleTopology B)) :
    letI : (comparisonUpperStar B X).mapDerivedCategory.Monoidal :=
      siteComparisonDerivedMonoidal B X
    siteComparisonEvaluationHom B X K M =
      Functor.closedComparison (comparisonUpperStar B X).mapDerivedCategory K M := by
  unfold siteComparisonEvaluationHom Functor.closedComparison
  rfl

private theorem restrictionAssertion {Y X : Scheme.{u}} (f : Y ⟶ X) [Etale f]
    [(comparisonUpperStar B X).PreservesFlat]
    [(comparisonUpperStar B Y).PreservesFlat]
    [(Etale.upperStar B f).PreservesFlat] [(upperStar B f).PreservesFlat]
    (K M : DerivedCategory (Sheaf X.smallEtaleTopology B)) :
    siteHomRestrictionAssertion B f
      (siteHomExactDerivedMonoidal (Etale.upperStar B f))
      (siteHomExactDerivedMonoidal (upperStar B f)) K M := by
  refine ⟨etaleRestriction_isIso B f K M,
    proetaleRestriction_isIso B f _ _, ?_⟩
  letI : (comparisonUpperStar B X).mapDerivedCategory.Monoidal :=
    siteComparisonDerivedMonoidal B X
  letI : (comparisonUpperStar B Y).mapDerivedCategory.Monoidal :=
    siteComparisonDerivedMonoidal B Y
  letI := siteHomExactDerivedMonoidal (Etale.upperStar B f)
  letI := siteHomExactDerivedMonoidal (upperStar B f)
  have := restrictionSquare_monoidal B f
  rw [siteComparisonEvaluationHom_eq_closedComparison,
    siteComparisonEvaluationHom_eq_closedComparison]
  unfold siteHomEtaleRestrictionEvaluation siteHomProEtaleRestrictionEvaluation
  exact CategoryTheory.closedComparison_square (Etale.upperStar B f).mapDerivedCategory
    (upperStar B f).mapDerivedCategory (comparisonUpperStar B X).mapDerivedCategory
    (comparisonUpperStar B Y).mapDerivedCategory (siteHomRestrictionSquareFor B f) K M
end RestrictionSquare

variable (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u})
```

## New

The same declaration signatures and construction bodies are in
`Sheaf.CategoryTheory.NativeDerivedHomSignedExact`. The old module adds:

```lean
public import Sheaf.CategoryTheory.NativeDerivedHomSignedExact
```

The new module imports the existing derived monoidal shortcut instances. It does not
introduce alternative local colimit or derived tensor structures.

The three relocated shift definitions and the existing proposition definitions
`siteHomExactThickAssertion` and `siteHomSiteExactThick` are marked `@[irreducible]`.
The proposition bodies and all three shift construction bodies remain unchanged.
Their proofs use explicit unfolding of the propositions once. These reduction controls
prevent repeated kernel expansion of concrete derived sheaf structures.

The private restriction-square proof supplies its four derived categories explicitly.
The private ordinary monoidal equality proof unfolds its two equal constructions directly
instead of comparing all tensor components. A proved private generic helper assembles the
signed shifts, triangle morphism and thick locus before specialization to sheaf categories.

## Users

`tools/downstream.py` was run separately for each of the three names. Only their
original module uses these names directly. Its sole downstream module is also listed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SiteHomComparisonThick | Q1, this item | Same declarations remain publicly available through the new public import; proof uses the two new intermediate statements. |
| Sheaf.Paper.LisseFlatHomSiteComparison | unchanged, not adapted | Public import of the item continues to expose exactly the same shift constructions and existing assertion types. No statement or proof adaptation required; its unchanged source compiles against the delivery. |
| Sheaf.CategoryTheory.NativeDerivedHomSignedExact | new | Owns the verbatim constructions and the native signed exactness intermediate. |
| Sheaf.CategoryTheory.ExactDerivedHomComparisonShift | new | Uses the publicly available constructions to state the shift square. |

No definition in a target changes its meaning. No source-library file is modified.

## Status

landed 20261025T164119-L-953435 2026-10-25 (merge of deliver/Q1/Sheaf.AlgebraicGeometry.SiteHomComparisonThick)
