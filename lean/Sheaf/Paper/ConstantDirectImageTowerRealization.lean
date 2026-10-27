module

public import Sheaf.Paper.ConnectedConstantH0
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.SfDerivedDirectImage
public import Sheaf.Paper.PointReductionUnits
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Sheaf.Paper.PointProEtaleSectionsExactOfUniverses
public import Sheaf.Paper.ConstantCoefficientScalarNormalization
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
import Sheaf.CategoryTheory.Sites.RGammaDerivedLimit
import Sheaf.Paper.ConstantScalarStrictUnit
import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.CategoryTheory.RightDerivedSingleH0
import Sheaf.Paper.ConstantTowerTransition
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-! # Realization of the completed constant direct-image tower

Source: Stacks Project, sites-cohomology.tex, Tag 0D6K, and derived.tex, Tag 05TD
(blueprint: lem-pod-constant-direct-image-tower-realization).

The theorem records the Roos triangle after exact point sections and the canonical
finite-reduction identifications of its degree-zero projections and transitions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u w

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale

namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (Y : Scheme.{u}) [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (Y ↘ Spec (.of D.k))]

/-- The existing forgetful functor on the ordinary integral coefficient modules.
Source: Stacks Tag 0D6K (blueprint: lem-pod-constant-direct-image-tower-realization). -/
abbrev constantTowerForget : ModuleCat.{u + 1}
    (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)) ⥤
      AddCommGrpCat.{u + 1} := forget₂ _ _

/-- Exactness of forgetting the ordinary coefficient action at cokernels.
Source: Stacks Tag 0D6K (blueprint: lem-pod-constant-direct-image-tower-realization). -/
instance constantTowerForgetColimits : PreservesFiniteColimits (constantTowerForget l E) :=
  @PreservesColimitsOfSize.preservesFiniteColimits.{0, 0, u + 1, u + 1, u + 2, u + 2}
    _ _ _ _ (constantTowerForget l E)
    (ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, u + 1, 0, 0} _)

/-- Exact point sections with the coefficient action forgotten by exact localization.
Source: Stacks Tag 0D6K (blueprint: lem-pod-constant-direct-image-tower-realization). -/
abbrev constantTowerAbSections [HasDerivedCategory.{w} AddCommGrpCat.{u + 1}] :
    DerivedCategory (scalarReductionSource.{u, u} l E (Spec (.of D.k))) ⥤
      DerivedCategory AddCommGrpCat.{u + 1} :=
  pointFibreIntegralAmbient D l E ⋙
    (constantTowerForget l E).mapDerivedCategory.{u + 1, w, u + 1, u + 1, u + 2, u + 2}

/-- The finite-reduction projection after sections, retaining the actual scalar unit,
adjoint comparison and identity-on-sections restriction comparison.
Source: Stacks Tags 07A6 and 0D6K
(blueprint: lem-pod-constant-direct-image-tower-realization). -/
def constantTowerFiniteProjection (n : ℕ) :
    (pointFibreIntegralAmbient D l E).obj (connectedIntegralImage D l hl E Y).obj ⟶
      ((pointUnitIntegralRestriction l E n).mapDerivedCategory.{u + 2, u + 1}).obj
        (finiteOrdinarySections D l E Y (n + 1) (by omega)
          (finiteCohomologyCoefficient l E Y (n + 1) (by omega))) :=
  (pointFibreIntegralAmbient D l E).map
      ((pointUnitIntegralSheafUnit D l E n).app
        (connectedIntegralImage D l hl E Y).obj) ≫
    (pointFibreIntegralAmbient D l E).map
      ((scalarReductionDerivedRestriction l E (Spec (.of D.k)) n).map
        (sfDirectImageReductionComparison l E (Y ↘ Spec (.of D.k))
          (connectedIntegralImage D l hl E Y) n)) ≫
    (connectedFiniteTowerIso D l hl E Y n).hom

/-- Realization of the completed constant direct-image tower by exact point sections.
Source: Stacks Project, sites-cohomology.tex, Tag 0D6K, and derived.tex, Tag 05TD
(blueprint: lem-pod-constant-direct-image-tower-realization).
Proof:
1. Put K equal to the completed regular module in degree zero. The canonical
   constantCoefficientReductionMap is invertible by
   lem-weil-constant-coefficient-objects-constructible. The strict-unit normalization
   lem-weil-constant-scalar-strict-unit identifies its quotient transitions with the
   actual ring quotient maps. The chosen connectedIntegralImage is exactly the
   SfIntegralDirectImage used by ordinary integral cohomology.
2. Apply lem-kun-site-rgamma-derived-limit to its specified Roos triangle. Exact
   point sections (lem-weil-point-proetale-sections-exact) identify derived sections
   with their termwise localization on objects and maps. Forget the coefficient action
   by exact localization. The product comparison e respects each projection; transport
   both product vertices and the boundary by e to obtain the displayed Roos triangle.
3. The finite-reduction comparison is the adjunct of the Roos projection. The unit
   equation of lem-weil-derived-scalar-extension-restriction-adjunction therefore
   identifies constantTowerFiniteProjection with that projection followed by the
   canonical finite-tower comparison. The def-trf-point-reduction-units restriction
   comparison is the identity on sections. Applying H0 gives precisely the recorded P.
4. Choose nonnegative injective resolutions of the finite regular modules and of
   their restrictions to completed coefficients, by prop-pur-kinjective-resolutions-exist
   and lem-weil-pbc-left-exact-injective-resolution-degree-zero. Bounded-below
   injectives are K-injective (lem-weil-pbc-bounded-below-injectives-kinjective).
   Left exactness identifies degree zero with ordinary direct image, through the
   actual resolution augmentation (lem-pod-finite-sheaf-h0-augmentation).
5. Exact restriction preserves the resolution quasi-isomorphism. By
   lem-weil-pbc-kinjective-hom-derived its comparison to the completed resolution is
   represented by a quasi-isomorphism j. The normalization in
   lem-weil-pbc-ringed-topoi-derived-pushforward-composition identifies the canonical
   restriction comparison with the inverse of the direct image of j. The augmentation
   equation and lem-kun-right-derived-single-h0 show that this comparison is the
   identity on the underlying degree-zero sections.
6. The specified sfDirectImageTransition is the completed direct image of the actual
   quotient, conjugated by these canonical comparisons. Their degree-zero maps are
   identities, so the augmentation square gives exactly the sectionwise quotient map.
   Equivalently apply lem-pod-constant-tower-transition to the quotient ring map.
   Exact point sections and the recorded finite-tower H0 comparison give the displayed
   formula for Q. No flatness of one finite quotient over another is used.
7. Consecutive maps of the Roos triangle compose to zero by
   lem-weil-pbc-hom-into-triangle-exact. Projecting the equation (1-s)p=0 to coordinate n
   gives p_n=t_n p_(n+1). Apply exact sections and H0 and the preceding identifications
   to obtain Q_n P_(n+1)=P_n. Empty and disconnected schemes are included throughout;
   no assertion about finiteness of higher cohomology is used.
-/
theorem constantDirectImageTowerRealization
    [HasDerivedCategory.{w} AddCommGrpCat.{u + 1}] :
    ∃ e : (constantTowerAbSections D l E).obj
          (∏ᶜ (sfDirectImageTerm l E (Y ↘ Spec (.of D.k))
            (integralCohomologyCoefficient D l hl E Y).obj)) ≅
        ∏ᶜ (fun n : ℕ ↦ (constantTowerAbSections D l E).obj
          (sfDirectImageTerm l E (Y ↘ Spec (.of D.k))
            (integralCohomologyCoefficient D l hl E Y).obj n)),
      (∀ n : ℕ, e.hom ≫ Pi.π _ n =
        (constantTowerAbSections D l E).map
          (Pi.π (sfDirectImageTerm l E (Y ↘ Spec (.of D.k))
            (integralCohomologyCoefficient D l hl E Y).obj) n)) ∧
      IsDerivedLimitTriangle
        (fun n ↦ (constantTowerAbSections D l E).map
          (sfDirectImageTransition l E (Y ↘ Spec (.of D.k))
            (integralCohomologyCoefficient D l hl E Y).obj n))
        ((constantTowerAbSections D l E).obj
          (connectedIntegralImage D l hl E Y).obj)
        ((constantTowerAbSections D l E).map
            (connectedIntegralImage D l hl E Y).projection ≫ e.hom)
        (e.inv ≫ (constantTowerAbSections D l E).map
            (connectedIntegralImage D l hl E Y).boundary ≫
          ((constantTowerAbSections D l E).commShiftIso (1 : ℤ)).hom.app
            (connectedIntegralImage D l hl E Y).obj) ∧
      (∀ n : ℕ,
        (constantTowerAbSections D l E).map
            (connectedIntegralImage D l hl E Y).projection ≫ e.hom ≫ Pi.π _ n =
          (constantTowerAbSections D l E).map
            ((connectedIntegralImage D l hl E Y).projection ≫
              Pi.π (sfDirectImageTerm l E (Y ↘ Spec (.of D.k))
                (integralCohomologyCoefficient D l hl E Y).obj) n)) ∧
      (∀ n : ℕ, constantTowerFiniteProjection D l hl E Y n =
        (pointFibreIntegralAmbient D l E).map
            ((connectedIntegralImage D l hl E Y).projection ≫
              Pi.π (sfDirectImageTerm l E (Y ↘ Spec (.of D.k))
                (integralCohomologyCoefficient D l hl E Y).obj) n) ≫
          (connectedFiniteTowerIso D l hl E Y n).hom) ∧
      (∀ (n : ℕ) (x : integralOrdinaryCohomology D l hl E Y
          (integralCohomologyCoefficient D l hl E Y) 0),
        ((Functor.mapDerivedCategoryHomologyFunctorIso.{_, _, _, _, u + 2, u + 1}
            (pointUnitIntegralRestriction l E n) 0).symm.app
              (finiteOrdinarySections D l E Y (n + 1) (by omega)
                (finiteCohomologyCoefficient l E Y (n + 1) (by omega)))).hom
          ((DerivedCategory.homologyFunctor.{u + 1} _ 0).map
            (constantTowerFiniteProjection D l hl E Y n) x) = P D l hl E Y n x) ∧
      (∀ (n : ℕ) (x : finiteOrdinaryCohomology D l E Y (n + 2)
          (by omega) (finiteCohomologyCoefficient l E Y (n + 2) (by omega)) 0),
        (connectedFiniteH0SectionsIso D l E Y n).hom (Q D l hl E Y n x) =
          (integralCoefficientSheafTransition l E Y n).hom.app
            ((proEtaleBaseChange (Y ↘ Spec (.of D.k))).op.obj
              (op (ProEt.mk (𝟙 (Spec (.of D.k))))))
            ((connectedFiniteH0SectionsIso D l E Y (n + 1)).hom x)) ∧
      (∀ (n : ℕ) (x : integralOrdinaryCohomology D l hl E Y
          (integralCohomologyCoefficient D l hl E Y) 0),
        Q D l hl E Y n (P D l hl E Y (n + 1) x) = P D l hl E Y n x) := by
  sorry

end WeilConjectures
