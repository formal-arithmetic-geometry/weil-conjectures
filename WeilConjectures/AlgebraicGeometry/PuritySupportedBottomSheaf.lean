/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityFiniteSetting
public import WeilConjectures.SixFunctors.Etale.SupportCohomology
public import WeilConjectures.SixFunctors.Etale.Derived.ClosedImmersionUpperShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClosedImmersion
public import Mathlib.CategoryTheory.Abelian.Injective.Extend
public import Mathlib.Algebra.Homology.Functor
import WeilConjectures.CategoryTheory.BottomCohomologyPresheaf
import WeilConjectures.AlgebraicGeometry.OpenSupportSiteRestriction
import WeilConjectures.AlgebraicGeometry.ComparisonInjectiveResolutionHomotopy
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful

/-!
# Sheafhood of supported cohomology in its bottom local degree

Source: blueprint, sec-smooth-purity/sk-prop-an/thm-pur-localized-top-chern.proof.md,
Step 3, universal case; Stacks Project, Tags 09XP, 09XQ and 099W
(blueprint: lem-pur-supported-bottom-gluing).

The supported presheaves below are cohomology of actual section complexes, before
sheafification. They use abelian injective resolutions, also for module coefficients.
The pro-etale presheaf is on the small etale site, by evaluation on its etale objects.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures

namespace AlgebraicGeometry

/-- The local support complex of the canonical abelian injective resolution.
Its cohomology sheaves are the local cohomology sheaves along Z. Extension to integer
indices makes all negative degrees zero. Source: Stacks 09XP--09XQ and blueprint Step 3
(blueprint: lem-pur-supported-bottom-gluing). -/
def Etale.puritySupportComplex {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ :=
  ((Etale.sectionsWithSupport AddCommGrpCat.{u + 1} i.openComplement.ι).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj (injectiveResolution F).cochainComplex

/-- The presheaf U ↦ H^d_{Z ×_X U}(U,F|_U), using sections of the supported
injective resolution and the actual restriction maps. Etale localization preserves
injectives, so this is the injective-resolution formula for the recorded supported
cohomology functor on each U. Source: Stacks 09XP and blueprint Step 3
(blueprint: lem-pur-supported-bottom-gluing). -/
def Etale.puritySupportPresheaf {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (d : ℤ) :
    X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  (((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj (Etale.puritySupportComplex i F)).asFunctor ⋙
      HomologicalComplex.homologyFunctor AddCommGrpCat.{u + 1} (ComplexShape.up ℤ) d

/-- The pro-etale support complex of an abelian injective resolution.
Source: Stacks 09XP (the same site construction), 099W and blueprint Step 3
(blueprint: lem-pur-supported-bottom-gluing). -/
def ProEtale.puritySupportComplex {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (F : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) :
    CochainComplex (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) ℤ :=
  ((ProEtale.sectionsWithSupport AddCommGrpCat.{u + 1}
    i.openComplement.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (injectiveResolution F).cochainComplex

/-- Pro-etale supported cohomology, evaluated on etale objects and with their
restriction maps. This is a presheaf on X_et, as in the specified supported comparison;
no claim about arbitrary pro-etale covers is encoded here.
Source: Stacks 099W, 09XP and blueprint Step 3
(blueprint: lem-pur-supported-bottom-gluing). -/
def ProEtale.puritySupportEtalePresheaf {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (F : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
    (d : ℤ) : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  (Scheme.toProEt X).op ⋙
    (((sheafToPresheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (ProEtale.puritySupportComplex i F)).asFunctor ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{u + 1} (ComplexShape.up ℤ) d

/-- The fixed signed finite Tate coefficient, regarded as an abelian etale sheaf.
N chooses an annihilating power of ell; it does not restrict the signed twist r.
Source: def-pur-conventions, signed twists, and blueprint Step 3
(blueprint: lem-pur-supported-bottom-gluing). -/
def purityBottomTwist (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) (N : ℕ)
    (hA : ((P.coefficients.l ^ (N + 1) : ℕ) : P.Coefficient) = 0) (r : ℤ) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (P.forgetEtale X).obj
    (Scheme.finiteEtaleTateSheaf P.Coefficient (P.coefficients.l ^ (N + 1)) X hA r)

private def pointwiseHomologyIso
    {T : Type*} [Category* T] {V : Type*} [Category* V] [Abelian V]
    (K : CochainComplex (T ⥤ V) ℤ) (d : ℤ) :
    K.asFunctor ⋙ HomologicalComplex.homologyFunctor V (.up ℤ) d ≅ K.homology d :=
  NatIso.ofComponents (fun t ↦ (K.sc d).mapHomologyIso ((evaluation T V).obj t))
    (fun {t t'} f ↦ by
      change ShortComplex.homologyMap
        ((K.sc d).mapNatTrans ((evaluation T V).map f)) ≫ _ = _
      rw [ShortComplex.homologyMap_mapNatTrans]
      simp
      rfl)

private theorem supportedKInjective {Z X : AlgebraicGeometry.Scheme.{u}}
    (i : Z ⟶ X) [AlgebraicGeometry.IsClosedImmersion i]
    (K : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    [K.IsKInjective] :
    CochainComplex.IsKInjective
      (((AlgebraicGeometry.Etale.sectionsWithSupport AddCommGrpCat.{u + 1}
        i.openComplement.ι).mapHomologicalComplex (.up ℤ)).obj K) := by
  let A := AddCommGrpCat.{u + 1}
  let S := AlgebraicGeometry.Etale.sectionsWithSupport A i.openComplement.ι
  let E := AlgebraicGeometry.Etale.closedUpperShriek A i i.openComplement.ι
  let R := AlgebraicGeometry.Etale.lowerStar A i
  let : R.PreservesHomology := {}
  let : E.PreservesKInjectiveComplexes :=
    (AlgebraicGeometry.Etale.lowerStarClosedUpperShriekAdjunction A i i.openComplement.ι
      i.range_eq_compl_range_openComplement_ι).preservesKInjectiveComplexes
  let : R.PreservesKInjectiveComplexes :=
    (AlgebraicGeometry.Etale.upperStarLowerStarAdjunction A i).preservesKInjectiveComplexes
  let u := Functor.whiskerLeft S
    (AlgebraicGeometry.Etale.upperStarLowerStarAdjunction A i).unit
  have (F : Sheaf X.smallEtaleTopology A) : IsIso (u.app F) :=
    AlgebraicGeometry.Etale.isIso_upperStarLowerStarAdjunction_unit_app_of_isZero A i
      i.openComplement.ι i.range_eq_compl_range_openComplement_ι
      (AlgebraicGeometry.Etale.isZero_upperStar_sectionsWithSupport A i.openComplement.ι F)
  let : IsIso u := NatIso.isIso_of_isIso_app u
  let e : S ≅ E ⋙ R := asIso u
  let : S.PreservesKInjectiveComplexes :=
    CategoryTheory.Functor.preservesKInjectiveComplexes_of_iso e.symm
  exact inferInstanceAs (CochainComplex.IsKInjective
    ((S.mapHomologicalComplex (.up ℤ)).obj K))

/-- Vanishing of local cohomology sheaves below d makes degree-d supported classes
satisfy existence and uniqueness of gluing on the small etale site. The same holds for
pro-etale supported cohomology on etale objects through the unit-induced comparison.
Source: blueprint thm-pur-localized-top-chern.proof.md, Step 3, universal case;
Stacks 09XP, 09XQ and 099W (blueprint: lem-pur-supported-bottom-gluing).

Proof:
1. The support kernel is naturally isomorphic to i_*i^!. Each factor is right
adjoint to an exact functor, so both preserve K-injective complexes. The canonical
injective resolution is bounded below and termwise injective, hence K-injective.
Thus its supported complex K is K-injective.
2. The vanishing hypothesis puts K in D≥d. For the left exact underlying-presheaf
functor G, the derived truncation comparison gives H^d(RG(K)) ≅ G(H^d(K)).
K-injectivity computes RG(K) termwise. Exactness of evaluation identifies its
homology presheaf with the presheaf defined above, naturally in the site object.
Transport the sheaf condition of H^d(K) to prove the etale clause.
3. Let I and J be the etale and pro-etale resolutions. Exactness of comparison
inverse image L and acyclicity of L(I) for comparison direct image R give a
quasi-isomorphism I → R(J), by the unit and an injective-resolution comparison.
Both complexes are K-injective, so this is a homotopy equivalence.
4. Replace open inverse image by explicit site restriction on both sites. The
restriction adjunction units commute with R definitionally, and R preserves
kernels. Thus pro-etale support followed by R is naturally isomorphic to R
followed by etale support. Apply this isomorphism termwise to J.
5. Apply support and the underlying-presheaf functor to the homotopy equivalence
of Step 3. Its homology isomorphism and Step 4 identify the actual two presheaves
in the statement. Transport etale sheafhood to prove the pro-etale clause.
All homology and comparison constructions are indexed by the integers; negative
degrees require no separate choice of maps.
-/
theorem purity_supported_bottom_isSheaf (P : PurityFiniteSetting.{u}) (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of P.field.k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of P.field.k))]
    [IsSeparated (X ↘ Spec (CommRingCat.of P.field.k))]
    {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (r : ℤ) (N : ℕ)
    (hA : ((P.coefficients.l ^ (N + 1) : ℕ) : P.Coefficient) = 0) (d : ℤ)
    (hvan : ∀ q : ℤ, q < d →
      IsZero ((Etale.puritySupportComplex i (purityBottomTwist P X N hA r)).homology q)) :
    Presheaf.IsSheaf X.smallEtaleTopology
      (Etale.puritySupportPresheaf i (purityBottomTwist P X N hA r) d) ∧
    Presheaf.IsSheaf X.smallEtaleTopology
      (ProEtale.puritySupportEtalePresheaf i
        ((ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} X).obj
          (purityBottomTwist P X N hA r)) d) := by
  let F := purityBottomTwist P X N hA r
  let K := Etale.puritySupportComplex i F
  have : (injectiveResolution F).cochainComplex.IsKInjective :=
    CochainComplex.isKInjective_of_injective (injectiveResolution F).cochainComplex 0
  have : K.IsKInjective := supportedKInjective i (injectiveResolution F).cochainComplex
  have hEt : Presheaf.IsSheaf X.smallEtaleTopology (Etale.puritySupportPresheaf i F d) :=
    Presheaf.isSheaf_bottom_cohomology_of_isKInjective X.smallEtaleTopology K d hvan
  refine ⟨hEt, ?_⟩
  let R := ProEtale.comparisonLowerStar AddCommGrpCat.{u + 1} X
  let S := Etale.sectionsWithSupport AddCommGrpCat.{u + 1} i.openComplement.ι
  let G := sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}
  let J := (injectiveResolution
    ((ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} X).obj F)).cochainComplex
  obtain ⟨e⟩ := ProEtale.comparisonInjectiveResolutionHomotopyEquiv F
  obtain ⟨c⟩ := ProEtale.nonempty_sectionsWithSupport_comparisonLowerStarIso i.openComplement.ι
  let h := (G.mapHomotopyEquiv (S.mapHomotopyEquiv e)).toHomologyIso d
  let cK := (G.mapHomologicalComplex (.up ℤ)).mapIso
    ((NatIso.mapHomologicalComplex c (.up ℤ)).app J)
  let Kpro := (G.mapHomologicalComplex (.up ℤ)).obj
    ((R.mapHomologicalComplex (.up ℤ)).obj (ProEtale.puritySupportComplex i
      ((ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} X).obj F)))
  let E : ProEtale.puritySupportEtalePresheaf i
      ((ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} X).obj F) d ≅
      Etale.puritySupportPresheaf i F d :=
    pointwiseHomologyIso Kpro d ≪≫
      (HomologicalComplex.homologyFunctor _ (.up ℤ) d).mapIso cK ≪≫ h.symm ≪≫
      (pointwiseHomologyIso ((G.mapHomologicalComplex (.up ℤ)).obj K) d).symm
  exact (Presheaf.isSheaf_of_iso_iff E).mpr hEt

end AlgebraicGeometry
