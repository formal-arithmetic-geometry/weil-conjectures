/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SupportCohomology
public import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.ComparisonPullbackExact
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import Mathlib.Algebra.Homology.Embedding.CochainComplex

import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy

/-!
# Supported cohomology comparison on etale objects

Source: Stacks Project, Tag 099W, `lemma-compare-cohomology`, and Tag 09XP,
`section-cohomology-support`
(blueprint: lem-pur-etale-supported-site-comparison-natural).

The comparison is constructed on the kernel complexes of the chosen abelian injective
resolutions, using the recorded kernel-of-restriction functor
`CategoryTheory.Sheaf.supportedSectionsFunctor` of `def-pur-support-cohomology`.
The pro-etale complex is evaluated through `comparisonLowerStar`: on etale objects
this is literally evaluation of the original pro-etale sheaf. Extending the nonnegative
complexes by zero gives the requested cohomology in every integer degree.
-/

@[expose] public section

universe u

set_option autoImplicit false

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale

variable {X Z : Scheme.{u}}

/-- The pair `U ×_X O ⟶ U`, where `O` is the open complement of `Z`.
The pullback is in the small etale site, whose finite limits are scheme fibre products.
Source: Stacks 09XP, restriction to the open complement
(blueprint: lem-pur-etale-supported-site-comparison-natural). -/
noncomputable def supportedSitePair (i : Z ⟶ X) [IsClosedImmersion i] (U : X.Etale) :
    Arrow X.Etale :=
  Arrow.mk (pullback.snd (terminal.from (Scheme.Etale.mk i.openComplement.ι))
    (terminal.from U))

/-- Base change of the open complement along a morphism of etale objects.
Source: Stacks 09XP, functoriality of supported sections
(blueprint: lem-pur-etale-supported-site-comparison-natural). -/
noncomputable def supportedSitePairMap (i : Z ⟶ X) [IsClosedImmersion i]
    {V U : X.Etale} (g : V ⟶ U) : supportedSitePair i V ⟶ supportedSitePair i U :=
  Arrow.homMk'
    (pullback.lift
      (pullback.fst (terminal.from (Scheme.Etale.mk i.openComplement.ι)) (terminal.from V))
      (pullback.snd (terminal.from (Scheme.Etale.mk i.openComplement.ι)) (terminal.from V) ≫ g)
      (by simp)) g (by simp)

/-- The degree-`q` cohomology of the kernel-of-restriction complex on `U`.
This is the injective-resolution computation of `def-pur-support-cohomology`, before
identifying the computation for different resolutions. On a complex `ν_*J` it is precisely
`H^q(ker(J(U) ⟶ J(U ×_X O)))` on the pro-etale site.
Source: Stacks 09XP, kernel and injective-resolution formulas
(blueprint: lem-pur-etale-supported-site-comparison-natural). -/
noncomputable def supportedSiteCohomology (i : Z ⟶ X) [IsClosedImmersion i]
    (U : X.Etale) (q : ℤ) :
    CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ ⥤
      AddCommGrpCat.{u + 1} :=
  (Sheaf.supportedSectionsFunctor X.smallEtaleTopology AddCommGrpCat.{u + 1}
    (supportedSitePair i U).hom).mapHomologicalComplex (ComplexShape.up ℕ) ⋙
      ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{u + 1} ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{u + 1} (ComplexShape.up ℤ) q

/-- Restriction of supported sections along `V ⟶ U`: the map of kernels induced by
restriction of sections from `U` to `V` and from `U ×_X O` to `V ×_X O`.
Source: Stacks 09XP, functorial kernel of restriction
(blueprint: lem-pur-etale-supported-site-comparison-natural). -/
noncomputable def supportedSiteRestrictionNatTrans (i : Z ⟶ X) [IsClosedImmersion i]
    {V U : X.Etale} (g : V ⟶ U) :
    Sheaf.supportedSectionsFunctor X.smallEtaleTopology AddCommGrpCat.{u + 1}
        (supportedSitePair i U).hom ⟶
      Sheaf.supportedSectionsFunctor X.smallEtaleTopology AddCommGrpCat.{u + 1}
        (supportedSitePair i V).hom where
  app F := kernel.map _ _ (F.obj.map g.op) (F.obj.map (supportedSitePairMap i g).left.op)
    (by rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp, Arrow.w]; rfl)
  naturality F G f := by
    apply equalizer.hom_ext
    simp [Sheaf.supportedSectionsFunctor]

/-- Restriction of the supported cohomology computation along `V ⟶ U`.
Source: Stacks 09XP, functorial kernel of restriction
(blueprint: lem-pur-etale-supported-site-comparison-natural). -/
noncomputable def supportedSiteRestriction (i : Z ⟶ X) [IsClosedImmersion i]
    {V U : X.Etale} (g : V ⟶ U) (q : ℤ)
    (K : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ) :
    (supportedSiteCohomology i U q).obj K ⟶ (supportedSiteCohomology i V q).obj K :=
  HomologicalComplex.homologyMap
    (HomologicalComplex.extendMap
      ((NatTrans.mapHomologicalComplex
        (supportedSiteRestrictionNatTrans i g) (ComplexShape.up ℕ)).app K)
      ComplexShape.embeddingUpNat) q

/-- The choices `I`, `J`, and the augmentation-compatible comparison `ν^*I ⟶ J`.
Resolutions are in abelian sheaves, as required for the support cohomology definition;
for an `A`-module sheaf the input is its underlying abelian sheaf.
Source: Stacks 099W and 09XP, comparison using injective resolutions
(blueprint: lem-pur-etale-supported-site-comparison-natural). -/
structure SupportedSiteComparisonResolution
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) where
  /-- An etale injective resolution of the underlying abelian sheaf. -/
  etale : InjectiveResolution F
  /-- A pro-etale injective resolution of its comparison inverse image. -/
  proetale : InjectiveResolution
    ((ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} X).obj F)
  /-- A chain map from the termwise inverse image to the second resolution. -/
  comparison :
    ((ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} X).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj etale.cocomplex ⟶ proetale.cocomplex
  /-- Compatibility with the two augmentations, in degree zero. -/
  augmentation :
    (ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} X).map (etale.ι.f 0) ≫
      comparison.f 0 = proetale.ι.f 0

namespace SupportedSiteComparisonResolution

variable {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}

/-- The adjunction transpose of `t`: in degree `n`, the unit followed by `ν_*tⁿ`.
Source: Stacks 099W, comparison adjunction
(blueprint: lem-pur-etale-supported-site-comparison-natural). -/
noncomputable def transpose (r : SupportedSiteComparisonResolution F) :
    r.etale.cocomplex ⟶
      ((ProEtale.comparisonLowerStar AddCommGrpCat.{u + 1} X).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj r.proetale.cocomplex :=
  (((ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} X).mapHomologicalComplex
    (ComplexShape.up ℕ)).homEquiv _ _) r.comparison

/-- The canonical map `c^q_U`, obtained by restricting the transpose to supported kernels
and then taking cohomology. The kernel functor supplies preservation of vanishing sections.
Source: Stacks 099W and 09XP
(blueprint: lem-pur-etale-supported-site-comparison-natural). -/
noncomputable def map (r : SupportedSiteComparisonResolution F)
    (i : Z ⟶ X) [IsClosedImmersion i] (U : X.Etale) (q : ℤ) :
    (supportedSiteCohomology i U q).obj r.etale.cocomplex ⟶
      (supportedSiteCohomology i U q).obj
        (((ProEtale.comparisonLowerStar AddCommGrpCat.{u + 1} X).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj r.proetale.cocomplex) :=
  (supportedSiteCohomology i U q).map r.transpose

private lemma transpose_f (r : SupportedSiteComparisonResolution F) (n : ℕ) :
    r.transpose.f n = (ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} X).unit.app
      (r.etale.cocomplex.X n) ≫
      (ProEtale.comparisonLowerStar AddCommGrpCat.{u + 1} X).map (r.comparison.f n) := rfl

private lemma transpose_augmentation (r : SupportedSiteComparisonResolution F) :
    r.etale.ι.f 0 ≫ r.transpose.f 0 =
      (ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} X).unit.app F ≫
        (ProEtale.comparisonLowerStar AddCommGrpCat.{u + 1} X).map (r.proetale.ι.f 0) := by
  rw [transpose_f]
  have hn := (ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} X).unit.naturality
    (r.etale.ι.f 0)
  have he := congrArg (fun h ↦ h ≫
    (ProEtale.comparisonLowerStar AddCommGrpCat.{u + 1} X).map (r.comparison.f 0)) hn
  simpa only [CochainComplex.single₀_obj_zero, Functor.id_map, Functor.comp_map,
    Category.assoc, ← Functor.map_comp, r.augmentation] using he

private lemma comparison_quasiIso (r : SupportedSiteComparisonResolution F) :
    QuasiIso r.comparison := by
  let L := ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} X
  let a := (L.mapHomologicalComplex (ComplexShape.up ℕ)).map r.etale.ι
  have : QuasiIso a := by dsimp [a]; infer_instance
  have ha : a ≫ r.comparison =
      (HomologicalComplex.singleMapHomologicalComplex L (ComplexShape.up ℕ) 0).hom.app F ≫
        r.proetale.ι := by
    apply HomologicalComplex.hom_ext
    intro n
    cases n with
    | zero =>
      change L.map (r.etale.ι.f 0) ≫ r.comparison.f 0 =
        𝟙 (L.obj F) ≫ r.proetale.ι.f 0
      simpa only [Category.id_comp] using r.augmentation
    | succ n => simp [a]
  have : QuasiIso (a ≫ r.comparison) := by
    rw [ha]
    infer_instance
  exact quasiIso_of_comp_left a r.comparison

private lemma transpose_quasiIso (r : SupportedSiteComparisonResolution F) :
    QuasiIso r.transpose := by
  let R := ProEtale.comparisonLowerStar AddCommGrpCat.{u + 1} X
  let adj := ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} X
  have := comparison_quasiIso r
  have := R.quasiIso_map_of_rightAcyclic_nat r.comparison
    (fun n ↦ ProEtale.rightAcyclic_comparisonUpperStar_obj_of_injective
      AddCommGrpCat.{u + 1} X (r.etale.cocomplex.X n))
    (fun n ↦ Functor.rightAcyclic_of_injective (F := R) (r.proetale.cocomplex.X n))
  have := ProEtale.isIso_comparisonAdjunction_unit AddCommGrpCat.{u + 1} X
  have (n : ℕ) : IsIso (((adj.mapHomologicalComplex (ComplexShape.up ℕ)).unit.app
      r.etale.cocomplex).f n) := by
    change IsIso (adj.unit.app _)
    infer_instance
  have : IsIso ((adj.mapHomologicalComplex (ComplexShape.up ℕ)).unit.app
      r.etale.cocomplex) := HomologicalComplex.Hom.isIso_of_components _
  change QuasiIso ((adj.mapHomologicalComplex (ComplexShape.up ℕ)).unit.app
    r.etale.cocomplex ≫ (R.mapHomologicalComplex (ComplexShape.up ℕ)).map r.comparison)
  infer_instance

private noncomputable def lowerResolution (r : SupportedSiteComparisonResolution F) :
    InjectiveResolution F where
  cocomplex := ((ProEtale.comparisonLowerStar AddCommGrpCat.{u + 1} X).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj r.proetale.cocomplex
  injective n := by
    have := Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} X)
    exact Functor.injective_obj (ProEtale.comparisonLowerStar AddCommGrpCat.{u + 1} X)
      (r.proetale.cocomplex.X n)
  ι := r.etale.ι ≫ r.transpose
  quasiIso := by
    have := transpose_quasiIso r
    infer_instance

end SupportedSiteComparisonResolution

private lemma supported_map_homotopy (i : Z ⟶ X) [IsClosedImmersion i]
    (U : X.Etale) (q : ℤ)
    {K L : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ}
    {f g : K ⟶ L} (h : Homotopy f g) :
    (supportedSiteCohomology i U q).map f = (supportedSiteCohomology i U q).map g :=
  (((Sheaf.supportedSectionsFunctor X.smallEtaleTopology AddCommGrpCat.{u + 1}
    (supportedSitePair i U).hom).mapHomotopy h).extend
      ComplexShape.embeddingUpNat).homologyMap_eq q

private lemma resolution_hom_isIso {C : Type*} [Category* C] [Abelian C]
    {F : C} {I J : InjectiveResolution F} (a : I.Hom J (𝟙 F))
    (H : C ⥤ AddCommGrpCat.{u + 1}) [H.Additive] (q : ℤ) :
    IsIso (HomologicalComplex.homologyMap
      (HomologicalComplex.extendMap ((H.mapHomologicalComplex (ComplexShape.up ℕ)).map a.hom)
        ComplexShape.embeddingUpNat) q) := by
  let e := InjectiveResolution.homotopyEquiv I J
  let h := InjectiveResolution.descHomotopy (𝟙 F) e.hom a.hom
    (by simp [e]) (by simp)
  let e' := H.mapHomotopyEquiv (e.copy h)
  have he := (HomologicalComplex.homotopyEquivalences_extendMap_iff e'.hom
    ComplexShape.embeddingUpNat).mpr e'.homotopyEquivalences_hom
  have : QuasiIso (HomologicalComplex.extendMap e'.hom ComplexShape.embeddingUpNat) :=
    homotopyEquivalences_le_quasiIso _ _ _ he
  change IsIso (HomologicalComplex.homologyMap
    (HomologicalComplex.extendMap e'.hom ComplexShape.embeddingUpNat) q)
  infer_instance

private noncomputable def supportedSiteRestrictionTrans
    (i : Z ⟶ X) [IsClosedImmersion i] {V U : X.Etale} (g : V ⟶ U) (q : ℤ) :
    supportedSiteCohomology i U q ⟶ supportedSiteCohomology i V q :=
  Functor.whiskerRight
    (NatTrans.mapHomologicalComplex (supportedSiteRestrictionNatTrans i g) (ComplexShape.up ℕ))
    (ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{u + 1} ⋙
      HomologicalComplex.homologyFunctor AddCommGrpCat.{u + 1} (ComplexShape.up ℤ) q)

private lemma supported_coefficient_square
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (f : F ⟶ G)
    (r : SupportedSiteComparisonResolution F) (s : SupportedSiteComparisonResolution G)
    (a : r.etale.Hom s.etale f)
    (b : r.proetale.Hom s.proetale
      ((ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} X).map f))
    (i : Z ⟶ X) [IsClosedImmersion i] (U : X.Etale) (q : ℤ) :
    r.map i U q ≫ (supportedSiteCohomology i U q).map
      (((ProEtale.comparisonLowerStar AddCommGrpCat.{u + 1} X).mapHomologicalComplex
        (ComplexShape.up ℕ)).map b.hom) =
      (supportedSiteCohomology i U q).map a.hom ≫ s.map i U q := by
  let R := ProEtale.comparisonLowerStar AddCommGrpCat.{u + 1} X
  let L := ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} X
  let adj := ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} X
  let t₁ : r.etale.Hom s.lowerResolution f :=
    { hom := r.transpose ≫ (R.mapHomologicalComplex (ComplexShape.up ℕ)).map b.hom
      ι_f_zero_comp_hom_f_zero := by
        change r.etale.ι.f 0 ≫ (r.transpose.f 0 ≫ R.map (b.hom.f 0)) =
          f ≫ (s.etale.ι.f 0 ≫ s.transpose.f 0)
        rw [← Category.assoc, r.transpose_augmentation, s.transpose_augmentation]
        have hb : r.proetale.ι.f 0 ≫ b.hom.f 0 = L.map f ≫ s.proetale.ι.f 0 := by
          exact b.ι_f_zero_comp_hom_f_zero
        calc
          _ = adj.unit.app F ≫ R.map (L.map f) ≫ R.map (s.proetale.ι.f 0) := by
            rw [Category.assoc, ← Functor.map_comp, hb, Functor.map_comp]
          _ = _ := by
            simpa only [Functor.id_map, Functor.comp_map, Category.assoc] using
              congrArg (fun k ↦ k ≫ R.map (s.proetale.ι.f 0))
                (adj.unit.naturality f).symm }
  let t₂ : r.etale.Hom s.lowerResolution f :=
    { hom := a.hom ≫ s.transpose
      ι_f_zero_comp_hom_f_zero := by
        change r.etale.ι.f 0 ≫ (a.hom.f 0 ≫ s.transpose.f 0) =
          f ≫ (s.etale.ι.f 0 ≫ s.transpose.f 0)
        have ha : r.etale.ι.f 0 ≫ a.hom.f 0 = f ≫ s.etale.ι.f 0 := by
          exact a.ι_f_zero_comp_hom_f_zero
        rw [← Category.assoc, ha, Category.assoc] }
  have h := InjectiveResolution.descHomotopy f t₁.hom t₂.hom
    t₁.ι_comp_hom t₂.ι_comp_hom
  change (supportedSiteCohomology i U q).map r.transpose ≫
      (supportedSiteCohomology i U q).map _ =
    (supportedSiteCohomology i U q).map a.hom ≫
      (supportedSiteCohomology i U q).map s.transpose
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact supported_map_homotopy i U q h

set_option maxHeartbeats 1000000 in
-- The four comparison clauses elaborate maps between large site-comparison functors.
/-- Independence of resolutions, invertibility, and naturality in etale objects and
finite-module coefficients of the supported site comparison.
Source: Stacks 099V--099W, comparison unit and acyclicity; 09XP, supported sections
(blueprint: lem-pur-etale-supported-site-comparison-natural).

Proof by comparison of injective resolutions on the etale site:
1. Exactness of comparison inverse image makes the chosen comparison lift a
   quasi-isomorphism, using the augmentation equation and two-out-of-three.
2. Its source terms are acyclic for comparison direct image, as are its injective
   target terms. The acyclic-complex theorem makes its direct image a quasi-isomorphism.
   The adjunction unit is an isomorphism, so the transpose is a quasi-isomorphism.
3. Direct image preserves injectives because its left adjoint is exact. Thus the
   pushed-forward resolution, augmented through the transpose, is an injective resolution
   of the original sheaf. The transpose is a homotopy equivalence of injective resolutions.
   Applying the additive supported-section functor preserves homotopy equivalences,
   proving invertibility on supported cohomology in every integer degree.
4. Two composites associated to coefficient-resolution lifts agree on augmentations.
   Homotopy uniqueness for injective resolutions makes them homotopic. Applying supported
   sections proves coefficient naturality, and the identity case proves independence.
5. Etale restriction is a natural transformation of supported-section functors;
   its naturality at the transpose gives the restriction square.
6. Full support is treated below using the zero group of sections on the empty complement.
Extension by zero preserves the homotopies used here, so all integer degrees are covered. -/
theorem etale_supported_site_comparison_natural
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (i : Z ⟶ X) [IsClosedImmersion i]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    (r : SupportedSiteComparisonResolution
      ((sheafCompose X.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} A)
        AddCommGrpCat.{u + 1})).obj F)) :
    (∀ (s : SupportedSiteComparisonResolution
        ((sheafCompose X.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} A)
          AddCommGrpCat.{u + 1})).obj F))
      (a : InjectiveResolution.Hom r.etale s.etale (𝟙 _))
      (b : InjectiveResolution.Hom r.proetale s.proetale (𝟙 _))
      (U : X.Etale) (q : ℤ),
      IsIso ((supportedSiteCohomology i U q).map a.hom) ∧
      IsIso ((supportedSiteCohomology i U q).map
        (((ProEtale.comparisonLowerStar AddCommGrpCat.{u + 1} X).mapHomologicalComplex
          (ComplexShape.up ℕ)).map b.hom)) ∧
      r.map i U q ≫ (supportedSiteCohomology i U q).map
        (((ProEtale.comparisonLowerStar AddCommGrpCat.{u + 1} X).mapHomologicalComplex
          (ComplexShape.up ℕ)).map b.hom) =
        (supportedSiteCohomology i U q).map a.hom ≫ s.map i U q) ∧
    (∀ (U : X.Etale) (q : ℤ), IsIso (r.map i U q)) ∧
    (∀ {V U : X.Etale} (g : V ⟶ U) (q : ℤ),
      supportedSiteRestriction i g q r.etale.cocomplex ≫ r.map i V q =
        r.map i U q ≫ supportedSiteRestriction i g q
          (((ProEtale.comparisonLowerStar AddCommGrpCat.{u + 1} X).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj r.proetale.cocomplex)) ∧
    (∀ (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) (φ : F ⟶ G)
      (s : SupportedSiteComparisonResolution
        ((sheafCompose X.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} A)
          AddCommGrpCat.{u + 1})).obj G))
      (a : InjectiveResolution.Hom r.etale s.etale
        ((sheafCompose X.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} A)
          AddCommGrpCat.{u + 1})).map φ))
      (b : InjectiveResolution.Hom r.proetale s.proetale
        ((ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} X).map
          ((sheafCompose X.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} A)
            AddCommGrpCat.{u + 1})).map φ)))
      (U : X.Etale) (q : ℤ),
      r.map i U q ≫ (supportedSiteCohomology i U q).map
        (((ProEtale.comparisonLowerStar AddCommGrpCat.{u + 1} X).mapHomologicalComplex
          (ComplexShape.up ℕ)).map b.hom) =
        (supportedSiteCohomology i U q).map a.hom ≫ s.map i U q) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s a b U q
    refine ⟨?_, ?_, ?_⟩
    · exact resolution_hom_isIso a
        (Sheaf.supportedSectionsFunctor X.smallEtaleTopology AddCommGrpCat.{u + 1}
          (supportedSitePair i U).hom) q
    · exact resolution_hom_isIso b
        (ProEtale.comparisonLowerStar AddCommGrpCat.{u + 1} X ⋙
          Sheaf.supportedSectionsFunctor X.smallEtaleTopology AddCommGrpCat.{u + 1}
            (supportedSitePair i U).hom) q
    · let L := ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} X
      let b' : r.proetale.Hom s.proetale
          (L.map (𝟙 ((sheafCompose X.smallEtaleTopology
            (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})).obj F))) :=
        { hom := b.hom
          ι_f_zero_comp_hom_f_zero := by
            rw [CategoryTheory.Functor.map_id]
            exact b.ι_f_zero_comp_hom_f_zero }
      exact supported_coefficient_square (𝟙 _) r s a b' i U q
  · intro U q
    let t : r.etale.Hom r.lowerResolution (𝟙 _) :=
      ⟨r.transpose, by
        change r.etale.ι.f 0 ≫ r.transpose.f 0 =
          𝟙 _ ≫ (r.etale.ι.f 0 ≫ r.transpose.f 0)
        exact (Category.id_comp _).symm⟩
    exact resolution_hom_isIso t
      (Sheaf.supportedSectionsFunctor X.smallEtaleTopology AddCommGrpCat.{u + 1}
        (supportedSitePair i U).hom) q
  · intro V U g q
    exact ((supportedSiteRestrictionTrans i g q).naturality r.transpose).symm
  · intro G φ s a b U q
    exact supported_coefficient_square _ r s a b i U q

/-- Ordinary section-complex cohomology on an etale object, in every integer degree.
For a pro-etale complex use `comparisonLowerStar` to evaluate on the same object.
Source: Stacks 099W, ordinary cohomology comparison
(blueprint: lem-pur-etale-supported-site-comparison-natural). -/
noncomputable def siteSectionCohomology (U : X.Etale) (q : ℤ) :
    CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ ⥤
      AddCommGrpCat.{u + 1} :=
  Functor.mapHomologicalComplex
    ((sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (op U))
    (ComplexShape.up ℕ) ⋙
    ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{u + 1} ⋙
      HomologicalComplex.homologyFunctor AddCommGrpCat.{u + 1} (ComplexShape.up ℤ) q

/-- The inclusion of supported sections into sections over `U`.
Source: Stacks 09XP, inclusion of the kernel into sections
(blueprint: lem-pur-etale-supported-site-comparison-natural). -/
noncomputable def supportedSiteInclusion (i : Z ⟶ X) [IsClosedImmersion i] (U : X.Etale) :
    Sheaf.supportedSectionsFunctor X.smallEtaleTopology AddCommGrpCat.{u + 1}
        (supportedSitePair i U).hom ⟶
      (sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (op U) where
  app F := kernel.ι (F.obj.map (supportedSitePair i U).hom.op)
  naturality F G f := by simp [Sheaf.supportedSectionsFunctor]; rfl

/-- Forgetting support on the chosen resolution, to its ordinary section-complex cohomology.
Source: Stacks 09XP, inclusion of the kernel into sections
(blueprint: lem-pur-etale-supported-site-comparison-natural). -/
noncomputable def supportedSiteForget (i : Z ⟶ X) [IsClosedImmersion i]
    (U : X.Etale) (q : ℤ)
    (K : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ) :
    (supportedSiteCohomology i U q).obj K ⟶
      (siteSectionCohomology U q).obj K :=
  HomologicalComplex.homologyMap
    (HomologicalComplex.extendMap
      ((NatTrans.mapHomologicalComplex
        (supportedSiteInclusion i U) (ComplexShape.up ℕ)).app K)
      ComplexShape.embeddingUpNat) q

private lemma fullSupport_inclusion_isIso (U : X.Etale) :
    IsIso (supportedSiteInclusion (𝟙 X) U) := by
  let : IsEmpty (𝟙 X : X ⟶ X).openComplement.toScheme :=
    ⟨fun x ↦ x.property ⟨x.val, rfl⟩⟩
  let : IsEmpty (Scheme.Etale.mk (𝟙 X : X ⟶ X).openComplement.ι).left :=
    inferInstanceAs (IsEmpty (𝟙 X : X ⟶ X).openComplement.toScheme)
  let : IsEmpty (supportedSitePair (𝟙 X) U).left.left :=
    Function.isEmpty (pullback.fst
      (terminal.from (Scheme.Etale.mk (𝟙 X : X ⟶ X).openComplement.ι))
      (terminal.from U)).left
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro F
  change IsIso (kernel.ι (F.obj.map (supportedSitePair (𝟙 X) U).hom.op))
  exact kernel.ι_of_zero
    ((Scheme.Etale.isTerminalSectionsOfIsEmpty F
      (supportedSitePair (𝟙 X) U).left).isZero.eq_of_tgt _ _)

private noncomputable def supportedSiteForgetNatTrans
    (i : Z ⟶ X) [IsClosedImmersion i] (U : X.Etale) (q : ℤ) :
    supportedSiteCohomology i U q ⟶ siteSectionCohomology U q :=
  Functor.whiskerRight
    (NatTrans.mapHomologicalComplex (supportedSiteInclusion i U) (ComplexShape.up ℕ))
    (ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{u + 1} ⋙
      HomologicalComplex.homologyFunctor AddCommGrpCat.{u + 1} (ComplexShape.up ℤ) q)

private lemma fullSupport_forget_isIso (U : X.Etale) (q : ℤ)
    (K : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ) :
    IsIso (supportedSiteForget (𝟙 X) U q K) := by
  have := fullSupport_inclusion_isIso U
  have : IsIso (NatTrans.mapHomologicalComplex
      (supportedSiteInclusion (𝟙 X) U) (ComplexShape.up ℕ)) :=
    (NatIso.mapHomologicalComplex
      (asIso (supportedSiteInclusion (𝟙 X) U)) (ComplexShape.up ℕ)).isIso_hom
  have : IsIso (supportedSiteForgetNatTrans (𝟙 X) U q) := by
    dsimp only [supportedSiteForgetNatTrans]
    infer_instance
  change IsIso ((supportedSiteForgetNatTrans (𝟙 X) U q).app K)
  infer_instance

/-- For `Z = X`, supported comparison is ordinary global cohomology comparison, under
its canonical identifications by forgetting support.
Source: Stacks 099W, (1), and 09XP, with empty complement
(blueprint: lem-pur-etale-supported-site-comparison-natural).

Proof: the open complement of the identity immersion is empty. A sheaf has zero
sections on that empty etale object. Hence its kernel complex is canonically the
ordinary section complex, so both forget-support maps are isomorphisms. The kernel
inclusion commutes with the adjunction transpose; applying degree-`q` cohomology gives
exactly the displayed unit-induced ordinary comparison. This is step 6 of the node. -/
theorem etale_supported_site_comparison_fullSupport
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    (r : SupportedSiteComparisonResolution
      ((sheafCompose X.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} A)
        AddCommGrpCat.{u + 1})).obj F))
    (U : X.Etale) (q : ℤ) :
    IsIso (supportedSiteForget (𝟙 X) U q r.etale.cocomplex) ∧
    IsIso (supportedSiteForget (𝟙 X) U q
      (((ProEtale.comparisonLowerStar AddCommGrpCat.{u + 1} X).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj r.proetale.cocomplex)) ∧
    r.map (𝟙 X) U q ≫ supportedSiteForget (𝟙 X) U q
      (((ProEtale.comparisonLowerStar AddCommGrpCat.{u + 1} X).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj r.proetale.cocomplex) =
      supportedSiteForget (𝟙 X) U q r.etale.cocomplex ≫
        (siteSectionCohomology U q).map r.transpose := by
  refine ⟨fullSupport_forget_isIso U q _, fullSupport_forget_isIso U q _, ?_⟩
  exact (supportedSiteForgetNatTrans (𝟙 X) U q).naturality r.transpose

end AlgebraicGeometry.Etale
