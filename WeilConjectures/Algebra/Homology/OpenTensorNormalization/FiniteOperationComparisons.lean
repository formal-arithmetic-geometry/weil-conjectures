/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalizationData
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.Algebra.Homology.OpenTensorNormalization.FiniteOpenOrdinaryComparison
import WeilConjectures.Algebra.Homology.OpenTensorNormalization.FiniteTensorTotalComparison
import WeilConjectures.Algebra.Homology.OpenTensorNormalization.FiniteTensorDerivedComparison

/-! # Finite operation comparisons for prescribed realizations

Source: Stacks 03D7, 0F6Z, 06YU and 0GL1.
(blueprint: lem-sf-finite-operation-comparisons)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectionRestriction
namespace SheafOfModules.OpenTensorNormalization

/-- The direct-image part of a finite pullback pin, before taking its mate.
It is an isomorphism fixed by the underlying section identifications.
Source: Stacks 03D7 (blueprint: lem-sf-finite-operation-comparisons). -/
def FiniteDirectPin {A : Type (u + 1)} [CommRing A] {X Y : Scheme.{u}}
    {R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    {S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    {i : (Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of A) ⟶ R.obj}
    {k : (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A) ⟶ S.obj}
    (eR : FiniteRealization A Y R i) (eS : FiniteRealization A X S k)
    (f : X ⟶ Y) (c : R ⟶ ((baseChange .ordinary f).sheafPushforwardContinuous
      CommRingCat.{u + 1} (topology .ordinary Y) (topology .ordinary X)).obj S) : Type _ :=
  { right : ProEtale.lowerStar (ModuleCat.{u + 1} A) f ⋙ eR.equivalence.functor ≅
      eS.equivalence.functor ⋙ direct .ordinary f R S c //
    ∀ (M : FiniteModules A X) (W : Y.ProEtᵒᵖ)
        (x : (eR.equivalence.functor.obj
          ((ProEtale.lowerStar (ModuleCat.{u + 1} A) f).obj M)).val.obj W),
      (eS.underlying.hom.app M).hom.app ((baseChange .ordinary f).op.obj W)
        ((right.hom.app M).val.app W x) =
      (eR.underlying.hom.app ((ProEtale.lowerStar (ModuleCat.{u + 1} A) f).obj M)).hom.app W x }

/-- The proved ordinary part of a finite pullback comparison: its right square,
left-adjoint comparison, and the defining mate equation.
Source: Stacks 03D7 (blueprint: lem-sf-finite-operation-comparisons). -/
structure FiniteOrdinaryPullPin {A : Type (u + 1)} [CommRing A] {X Y : Scheme.{u}}
    {R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    {S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    {i : (Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of A) ⟶ R.obj}
    {k : (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A) ⟶ S.obj}
    (eR : FiniteRealization A Y R i) (eS : FiniteRealization A X S k)
    (f : X ⟶ Y) (c : R ⟶ ((baseChange .ordinary f).sheafPushforwardContinuous
      CommRingCat.{u + 1} (topology .ordinary Y) (topology .ordinary X)).obj S)
    (p : Pullback R S (direct .ordinary f R S c)) where
  right : FiniteDirectPin eR eS f c
  ordinary : ProEtale.upperStar (ModuleCat.{u + 1} A) f ⋙ eS.equivalence.functor ≅
    eR.equivalence.functor ⋙ p.ordinary
  mate : ∀ M : FiniteModules A Y,
    eR.equivalence.functor.map
        ((ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).unit.app M) ≫
      right.val.hom.app ((ProEtale.upperStar (ModuleCat.{u + 1} A) f).obj M) =
    p.adjunction.unit.app (eR.equivalence.functor.obj M) ≫
      (direct .ordinary f R S c).map (ordinary.inv.app M)
  limits : PreservesFiniteLimits p.ordinary
  colimits : PreservesFiniteColimits p.ordinary
  derivedExact : IsIso p.epsilon

private theorem exact_square_model
    {C D B E : Type*} [Category C] [Category D] [Category B] [Category E]
    [Abelian C] [Abelian D] [Abelian B] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory B] [HasDerivedCategory E]
    (F : C ⥤ D) (V : D ⥤ E) (G : C ⥤ B) (H : B ⥤ E)
    [F.Additive] [V.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (c : F ⋙ V ≅ G ⋙ H) (P : CochainComplex C ℤ) :
    (Functor.mapDerivedCategorySquareIso c).hom.app (DerivedCategory.Q.obj P) ≫
      H.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app P) ≫
      H.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj P) =
    V.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
      V.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex c.hom (.up ℤ)).app P) := by
  dsimp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app]
  rw [Category.assoc, Category.assoc,
    Functor.mapDerivedCategoryCompIso_hom_app_factors,
    Functor.mapDerivedCategoryNatIso_fac]
  rw [← Functor.mapDerivedCategoryCompIso_hom_app_factors F V P]
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]

private theorem exact_pullback_comparison
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (L : DerivedCategory C ⥤ DerivedCategory D)
    (epsilon : DerivedCategory.Qh ⋙ L ⟶
      F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [L.IsLeftDerivedFunctor epsilon (HomotopyCategory.quasiIso C (.up ℤ))] :
    ∃ e : F.mapDerivedCategory ≅ L, ∀ P : CochainComplex C ℤ,
      e.hom.app (DerivedCategory.Q.obj P) ≫
        derivedPullbackComplexComparison F L epsilon P =
      F.mapDerivedCategoryFactors.hom.app P := by
  let e := (Functor.leftDerivedUnique F.mapDerivedCategory L
    epsilon F.mapDerivedCategoryFactorsh.hom
    (HomotopyCategory.quasiIso C (.up ℤ))).symm
  have he : Functor.whiskerLeft DerivedCategory.Qh e.hom ≫ epsilon =
      F.mapDerivedCategoryFactorsh.hom := by
    simp [e]
  refine ⟨e, ?_⟩
  intro P
  have hn := e.hom.naturality ((DerivedCategory.quotientCompQhIso C).inv.app P)
  simp only [derivedPullbackComplexComparison]
  rw [← reassoc_of% hn]
  have heP := congrArg (fun t ↦ t.app ((HomotopyCategory.quotient C (.up ℤ)).obj P)) he
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at heP
  rw [reassoc_of% heP, Functor.mapDerivedCategoryFactorsh_hom_app]
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  simp

private theorem finite_pull_pin_exists
    {A : Type (u + 1)} [CommRing A] {X Y : Scheme.{u}}
    {R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    {S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    {i : (Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of A) ⟶ R.obj}
    {k : (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A) ⟶ S.obj}
    (eR : FiniteRealization A Y R i) (eS : FiniteRealization A X S k)
    (f : X ⟶ Y) (c : R ⟶ ((baseChange .ordinary f).sheafPushforwardContinuous
      CommRingCat.{u + 1} (topology .ordinary Y) (topology .ordinary X)).obj S)
    (p : Pullback R S (direct .ordinary f R S c))
    (pin : FiniteOrdinaryPullPin eR eS f c p) :
    ∃ d : finitePull A f ⋙ eS.derived ≅ eR.derived ⋙ p.derived,
      Nonempty (FinitePullPin eR eS f c p d) := by
  let := pin.limits
  let := pin.colimits
  let := p.universal
  obtain ⟨h, hh⟩ := exact_pullback_comparison p.ordinary p.derived p.epsilon
  let a := Functor.mapDerivedCategorySquareIso pin.ordinary
  let d := a ≪≫ Functor.isoWhiskerLeft eR.derived h
  refine ⟨d, ⟨{
    right := pin.right.val
    right_sections := pin.right.property
    ordinary := pin.ordinary
    mate := pin.mate
    model := ?_ }⟩⟩
  intro P
  have hn := h.hom.naturality (eR.equivalence.functor.mapDerivedCategoryFactors.hom.app P)
  dsimp only [d, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app]
  rw [Category.assoc]
  erw [← reassoc_of% hn, hh]
  exact exact_square_model _ _ _ _ pin.ordinary P

private theorem finite_open_pin_exists
    (A : Type (u + 1)) [CommRing A] {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (i : (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A) ⟶ R.obj)
    [Presheaf.IsLocallySurjective (ProEt.topology X) i]
    (eX : FiniteRealization A X R i)
    (eU : FiniteRealization A U (restrictRing .ordinary j R)
      (Functor.whiskerLeft (openInclusion .ordinary j).op i))
    (o : OpenExtension .ordinary j R) :
    ∃ (ds : finiteShriek A j ⋙ eX.derived ≅ eU.derived ⋙ openExtensionDerived o)
      (dr : finitePull A j ⋙ eU.derived ≅
        eX.derived ⋙ (restrictionModel (m := .ordinary) j R).functor),
      Nonempty (FiniteOpenPin j R eX eU o ds dr) := by
  let : HasDerivedCategory (Mod R) := HasDerivedCategory.standard _
  let : HasDerivedCategory (Mod (restrictRing .ordinary j R)) :=
    HasDerivedCategory.standard _
  let : o.ordinary.Additive := o.additive
  let : PreservesFiniteLimits o.ordinary := o.limits
  let : PreservesFiniteColimits o.ordinary := o.colimits
  let : (restrict .ordinary j R).Additive := (restriction_exact .ordinary j R).1
  let : PreservesFiniteLimits (restrict .ordinary j R) :=
    (restriction_exact .ordinary j R).2.1
  let : PreservesFiniteColimits (restrict .ordinary j R) :=
    (restriction_exact .ordinary j R).2.2
  obtain ⟨star, shriek, hs, hu⟩ :=
    finite_open_ordinary_comparison_exists A j R i eX eU o
  let ds := Functor.mapDerivedCategorySquareIso shriek
  let dr := Functor.mapDerivedCategorySquareIso star
  refine ⟨ds, dr, ⟨{
    star := star
    sections := hs
    shriek := shriek
    unit := hu
    models := ?_ }⟩⟩
  constructor
  · intro P
    exact exact_square_model _ _ _ _ shriek P
  · intro P
    exact exact_square_model _ _ _ _ star P

/-- Prescribed realizations and ordinary pullback pins extend to the derived
pullback, open extension and tensor comparisons.

Proof: use the two supplied ordinary pullback comparisons and their mate equations. Fixed
coefficient inverse image is exact. Hence its conjugate through the realization
equivalences is exact, so the ordinary ringed pullback is exact as well.
The universal property of the left derived functor then gives its derived
comparison, and uniqueness on the localization gives the equation on every
complex required by finitePullModel. Apply this argument to g and gU.

For each open, the underlying restriction functors identify by the published
upperStarIsoOpenImmersionRestriction. Lift this sectionwise identification to
module sheaves using scalar compatibility. Its mate under the two extension
by zero adjunctions gives the shriek comparison and the stated unit equation.
Both operations are exact; localizing their termwise comparisons gives the two
FiniteExactPin equations and therefore the open pins.

The module tensor universal property gives the comparison of ordinary tensor
products sending x tensor y to x tensor y under the underlying identifications.
It is invertible because the realizations and their inverses preserve these
bilinear universal properties. Apply it in each bidegree and commute the exact
realization equivalence with the direct sums of the signed total complex.
Naturality in both variables makes the resulting map commute with both parts
of the differential and its sign. This gives the total comparison and its
pure-summand equation. Equivalences of these module categories preserve flat
objects and flat K-flat complexes by the same tensor comparison and exactness.
The two tensor localization factorizations consequently descend the total
comparison to the tensor functor comparison; uniqueness of descent proves the
representative equation in finiteTensorModel. Carry this out on X and U.
Assemble the four original realizations and these eight comparisons, retaining
all six pins. No base-change or projection-arrow equality is used in this
construction; those are conclusions of the separate transport lemma.
Source: Stacks 03D7 (module adjunction), 0F6Z (open restriction), 015F (exact
localization), 06YU and 0GL1 (derived tensor and its open projection map).
(blueprint: lem-sf-finite-operation-comparisons) -/
theorem finite_operation_comparisons_exists (A : Type (u + 1)) [CommRing A]
    [Finite A] {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) (sq : OpenImmersionSquare gU j' j g)
    [IsOpenImmersion j] [IsOpenImmersion j']
    {t : SiteSquare (finiteInput A gU j' j g sq)}
    (o : Operations (finiteInput A gU j' j g sq) t)
    (rX : FiniteRealization A X
      ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj (CommRingCat.of A))
      (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A))))
    (rX' : FiniteRealization A X'
      ((constantSheaf (ProEt.topology X') CommRingCat.{u + 1}).obj (CommRingCat.of A))
      (toSheafify (ProEt.topology X') ((Functor.const X'.ProEtᵒᵖ).obj (CommRingCat.of A))))
    (rU : FiniteRealization A U
      (restrictRing .ordinary j
        ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj (CommRingCat.of A)))
      (Functor.whiskerLeft (openInclusion .ordinary j).op
        (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A)))))
    (rU' : FiniteRealization A U'
      (restrictRing .ordinary j'
        ((constantSheaf (ProEt.topology X') CommRingCat.{u + 1}).obj (CommRingCat.of A)))
      (Functor.whiskerLeft (openInclusion .ordinary j').op
        (toSheafify (ProEt.topology X')
          ((Functor.const X'.ProEtᵒᵖ).obj (CommRingCat.of A)))))
    (pull : FiniteOrdinaryPullPin rX rX' g
      (proEtaleConstantDirectImageMap g CommRingCat.{u + 1} (CommRingCat.of A)) o.gPull)
    (pullU : FiniteOrdinaryPullPin rU rU' gU (cornerCoefficient t) o.gUPull) :
    ∃ e : FiniteComparisons A o, e.realizeX = rX ∧ e.realizeX' = rX' ∧
      e.realizeU = rU ∧ e.realizeU' = rU' := by
  obtain ⟨dg, ⟨pg⟩⟩ := finite_pull_pin_exists rX rX' g _ o.gPull pull
  obtain ⟨dgU, ⟨pgU⟩⟩ := finite_pull_pin_exists rU rU' gU _ o.gUPull pullU
  obtain ⟨sj, rj, ⟨pj⟩⟩ := finite_open_pin_exists A j _ _ rX rU o.opens.extension
  obtain ⟨sj', rj', ⟨pj'⟩⟩ := finite_open_pin_exists A j' _ _ rX' rU' o.opens.extension'
  have : (proEtaleOpenComposition j).IsCocontinuous
      (ProEt.topology U) (ProEt.topology X) :=
    ProEt.isCocontinuous_overMap (inferInstance : WeaklyEtale j)
  have : Presheaf.IsLocallySurjective (ProEt.topology U)
      (Functor.whiskerLeft (openInclusion .ordinary j).op
        (toSheafify (ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A)))) :=
    Presheaf.isLocallySurjective_whisker (ProEt.topology U) (ProEt.topology X)
      (proEtaleOpenComposition j) _
  obtain ⟨totalX, htotalX⟩ := finite_tensor_total_comparison_exists A X _ _ rX
  obtain ⟨tensorX, htensorX⟩ :=
    finite_tensor_derived_comparison_exists A X _ _ rX totalX htotalX o.tensorX
  obtain ⟨totalU, htotalU⟩ := finite_tensor_total_comparison_exists A U _ _ rU
  obtain ⟨tensorU, htensorU⟩ :=
    finite_tensor_derived_comparison_exists A U _ _ rU totalU htotalU o.tensorU
  let a := (ProEtale.upperStar (ModuleCat.{u + 1} A) j).leftDerivedFunctorIsoMapDerivedCategory
  let openPull := Functor.isoWhiskerRight a rU.derived ≪≫ rj
  have hj : Functor.isoWhiskerRight a.symm rU.derived ≪≫ openPull = rj := by
    dsimp only [openPull]
    rw [← Iso.trans_assoc, ← Functor.isoWhiskerRight_trans,
      Iso.symm_self_id, Functor.isoWhiskerRight_refl, Iso.refl_trans]
  refine ⟨{
    realizeX := rX
    realizeX' := rX'
    realizeU := rU
    realizeU' := rU'
    shriek := sj
    shriek' := sj'
    pull := dg
    pullU := dgU
    openPull := openPull
    tensorX := tensorX
    tensorU := tensorU
    openPull' := rj'
    pull_pin := pg
    pullU_pin := pgU
    open_pin := ?_
    open'_pin := pj'
    tensorX_pin := FiniteTensorPin.mk (fun P Q ↦ totalX.app (P, Q)) htotalX htensorX
    tensorU_pin := FiniteTensorPin.mk (fun P Q ↦ totalU.app (P, Q)) htotalU htensorU },
    rfl, rfl, rfl, rfl⟩
  change FiniteOpenPin j _ rX rU _ sj
    (Functor.isoWhiskerRight a.symm rU.derived ≪≫ openPull)
  rw [hj]
  exact pj

end SheafOfModules.OpenTensorNormalization
