/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q106
-/
module

public import Sheaf.Compactification.NagataDensityNormalizationSetup
public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.AlgebraicGeometry.ProEtaleModuleObjects
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.OpenClosed
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.UnitCoherence
import WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormulaAdjunction
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.BaseChange
import Sheaf.AlgebraicGeometry.ProEtaleAbelianClosedSupport

/-! # Extension by zero through the schematic closure

Source: blueprint main-20261015, sec-proetale-coefficients,
`sk-lem-nagata-density-normalization/det-nagata-density-normalization-sheaves.md`.
(blueprint: det-nagata-density-normalization-sheaves).

The base-change inverse is fixed by its adjunction transpose, and the forward
comparison is the specified closed-pullback unit followed by that base change.
The complex and derived clauses use that very morphism, without boundedness.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Pullback composition for the actual schematic-image factorization j = j_Z ; i.
Source: blueprint density-normalization sheaves, base-change clause
(blueprint: det-nagata-density-normalization-sheaves).
This uses the existing coefficient-compatible pullback comparison, so its mate
is the canonical open-extension base change, rather than an arbitrary isomorphism. -/
noncomputable def nagataClosurePullbackComparison {X S : Scheme.{u}} {f : X ⟶ S}
    (c : Compactification f) :
    upperStar Λ c.i ≅ upperStar Λ c.i.imageι ⋙ upperStar Λ c.i.toImage :=
  eqToIso (congrArg (upperStar Λ) c.i.toImage_imageι.symm) ≪≫
    upperStarComp Λ c.i.toImage c.i.imageι

private theorem supportedUnit {Z U Y : Scheme.{u}}
    (i : Z ⟶ Y) [IsClosedImmersion i] (j : U ⟶ Y)
    [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range j = (Set.range i)ᶜ)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (hM : IsZero ((ProEtale.upperStar Ab.{u + 1} j).obj M.X)) :
    IsIso ((upperStarLowerStarAdjunction Λ i).unit.app M) := by
  have hab := (ProEtale.abelian_closed_support i j hij).2 M.X hM
  let N := ((ProEtale.upperStar Ab.{u + 1} i).mapMod (condensedRingObj Λ Y)).obj M
  have he := extendUnitHom_extendScalarsIsoComapInv_hom_app Λ i N
  have : IsIso (Mod.extendUnitHom (condensedPullbackHom Λ i) N ≫
      ((Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ i)).hom.app N).hom) := by
    rw [he]
    infer_instance
  have : IsIso (Mod.extendUnitHom (condensedPullbackHom Λ i) N) :=
    IsIso.of_isIso_comp_right _
      (((Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ i)).hom.app N).hom)
  have hu : ((upperStarLowerStarAdjunction Λ i).unit.app M).hom =
      (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} i).unit.app M.X ≫
        (ProEtale.lowerStar Ab.{u + 1} i).map
          (Mod.extendUnitHom (condensedPullbackHom Λ i) N) := by
    have h := upperStarLowerStarAdjunction_homEquiv_hom Λ i M
      ((upperStar Λ i).obj M) (𝟙 _)
    rw [Adjunction.homEquiv_id, Mod.id_hom'] at h
    erw [Category.comp_id] at h
    exact h
  have : IsIso ((Mod.forget _).map ((upperStarLowerStarAdjunction Λ i).unit.app M)) := by
    change IsIso (((upperStarLowerStarAdjunction Λ i).unit.app M).hom)
    rw [hu]
    infer_instance
  exact isIso_of_reflects_iso _ (Mod.forget _)

private theorem openUnit {U Y : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j] :
    IsIso (openImmersionLowerShriekUpperStarAdjunction Λ j).unit := by
  let ff := (Mod.comapEquivalenceOfIsIso (condensedPullbackHom Λ j)).fullyFaithfulFunctor.comp
    (ProEtale.openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j).fullyFaithfulMapModLeft
  have : (openImmersionLowerShriek Λ j).Full := ff.full
  have : (openImmersionLowerShriek Λ j).Faithful := ff.faithful
  exact Adjunction.unit_isIso_of_L_fully_faithful _

private theorem cartesianCounit {X Y X' Y' : Scheme.{u}}
    {j : X ⟶ Y} {g : Y' ⟶ Y} {j' : X' ⟶ Y'} {g' : X' ⟶ X}
    [IsOpenImmersion j] [IsOpenImmersion j'] (sq : IsPullback g' j' j g)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    IsIso ((openImmersionLowerShriekUpperStarAdjunction Λ j').counit.app
      ((upperStar Λ g).obj ((openImmersionLowerShriek Λ j).obj M))) := by
  let N := (upperStar Λ g).obj ((openImmersionLowerShriek Λ j).obj M)
  let e := upperStarObjXIso Λ g ((openImmersionLowerShriek Λ j).obj M) ≪≫
    ((ProEtale.openImmersionLowerShriekBaseChangeIso Ab.{u + 1} sq).app M.X).symm
  have hAb := (ProEtale.openImmersionLowerShriekUpperStarAdjunction
    Ab.{u + 1} j').isIso_counit_app_of_iso e
  have hlin : IsIso ((linearOpenImmersionLowerShriekAdjunction Λ j').counit.app N) := by
    have : IsIso ((Mod.forget _).map
        ((linearOpenImmersionLowerShriekAdjunction Λ j').counit.app N)) := by
      change IsIso (((ProEtale.openImmersionLowerShriekUpperStarAdjunction
        Ab.{u + 1} j').homEquiv _ N.X).symm (𝟙 _))
      rw [Adjunction.homEquiv_symm_id]
      exact hAb
    exact isIso_of_reflects_iso _ (Mod.forget _)
  let scalar := Mod.restrictCoextendAdjunction (condensedPullbackHom Λ j')
  have ff := Functor.FullyFaithful.ofIso
    (Mod.comapEquivalenceOfIsIso (condensedPullbackHom Λ j')).fullyFaithfulInverse
    ((Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ j')).symm ≪≫
      Mod.extendScalarsIsoCoextendScalars (condensedPullbackHom Λ j'))
  have := ff.full
  have := ff.faithful
  have : IsIso scalar.counit := scalar.counit_isIso_of_R_fully_faithful
  dsimp only [openImmersionLowerShriekUpperStarAdjunction]
  simp only [Adjunction.ofNatIsoRight_counit, NatTrans.comp_app, Functor.whiskerRight_app,
    Adjunction.comp_counit_app]
  infer_instance

private theorem comparisonOfUnits
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {L : C ⥤ D} {A : D ⥤ C} {R : D ⥤ E} {F : E ⥤ D}
    {L' : C ⥤ E} {R' : E ⥤ C}
    (a : L ⊣ A) (a' : L' ⊣ R') (e : A ≅ R ⋙ R')
    (η : 𝟭 D ⟶ R ⋙ F) [IsIso a.unit]
    (hη : ∀ M, IsIso (η.app (L.obj M)))
    (hε : ∀ M, IsIso (a'.counit.app (R.obj (L.obj M)))) :
    ∃ β : L ⋙ R ≅ L',
      (∀ M, β.inv.app M = (a'.homEquiv M (R.obj (L.obj M))).symm
        (a.unit.app M ≫ e.hom.app (L.obj M))) ∧
      ∃ θ : L ≅ L' ⋙ F,
        ∀ M, θ.hom.app M = η.app (L.obj M) ≫ F.map (β.hom.app M) := by
  let t : 𝟭 C ⟶ (L ⋙ R) ⋙ R' := a.unit ≫ Functor.whiskerLeft L e.hom
  let α : L' ⟶ L ⋙ R :=
    { app M := (a'.homEquiv M (R.obj (L.obj M))).symm
        (a.unit.app M ≫ e.hom.app (L.obj M))
      naturality M N φ := by
        apply (a'.homEquiv M ((L ⋙ R).obj N)).injective
        rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
        change φ ≫ (a'.homEquiv N (R.obj (L.obj N)))
            ((a'.homEquiv N (R.obj (L.obj N))).symm
              (a.unit.app N ≫ e.hom.app (L.obj N))) =
          (a'.homEquiv M (R.obj (L.obj M)))
            ((a'.homEquiv M (R.obj (L.obj M))).symm
              (a.unit.app M ≫ e.hom.app (L.obj M))) ≫ R'.map ((L ⋙ R).map φ)
        rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
        exact t.naturality φ }
  have hαiso (M) : IsIso (α.app M) := by
    change IsIso ((a'.homEquiv M ((L ⋙ R).obj M)).symm (t.app M))
    rw [Adjunction.homEquiv_counit]
    have : IsIso (a'.counit.app ((L ⋙ R).obj M)) := hε M
    dsimp only [t, NatTrans.comp_app, Functor.whiskerLeft_app]
    infer_instance
  have : ∀ M, IsIso (α.app M) := hαiso
  have : IsIso α := NatIso.isIso_of_isIso_app α
  let β : L ⋙ R ≅ L' := (asIso α).symm
  let η' : L ⟶ (L ⋙ R) ⋙ F := Functor.whiskerLeft L η
  have : ∀ M, IsIso (η'.app M) := hη
  have : IsIso η' := NatIso.isIso_of_isIso_app η'
  let θ : L ≅ L' ⋙ F := asIso η' ≪≫ Functor.isoWhiskerRight β F
  exact ⟨β, fun _ ↦ rfl, θ, fun _ ↦ rfl⟩

/-- Extension through the schematic closure, with the actual unit, canonical
base change, its natural comparison, and the same map on unbounded complexes and
in the derived category.
Source: blueprint main-20261015, density-normalization sheaves, entire statement
(blueprint: det-nagata-density-normalization-sheaves).

Proof: (1) nagataDensityNormalizationSetup supplies the qcqs schemes, complementary
open V, quasi-compact open j_Z, and Cartesian image square; Noetherian opens make
j and j_V quasi-compact. The condensed coefficients use the standing commutative
convention of the cited module operations. (2) Apply
sheafification_tensor_local_iso and sectionModuleEquivalence to the pulled-back
coefficient rings; internal_module_operations_transport identifies the additive
exact equivalences, operations, and actual adjunction units. (3) Transport
proEtale_openClosed_sequence_ring_sheaf to get exact i_*, j_!, j_Z,! and the
localization sequence 0 -> j_V,! j_V^* N -> N -> i_* i^* N -> 0. Closed pullback
is exact by closed_inverseImage_preserves_limits. (4) Open-extension base change
in the Cartesian image square gives beta; its inverse is the transpose of the
open unit followed by pullback composition, as explicitly normalized below.
(5) Base change to V gives j_V^* j_! M = 0 since X times V is empty. (6) Apply
the localization sequence to j_! M: the actual closed unit is mono and epi in
an abelian category and hence invertible. Compose with i_* beta to get theta,
natural in M. (7) Apply theta in every integer degree. Naturality makes it a
chain map and its inverse a chain map. Localization Q takes this very chain
isomorphism to an isomorphism in the unbounded derived category; equivalently
use exact-functor-derived-factorization and localization-universal-property.
-/
theorem nagataDensityNormalizationSheaves {X S : Scheme.{u}} (f : X ⟶ S)
    (c : Compactification f) [IsNoetherian c.Z]
    [HasDerivedCategory.{w}
      (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology c.Z) Ab.{u + 1})
        (condensedRingObj Λ c.Z))] :
    (∀ M, IsIso ((upperStarLowerStarAdjunction Λ c.i.imageι).unit.app
      ((openImmersionLowerShriek Λ c.i).obj M))) ∧
    ∃ β : openImmersionLowerShriek Λ c.i ⋙ upperStar Λ c.i.imageι ≅
        openImmersionLowerShriek Λ c.i.toImage,
      (∀ M, β.inv.app M =
        ((openImmersionLowerShriekUpperStarAdjunction Λ c.i.toImage).homEquiv M
          ((upperStar Λ c.i.imageι).obj ((openImmersionLowerShriek Λ c.i).obj M))).symm
            ((openImmersionLowerShriekUpperStarAdjunction Λ c.i).unit.app M ≫
              (nagataClosurePullbackComparison Λ c).hom.app
                ((openImmersionLowerShriek Λ c.i).obj M))) ∧
      ∃ θ : openImmersionLowerShriek Λ c.i ≅
          openImmersionLowerShriek Λ c.i.toImage ⋙ lowerStar Λ c.i.imageι,
        (∀ M, θ.hom.app M =
          (upperStarLowerStarAdjunction Λ c.i.imageι).unit.app
              ((openImmersionLowerShriek Λ c.i).obj M) ≫
            (lowerStar Λ c.i.imageι).map (β.hom.app M)) ∧
        ∀ K : CochainComplex
            (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
              (condensedRingObj Λ X)) ℤ,
          IsIso ((NatTrans.mapHomologicalComplex θ.hom (ComplexShape.up ℤ)).app K) ∧
          IsIso (DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex θ.hom (ComplexShape.up ℤ)).app K)) := by
  have hunit (M) : IsIso ((upperStarLowerStarAdjunction Λ c.i.imageι).unit.app
      ((openImmersionLowerShriek Λ c.i).obj M)) := by
    let j := (Scheme.openComplementOfIsClosedImmersion c.i.imageι).ι
    have hij : Set.range j = (Set.range c.i.imageι)ᶜ := Scheme.Opens.range_ι _
    have hd : Disjoint (Set.range c.i.base) (Set.range j.base) := by
      rw [hij]
      apply Set.disjoint_compl_right_iff_subset.mpr
      rintro _ ⟨x, rfl⟩
      exact ⟨c.i.toImage x, congr($(c.i.toImage_imageι) x)⟩
    exact supportedUnit Λ c.i.imageι j hij _
      (ProEtale.isZero_upperStar_openImmersionLowerShriek Ab.{u + 1} c.i j
        (Set.disjoint_iff_inter_eq_empty.mp hd) M.X)
  have sq : IsPullback (𝟙 X) c.i.toImage c.i c.i.imageι :=
    IsPullback.of_horiz_isIso_mono ⟨by simp⟩
  have : IsIso (openImmersionLowerShriekUpperStarAdjunction Λ c.i).unit := openUnit Λ c.i
  obtain ⟨β, hβ, θ, hθ⟩ := comparisonOfUnits
    (openImmersionLowerShriekUpperStarAdjunction Λ c.i)
    (openImmersionLowerShriekUpperStarAdjunction Λ c.i.toImage)
    (nagataClosurePullbackComparison Λ c)
    (upperStarLowerStarAdjunction Λ c.i.imageι).unit hunit (cartesianCounit Λ sq)
  refine ⟨hunit, β, hβ, θ, hθ, ?_⟩
  intro K
  have hK : IsIso ((NatTrans.mapHomologicalComplex θ.hom (ComplexShape.up ℤ)).app K) :=
    ((NatIso.mapHomologicalComplex θ (ComplexShape.up ℤ)).app K).isIso_hom
  exact ⟨hK, Functor.map_isIso _ _⟩

end AlgebraicGeometry.ProEtale.CondensedRing
