/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Sheaf.Compactification.BoundaryRefinement
public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.Paper.ConstantModelTorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.AlgebraicGeometry.ProEtaleOpenClosedDetection
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.CategoryTheory.Triangulated.LocalizingIsoLocus
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.Paper.ProfinitePointPullback
import all Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeMono
import Sheaf.Paper.CompactificationLocalizing
import Sheaf.Paper.CondensedModuleDerivedPushpull
import Sheaf.Paper.FiniteProperBaseChange
import Sheaf.Paper.IntegralProperBaseChange
import Sheaf.Paper.ProperBaseChangeRational

/-!
# Compactification refinement on the ambient localizing category

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-sf-comp-coherence,
det-sf-comp-coherence-refinement; Stacks Project, Tags 09AH, 08BJ, 015F and 0D6E
(blueprint: det-sf-comp-coherence-refinement).

The restriction comparison is the canonical counit mate of pullback composition.
Its inverse, followed by the open adjunction, defines the refinement map on the entire
unbounded module-object derived category. Only its invertibility is restricted to Loc(Dctf).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false in
private theorem restrictionMate_isIso
    {A B C : Type*} [Category A] [Category B] [Category C]
    {J : A ⥤ B} {U : B ⥤ A} {H : B ⥤ C} {R : C ⥤ B}
    {J' : A ⥤ C} {U' : C ⥤ A}
    (a : J ⊣ U) (b : H ⊣ R) (c : J' ⊣ U')
    (e : U ≅ H ⋙ U') [IsIso a.unit]
    (hc : ∀ K : A, IsIso (c.counit.app (H.obj (J.obj K)))) :
    IsIso (Functor.whiskerLeft R e.hom ≫ (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight b.counit U' ≫ (Functor.leftUnitor _).hom) := by
  let ρ : R ⋙ U ⟶ U' := Functor.whiskerLeft R e.hom ≫
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight b.counit U' ≫
    (Functor.leftUnitor _).hom
  have hcomp (K : A) :
      ((conjugateEquiv (a.comp b) c).symm ρ).app K =
        J'.map (a.unit.app K ≫ e.hom.app (J.obj K)) ≫
          c.counit.app (H.obj (J.obj K)) := by
    have hinner : U.map (b.unit.app (J.obj K)) ≫
        e.hom.app (R.obj (H.obj (J.obj K))) ≫
          U'.map (b.counit.app (H.obj (J.obj K))) = e.hom.app (J.obj K) := by
      have hn := e.hom.naturality (b.unit.app (J.obj K))
      dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
      rw [← Category.assoc, hn, Category.assoc]
      simp only [← U'.map_comp, b.left_triangle_components,
        Functor.map_id, Category.comp_id]
    simp only [conjugateEquiv_symm_apply_app, Adjunction.comp_unit_app,
      ρ, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.associator_inv_app, Functor.whiskerRight_app,
      Functor.leftUnitor_hom_app, Functor.comp_obj, Category.id_comp,
      Functor.map_comp, Category.assoc]
    erw [CategoryTheory.Functor.map_id]
    simp only [Category.id_comp]
    simpa only [Functor.map_comp, Category.assoc] using
      congrArg (fun z ↦ J'.map (a.unit.app K) ≫ J'.map z ≫
        c.counit.app (H.obj (J.obj K))) hinner
  have hσ : IsIso ((conjugateEquiv (a.comp b) c).symm ρ) := by
    have hσapp (K : A) : IsIso (((conjugateEquiv (a.comp b) c).symm ρ).app K) := by
      rw [hcomp]
      have := hc K
      infer_instance
    exact NatIso.isIso_of_isIso_app _
  exact conjugateEquiv_symm_of_iso (a.comp b) c ρ

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The identity direct-image identification is linear for the pulled-back coefficient ring.
Source: blueprint refinement clause (3), canonical identity identifications
(blueprint: det-sf-comp-coherence-refinement).
Proof: expand the action on lowerStar; condensedPushforwardHom_id is the inverse identity
identification on the coefficient ring. Naturality and the tensor identity of the abelian
identity compositor cancel this inverse, leaving exactly the action of M. -/
theorem refinementLowerStarId_linear (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    Mod.act (((lowerStar Λ (𝟙 X)).obj M).X) ≫
        (ProEtale.lowerStarId Ab.{u + 1} X).hom.app M.X =
      (condensedRingObj Λ X) ◁ (ProEtale.lowerStarId Ab.{u + 1} X).hom.app M.X ≫
        Mod.act M.X := by
  obtain ⟨e, he, _⟩ := existsUnique_profinitePointModuleDirectImageIdentity Λ X
  have h := Mod.act_hom (e.hom.app M)
  change _ ≫ (e.hom.app M).hom = _ ◁ (e.hom.app M).hom ≫ _ at h
  change ∀ M, (e.hom.app M).hom = _ at he
  rw [he M] at h
  exact h

/-- The linear identity components are natural.
Source: blueprint refinement clause (3), canonical identity identifications
(blueprint: det-sf-comp-coherence-refinement).
Proof: apply the faithful module forgetful functor. Both sides become the naturality
square of ProEtale.lowerStarId on the underlying abelian-sheaf morphism. -/
theorem refinementLowerStarId_naturality (X : Scheme.{u})
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (v : M ⟶ N) :
    (lowerStar Λ (𝟙 X)).map v ≫
        (Mod.isoMk ((ProEtale.lowerStarId Ab.{u + 1} X).app N.X)
          (refinementLowerStarId_linear Λ X N)).hom =
      (Mod.isoMk ((ProEtale.lowerStarId Ab.{u + 1} X).app M.X)
          (refinementLowerStarId_linear Λ X M)).hom ≫ v := by
  apply Mod.hom_ext
  exact (ProEtale.lowerStarId Ab.{u + 1} X).hom.naturality v.hom

/-- The canonical identity direct-image isomorphism, with its actual abelian-sheaf components.
Source: blueprint refinement clause (3)
(blueprint: det-sf-comp-coherence-refinement). -/
def refinementLowerStarId (X : Scheme.{u}) : lowerStar Λ (𝟙 X) ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun M ↦ Mod.isoMk ((ProEtale.lowerStarId Ab.{u + 1} X).app M.X)
      (refinementLowerStarId_linear Λ X M))
    (fun v ↦ refinementLowerStarId_naturality Λ X v)

/-- The canonical derived identity identification, obtained by deriving the identity
identification on module sheaves. Source: blueprint refinement clause (3)
(blueprint: det-sf-comp-coherence-refinement). -/
def refinementDerivedLowerStarId (X : Scheme.{u}) :
    (lowerStar Λ (𝟙 X)).rightDerivedFunctor ≅ 𝟭 _ :=
  Functor.rightDerivedFunctorNatIso (refinementLowerStarId Λ X) ≪≫
    (𝟭 _).rightDerivedFunctorIsoMapDerivedCategory ≪≫ Functor.mapDerivedCategoryIdIso _

/-- The canonical unbounded derived direct-image compositor, normalized by the underived
module compositor and the K-injective derived-functor units. Source: blueprint refinement
clause (3); Stacks Tag 0D6E (blueprint: det-sf-comp-coherence-refinement). -/
def refinementDerivedLowerStarComp {X Y Z : Scheme.{u}} (a : X ⟶ Y) (h : Y ⟶ Z) :
    (lowerStar Λ (a ≫ h)).rightDerivedFunctor ≅
      (lowerStar Λ a).rightDerivedFunctor ⋙ (lowerStar Λ h).rightDerivedFunctor :=
  letI := (upperStarLowerStarAdjunction Λ a).preservesKInjectiveComplexes
  Functor.rightDerivedFunctorNatIso (lowerStarComp Λ a h).symm ≪≫
    Functor.rightDerivedFunctorCompIso (lowerStar Λ a) (lowerStar Λ h)

/-- Open extension followed by open restriction has its invertible canonical unit, also on
unbounded complexes. Source: blueprint refinement proof step 1; Stacks Tags 09AH and 015F
(blueprint: det-sf-comp-coherence-refinement).
Proof: the sheaf open adjunction has invertible unit, since restriction of extension by
zero is the original module with the same action. Both functors are exact. Descend their
termwise unit and counit through quasi-isomorphisms; the triangle identities and inverse
unit descend too. This is the derived adjunction used here. -/
theorem refinementOpenUnit_isIso {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    IsIso (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).unit := by
  let a₀ := ProEtale.openImmersionLowerShriekAdjunction Ab.{u + 1} j
  have : IsIso a₀.unit :=
    (ProEtale.openImmersionAdjunctionTriple Ab.{u + 1} j).isIso_unit_iff_isIso_counit.mpr
      (ProEtale.isIso_openImmersionRestrictionLowerStarAdjunction_counit Ab.{u + 1} j)
  have ff₀ := a₀.fullyFaithfulLOfIsIsoUnit
  have := ff₀.full
  have := ff₀.faithful
  have hu : IsIso (ProEtale.openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j).unit :=
    Adjunction.unit_isIso_of_L_fully_faithful _
  have hlin : IsIso (linearOpenImmersionLowerShriekAdjunction Λ j).unit := by
    have hlinapp (M) : IsIso ((linearOpenImmersionLowerShriekAdjunction Λ j).unit.app M) := by
      have hh : IsIso ((Mod.forget _).map
          ((linearOpenImmersionLowerShriekAdjunction Λ j).unit.app M)) := by
        dsimp [linearOpenImmersionLowerShriekAdjunction, Adjunction.mapModLeftAdjunction,
          Adjunction.mkOfHomEquiv, Adjunction.mk', Mod.forget, Mod.Hom.mk']
        rw [Adjunction.homEquiv_unit]
        simp only [Mod.id_hom']
        erw [CategoryTheory.Functor.map_id, Category.comp_id]
        infer_instance
      exact isIso_of_reflects_iso _ (Mod.forget _)
    exact NatIso.isIso_of_isIso_app _
  have ff := (linearOpenImmersionLowerShriekAdjunction Λ j).fullyFaithfulLOfIsIsoUnit
  have := ff.full
  have := ff.faithful
  have : (Mod.comap (condensedPullbackHom Λ j)).Full :=
    (Mod.comapEquivalenceOfIsIso (condensedPullbackHom Λ j)).fullyFaithfulFunctor.full
  have : (Mod.comap (condensedPullbackHom Λ j)).Faithful :=
    (Mod.comapEquivalenceOfIsIso (condensedPullbackHom Λ j)).fullyFaithfulFunctor.faithful
  have : (openImmersionLowerShriek Λ j).Full :=
    inferInstanceAs ((Mod.comap (condensedPullbackHom Λ j)) ⋙
      linearOpenImmersionLowerShriek Λ j).Full
  have : (openImmersionLowerShriek Λ j).Faithful :=
    inferInstanceAs ((Mod.comap (condensedPullbackHom Λ j)) ⋙
      linearOpenImmersionLowerShriek Λ j).Faithful
  have := (openImmersionLowerShriekUpperStarAdjunction Λ j).unit_isIso_of_L_fully_faithful
  exact Adjunction.isIso_mapDerivedCategoryAdjunction_unit
    (openImmersionLowerShriekUpperStarAdjunction Λ j)

attribute [instance] refinementOpenUnit_isIso

/-- The canonical restriction map j* Rh* M → j'* M: pullback composition, followed by the
counit of Lh* ⊣ Rh*. The commuting open triangle fixes every coefficient identification.
Source: blueprint refinement, The restriction to X, proof steps 1--2
(blueprint: det-sf-comp-coherence-refinement). -/
def refinementOpenRestriction {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : d.Refinement c) :
    (lowerStar Λ r.hom).rightDerivedFunctor ⋙ (upperStar Λ c.i).mapDerivedCategory ⟶
      (upperStar Λ d.i).mapDerivedCategory :=
  Functor.whiskerLeft (lowerStar Λ r.hom).rightDerivedFunctor
      (Functor.mapDerivedCategoryNatIso
        (eqToIso (congrArg (upperStar Λ) r.i_hom.symm) ≪≫ upperStarComp Λ d.i r.hom) ≪≫
        Functor.mapDerivedCategoryCompIso (upperStar Λ r.hom) (upperStar Λ d.i)).hom ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (Functor.whiskerLeft (lowerStar Λ r.hom).rightDerivedFunctor
          (leftDerivedUpperStarIsoMapDerivedCategory Λ r.hom).inv ≫
        (derivedUpperStarLowerStarAdjunction Λ r.hom).counit)
      (upperStar Λ d.i).mapDerivedCategory ≫
    (Functor.leftUnitor _).hom

set_option backward.isDefEq.respectTransparency false in
/-- For a boundary-preserving refinement the specified restriction map is invertible on
all unbounded complexes; no proper base change for arbitrary complexes is assumed.
Source: blueprint refinement, The restriction to X, proof step 2
(blueprint: det-sf-comp-coherence-refinement).
Proof: choose a K-injective resolution I of M. Over V → X, the inverse-image-open equality
identifies V ×_Z Z' with V, hence j* h* I = j'* I sectionwise, including the coefficient
action. The counit mate defining refinementOpenRestriction is exactly this identification.
Restriction is exact, and j'* preserves K-injectives because j'! is its exact left adjoint.
Thus the sectionwise identity represents the stated map in the unbounded derived category,
and is invertible. Functorial resolutions give naturality and independence of I. -/
theorem refinementOpenRestriction_isIso {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification.BoundaryCompactification f} (r : d ⟶ c) :
    IsIso (refinementOpenRestriction Λ r.hom.hom) := by
  have sq : IsPullback (𝟙 X) d.obj.obj.i c.obj.obj.i r.hom.hom.hom :=
    IsOpenImmersion.isPullback _ _ _ _
      (by simpa only [Category.id_comp] using r.hom.hom.i_hom) r.property
  let a := derivedOpenImmersionLowerShriekUpperStarAdjunction Λ c.obj.obj.i
  let b := (derivedUpperStarLowerStarAdjunction Λ r.hom.hom.hom).ofNatIsoLeft
    (leftDerivedUpperStarIsoMapDerivedCategory Λ r.hom.hom.hom)
  let a' := derivedOpenImmersionLowerShriekUpperStarAdjunction Λ d.obj.obj.i
  let e := Functor.mapDerivedCategoryNatIso
      (eqToIso (congrArg (upperStar Λ) r.hom.hom.i_hom.symm) ≪≫
        upperStarComp Λ d.obj.obj.i r.hom.hom.hom) ≪≫
    Functor.mapDerivedCategoryCompIso (upperStar Λ r.hom.hom.hom)
      (upperStar Λ d.obj.obj.i)
  have : IsIso a.unit := refinementOpenUnit_isIso Λ c.obj.obj.i
  have hc (K) : IsIso (a'.counit.app
      ((upperStar Λ r.hom.hom.hom).mapDerivedCategory.obj
        ((openImmersionLowerShriek Λ c.obj.obj.i).mapDerivedCategory.obj K))) := by
    have hbase := cartesianDerivedCounit Λ sq K
    let eK := (Functor.mapDerivedCategoryCompIso
      (openImmersionLowerShriek Λ c.obj.obj.i) (upperStar Λ r.hom.hom.hom)).app K
    exact (NatTrans.isIso_app_iff_of_iso _ eK).mp hbase
  have hi := CategoryTheory.restrictionMate_isIso a b a' e hc
  simpa only [refinementOpenRestriction, e, b, Adjunction.ofNatIsoLeft_counit] using hi

/-- The canonical θ_h,K: restriction of Rh*j'!K to X, then the inverse open unit.
Source: blueprint refinement, displayed θ (blueprint: det-sf-comp-coherence-refinement). -/
def refinementTheta {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification.BoundaryCompactification f} (r : d ⟶ c)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    (upperStar Λ c.obj.obj.i).mapDerivedCategory.obj
        ((lowerStar Λ r.hom.hom.hom).rightDerivedFunctor.obj
          ((openImmersionLowerShriek Λ d.obj.obj.i).mapDerivedCategory.obj K)) ≅ K :=
  letI := refinementOpenRestriction_isIso Λ r
  asIso ((refinementOpenRestriction Λ r.hom.hom).app
      ((openImmersionLowerShriek Λ d.obj.obj.i).mapDerivedCategory.obj K)) ≪≫
    (asIso ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ d.obj.obj.i).unit.app K)).symm

/-- The refinement map is the adjoint of θ⁻¹, with no choice of an arbitrary isomorphism.
Source: blueprint refinement, displayed e and clause (1)
(blueprint: det-sf-comp-coherence-refinement). -/
def localizingRefinementMap {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification.BoundaryCompactification f} (r : d ⟶ c)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    (openImmersionLowerShriek Λ c.obj.obj.i).mapDerivedCategory.obj K ⟶
      (lowerStar Λ r.hom.hom.hom).rightDerivedFunctor.obj
        ((openImmersionLowerShriek Λ d.obj.obj.i).mapDerivedCategory.obj K) :=
  ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ c.obj.obj.i).homEquiv _ _).symm
    (refinementTheta Λ r K).inv

/-- Uniqueness, invertibility on Loc(Dctf), and identity/composition for the canonical
refinement maps. Uniqueness and coherence hold for arbitrary unbounded K.
Source: blueprint main-20261015, det-sf-comp-coherence-refinement, clauses (1)--(3)
(blueprint: det-sf-comp-coherence-refinement).

Proof, following all nine node steps:
1. Cartesian coefficients make immersion pullbacks exact. The ringed open/closed
localization supplies exact extension by zero, its adjunction, invertible unit, and
closed restriction zero. Descend the exact termwise adjunction to derived categories.
2. On a K-injective resolution, restriction of h* is restriction to V ×_Z Z' = V over X.
This respects coefficients; exact restriction and preservation of K-injectives by the
right adjoint of j'! give refinementTheta, independent of resolutions.
3. The adjunction followed by θ identifies maps j!K → Rh*j'!K with End(K). The identity
has exactly one preimage, localizingRefinementMap. Naturality and compatibility with
shifts follow from the same termwise construction and the adjunction bijection.
4. Apply det-sf-comp-coherence-single to the compactifications (j,id) and (j',h) of j:
the two functors are exact and preserve ambient sums on Loc(Dctf). The same result
for j' gives j'!K in Dctf on generators. Quasi-compact open immersions are finite type.
5. On a generator, restrict to the closed complement and its pullback. Both extensions
by zero vanish there. Proper base change gives closed restriction of Rh*j'!K zero:
use the finite, integral, or rational coefficient theorem, respectively. Dctf lies in Dbc;
Z_l and Q_l are the valuation/field cases of the degree-one extension.
6. A cone of the comparison has zero open restriction by step 3 and zero closed
restriction by step 5. Exact restriction commutes with cohomology. Open/closed detection
on each module cohomology sheaf makes the cone acyclic, hence the comparison invertible.
7. det-sf-determination-localizing extends the isomorphism locus from the generators to
Loc(Dctf), since the functors are exact, sum preserving, and the map commutes with shifts.
8. The canonical derived compositor is normalized on K-injectives by the underived
module compositor and derived-functor units. On X those maps are sectionwise identities,
so it identifies the composite restriction comparisons with the restriction of ha.
9. For identity refinement the canonical identity has identity restriction. For successive
refinements, the composite is proper and boundary preserving; the transported composite
map also has identity restriction by step 8. Uniqueness from step 3 proves both equations.
The equations in step 9 require no boundedness or membership in the localizing closure. -/
theorem localizingRefinement_coherence
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    (p : ℕ) [CharP k p] (_hp : 0 < p) (_hpℓ : p ≠ ℓ)
    (_hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    (∀ (c d : Compactification.DenseBoundaryCompactification f) (r : d ⟶ c)
      (K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))),
      ∀ b : (openImmersionLowerShriek Λ c.obj.obj.obj.i).mapDerivedCategory.obj K ⟶
        (lowerStar Λ r.hom.hom.hom.hom).rightDerivedFunctor.obj
          ((openImmersionLowerShriek Λ d.obj.obj.obj.i).mapDerivedCategory.obj K),
        (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ c.obj.obj.obj.i).unit.app K ≫
            (upperStar Λ c.obj.obj.obj.i).mapDerivedCategory.map b ≫
              (refinementTheta Λ r.hom K).hom = 𝟙 K ↔
          b = localizingRefinementMap Λ r.hom K) ∧
    (∀ (c d : Compactification.DenseBoundaryCompactification f) (r : d ⟶ c)
      (K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))),
      localizingClosureProEtale Λ X K → IsIso (localizingRefinementMap Λ r.hom K)) ∧
    (∀ (c : Compactification.DenseBoundaryCompactification f)
      (K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))),
      localizingRefinementMap Λ (𝟙 c.obj) K ≫
          (refinementDerivedLowerStarId Λ c.obj.obj.obj.Z).hom.app
            ((openImmersionLowerShriek Λ c.obj.obj.obj.i).mapDerivedCategory.obj K) = 𝟙 _) ∧
    (∀ (c d e : Compactification.DenseBoundaryCompactification f)
      (r : d ⟶ c) (s : e ⟶ d)
      (K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))),
      localizingRefinementMap Λ (s ≫ r).hom K ≫
          (refinementDerivedLowerStarComp Λ s.hom.hom.hom.hom r.hom.hom.hom.hom).hom.app
            ((openImmersionLowerShriek Λ e.obj.obj.obj.i).mapDerivedCategory.obj K) =
        localizingRefinementMap Λ r.hom K ≫
          (lowerStar Λ r.hom.hom.hom.hom).rightDerivedFunctor.map
            (localizingRefinementMap Λ s.hom K)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
