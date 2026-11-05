/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteCoefficientDirectImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Triangulated.Functor
public import WeilConjectures.AlgebraicGeometry.CondensedClosedSupportAdjunction

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Mono
import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedSupport
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedCounit
import WeilConjectures.Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import WeilConjectures.Mathlib.CategoryTheory.Sites.Pullback
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import WeilConjectures.CategoryTheory.Triangulated.Recollement
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Category.Grp.Colimits
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic

/-!
# Closed support for arbitrary condensed coefficients

Source: blueprint `sec-smooth-purity/sk-prop-sf-localization`,
`sk-lem-formal-closed-support-adjunction.md` and its proof
(blueprint: det-lem-formal-closed-support-adjunction).

Inverse image uses the canonical coefficient isomorphism and restriction of scalars along
its inverse. This works for noncommutative rings as well. The finite constant-coefficient
kernel construction is generalized to these coefficients, with the same module operations.
-/

@[expose] public section

set_option autoImplicit false

universe u

open scoped CategoryTheory.Obj

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]

/-- The kernel of the canonical open unit, functorially in the module.
Source: blueprint formula for Gamma (blueprint: det-lem-formal-closed-support-adjunction). -/
noncomputable def supportKernel {U X : Scheme.{u}} (j : U ⟶ X) :
    supportModules Λ X ⥤ supportModules Λ X where
  obj M := kernel ((supportPullbackAdjunction Λ j).unit.app M)
  map f := kernel.map _ _ f ((lowerStar Λ j).map ((supportPullback Λ j).map f))
    ((supportPullbackAdjunction Λ j).unit.naturality f).symm
  map_id M := equalizer.hom_ext (by simp)
  map_comp f g := equalizer.hom_ext (by simp)

/-- Kernel inclusion, natural in the module.
Source: blueprint proof Step 5 (blueprint: det-lem-formal-closed-support-adjunction). -/
noncomputable def supportKernelι {U X : Scheme.{u}} (j : U ⟶ X) :
    supportKernel Λ j ⟶ 𝟭 _ where
  app M := kernel.ι _
  naturality M N f := by simp [supportKernel]

/-- The support functor is precisely i* ker(id -> j* j*).
Source: blueprint statement formula (blueprint: det-lem-formal-closed-support-adjunction). -/
noncomputable def closedSupport {Z U X : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X) :
    supportModules Λ X ⥤ supportModules Λ Z :=
  supportKernel Λ j ⋙ supportPullback Λ i

/-- Additivity of the kernel formula.
Source: blueprint proof Step 5 (blueprint: det-lem-formal-closed-support-adjunction).
The induced map on kernels is the restriction of the given module map; restriction commutes
with zero and addition. Inverse image is additive, so the composite is additive. -/
@[instance] theorem closedSupport_additive {Z U X : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X) :
    (closedSupport Λ i j).Additive := by
  have : (supportKernel Λ j).Additive :=
    ⟨equalizer.hom_ext (by simp [supportKernel])⟩
  exact inferInstanceAs ((supportKernel Λ j ⋙ supportPullback Λ i).Additive)

/-- The comparison from the kernel to i* i^* of that kernel, given by the unit.
Source: blueprint proof Step 5 (blueprint: det-lem-formal-closed-support-adjunction). -/
noncomputable def closedSupportKernelComparison {Z U X : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X) :
    supportKernel Λ j ⟶ closedSupport Λ i j ⋙ lowerStar Λ i :=
  Functor.whiskerLeft (supportKernel Λ j) (supportPullbackAdjunction Λ i).unit ≫
    (Functor.associator _ _ _).inv

private theorem supportCounitOfAbelian {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hAb : IsIso (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).counit) :
    IsIso (supportPullbackAdjunction Λ f).counit := by
  let adj := (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).mapModAdjunction
    (condensedRingObj Λ Y)
  have hε (N) : IsIso (adj.counit.app N) := by
    have hh : IsIso ((Mod.forget _).map (adj.counit.app N)) := by
      change IsIso (adj.counit.app N).hom
      dsimp only [adj]
      rw [Adjunction.mapModAdjunction_counit_app_hom]
      infer_instance
    exact isIso_of_reflects_iso _ (Mod.forget _)
  have : IsIso adj.counit := NatIso.isIso_of_isIso_app _
  have ff := adj.fullyFaithfulROfIsIsoCounit
  have he := (supportCoefficientEquivalence Λ f).fullyFaithfulInverse
  have hcomp := he.comp ff
  have hfull := hcomp.ofIso
    ((Functor.associator _ _ _).symm ≪≫ comapPullbackHomCompIso Λ f)
  have := hfull.full
  have := hfull.faithful
  exact (supportPullbackAdjunction Λ f).counit_isIso_of_R_fully_faithful

set_option backward.isDefEq.respectTransparency false in
private theorem supportUnitOfAbelian {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : supportModules Λ Y)
    (hAb : IsIso ((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).unit.app M.X)) :
    IsIso ((supportPullbackAdjunction Λ f).unit.app M) := by
  let adj := (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).mapModAdjunction
    (condensedRingObj Λ Y)
  have hη : IsIso (adj.unit.app M) := by
    have hh : IsIso ((Mod.forget _).map (adj.unit.app M)) := by
      change IsIso (adj.unit.app M).hom
      dsimp only [adj]
      rw [Adjunction.mapModAdjunction_unit_app_hom]
      exact hAb
    exact isIso_of_reflects_iso _ (Mod.forget _)
  have hcomp : IsIso ((adj.comp (supportCoefficientEquivalence Λ f).toAdjunction).unit.app M) := by
    rw [Adjunction.comp_unit_app]
    infer_instance
  change IsIso (((adj.comp (supportCoefficientEquivalence Λ f).toAdjunction).ofNatIsoRight
    ((Functor.associator _ _ _).symm ≪≫ comapPullbackHomCompIso Λ f)).unit.app M)
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app]
  infer_instance

private theorem supportOpenCounit {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    IsIso (supportPullbackAdjunction Λ j).counit := by
  have ff := (ProEtale.openImmersionRestrictionLowerStarAdjunction Ab.{u + 1} j
    ).fullyFaithfulROfIsIsoCounit
  have := ff.full
  have := ff.faithful
  exact supportCounitOfAbelian Λ j
    ((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} j).counit_isIso_of_R_fully_faithful)

/-- Clause (1): the kernel comparison is a natural isomorphism.
Source: blueprint proof Steps 3--5 (blueprint: det-lem-formal-closed-support-adjunction).
Restriction of the open unit is invertible, hence the kernel restricts to zero on U.
The open--closed exact sequence applied to the kernel then identifies it, by its closed
unit, with i* i^* of itself. The coefficient actions lift these abelian-sheaf identities. -/
theorem closedSupportKernelComparison_isIso {Z U X : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ) :
    IsIso (closedSupportKernelComparison Λ i j) := by
  have := supportOpenCounit Λ j
  have hunit (M : supportModules Λ X) :
      IsIso ((supportPullback Λ j).map ((supportPullbackAdjunction Λ j).unit.app M)) := by
    have h := (supportPullbackAdjunction Λ j).left_triangle_components M
    have : IsIso ((supportPullback Λ j).map
        ((supportPullbackAdjunction Λ j).unit.app M) ≫
          (supportPullbackAdjunction Λ j).counit.app ((supportPullback Λ j).obj M)) := by
      rw [h]
      exact IsIso.id _
    exact IsIso.of_isIso_comp_right _
      ((supportPullbackAdjunction Λ j).counit.app ((supportPullback Λ j).obj M))
  have hcomp (M : supportModules Λ X) :
      IsIso ((closedSupportKernelComparison Λ i j).app M) := by
    have hzero : IsZero ((supportPullback Λ j).obj ((supportKernel Λ j).obj M)) :=
      (isZero_kernel_of_mono
        ((supportPullback Λ j).map ((supportPullbackAdjunction Λ j).unit.app M))).of_iso
          (PreservesKernel.iso _ _)
    have habzero := (Mod.forget (condensedRingObj Λ U)).map_isZero hzero
    have hab := (ProEtale.abelian_closed_support_counit_and_unit i j
      (by rw [hij, compl_compl])).2 ((supportKernel Λ j).obj M).X habzero
    have hu := supportUnitOfAbelian Λ i ((supportKernel Λ j).obj M) hab
    simpa only [closedSupportKernelComparison, Functor.whiskerLeft_app,
      NatTrans.comp_app, Functor.associator_inv_app, Category.comp_id] using hu
  exact NatIso.isIso_of_isIso_app _

/-- The support inclusion, obtained from the inverse kernel comparison.
Source: blueprint proof Step 5 (blueprint: det-lem-formal-closed-support-adjunction). -/
noncomputable def closedSupportCounit {Z U X : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ) :
    closedSupport Λ i j ⋙ lowerStar Λ i ⟶ 𝟭 _ :=
  letI := closedSupportKernelComparison_isIso Λ i j hij
  (asIso (closedSupportKernelComparison Λ i j)).inv ≫ supportKernelι Λ j

set_option backward.isDefEq.respectTransparency false in
private theorem supportCrossZero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] {X U Z : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X) [IsOpenImmersion j]
    (hij : Set.range j = (Set.range i)ᶜ)
    (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :
    IsZero ((supportPullback Λ j).obj ((lowerStar Λ i).obj M)) := by
  have hdisjoint : Set.range i.base ∩ Set.range j.base = ∅ := by
    rw [hij]
    exact Set.inter_compl_self _
  have hz : IsZero ((ProEtale.openImmersionRestriction Ab.{u + 1} j).obj
      ((ProEtale.lowerStar Ab.{u + 1} i).obj M.X)) := by
    refine Sheaf.isZero_of_isZero_obj _ ?_
    rintro ⟨T⟩
    let V := (MorphismProperty.Over.pullback @WeaklyEtale ⊤ i).obj
      ((MorphismProperty.Over.map ⊤ (inferInstance : @WeaklyEtale _ _ j)).obj T)
    have hempty : IsEmpty V.left := by
      refine ⟨fun z ↦ ?_⟩
      have hz : (pullback.fst (T.hom ≫ j) i ≫ T.hom ≫ j).base z ∈
          Set.range i.base ∩ Set.range j.base := by
        refine ⟨?_, ⟨T.hom.base (pullback.fst (T.hom ≫ j) i z), ?_⟩⟩
        · rw [pullback.condition]
          exact ⟨_, rfl⟩
        · rfl
      rw [hdisjoint] at hz
      exact hz
    exact (isZero_zero Ab.{u + 1}).of_iso
      ((Scheme.ProEt.isTerminalSectionsOfIsEmpty M.X V).uniqueUpToIso
        HasZeroObject.zeroIsTerminal)
  have hz' : IsZero ((ProEtale.upperStar Ab.{u + 1} j).obj
      ((ProEtale.lowerStar Ab.{u + 1} i).obj M.X)) :=
    hz.of_iso ((ProEtale.upperStarIsoOpenImmersionRestriction Ab.{u + 1} j).app _)
  apply (IsZero.iff_id_eq_zero _).2
  apply (Mod.forget (condensedRingObj Λ U)).map_injective
  exact hz'.eq_of_src _ _

/-- Clause (1): the adjunction with its canonical support inclusion as counit.
Source: blueprint proof Step 5 (blueprint: det-lem-formal-closed-support-adjunction).
A map from i*A to M has zero composite to j*j^*M, by the open adjunction and j^*i*=0.
It factors uniquely through the kernel. Full faithfulness of i* gives a unique A -> H M.
The construction is natural in both variables and its counit is the displayed inclusion.
A fixed counit determines an adjunction, giving the asserted uniqueness. -/
theorem existsUnique_closedSupportAdjunction {Z U X : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ) :
    ∃! adj : lowerStar Λ i ⊣ closedSupport Λ i j,
      adj.counit = closedSupportCounit Λ i j hij := by
  classical
  have := supportCounitOfAbelian Λ i (ProEtale.abelian_closed_support_counit_and_unit i j
    (by rw [hij, compl_compl])).1
  have ff := (supportPullbackAdjunction Λ i).fullyFaithfulROfIsIsoCounit
  have := ff.full
  have := ff.faithful
  have := closedSupportKernelComparison_isIso Λ i j hij
  let ε := closedSupportCounit Λ i j hij
  have hε (M : supportModules Λ X) : Mono (ε.app M) := by
    change Mono ((inv (closedSupportKernelComparison Λ i j)).app M ≫
      kernel.ι ((supportPullbackAdjunction Λ j).unit.app M))
    infer_instance
  have hvanish {B : supportModules Λ Z} {M : supportModules Λ X}
      (f : (lowerStar Λ i).obj B ⟶ M) :
      f ≫ (supportPullbackAdjunction Λ j).unit.app M = 0 := by
    apply ((supportPullbackAdjunction Λ j).homEquiv _ _).symm.injective
    rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
    simp only [Functor.map_comp, Functor.map_zero, zero_comp]
    rw [Category.assoc, Adjunction.left_triangle_components, Category.comp_id]
    exact (supportCrossZero Λ i j (by rw [hij, compl_compl]) B).eq_of_src _ _
  let e (B : supportModules Λ Z) (M : supportModules Λ X) :
      (B ⟶ (closedSupport Λ i j).obj M) ≃ ((lowerStar Λ i).obj B ⟶ M) :=
    Equiv.ofBijective (fun g ↦ (lowerStar Λ i).map g ≫ ε.app M) (by
      constructor
      · intro g h heq
        exact (lowerStar Λ i).map_injective ((cancel_mono (ε.app M)).1 heq)
      · intro f
        refine ⟨(lowerStar Λ i).preimage
          (kernel.lift _ f (hvanish f) ≫ (closedSupportKernelComparison Λ i j).app M), ?_⟩
        simp [ε, closedSupportCounit, supportKernelι, Category.assoc])
  let adj : lowerStar Λ i ⊣ closedSupport Λ i j := Adjunction.mkOfHomEquiv
    { homEquiv := fun B M ↦ (e B M).symm
      homEquiv_naturality_left_symm := by
        intro B' B M f g
        change (lowerStar Λ i).map (f ≫ g) ≫ ε.app M =
          (lowerStar Λ i).map f ≫ ((lowerStar Λ i).map g ≫ ε.app M)
        simp [Functor.map_comp, Category.assoc]
      homEquiv_naturality_right := by
        intro B M N f g
        apply (e B N).injective
        rw [Equiv.apply_symm_apply]
        change f ≫ g = (lowerStar Λ i).map
          ((e B M).symm f ≫ (closedSupport Λ i j).map g) ≫ ε.app N
        have hn := ε.naturality g
        change (lowerStar Λ i).map ((closedSupport Λ i j).map g) ≫ ε.app N =
          ε.app M ≫ g at hn
        rw [Functor.map_comp, Category.assoc, hn]
        have hf := (e B M).apply_symm_apply f
        change (lowerStar Λ i).map ((e B M).symm f) ≫ ε.app M = f at hf
        rw [← Category.assoc, hf] }
  have hadj : adj.counit = ε := by
    apply NatTrans.ext
    funext M
    change (e ((closedSupport Λ i j).obj M) M) (𝟙 _) = ε.app M
    simp [e]
  exact ⟨adj, hadj, fun a ha ↦ Adjunction.ext_counit (ha.trans hadj.symm)⟩

/-- The uniquely counit-normalized support adjunction.
Source: blueprint clause (1) (blueprint: det-lem-formal-closed-support-adjunction). -/
noncomputable def closedSupportAdjunction {Z U X : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ) :
    lowerStar Λ i ⊣ closedSupport Λ i j :=
  Classical.choose (ExistsUnique.exists (existsUnique_closedSupportAdjunction Λ i j hij))

/-- Closed direct image is exact for a quasi-compact open complement, also for
noncommutative coefficient rings.
Source: blueprint proof Steps 3 and 5 (blueprint: det-lem-formal-closed-support-adjunction).
The support adjunction exhibits closed direct image as a left adjoint, so it preserves
colimits, in particular finite colimits. The quasi-compact complement hypothesis is the
one in Stacks, Tag 09BM. -/
theorem closedSupport_lowerStarExact {Z U X : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ) :
    PreservesFiniteColimits (lowerStar Λ i) := by
  have : PreservesColimitsOfSize.{u + 1, u + 1} (lowerStar Λ i) :=
    (closedSupportAdjunction Λ i j hij).leftAdjoint_preservesColimits
  infer_instance

end AlgebraicGeometry.ProEtale.CondensedRing
