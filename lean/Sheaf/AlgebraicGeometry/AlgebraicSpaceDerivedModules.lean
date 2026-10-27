module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex
public import WeilConjectures.AlgebraicGeometry.FiniteTorDimensionOver
public import Sheaf.CategoryTheory.RingedSiteDualityMaps

import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-! # Derived module operations on algebraic spaces

Source: Stacks Project, Derived Categories of Spaces, definition of D_QCoh;
Cohomology on Sites, Tags 079V and 08J7; More on Morphisms of Spaces, Tag 0DKN
(blueprint: def-sfb-space-derived-module-calculus).

The small affine model is equivalent to the original small étale ringed topos.
Direct image is the right derived functor of the original compatible-chart functor,
conjugated by that equivalence. Scheme-chart restriction retains all Zariski sections.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u w wT

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- The unbounded derived category of the small affine model of the existing module topos.
Source: Stacks, Tags 05RU and 03ED (blueprint: def-sfb-space-derived-module-calculus). -/
abbrev DerivedModules {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasDerivedCategory.{w} X.SmallModules] := DerivedCategory X.SmallModules

/-- Quasi-coherent cohomology is tested after the inverse of actual chart restriction.
Source: Stacks, Derived Categories of Spaces, D_QCoh
(blueprint: def-sfb-space-derived-module-calculus). -/
def derivedQCohProperty {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasDerivedCategory.{w} X.SmallModules] : ObjectProperty X.DerivedModules :=
  fun K ↦ ∀ n : ℤ,
    ((X.smallModuleEquivalence.inverse).obj
      ((DerivedCategory.homologyFunctor X.SmallModules n).obj K)).IsQuasicoherent

/-- The full subcategory with quasi-coherent cohomology, not the derived category of QCoh.
Source: Stacks, Derived Categories of Spaces, D_QCoh
(blueprint: def-sfb-space-derived-module-calculus). -/
abbrev DerivedQCoh {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasDerivedCategory.{w} X.SmallModules] := X.derivedQCohProperty.FullSubcategory

/-- The structure sheaf in degree zero.
Source: Stacks, Tag 0E5V (blueprint: def-sfb-space-derived-module-calculus). -/
def derivedStructure {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasDerivedCategory.{w} X.SmallModules] : X.DerivedModules :=
  (DerivedCategory.singleFunctor X.SmallModules 0).obj
    (SheafOfModules.unit X.smallStructureRings)

private lemma selfChartCover {S : Scheme.{u}} (X : AlgebraicSpace S) :
    X.etaleTopology.CoversTop (id : X.EtaleSite → X.EtaleSite) := by
  intro T
  apply GrothendieckTopology.covering_of_eq_top
  apply Sieve.ext
  intro U f
  simp

private def emptyGeneratingSections {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (M : SheafOfModules.{u} R) (hM : IsZero M) : M.GeneratingSections where
  I := PEmpty.{u + 1}
  s i := i.elim
  epi := hM.epi _

private lemma quasiCoherent_of_unitIso {S : Scheme.{u}} (X : AlgebraicSpace S)
    (M : X.Modules) (e : M ≅ SheafOfModules.unit X.structureSheaf) :
    M.IsQuasicoherent := by
  let q : M.QuasicoherentData :=
    { I := X.EtaleSite
      X := id
      coversTop := selfChartCover X
      presentation T := by
        let eT : M.over T ≅ SheafOfModules.unit (X.structureSheaf.over T) :=
          (SheafOfModules.overFunctor X.structureSheaf T).mapIso e
        let d : SheafOfModules.free PUnit.{u + 1} ≅ M.over T :=
          SheafOfModules.freeUniqueIso _ ≪≫ eT.symm
        let g : (M.over T).GeneratingSections :=
          { I := PUnit.{u + 1}
            s := (M.over T).freeHomEquiv d.hom
            epi := by
              rw [Equiv.symm_apply_apply]
              infer_instance }
        have : IsIso g.π := by
          change IsIso ((M.over T).freeHomEquiv.symm ((M.over T).freeHomEquiv d.hom))
          rw [Equiv.symm_apply_apply]
          infer_instance
        exact
          { generators := g
            relations := emptyGeneratingSections _ (isZero_kernel_of_mono g.π) } }
  exact q.isQuasicoherent

private lemma quasiCoherent_of_isZero {S : Scheme.{u}} (X : AlgebraicSpace S)
    (M : X.Modules) (hM : IsZero M) : M.IsQuasicoherent := by
  let q : M.QuasicoherentData :=
    { I := X.EtaleSite
      X := id
      coversTop := selfChartCover X
      presentation T := by
        have : (SheafOfModules.overFunctor X.structureSheaf T).PreservesZeroMorphisms :=
          ⟨by intros; rfl⟩
        let g := emptyGeneratingSections _
          (Functor.map_isZero (SheafOfModules.overFunctor X.structureSheaf T) hM)
        have hF : IsZero (SheafOfModules.free (R := X.structureSheaf.over T) g.I) :=
          (IsZero.iff_id_eq_zero _).mpr
            ((SheafOfModules.freeHomEquiv _).injective (by
              funext i
              exact i.elim))
        exact
          { generators := g
            relations := emptyGeneratingSections _ (IsZero.of_mono (kernel.ι g.π) hF) } }
  exact q.isQuasicoherent

/-- Structure-sheaf cohomology is quasi-coherent, including on the empty space.
Source: Stacks, Tags 03M0 and 0E5V (blueprint: def-sfb-space-derived-module-calculus).
Proof: the only nonzero cohomology is O in degree zero. On every chart it is free
of rank one, and the zero sheaves in the other degrees have the empty presentation.
The restriction equivalence preserves these sheaves and their cohomology. -/
theorem derivedStructure_quasiCoherent {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasDerivedCategory.{w} X.SmallModules] :
    X.derivedQCohProperty X.derivedStructure := by
  intro n
  by_cases hn : n = 0
  · subst n
    let e : (X.smallModuleEquivalence.inverse).obj
        (SheafOfModules.unit X.smallStructureRings) ≅
        SheafOfModules.unit X.structureSheaf :=
      (X.smallModuleEquivalence.inverse).mapIso (Iso.refl _ :
        X.smallModuleRestriction.obj (SheafOfModules.unit X.structureSheaf) ≅
          SheafOfModules.unit X.smallStructureRings).symm ≪≫
        (X.smallModuleEquivalence.unitIso.app _).symm
    exact quasiCoherent_of_unitIso X _
      ((X.smallModuleEquivalence.inverse).mapIso
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso X.SmallModules 0).app
          (SheafOfModules.unit X.smallStructureRings)) ≪≫ e)
  · apply quasiCoherent_of_isZero X
    apply Functor.map_isZero
    exact IsZero.of_iso
      (HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) 0
        (SheafOfModules.unit X.smallStructureRings) n hn)
      ((DerivedCategory.homologyFunctorFactors X.SmallModules n).app
        ((CochainComplex.singleFunctor X.SmallModules 0).obj
          (SheafOfModules.unit X.smallStructureRings)))

/-- The structure sheaf as an object of D_QCoh.
Source: Stacks, Tag 0E5V (blueprint: def-sfb-space-derived-module-calculus). -/
def derivedQCohStructure {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasDerivedCategory.{w} X.SmallModules] : X.DerivedQCoh :=
  ⟨X.derivedStructure, X.derivedStructure_quasiCoherent⟩

/-- The original direct image expressed on the equivalent small module categories.
Source: Stacks, Tags 03G8 and 079V (blueprint: def-sfb-space-derived-module-calculus). -/
def smallModuleDirectImage {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    X.SmallModules ⥤ Y.SmallModules :=
  X.smallModuleEquivalence.inverse ⋙ moduleDirectImage f ⋙ Y.smallModuleRestriction

/-- The compatible-chart direct image and its small-model conjugate are additive.
Source: Stacks, Tags 03G8 and 079V (blueprint: def-sfb-space-derived-module-calculus).
Proof: every chart projection of the sum of module maps is the sum of its projections.
Limit uniqueness therefore proves additivity of direct image. Restriction is sectionwise
additive, and its inverse equivalence preserves the finite biproduct diagrams.
Their composite is consequently additive. -/
@[instance] theorem smallModuleDirectImage_additive
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (smallModuleDirectImage f).Additive := by
  have : X.smallModuleEquivalence.inverse.Additive :=
    Functor.additive_of_preserves_binary_products _
  have : (moduleDirectImage f).Additive :=
    Functor.additive_of_preserves_binary_products _
  have : Y.smallModuleRestriction.Additive := ⟨by intros; rfl⟩
  dsimp only [smallModuleDirectImage]
  infer_instance

/-- K-injective resolutions exist in the small-model module category.
Source: Stacks, Tag 079V (blueprint: def-sfb-space-derived-module-calculus).
Proof: modules on a small ringed site form a Grothendieck abelian category, by the
standard generator and exact filtered-colimit construction. The unbounded K-injective
resolution theorem applies. This is an existence property, not a chosen abelian structure. -/
@[instance] theorem smallModules_hasKInjectiveResolutions
    {S : Scheme.{u}} (X : AlgebraicSpace S) : Abelian.HasKInjectiveResolutions X.SmallModules := by
  have : IsGrothendieckAbelian.{u} X.SmallModules :=
    SheafOfModules.isGrothendieckAbelian X.smallStructureRings
  exact Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian

/-- Canonical unbounded direct image, computed by K-injective resolutions.
Source: Stacks, Tag 079V (blueprint: def-sfb-space-derived-module-calculus). -/
def derivedDirectImage {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [HasDerivedCategory.{w} X.SmallModules] [HasDerivedCategory.{w} Y.SmallModules] :
    X.DerivedModules ⥤ Y.DerivedModules :=
  (smallModuleDirectImage f).rightDerivedFunctor

/-- A presentation of Rf_* on D_QCoh, with its identification with the already fixed
ambient K-injective derived direct image. This supplies no arbitrary replacement functor:
the comparison is part of the data, and identifies every object and map with Rf_*.
Source: Stacks, Tag 0E58 (blueprint: def-sfb-space-derived-module-calculus). -/
structure QCohDirectImagePresentation {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [HasDerivedCategory.{w} X.SmallModules]
    [HasDerivedCategory.{w} Y.SmallModules] where
  /-- The restriction to the full subcategories with quasi-coherent cohomology. -/
  functor : X.DerivedQCoh ⥤ Y.DerivedQCoh
  /-- Its specified identification with the ambient canonical direct image. -/
  comparison : functor ⋙ Y.derivedQCohProperty.ι ≅
    X.derivedQCohProperty.ι ⋙ derivedDirectImage f

/-- The actual restriction to Zariski opens of a scheme chart, on small-model modules.
Source: Stacks, Tags 03G7 and 039Z (blueprint: def-sfb-space-derived-module-calculus). -/
def smallSchemeRestriction {S : Scheme.{u}} (X : AlgebraicSpace S) (T : X.EtaleSite) :
    X.SmallModules ⥤ SheafOfModules.{u} (moduleRings (X.etaleForget.obj T).toRingedSpace) :=
  X.smallModuleEquivalence.inverse ⋙ X.schemeRestriction T

/-- Scheme-chart restriction is additive.
Source: Stacks, Tags 03G7 and 03M0 (blueprint: def-sfb-space-derived-module-calculus).
Proof: restriction takes the given sectionwise sums of linear maps to those same sums.
The inverse small-model equivalence is additive because it preserves biproducts. -/
@[instance] theorem smallSchemeRestriction_additive {S : Scheme.{u}} (X : AlgebraicSpace S)
    (T : X.EtaleSite) : (smallSchemeRestriction X T).Additive := by
  have : X.smallModuleEquivalence.inverse.Additive :=
    Functor.additive_of_preserves_binary_products _
  have : (X.schemeRestriction T).Additive := ⟨by intros; rfl⟩
  constructor
  intro M N a b
  change (X.schemeRestriction T).map
      (X.smallModuleEquivalence.inverse.map (a + b)) = _
  rw [Functor.map_add, Functor.map_add]
  rfl

/-- Derived Zariski restriction on a scheme chart. The right derived functor is essential:
restriction from the étale topos to the Zariski topos is not exact on arbitrary modules.
On quasi-coherent cohomology it is the usual Zariski/étale comparison.
Source: Stacks, Tags 03G7 and 079V (blueprint: def-sfb-space-derived-module-calculus). -/
def derivedSchemeRestriction {S : Scheme.{u}} (X : AlgebraicSpace S) (T : X.EtaleSite)
    [HasDerivedCategory.{w} X.SmallModules]
    [HasDerivedCategory.{wT}
      (SheafOfModules.{u} (moduleRings (X.etaleForget.obj T).toRingedSpace))]
    (K : X.DerivedModules) : schemeDerivedCategory (X.etaleForget.obj T) :=
  (smallSchemeRestriction X T).rightDerivedFunctor.obj K

/-- The structure morphism of a scheme chart over a representable target.
Source: Stacks, Tag 0DKN (blueprint: def-sfb-space-derived-module-calculus). -/
def chartToScheme {S : Scheme.{u}} {X : AlgebraicSpace S} (Y : Over S)
    (f : X ⟶ schemeSpace Y) (T : X.EtaleSite) : X.etaleForget.obj T ⟶ Y.left :=
  (yoneda.preimage (T.obj.hom ≫ f.hom.hom)).left

/-- The internal derived Hom is the existing K-injective Hom on the equivalent small site.
Source: Stacks, Tag 08J7 (blueprint: def-sfb-space-derived-module-calculus). -/
def derivedHom {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasDerivedCategory.{w} X.SmallModules] :
    X.DerivedModulesᵒᵖ × X.DerivedModules ⥤ X.DerivedModules :=
  derivedInternalHomOfUniverses.{u, u, u, w}
    X.smallEtaleModelTopology X.smallStructureSheaf

/-- The normalized closed tensor-Hom model on the small site.
Source: Stacks, Tags 08JD and 0A98 (blueprint: def-sfb-space-derived-module-calculus). -/
def derivedDualityModel {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasDerivedCategory.{w} X.SmallModules] :
    RingedSiteDualityModel.{u, u, u, w}
      X.smallEtaleModelTopology X.smallStructureSheaf :=
  Classical.choice (ringedSiteDualityMaps_exists.{u, u, u, w} _ _)

/-- Scalar multiplication, the transpose of the ordinary normalized left unitor.
Source: Stacks, Tag 0E5V(3) (blueprint: def-sfb-space-derived-module-calculus). -/
def derivedScalarEndomorphism {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasDerivedCategory.{w} X.SmallModules] (K : X.DerivedModules) :
    X.derivedStructure ⟶ X.derivedHom.obj (op K, K) :=
  (X.derivedDualityModel.closed).transpose _ K K
    ((X.derivedDualityModel.closed.tensor).map
      (Prod.mkHom X.derivedDualityModel.unitIso.inv (𝟙 K)) ≫
      (X.derivedDualityModel.closed.monoidal.leftUnitor K).hom)

end AlgebraicGeometry.AlgebraicSpace
