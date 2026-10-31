/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.RingedSectionLocalizationOfUniversesSupplement
public import WeilConjectures.AlgebraicGeometry.FlatRingedIdealCompleteEquivalenceSupplement
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebra
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.InverseImageScalarRestrictionComparison
import WeilConjectures.CategoryTheory.FixedPairCreatedAbelianStructure
import all WeilConjectures.CategoryTheory.RingedEquivalenceModuleHom
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import Mathlib.Algebra.Category.Ring.Limits
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.RingedToposMorphismSupplement
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod

import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import all WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Types.Basic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import all Mathlib.LinearAlgebra.TensorProduct.Vanishing
import all Mathlib.RingTheory.TensorProduct.DirectLimitFG
import all Mathlib.LinearAlgebra.TensorProduct.Finiteness
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Mathlib.CategoryTheory.Sites.Limits
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Mathlib.CategoryTheory.Limits.Types.Pullbacks
import all Mathlib.CategoryTheory.Functor.EpiMono
import all Mathlib.CategoryTheory.Limits.Types.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.Additive
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import all WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.RingTheory.Flat.CategoryTheory
import all Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.AlgebraicGeometry.RingedTopoiCanonicalTensorPullbackUnitExistence
import all WeilConjectures.AlgebraicGeometry.RingedTopoiTensorComparisonData
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.AlgebraicGeometry.RingedTopoiTensorSections
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import all WeilConjectures.CategoryTheory.ModulePullbackPushforwardAdjunctionSupplement

/-! # Flat complete scalar restriction for native equivariant module sheaves

Source: Stacks Project, Algebraization, Tag 099I and the action-topos argument in
lem-pur-equivariant-complete-restriction (blueprint: lem-pur-equivariant-complete-restriction).
The algebraic inverse-image interfaces specify the actual transported ring and module
operations. Fixed pairs are formed in module sheaves before passing to derived categories.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.EquivariantCompleteRestriction

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/-- The coefficient module category is the recorded ringedSiteModules.
Source: Stacks 099I, 03D2 and 05VD
(blueprint: lem-pur-equivariant-complete-restriction).
-/
abbrev Modules (R : Sheaf J CommRingCat.{u}) := ringedSiteModules.{u} (siteModuleRings R)

/-- The underlying sheaf of sets of a commutative ring sheaf.
Source: Stacks 099I, 03D2 and 05VD
(blueprint: lem-pur-equivariant-complete-restriction).
-/
abbrev ringSets (R : Sheaf J CommRingCat.{u}) :=
  (sheafCompose J (forget CommRingCat)).obj R

/-- Forget the module operations using the existing module-sheaf functor.
Source: Stacks 099I, 03D2 and 05VD
(blueprint: lem-pur-equivariant-complete-restriction).
-/
abbrev moduleSets (R : Sheaf J CommRingCat.{u}) :=
  SheafOfModules.toSheaf (siteModuleRings R) ⋙ sheafCompose J (forget AddCommGrpCat)

/-- Ordinary scalar restriction, before taking complexes.
Source: Stacks 099I, 03D2 and 05VD
(blueprint: lem-pur-equivariant-complete-restriction).
-/
abbrev restriction {R B : Sheaf J CommRingCat.{u}} (c : R ⟶ B) :=
  SheafOfModules.restrictScalars.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).map c)

set_option maxHeartbeats 1600000 in
-- Naturality unfolds the composite underlying-sheaf functor and its module operations.
/-- Transported module addition makes the algebraic inverse image additive.
Source: Stacks 099I, 03D2 and 05VD
(blueprint: lem-pur-equivariant-complete-restriction).
Proof: apply the moduleAdd graph identity to the universal pair of module elements;
naturality of moduleUnderlying then gives preservation of sums of module maps.
-/
theorem imageAdditive {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (A : SheafOfModules.AlgebraicInverseImage L R S) : A.modules.Additive := by
  constructor
  intro M N f g
  ext U z
  have eval (k : M ⟶ N) :
      (A.moduleUnderlying.inv.app N).hom.app U
          ((L.map ((moduleSets R).map k)).hom.app U
            ((A.moduleUnderlying.hom.app M).hom.app U z)) =
        (A.modules.map k).val.app U z := by
    have h := congrArg
      (fun q ↦ q.hom.app U ((A.moduleUnderlying.hom.app M).hom.app U z))
      (A.moduleUnderlying.inv.naturality k)
    change (A.moduleUnderlying.inv.app N).hom.app U
        ((L.map ((moduleSets R).map k)).hom.app U
          ((A.moduleUnderlying.hom.app M).hom.app U z)) =
      (A.modules.map k).val.app U
        ((A.moduleUnderlying.inv.app M).hom.app U
          ((A.moduleUnderlying.hom.app M).hom.app U z)) at h
    have hz : (A.moduleUnderlying.inv.app M).hom.app U
        ((A.moduleUnderlying.hom.app M).hom.app U z) = z :=
      congrArg (fun q ↦ q.hom.app U z) (A.moduleUnderlying.hom_inv_id_app M)
    rw [hz] at h
    exact h
  have h := A.moduleAdd N ((moduleSets R).obj M)
    ((moduleSets R).map f) ((moduleSets R).map g) ((moduleSets R).map (f + g))
    (fun _ _ ↦ rfl) U ((A.moduleUnderlying.hom.app M).hom.app U z)
  dsimp only [id] at h
  rw [eval (f + g), eval f, eval g] at h
  exact h

/-- An algebraic lift of a topos automorphism is a module autoequivalence.
Source: Stacks 099I, 03D2 and 05VD
(blueprint: lem-pur-equivariant-complete-restriction).
Proof: transport the operations by the inverse equivalence; the unit and counit of the
topos equivalence preserve the transported operations and give inverse module functors.
-/
theorem imageEquivalence (σ : Sheaf J (Type u) ≌ Sheaf J (Type u))
    (R : Sheaf J CommRingCat.{u})
    (A : SheafOfModules.AlgebraicInverseImage σ.functor R R) :
    A.modules.IsEquivalence := by
  let d : RingedToposMorphism.RingData (siteModuleRings R) (siteModuleRings R) := {
    inverse := σ.functor
    direct := σ.inverse
    adj := σ.toAdjunction
    leftExact := inferInstance
    ringMap := A.ringUnderlying.hom
    ring_zero := A.ringZero
    ring_one := A.ringOne
    ring_add := A.ringAdd
    ring_mul := A.ringMul }
  obtain ⟨m⟩ := SheafOfModules.ringData_inducedModules R R d
  let e := d.withModules m
  have : e.inverse.IsEquivalence := σ.isEquivalence_functor
  have : IsIso e.ringMap := inferInstanceAs (IsIso A.ringUnderlying.hom)
  obtain ⟨I, hI, hE, _⟩ := CategoryTheory.inverse_image_equivalence e
  have hc : I.ringUnderlying.hom = A.ringUnderlying.hom := hI
  obtain ⟨ρ, _⟩ := SheafOfModules.InverseImageScalarRestriction.exists_comparison
    A I (𝟙 R) (𝟙 R) (by
      simp only [Functor.map_id, Category.id_comp, Category.comp_id]
      exact hc)
  have : I.modules.IsEquivalence := hE
  have hr : restriction (𝟙 R) = 𝟭 (Modules R) := by
    dsimp only [restriction]
    rw [Functor.map_id]
    rfl
  exact Functor.isEquivalence_of_iso
    ((Functor.rightUnitor I.modules).symm ≪≫
      (by simpa only [hr] using ρ) ≪≫ Functor.leftUnitor A.modules)

attribute [instance] imageAdditive imageEquivalence

/-- The canonical ordinary coefficient comparison is uniquely normalized.
Source: Stacks 099I, 03D2 and 05VD
(blueprint: lem-pur-equivariant-complete-restriction).
Proof: compose the two moduleUnderlying isomorphisms. The moduleAdd and moduleSMul
graph identities and the ring square make this composite additive and linear. Its inverse
is linear by the same identities. Naturality follows from moduleUnderlying; faithfulness
of forgetting operations gives uniqueness. This is the ordinary comparison in proof step 7.
-/
theorem comparisonExists
    {R B : Sheaf J CommRingCat.{u}} {S T : Sheaf K CommRingCat.{u}}
    (L : Sheaf J (Type u) ⥤ Sheaf K (Type u)) [PreservesFiniteLimits L]
    (A : SheafOfModules.AlgebraicInverseImage L R S)
    (A' : SheafOfModules.AlgebraicInverseImage L B T)
    (c : R ⟶ B) (d : S ⟶ T)
    (hc : A.ringUnderlying.hom ≫ (sheafCompose K (forget CommRingCat)).map d =
      L.map ((sheafCompose J (forget CommRingCat)).map c) ≫ A'.ringUnderlying.hom) :
    ∃! e : restriction c ⋙ A.modules ≅ A'.modules ⋙ restriction d,
      ∀ M : Modules B,
        (moduleSets S).map (e.hom.app M) =
          A.moduleUnderlying.hom.app ((restriction c).obj M) ≫
            A'.moduleUnderlying.inv.app M := by
  obtain ⟨ρ, hρ⟩ := SheafOfModules.InverseImageScalarRestriction.exists_comparison
    A A' c d hc.symm
  let e := ρ.symm
  have he (M : Modules B) :
      (moduleSets S).map (e.hom.app M) =
        A.moduleUnderlying.hom.app ((restriction c).obj M) ≫
          A'.moduleUnderlying.inv.app M := by
    change (moduleSets S).map (ρ.inv.app M) = _
    apply (cancel_epi ((moduleSets S).map (ρ.hom.app M))).1
    rw [← Functor.map_comp, Iso.hom_inv_id_app, Functor.map_id]
    rw [← Category.assoc, hρ M, Iso.hom_inv_id_app]
    rfl
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply (moduleSets S).map_injective
  exact (he' M).trans (he M).symm

/-- The specified ordinary comparison, determined by its underlying-sheaf equation.
Source: Stacks 099I, 03D2 and 05VD
(blueprint: lem-pur-equivariant-complete-restriction).
-/
def comparison
    {R B : Sheaf J CommRingCat.{u}} {S T : Sheaf K CommRingCat.{u}}
    (L : Sheaf J (Type u) ⥤ Sheaf K (Type u)) [PreservesFiniteLimits L]
    (A : SheafOfModules.AlgebraicInverseImage L R S)
    (A' : SheafOfModules.AlgebraicInverseImage L B T)
    (c : R ⟶ B) (d : S ⟶ T)
    (hc : A.ringUnderlying.hom ≫ (sheafCompose K (forget CommRingCat)).map d =
      L.map ((sheafCompose J (forget CommRingCat)).map c) ≫ A'.ringUnderlying.hom) :
    restriction c ⋙ A.modules ≅ A'.modules ⋙ restriction d :=
  (comparisonExists L A A' c d hc).choose

/-- A coefficient map with its actual semilinear action and fixed global section.
Source: Stacks 099I, 03D2 and 05VD
(blueprint: lem-pur-equivariant-complete-restriction).
-/
structure Datum (J : GrothendieckTopology C) where
  sigma : Sheaf J (Type u) ≌ Sheaf J (Type u)
  R : Sheaf J CommRingCat.{u}
  B : Sheaf J CommRingCat.{u}
  actionR : SheafOfModules.AlgebraicInverseImage sigma.functor R R
  actionB : SheafOfModules.AlgebraicInverseImage sigma.functor B B
  c : R ⟶ B
  equivariant : actionR.ringUnderlying.hom ≫ (sheafCompose J (forget CommRingCat)).map c =
    sigma.functor.map ((sheafCompose J (forget CommRingCat)).map c) ≫
      actionB.ringUnderlying.hom
  t : (R.obj ⋙ forget CommRingCat).sections
  fixed : ∀ (X : Sheaf J (Type u)) (a : X ⟶ ringSets R),
    (∀ (U : Cᵒᵖ) (x : X.obj.obj U), a.hom.app U x = t.val U) →
    ∀ (U : Cᵒᵖ) (x : (sigma.functor.obj X).obj.obj U),
      (sigma.functor.map a ≫ actionR.ringUnderlying.hom).hom.app U x = t.val U

namespace Datum

variable (x : Datum J)

/-- The image c(t) as a compatible global section of B.
Source: Stacks 099I, 03D2 and 05VD
(blueprint: lem-pur-equivariant-complete-restriction).
-/
def sectionB : (x.B.obj ⋙ forget CommRingCat).sections :=
  (Functor.sectionsFunctor Cᵒᵖ).map
    ((sheafCompose J (forget CommRingCat)).map x.c).hom x.t

/-- Restriction of semilinear module sheaves, before localization.
Source: Stacks 099I, 03D2 and 05VD
(blueprint: lem-pur-equivariant-complete-restriction).
-/
abbrev pairRestriction : Endofunctor.IsoAlgebra x.actionB.modules ⥤
    Endofunctor.IsoAlgebra x.actionR.modules :=
  Endofunctor.IsoAlgebra.mapOfNatIso
    (comparison x.sigma.functor x.actionR x.actionB x.c x.c x.equivariant)

/-- Restriction on fixed pairs preserves finite limits and colimits.
Source: Stacks Project, Algebraization, Tag 099I (blueprint:
lem-pur-equivariant-complete-restriction). The ordinary scalar restriction is exact,
and the fixed-pair comparison is an isomorphism of additive functors. -/
theorem pairRestrictionPreservesFiniteLimits :
    PreservesFiniteLimits x.pairRestriction := by
  have := (siteRestrictScalars_exact x.c).1
  infer_instance

/-- The termwise fixed-pair restriction preserves finite colimits.
Source: Stacks Project, Algebraization, Tag 099I (blueprint:
lem-pur-equivariant-complete-restriction). Proof: finite colimits are created by ordinary
forgetting, and ordinary restriction preserves them; use the invertible comparison. -/
theorem pairRestrictionPreservesFiniteColimits :
    PreservesFiniteColimits x.pairRestriction := by
  have := (siteRestrictScalars_exact x.c).2
  infer_instance

attribute [instance] pairRestrictionPreservesFiniteLimits pairRestrictionPreservesFiniteColimits

/-- The single global derived internal Hom test required by the node.
Source: Stacks 099I, 03D2 and 05VD
(blueprint: lem-pur-equivariant-complete-restriction).
-/
def ordinaryComplete (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (Modules R)]
    (t : (R.obj ⋙ forget CommRingCat).sections) : ObjectProperty (DerivedCategory (Modules R)) :=
  fun M ↦ IsZero ((derivedInternalHom J R).obj
    (op ((DerivedCategory.singleFunctor _ 0).obj
      (ringedSectionLocalizationOfUniverses R t)), M))

variable [HasDerivedCategory.{w} (Modules x.R)] [HasDerivedCategory.{w} (Modules x.B)]
  [HasDerivedCategory.{w} (Endofunctor.IsoAlgebra x.actionR.modules)]
  [HasDerivedCategory.{w} (Endofunctor.IsoAlgebra x.actionB.modules)]

/-- Completeness in the native derived category is tested after ordinary forgetting.
Source: Stacks 099I, 03D2 and 05VD
(blueprint: lem-pur-equivariant-complete-restriction).
-/
def nativeCompleteR : ObjectProperty
    (DerivedCategory (Endofunctor.IsoAlgebra x.actionR.modules)) :=
  fun M ↦ ordinaryComplete x.R x.t
    ((Endofunctor.IsoAlgebra.forget x.actionR.modules).mapDerivedCategory.obj M)

/-- The corresponding native c(t)-complete object property.
Source: Stacks 099I, 03D2 and 05VD
(blueprint: lem-pur-equivariant-complete-restriction).
-/
def nativeCompleteB : ObjectProperty
    (DerivedCategory (Endofunctor.IsoAlgebra x.actionB.modules)) :=
  fun M ↦ ordinaryComplete x.B x.sectionB
    ((Endofunctor.IsoAlgebra.forget x.actionB.modules).mapDerivedCategory.obj M)

/-- The native functor is termwise pairRestriction followed by localization.
Source: Stacks 099I, 03D2 and 05VD
(blueprint: lem-pur-equivariant-complete-restriction).
-/
def derivedRestriction : DerivedCategory (Endofunctor.IsoAlgebra x.actionB.modules) ⥤
    DerivedCategory (Endofunctor.IsoAlgebra x.actionR.modules) :=
  letI := (siteRestrictScalars_exact x.c).1
  letI := (siteRestrictScalars_exact x.c).2
  letI := x.pairRestrictionPreservesFiniteLimits
  letI := x.pairRestrictionPreservesFiniteColimits
  x.pairRestriction.mapDerivedCategory

/-- Forgetting the action on complete objects uses the full-subcategory lift.
Source: Stacks 099I, 03D2 and 05VD
(blueprint: lem-pur-equivariant-complete-restriction).
-/
def forgetCompleteR : x.nativeCompleteR.FullSubcategory ⥤
    (ordinaryComplete x.R x.t).FullSubcategory :=
  ObjectProperty.lift _
    (ObjectProperty.ι x.nativeCompleteR ⋙
      (Endofunctor.IsoAlgebra.forget x.actionR.modules).mapDerivedCategory)
    (fun M ↦ M.property)

/-- Forgetting the action on c(t)-complete objects uses the same construction.
Source: Stacks 099I, 03D2 and 05VD
(blueprint: lem-pur-equivariant-complete-restriction).
-/
def forgetCompleteB : x.nativeCompleteB.FullSubcategory ⥤
    (ordinaryComplete x.B x.sectionB).FullSubcategory :=
  ObjectProperty.lift _
    (ObjectProperty.ι x.nativeCompleteB ⋙
      (Endofunctor.IsoAlgebra.forget x.actionB.modules).mapDerivedCategory)
    (fun M ↦ M.property)

/-- The quotient ring-sheaf isomorphism criterion, with local kernel and lifting.
Source: Stacks 099I, 03D2 and 05VD
(blueprint: lem-pur-equivariant-complete-restriction).
The first clause tests membership in the kernel modulo the image principal ideal locally;
the second is local surjectivity modulo c(t). Thus sectionwise quotient surjectivity is not
required on a site where quotients must be sheafified.
-/
def quotientIso : Prop :=
  (∀ (U : C) (a : x.R.obj.obj (op U)),
    (∃ S : Sieve U, S ∈ J U ∧ ∀ (V : C) (f : V ⟶ U), S f →
      ∃ b : x.B.obj.obj (op V),
        x.B.obj.map f.op (x.c.hom.app (op U) a) =
          @id (x.B.obj.obj (op V)) (x.sectionB.val (op V)) * b) →
    ∃ S : Sieve U, S ∈ J U ∧ ∀ (V : C) (f : V ⟶ U), S f →
      ∃ b : x.R.obj.obj (op V), x.R.obj.map f.op a =
        @id (x.R.obj.obj (op V)) (x.t.val (op V)) * b) ∧
  (∀ (U : C) (b : x.B.obj.obj (op U)),
    ∃ S : Sieve U, S ∈ J U ∧ ∀ (V : C) (f : V ⟶ U), S f →
      ∃ (a : x.R.obj.obj (op V)) (b' : x.B.obj.obj (op V)),
        x.B.obj.map f.op b - x.c.hom.app (op V) a =
          @id (x.B.obj.obj (op V)) (x.sectionB.val (op V)) * b')

/-- The flat complete-restriction equivalence and its ordinary forgetful square.
Source: Stacks 099I, 03D2 and 05VD
(blueprint: lem-pur-equivariant-complete-restriction).
Proof (the seven steps of the DAG):
1. Choose an invariant small site for the topos automorphism using
lem-pur-topos-automorphism-site-presentation. Ringed presentation transport preserves
module pairs, ordinary derived categories, localization and internal Hom.
2. Realize the two semilinear module categories on the same integer action site by
lem-sf-twisted-action-ringed-site. Exact conservative forgetting, with its tensor comparison,
detects flatness of the coefficient extension and the isomorphism of principal quotients.
3. By lem-pur-native-ringed-restriction-localization and the slice Hom comparison,
the single global test is local principal completeness. The complete-elements ideal theorem
extends the generator test to every locally generated ideal section, including zero divisors.
4. The fixed-pair derived-forget theorem preserves K-injectives. The two-injective Hom
comparison and derived conservativity identify action-site completeness with nativeComplete.
5. Apply Stacks 099I, lem-weil-pbc-flat-ringed-ideal-complete-equivalence, on both the
action site and the original site. The two termwise forget/restrict composites coincide,
so their localizations give the displayed commuting square.
6. Full faithfulness gives the unique lift of each ambient derived arrow between complete
objects. The subcategories are full, so these are precisely the asserted native arrows.
7. Exact inverse image transports flatness and quotients (Stacks 05VD). Its canonical
ordinary comparison descends on complexes, and uniqueness on the target proves the
pullback statement below, without assuming preservation of all complete objects.
-/
theorem completeRestriction
    (hflat : SheafOfModules.IsFlat ((restriction x.c).obj
      (SheafOfModules.unit (siteModuleRings x.B))))
    (hquot : x.quotientIso) :
    (∃ (e : x.nativeCompleteB.FullSubcategory ≌ x.nativeCompleteR.FullSubcategory)
      (e₀ : (ordinaryComplete x.B x.sectionB).FullSubcategory ≌
        (ordinaryComplete x.R x.t).FullSubcategory),
      Nonempty (e.functor ⋙ ObjectProperty.ι x.nativeCompleteR ≅
        ObjectProperty.ι x.nativeCompleteB ⋙ x.derivedRestriction) ∧
      Nonempty (e₀.functor ⋙ ObjectProperty.ι (ordinaryComplete x.R x.t) ≅
        ObjectProperty.ι (ordinaryComplete x.B x.sectionB) ⋙ siteDerivedRestrictScalars x.c) ∧
      Nonempty (e.functor ⋙ x.forgetCompleteR ≅ x.forgetCompleteB ⋙ e₀.functor)) ∧
    (∀ (M N : DerivedCategory (Endofunctor.IsoAlgebra x.actionB.modules)),
      x.nativeCompleteB M → x.nativeCompleteB N →
      ∀ h : x.derivedRestriction.obj M ⟶ x.derivedRestriction.obj N,
        ∃! b : M ⟶ N, x.derivedRestriction.map b = h) := by
  sorry

set_option maxHeartbeats 2000000 in
-- Elaborating the full completeness theorem expands its large equivalence statement.
/-- Injectivity of complete scalar restriction, extracted before substituting
large derived pullback objects. Source: the full-faithfulness clause of
`completeRestriction` (blueprint: lem-pur-equivariant-complete-restriction).
Proof: apply uniqueness of a lift of the restricted second arrow to both arrows.
-/
private theorem completeRestriction_map_injective
    (hflat : SheafOfModules.IsFlat ((restriction x.c).obj
      (SheafOfModules.unit (siteModuleRings x.B))))
    (hquot : x.quotientIso)
    (M N : DerivedCategory (Endofunctor.IsoAlgebra x.actionB.modules))
    (hM : x.nativeCompleteB M) (hN : x.nativeCompleteB N)
    (a b : M ⟶ N) (hab : x.derivedRestriction.map a = x.derivedRestriction.map b) :
    a = b := by
  obtain ⟨_, _, hu⟩ := (Datum.completeRestriction.{u, w} x hflat hquot).2
    M N hM hN (x.derivedRestriction.map b)
  exact (hu a hab).trans (hu b rfl).symm

end Datum
/-- An exact inverse image on the native equivariant module categories, together with
its coefficient-ring identifications. The normalization equation identifies the scalar
comparison with the one obtained on underlying sheaves by the two algebraic inverse images.
Source: Stacks Project, Modules on Sites, Tags 03D2 and 05VD (blueprint:
lem-pur-equivariant-complete-restriction). -/
structure Pullback (x : Datum J) (y : Datum K) where
  inverseImage : Sheaf J (Type u) ⥤ Sheaf K (Type u)
  leftAdjoint : inverseImage.IsLeftAdjoint
  leftExact : PreservesFiniteLimits inverseImage
  coefficientsR : SheafOfModules.AlgebraicInverseImage inverseImage x.R y.R
  coefficientsB : SheafOfModules.AlgebraicInverseImage inverseImage x.B y.B
  coefficientSquare : coefficientsR.ringUnderlying.hom ≫
      (sheafCompose K (forget CommRingCat)).map y.c =
    inverseImage.map ((sheafCompose J (forget CommRingCat)).map x.c) ≫
      coefficientsB.ringUnderlying.hom
  sectionCompatibility : ∀ (X : Sheaf J (Type u)) (a : X ⟶ ringSets x.R),
    (∀ (U : Cᵒᵖ) (z : X.obj.obj U), a.hom.app U z = x.t.val U) →
    ∀ (V : Dᵒᵖ) (z : (inverseImage.obj X).obj.obj V),
      (inverseImage.map a ≫ coefficientsR.ringUnderlying.hom).hom.app V z = y.t.val V
  modulesR : Endofunctor.IsoAlgebra x.actionR.modules ⥤
    Endofunctor.IsoAlgebra y.actionR.modules
  modulesB : Endofunctor.IsoAlgebra x.actionB.modules ⥤
    Endofunctor.IsoAlgebra y.actionB.modules
  additiveR : modulesR.Additive
  additiveB : modulesB.Additive
  exactRLeft : PreservesFiniteLimits modulesR
  exactRRight : PreservesFiniteColimits modulesR
  exactBLeft : PreservesFiniteLimits modulesB
  exactBRight : PreservesFiniteColimits modulesB
  underlyingR : modulesR ⋙ Endofunctor.IsoAlgebra.forget y.actionR.modules ≅
    Endofunctor.IsoAlgebra.forget x.actionR.modules ⋙ coefficientsR.modules
  underlyingB : modulesB ⋙ Endofunctor.IsoAlgebra.forget y.actionB.modules ≅
    Endofunctor.IsoAlgebra.forget x.actionB.modules ⋙ coefficientsB.modules
  scalarComparison : x.pairRestriction ⋙ modulesR ≅ modulesB ⋙ y.pairRestriction
  normalized : ∀ M : Endofunctor.IsoAlgebra x.actionB.modules,
    (moduleSets y.R).map ((Endofunctor.IsoAlgebra.forget y.actionR.modules).map
      (scalarComparison.hom.app M)) =
    (moduleSets y.R).map (underlyingR.hom.app (x.pairRestriction.obj M)) ≫
      coefficientsR.moduleUnderlying.hom.app
        ((restriction x.c).obj ((Endofunctor.IsoAlgebra.forget x.actionB.modules).obj M)) ≫
        coefficientsB.moduleUnderlying.inv.app
          ((Endofunctor.IsoAlgebra.forget x.actionB.modules).obj M) ≫
          (moduleSets y.B).map (underlyingB.inv.app M)

namespace Pullback

variable {x : Datum J} {y : Datum K} (v : Pullback x y)

attribute [instance] additiveR additiveB exactRLeft exactRRight exactBLeft exactBRight

/-- Exact inverse image transports flatness of the coefficient extension.
Source: Stacks Project, Modules on Sites, Tag 05VD.
(blueprint: lem-pur-equivariant-complete-restriction).
Proof: apply preservation of flatness by algebraic inverse image to the source
coefficient module. The normalized scalar comparison identifies its image with
restriction of the image of the source rank-one module. The algebraic inverse-image
rank-one comparison identifies that last module with the target ring. Transport
flatness along these two module isomorphisms. This includes the zero ring.
-/
private theorem coefficientFlat (v : Pullback x y)
    (hflat : SheafOfModules.IsFlat ((restriction x.c).obj
      (SheafOfModules.unit (siteModuleRings x.B)))) :
    SheafOfModules.IsFlat ((restriction y.c).obj
      (SheafOfModules.unit (siteModuleRings y.B))) := by
  let := v.leftExact
  let := v.leftAdjoint
  let M := (restriction x.c).obj (SheafOfModules.unit (siteModuleRings x.B))
  have hM : SheafOfModules.IsFlatOnSite.{u, u, u, u} (J := J) (R := x.R) M := by
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso x.R M).symm hflat
  let I := SheafOfModules.inverseImageOfUniverses_adapted v.coefficientsR
  have hI : SheafOfModules.IsFlatOnSite.{u, u, u, u}
      (J := K) (R := y.R) (v.coefficientsR.modules.obj M) :=
    SheafOfModules.isFlat_algebraicInverseImageOfUniverses.{u, u, u, u, u, u}
      (J := J) (K := K) (R := x.R) (RI := y.R) v.inverseImage _
      (Adjunction.ofIsLeftAdjoint v.inverseImage) I M hM
  let a := comparison v.inverseImage v.coefficientsR v.coefficientsB x.c y.c
    v.coefficientSquare
  obtain ⟨b, _⟩ := SheafOfModules.inverseImage_unit_iso x.B y.B v.inverseImage v.coefficientsB
  let d := (a.app (SheafOfModules.unit (siteModuleRings x.B))) ≪≫
    (restriction y.c).mapIso b.symm
  let := SheafOfModules.monoidalCategory y.R
  let := SheafOfModules.symmetricCategory y.R
  have hF : ObjectProperty.flat (v.coefficientsR.modules.obj M) :=
    SheafOfModules.categorical_of_flatOnSite_adapted y.R _ hI
  exact (ObjectProperty.prop_of_iso ObjectProperty.flat d hF).2


private def sectionMap (R : Sheaf J CommRingCat.{u})
    (t : (R.obj ⋙ forget CommRingCat).sections) (X : Sheaf J (Type u)) : X ⟶ ringSets R :=
  ⟨{ app U := ↾fun _ ↦ t.val U
     naturality := by
       intro U V f
       ext z
       exact (t.property f).symm }⟩

private def addMap {R : Sheaf J CommRingCat.{u}} {X : Sheaf J (Type u)}
    (a b : X ⟶ ringSets R) : X ⟶ ringSets R :=
  ⟨{ app U := ↾fun z ↦ @id (R.obj.obj U) (a.hom.app U z) + @id (R.obj.obj U) (b.hom.app U z)
     naturality := by
       intro U V f
       ext z
       exact ((map_add (R.obj.map f).hom _ _).trans
         (congrArg₂ (fun p q : R.obj.obj V ↦ p + q)
           (NatTrans.naturality_apply a.hom f z).symm
           (NatTrans.naturality_apply b.hom f z).symm)).symm }⟩

private def mulMap {R : Sheaf J CommRingCat.{u}} {X : Sheaf J (Type u)}
    (a b : X ⟶ ringSets R) : X ⟶ ringSets R :=
  ⟨{ app U := ↾fun z ↦ @id (R.obj.obj U) (a.hom.app U z) * @id (R.obj.obj U) (b.hom.app U z)
     naturality := by
       intro U V f
       ext z
       exact ((map_mul (R.obj.map f).hom _ _).trans
         (congrArg₂ (fun p q : R.obj.obj V ↦ p * q)
           (NatTrans.naturality_apply a.hom f z).symm
           (NatTrans.naturality_apply b.hom f z).symm)).symm }⟩

private theorem productSections
    (L : Sheaf J (Type u) ⥤ Sheaf K (Type u)) [PreservesFiniteLimits L]
    (A B : Sheaf J (Type u)) (U : Dᵒᵖ)
    (a : (L.obj A).obj.obj U) (b : (L.obj B).obj.obj U) :
    ∃ z : (L.obj (A ⨯ B)).obj.obj U,
      (L.map prod.fst).hom.app U z = a ∧ (L.map prod.snd).hom.app U z = b := by
  let E := L ⋙ sheafToPresheaf K (Type u) ⋙ (evaluation Dᵒᵖ (Type u)).obj U
  let h := isLimitOfHasBinaryProductOfPreservesLimit E A B
  let z := BinaryFan.IsLimit.lift h (↾fun _ : PUnit.{u + 1} ↦ a)
    (↾fun _ : PUnit.{u + 1} ↦ b)
  refine ⟨z PUnit.unit, ?_, ?_⟩
  · exact congrArg (fun f ↦ f PUnit.unit) (BinaryFan.IsLimit.lift_fst h _ _)
  · exact congrArg (fun f ↦ f PUnit.unit) (BinaryFan.IsLimit.lift_snd h _ _)

private def value {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (A : SheafOfModules.AlgebraicInverseImage L R S)
    {X : Sheaf J (Type u)} (a : X ⟶ ringSets R) (U : Dᵒᵖ)
    (z : (L.obj X).obj.obj U) : S.obj.obj U :=
  A.ringUnderlying.hom.hom.app U ((L.map a).hom.app U z)

private theorem value_mul
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (A : SheafOfModules.AlgebraicInverseImage L R S)
    {X : Sheaf J (Type u)} (a b : X ⟶ ringSets R) (U : Dᵒᵖ)
    (z : (L.obj X).obj.obj U) :
    value L A (mulMap a b) U z = value L A a U z * value L A b U z :=
  A.ringMul X a b (mulMap a b) (fun _ _ ↦ rfl) U z

private theorem value_add
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (A : SheafOfModules.AlgebraicInverseImage L R S)
    {X : Sheaf J (Type u)} (a b : X ⟶ ringSets R) (U : Dᵒᵖ)
    (z : (L.obj X).obj.obj U) :
    value L A (addMap a b) U z = value L A a U z + value L A b U z :=
  A.ringAdd X a b (addMap a b) (fun _ _ ↦ rfl) U z

private theorem value_comp
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (A : SheafOfModules.AlgebraicInverseImage L R S)
    {X Y : Sheaf J (Type u)} (f : X ⟶ Y) (a : Y ⟶ ringSets R) (U : Dᵒᵖ)
    (z : (L.obj X).obj.obj U) :
    value L A (f ≫ a) U z = value L A a U ((L.map f).hom.app U z) := by
  simp only [value, Functor.map_comp]
  rfl

private theorem value_coefficient
    {X : Sheaf J (Type u)} (a : X ⟶ ringSets x.R) (U : Dᵒᵖ)
    (z : (v.inverseImage.obj X).obj.obj U) :
    value v.inverseImage v.coefficientsB
        (a ≫ (sheafCompose J (forget CommRingCat)).map x.c) U z =
      y.c.hom.app U (value v.inverseImage v.coefficientsR a U z) := by
  have h := congrArg (fun f ↦ f.hom.app U ((v.inverseImage.map a).hom.app U z))
    v.coefficientSquare
  dsimp only [value]
  rw [Functor.map_comp]
  exact h.symm

private theorem value_sectionR (X : Sheaf J (Type u)) (U : Dᵒᵖ)
    (z : (v.inverseImage.obj X).obj.obj U) :
    value v.inverseImage v.coefficientsR (sectionMap x.R x.t X) U z = y.t.val U :=
  v.sectionCompatibility X (sectionMap x.R x.t X) (fun _ _ ↦ rfl) U z

private theorem value_sectionB (X : Sheaf J (Type u)) (U : Dᵒᵖ)
    (z : (v.inverseImage.obj X).obj.obj U) :
    value v.inverseImage v.coefficientsB (sectionMap x.B x.sectionB X) U z =
      y.sectionB.val U := by
  have h : sectionMap x.B x.sectionB X =
      sectionMap x.R x.t X ≫ (sheafCompose J (forget CommRingCat)).map x.c := by
    ext V q
    rfl
  rw [h, value_coefficient, value_sectionR]
  rfl

private theorem locallySurjectiveImage
    (L : Sheaf J (Type u) ⥤ Sheaf K (Type u)) [L.IsLeftAdjoint]
    {A B : Sheaf J (Type u)} (f : A ⟶ B)
    (hf : ∀ (U : Cᵒᵖ) (z : B.obj.obj U),
      ∃ S : Sieve U.unop, S ∈ J U.unop ∧ ∀ (V : C) (a : V ⟶ U.unop), S a →
        ∃ w : A.obj.obj (op V), f.hom.app (op V) w = B.obj.map a.op z)
    (U : Dᵒᵖ) (z : (L.obj B).obj.obj U) :
    ∃ S : Sieve U.unop, S ∈ K U.unop ∧ ∀ (V : D) (a : V ⟶ U.unop), S a →
      ∃ w : (L.obj A).obj.obj (op V),
        (L.map f).hom.app (op V) w = (L.obj B).obj.map a.op z := by
  have hsource (V : Cᵒᵖ) (w : B.obj.obj V) := hf V w
  obtain ⟨S, hS, hs⟩ := Sheaf.map_jointly_locally_surjective L _
    (Adjunction.ofIsLeftAdjoint L) (fun _ : Unit ↦ f) (by
      intro V w
      obtain ⟨S, hS, hs⟩ := hsource V w
      refine ⟨S, hS, ?_⟩
      intro W a ha
      obtain ⟨z, hz⟩ := hs W a ha
      exact ⟨(), z, hz⟩) U z
  refine ⟨S, hS, ?_⟩
  intro V a ha
  obtain ⟨_, w, hw⟩ := hs V a ha
  exact ⟨w, hw⟩

private theorem value_of_lift
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (A : SheafOfModules.AlgebraicInverseImage L R S)
    {X : Sheaf J (Type u)} (a : X ⟶ ringSets R) {U V : Dᵒᵖ} (f : U ⟶ V)
    (z : (L.obj (ringSets R)).obj.obj U) (w : (L.obj X).obj.obj V)
    (hw : (L.map a).hom.app V w = (L.obj (ringSets R)).obj.map f z) :
    value L A a V w = S.obj.map f (A.ringUnderlying.hom.hom.app U z) := by
  dsimp only [value]
  rw [hw]
  exact NatTrans.naturality_apply A.ringUnderlying.hom.hom f z

private theorem quotientSurjective (v : Pullback x y) (hquot : x.quotientIso) :
    ∀ (U : D) (b : y.B.obj.obj (op U)),
      ∃ S : Sieve U, S ∈ K U ∧ ∀ (V : D) (f : V ⟶ U), S f →
        ∃ (a : y.R.obj.obj (op V)) (b' : y.B.obj.obj (op V)),
          y.B.obj.map f.op b - y.c.hom.app (op V) a =
            @id (y.B.obj.obj (op V)) (y.sectionB.val (op V)) * b' := by
  let := v.leftExact
  let := v.leftAdjoint
  let T := ringSets x.R ⨯ ringSets x.B
  let a : T ⟶ ringSets x.R := prod.fst
  let b : T ⟶ ringSets x.B := prod.snd
  let c := (sheafCompose J (forget CommRingCat)).map x.c
  let g : T ⟶ ringSets x.B :=
    addMap (a ≫ c) (mulMap (sectionMap x.B x.sectionB T) b)
  have hg (U : Cᵒᵖ) (z : (ringSets x.B).obj.obj U) :
      ∃ S : Sieve U.unop, S ∈ J U.unop ∧ ∀ (V : C) (f : V ⟶ U.unop), S f →
        ∃ w : T.obj.obj (op V), g.hom.app (op V) w = x.B.obj.map f.op z := by
    obtain ⟨S, hS, hs⟩ := hquot.2 U.unop z
    refine ⟨S, hS, ?_⟩
    intro V f hf
    obtain ⟨r, q, hq⟩ := hs V f hf
    obtain ⟨w, hw₁, hw₂⟩ := productSections (𝟭 (Sheaf J (Type u)))
      (ringSets x.R) (ringSets x.B) (op V) r q
    refine ⟨w, ?_⟩
    change x.c.hom.app (op V) (a.hom.app (op V) w) +
      @id (x.B.obj.obj (op V)) (x.sectionB.val (op V)) *
        @id (x.B.obj.obj (op V)) (b.hom.app (op V) w) = _
    change a.hom.app (op V) w = r at hw₁
    change b.hom.app (op V) w = q at hw₂
    rw [hw₁, hw₂]
    exact (sub_eq_iff_eq_add'.mp hq).symm
  intro U z
  let z' := v.coefficientsB.ringUnderlying.inv.hom.app (op U) z
  obtain ⟨S, hS, hs⟩ := locallySurjectiveImage v.inverseImage g hg (op U) z'
  refine ⟨S, hS, ?_⟩
  intro V f hf
  obtain ⟨w, hw⟩ := hs V f hf
  refine ⟨value v.inverseImage v.coefficientsR a (op V) w,
    value v.inverseImage v.coefficientsB b (op V) w, ?_⟩
  have he := value_of_lift v.inverseImage v.coefficientsB g f.op z' w hw
  have hz : v.coefficientsB.ringUnderlying.hom.hom.app (op U) z' = z :=
    congrArg (fun k ↦ k.hom.app (op U) z) v.coefficientsB.ringUnderlying.inv_hom_id
  rw [hz] at he
  change value v.inverseImage v.coefficientsB
    (addMap (a ≫ c) (mulMap (sectionMap x.B x.sectionB T) b)) (op V) w = _ at he
  rw [value_add, value_mul, value_sectionB] at he
  dsimp only [c] at he
  rw [value_coefficient] at he
  exact sub_eq_iff_eq_add'.mpr he.symm

private theorem quotientKernelPoint (v : Pullback x y) (hquot : x.quotientIso)
    (U : D) (r : y.R.obj.obj (op U)) (q : y.B.obj.obj (op U))
    (hq : y.c.hom.app (op U) r = @id (y.B.obj.obj (op U)) (y.sectionB.val (op U)) * q) :
    ∃ S : Sieve U, S ∈ K U ∧ ∀ (V : D) (f : V ⟶ U), S f →
      ∃ b : y.R.obj.obj (op V), y.R.obj.map f.op r =
        @id (y.R.obj.obj (op V)) (y.t.val (op V)) * b := by
  let := v.leftExact
  let := v.leftAdjoint
  let L := v.inverseImage
  let T := ringSets x.R ⨯ ringSets x.B
  let a : T ⟶ ringSets x.R := prod.fst
  let b : T ⟶ ringSets x.B := prod.snd
  let c := (sheafCompose J (forget CommRingCat)).map x.c
  let f : T ⟶ ringSets x.B := a ≫ c
  let g : T ⟶ ringSets x.B := mulMap (sectionMap x.B x.sectionB T) b
  let E := SheafOfModules.equationSheaf f g
  let i : E ⟶ T := SheafOfModules.equationι f g
  let P := E ⨯ ringSets x.R
  let p : P ⟶ E := prod.fst
  let s : P ⟶ ringSets x.R := prod.snd
  let f' : P ⟶ ringSets x.R := p ≫ i ≫ a
  let g' : P ⟶ ringSets x.R := mulMap (sectionMap x.R x.t P) s
  let W := SheafOfModules.equationSheaf f' g'
  let j : W ⟶ P := SheafOfModules.equationι f' g'
  let k : W ⟶ E := j ≫ p
  have hk (V : Cᵒᵖ) (z : E.obj.obj V) :
      ∃ S : Sieve V.unop, S ∈ J V.unop ∧ ∀ (Z : C) (h : Z ⟶ V.unop), S h →
        ∃ w : W.obj.obj (op Z), k.hom.app (op Z) w = E.obj.map h.op z := by
    obtain ⟨S, hS, hs⟩ := hquot.1 V.unop (a.hom.app V (i.hom.app V z)) (by
      refine ⟨⊤, J.top_mem _, ?_⟩
      intro Z h _
      let z' := E.obj.map h.op z
      refine ⟨b.hom.app (op Z) (i.hom.app (op Z) z'), ?_⟩
      have hn := NatTrans.naturality_apply (i ≫ a ≫ c).hom h.op z
      change x.c.hom.app (op Z) (a.hom.app (op Z) (i.hom.app (op Z) z')) =
        x.B.obj.map h.op (x.c.hom.app V (a.hom.app V (i.hom.app V z))) at hn
      rw [← hn]
      exact z'.property)
    refine ⟨S, hS, ?_⟩
    intro Z h hh
    obtain ⟨t, ht⟩ := hs Z h hh
    obtain ⟨w, hw₁, hw₂⟩ := productSections (𝟭 (Sheaf J (Type u)))
      E (ringSets x.R) (op Z) (E.obj.map h.op z) t
    have he : f'.hom.app (op Z) w = g'.hom.app (op Z) w := by
      change a.hom.app (op Z) (i.hom.app (op Z) (p.hom.app (op Z) w)) =
        @id (x.R.obj.obj (op Z)) (x.t.val (op Z)) *
          @id (x.R.obj.obj (op Z)) (s.hom.app (op Z) w)
      change p.hom.app (op Z) w = E.obj.map h.op z at hw₁
      change s.hom.app (op Z) w = t at hw₂
      rw [hw₁, hw₂]
      exact (NatTrans.naturality_apply (i ≫ a).hom h.op z).trans ht
    obtain ⟨w', hw'⟩ := SheafOfModules.equation_sections (𝟭 (Sheaf J (Type u)))
      f' g' (op Z) w he
    refine ⟨w', ?_⟩
    change p.hom.app (op Z) (j.hom.app (op Z) w') = E.obj.map h.op z
    change j.hom.app (op Z) w' = w at hw'
    rw [hw']
    exact hw₁
  let r' := v.coefficientsR.ringUnderlying.inv.hom.app (op U) r
  let q' := v.coefficientsB.ringUnderlying.inv.hom.app (op U) q
  obtain ⟨z, hz₁, hz₂⟩ := productSections L (ringSets x.R) (ringSets x.B) (op U) r' q'
  have hr : value L v.coefficientsR a (op U) z = r := by
    dsimp only [value]
    rw [hz₁]
    exact congrArg (fun k ↦ k.hom.app (op U) r) v.coefficientsR.ringUnderlying.inv_hom_id
  have hq' : value L v.coefficientsB b (op U) z = q := by
    dsimp only [value]
    rw [hz₂]
    exact congrArg (fun k ↦ k.hom.app (op U) q) v.coefficientsB.ringUnderlying.inv_hom_id
  have he : (L.map f).hom.app (op U) z = (L.map g).hom.app (op U) z := by
    apply (ConcreteCategory.bijective_of_isIso
      (v.coefficientsB.ringUnderlying.hom.hom.app (op U))).injective
    change value L v.coefficientsB f (op U) z = value L v.coefficientsB g (op U) z
    dsimp only [f, g, c]
    rw [value_coefficient, value_mul, value_sectionB, hr, hq']
    exact hq
  obtain ⟨z', hz'⟩ := SheafOfModules.equation_sections L f g (op U) z he
  obtain ⟨S, hS, hs⟩ := locallySurjectiveImage L k hk (op U) z'
  refine ⟨S, hS, ?_⟩
  intro V h hh
  obtain ⟨w, hw⟩ := hs V h hh
  refine ⟨value L v.coefficientsR (j ≫ s) (op V) w, ?_⟩
  have hrel := congrArg (fun f ↦ f.hom.app (op V) w)
    (L.congr_map (SheafOfModules.equation_condition f' g'))
  have hrel' : value L v.coefficientsR (j ≫ f') (op V) w =
      value L v.coefficientsR (j ≫ g') (op V) w := by
    apply congrArg (v.coefficientsR.ringUnderlying.hom.hom.app (op V))
    exact hrel
  have hleft : value L v.coefficientsR (j ≫ f') (op V) w = y.R.obj.map h.op r := by
    have hraw : (L.map (j ≫ f')).hom.app (op V) w =
        (L.obj (ringSets x.R)).obj.map h.op r' := by
      have hcomp : j ≫ f' = k ≫ i ≫ a := by
        dsimp only [f', k]
        simp only [Category.assoc]
      have hmap : L.map (j ≫ f') = L.map k ≫ L.map i ≫ L.map a := by
        calc
          L.map (j ≫ f') = L.map (k ≫ (i ≫ a)) := congrArg L.map hcomp
          _ = L.map k ≫ L.map (i ≫ a) := L.map_comp k (i ≫ a)
          _ = L.map k ≫ (L.map i ≫ L.map a) :=
            congrArg (fun m ↦ L.map k ≫ m) (L.map_comp i a)
      rw [hmap]
      change (L.map a).hom.app (op V)
        ((L.map i).hom.app (op V) ((L.map k).hom.app (op V) w)) = _
      rw [hw]
      rw [NatTrans.naturality_apply, hz', NatTrans.naturality_apply, hz₁]
    have he := value_of_lift L v.coefficientsR (j ≫ f') h.op r' w hraw
    have hr' : v.coefficientsR.ringUnderlying.hom.hom.app (op U) r' = r :=
      congrArg (fun k ↦ k.hom.app (op U) r) v.coefficientsR.ringUnderlying.inv_hom_id
    exact he.trans (congrArg (y.R.obj.map h.op) hr')
  rw [hleft, value_comp, value_mul, value_sectionR] at hrel'
  simpa only [value_comp, id_eq] using hrel'

/-- Exact inverse image preserves the isomorphism of principal quotient ring sheaves.
Source: Stacks Project, Modules on Sites, Tag 03D2; Algebraization, Tag 099I.
(blueprint: lem-pur-equivariant-complete-restriction).
Proof: the relation c(a) = c(t)b defines a finite-limit sheaf. The source kernel
condition says its projection to a locally lifts through multiplication by t.
The sheaf of these lifts again uses finite limits, so inverse image preserves
both relation sheaves. A left adjoint between sheaf topoi preserves locally
surjective families; applying this to the source lift projection proves the
target kernel condition. For surjectivity use the locally surjective map
(a,b) ↦ c(a) + c(t)b. Its image under inverse image is the corresponding target
map by the ring-operation graphs and section compatibility. Transitivity of
covering sieves handles the locally given kernel witness. No claim of
sectionwise surjectivity of a sheaf quotient is made.
-/
private theorem coefficientQuotient (v : Pullback x y) (hquot : x.quotientIso) : y.quotientIso := by
  refine ⟨?_, quotientSurjective v hquot⟩
  intro U a ha
  obtain ⟨S, hS, hs⟩ := ha
  let T : Sieve U :=
    { arrows V f := ∃ b : y.R.obj.obj (op V), y.R.obj.map f.op a =
        @id (y.R.obj.obj (op V)) (y.t.val (op V)) * b
      downward_closed := by
        intro V W f hf g
        obtain ⟨b, hb⟩ := hf
        refine ⟨y.R.obj.map g.op b, ?_⟩
        rw [op_comp, y.R.obj.map_comp]
        change y.R.obj.map g.op (y.R.obj.map f.op a) = _
        rw [hb, map_mul]
        have ht := y.t.property g.op
        change y.R.obj.map g.op (y.t.val (op V)) = y.t.val (op W) at ht
        simpa only [id_eq] using congrArg
          (fun z : y.R.obj.obj (op W) ↦ z * y.R.obj.map g.op b) ht }
  have hT : T ∈ K U := by
    apply K.transitive hS T
    intro V f hf
    obtain ⟨b, hb⟩ := hs V f hf
    have hn := NatTrans.naturality_apply y.c.hom f.op a
    change y.c.hom.app (op V) (y.R.obj.map f.op a) =
      y.B.obj.map f.op (y.c.hom.app (op U) a) at hn
    obtain ⟨P, hP, hp⟩ := quotientKernelPoint v hquot V (y.R.obj.map f.op a) b (hn.trans hb)
    apply K.superset_covering _ hP
    intro W g hg
    obtain ⟨r, hr⟩ := hp W g hg
    refine ⟨r, ?_⟩
    rw [op_comp, y.R.obj.map_comp]
    exact hr
  exact ⟨T, hT, fun V f hf ↦ hf⟩



variable [HasDerivedCategory.{w} (Modules x.R)] [HasDerivedCategory.{w} (Modules x.B)]
  [HasDerivedCategory.{w} (Modules y.R)] [HasDerivedCategory.{w} (Modules y.B)]
  [HasDerivedCategory.{w} (Endofunctor.IsoAlgebra x.actionR.modules)]
  [HasDerivedCategory.{w} (Endofunctor.IsoAlgebra x.actionB.modules)]
  [HasDerivedCategory.{w} (Endofunctor.IsoAlgebra y.actionR.modules)]
  [HasDerivedCategory.{w} (Endofunctor.IsoAlgebra y.actionB.modules)]

/-- The canonical coefficient comparison on derived categories is obtained by taking
complexes of the native equivariant module functors and then localizing.
Source: Stacks Project, Modules on Sites, Tags 03D2 and 05VD (blueprint:
lem-pur-equivariant-complete-restriction). -/
def derivedComparison :
    x.derivedRestriction ⋙ v.modulesR.mapDerivedCategory ≅
      v.modulesB.mapDerivedCategory ⋙ y.derivedRestriction :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso v.scalarComparison ≪≫
      Functor.mapDerivedCategoryCompIso _ _

set_option maxHeartbeats 2000000 in
-- Checking the derived comparison and its instantiated completeness predicates is expensive.
set_option linter.unusedSectionVars false in
-- Preserve the ordinary derived-category instances of the existing public declaration.
set_option linter.unusedVariables false in
-- Keep the source-completeness hypotheses in the API; this proof needs only target completeness.
/-- Pullback of a lift is the unique lift of the pulled-back arrow when the target
objects are complete. No preservation of completeness by the inverse image is assumed.
Source: Stacks Project, Algebraization, Tag 099I, and Modules on Sites, Tag 05VD
(blueprint: lem-pur-equivariant-complete-restriction).
Proof: the normalized termwise comparison descends through localization. Its naturality
identifies the restriction of the pulled-back lift with the transported pulled-back arrow.
Flat base change preserves the coefficient hypotheses. Full faithfulness of target complete
restriction then gives uniqueness, precisely when the two target objects are complete. -/
theorem uniqueLift
    (hflat : SheafOfModules.IsFlat ((restriction x.c).obj
      (SheafOfModules.unit (siteModuleRings x.B))))
    (hquot : x.quotientIso)
    (M N : DerivedCategory (Endofunctor.IsoAlgebra x.actionB.modules))
    (hsourceM : x.nativeCompleteB M) (hsourceN : x.nativeCompleteB N)
    (hM : y.nativeCompleteB (v.modulesB.mapDerivedCategory.obj M))
    (hN : y.nativeCompleteB (v.modulesB.mapDerivedCategory.obj N))
    (h : x.derivedRestriction.obj M ⟶ x.derivedRestriction.obj N)
    (b : M ⟶ N) (hb : x.derivedRestriction.map b = h) :
    y.derivedRestriction.map (v.modulesB.mapDerivedCategory.map b) =
        (Pullback.derivedComparison v).inv.app M ≫ v.modulesR.mapDerivedCategory.map h ≫
          (Pullback.derivedComparison v).hom.app N ∧
      ∀ a : v.modulesB.mapDerivedCategory.obj M ⟶ v.modulesB.mapDerivedCategory.obj N,
        y.derivedRestriction.map a =
          (Pullback.derivedComparison v).inv.app M ≫ v.modulesR.mapDerivedCategory.map h ≫
            (Pullback.derivedComparison v).hom.app N →
        a = v.modulesB.mapDerivedCategory.map b := by
  have heq : y.derivedRestriction.map (v.modulesB.mapDerivedCategory.map b) =
      (Pullback.derivedComparison v).inv.app M ≫ v.modulesR.mapDerivedCategory.map h ≫
        (Pullback.derivedComparison v).hom.app N := by
    have hn := (Pullback.derivedComparison v).hom.naturality b
    change v.modulesR.mapDerivedCategory.map (x.derivedRestriction.map b) ≫
        (Pullback.derivedComparison v).hom.app N =
      (Pullback.derivedComparison v).hom.app M ≫
        y.derivedRestriction.map (v.modulesB.mapDerivedCategory.map b) at hn
    rw [hb] at hn
    apply (cancel_epi ((Pullback.derivedComparison v).hom.app M)).mp
    simpa only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp] using hn.symm
  refine ⟨heq, ?_⟩
  intro a ha
  exact Datum.completeRestriction_map_injective y (coefficientFlat v hflat)
    (coefficientQuotient v hquot) _ _ hM hN a (v.modulesB.mapDerivedCategory.map b)
    (ha.trans heq.symm)

end Pullback
end CategoryTheory.EquivariantCompleteRestriction
