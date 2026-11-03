/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.CompletionMap
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.Algebra.Homology.ProperBaseChange.KFlatResolutionGeneral
public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsAdjunctionQh

/-! # The canonical derived reduction Hom equivalence

Source: blueprint proper base change, order 1260, proof step 6.
(blueprint: lem-weil-pbc-adic-reduction-adjunction-hom-equiv).
-/

@[expose] public section
set_option autoImplicit false

universe t
open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings TensorProduct
namespace AlgebraicGeometry.Scheme

-- The imported adjunction specializes its site-size instance to another coefficient universe.
-- Keep that instance out of this proof; the site here already has size t + 1.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Restriction of scalars is exact, also when the small site's object and morphism
universes differ. Source: order 1260, proof step 6; Stacks Tag 03D3.
Proof: restriction leaves the underlying abelian sheaf unchanged. Kernels and cokernels
are computed on those sheaves, with the restricted action, so it preserves both.
(blueprint: lemma-weil-pbc-adic-completion-reduction) -/
theorem adicRestrictScalars_exact (X : Scheme.{t}) {A B : Type t}
    [CommRing A] [CommRing B] (φ : A →+* B) :
    PreservesFiniteLimits (SheafOfModules.restrictScalars.{t + 1} (adicModuleMap X φ)) ∧
      PreservesFiniteColimits (SheafOfModules.restrictScalars.{t + 1} (adicModuleMap X φ)) := by
  let F := SheafOfModules.restrictScalars.{t + 1} (adicModuleMap X φ)
  let UA := SheafOfModules.toSheaf.{t + 1, t, t + 1, t + 1} (adicModuleRing X A)
  let UB := SheafOfModules.toSheaf.{t + 1, t, t + 1, t + 1} (adicModuleRing X B)
  have hs : HasSheafify (ProEt.topology X) AddCommGrpCat.{t + 1} :=
    SheafOfModules.hasSheafify_coefficientUniverse.{t + 1, t, t + 1}
      (C := X.ProEt) (J := ProEt.topology X)
  have hw : GrothendieckTopology.WEqualsLocallyBijective.{t + 1, t + 1, t,
      t + 2, t + 1, t + 1} (ProEt.topology X) AddCommGrpCat.{t + 1} :=
    SheafOfModules.wEqualsLocallyBijective_coefficientUniverse.{t + 1, t, t + 1}
      (C := X.ProEt) (J := ProEt.topology X)
  have : PreservesFiniteColimits UA :=
    @SheafOfModules.preservesFiniteColimits_toSheaf.{t + 1, t, t + 1, t + 1}
      X.ProEt inferInstance (ProEt.topology X) _ hs hw
  have : PreservesFiniteColimits UB :=
    @SheafOfModules.preservesFiniteColimits_toSheaf.{t + 1, t, t + 1, t + 1}
      X.ProEt inferInstance (ProEt.topology X) _ hs hw
  have : PreservesFiniteLimits (F ⋙ UA) :=
    inferInstanceAs (PreservesFiniteLimits UB)
  have : PreservesFiniteColimits (F ⋙ UA) :=
    inferInstanceAs (PreservesFiniteColimits UB)
  have : ReflectsFiniteColimits UA :=
    { reflects := fun _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms }
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves F UA,
    preservesFiniteColimits_of_reflects_of_preserves F UA⟩

/-- Exact derived restriction along the constant coefficient map.
Source: order 1260, proof step 6 (blueprint: lemma-weil-pbc-adic-completion-reduction). -/
noncomputable def adicDerivedRestrict (X : Scheme.{t}) {A B : Type t}
    [CommRing A] [CommRing B] (φ : A →+* B) :
    proEtaleDerivedCategory X B ⥤ proEtaleDerivedCategory X A :=
  letI := HasDerivedCategory.standard (SheafOfModules.{t + 1} (adicModuleRing X A))
  letI := HasDerivedCategory.standard (SheafOfModules.{t + 1} (adicModuleRing X B))
  letI := (adicRestrictScalars_exact X φ).1
  letI := (adicRestrictScalars_exact X φ).2
  (SheafOfModules.restrictScalars.{t + 1} (adicModuleMap X φ)).mapDerivedCategory

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

/-- Restriction along the actual continuous coefficient quotient is exact.
Source: blueprint `def-pe-derived-complete`, coefficient reductions.
Proof: kernels and cokernels of module objects are computed on underlying abelian sheaves.
(blueprint: lem-weil-pbc-adic-reduction-adjunction-hom-equiv). -/
theorem adicRestrictScalars_exact (n : ℕ) :
    PreservesFiniteLimits (Mod.comap (AdicCompletion.quotient l E X n) :
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (AdicCompletion.finiteRing l E X n) ⥤ AdicCompletion.Modules l E X) ∧
      PreservesFiniteColimits (Mod.comap (AdicCompletion.quotient l E X n) :
        Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (AdicCompletion.finiteRing l E X n) ⥤ AdicCompletion.Modules l E X) :=
  ⟨inferInstance, inferInstance⟩

/-- Exact restriction from finite to integral continuous coefficient modules.
Source: blueprint `def-pe-derived-complete`, reduction with its coefficient action.
(blueprint: lem-weil-pbc-adic-reduction-adjunction-hom-equiv). -/
def adicDerivedRestrict (n : ℕ) :
    AdicCompletion.FiniteDerived l E X n ⥤ DerivedCategory (AdicCompletion.Modules l E X) :=
  AdicCompletion.restrict l E X n

/-- The canonical comparison with termwise restriction on a complex.
Source: blueprint `def-pe-derived-complete`, coefficient reductions.
(blueprint: lem-weil-pbc-adic-reduction-adjunction-hom-equiv). -/
def adicDerivedRestrictFactors (n : ℕ)
    (P : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (AdicCompletion.finiteRing l E X n)) ℤ) :
    (adicDerivedRestrict l E X n).obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj
        (((Mod.comap (AdicCompletion.quotient l E X n)).mapHomologicalComplex (.up ℤ)).obj P) :=
  (Mod.comap (AdicCompletion.quotient l E X n)).mapDerivedCategoryFactors.app P

/-- The scalar unit for reduction to positive level n+1.
Source: blueprint `def-pe-derived-complete`, the maps K to K_n induced by the quotient.
(blueprint: lem-weil-pbc-adic-reduction-adjunction-hom-equiv). -/
def adicReductionDerivedUnit (n : ℕ) (K : DerivedCategory (AdicCompletion.Modules l E X)) :
    K ⟶ (adicDerivedRestrict l E X n).obj ((AdicCompletion.derivedReduction l E X n).obj K) :=
  (Mod.derivedExtendMapDerivedCategoryAdjunction
    (AdicCompletion.quotient l E X n)).unit.app K

/-- The scalar unit agrees with the ordinary tensor unit through the derived counit.
Source: blueprint `def-pe-derived-complete`, canonical quotient maps.
Proof: apply the normalized derived extension--restriction unit computation to the
continuous pulled-back quotient morphism and the given homotopy object.
(blueprint: lem-weil-pbc-adic-reduction-adjunction-hom-equiv). -/
theorem adicReductionDerivedUnit_cochain (n : ℕ)
    (P : HomotopyCategory (AdicCompletion.Modules l E X) (.up ℤ)) :
    adicReductionDerivedUnit l E X n (DerivedCategory.Qh.obj P) ≫
        (adicDerivedRestrict l E X n).map
          ((Mod.extendScalars (AdicCompletion.quotient l E X n)).leftDerivedFunctorCounit.app P) =
      DerivedCategory.Qh.map
          (((Mod.extendRestrictAdjunction (AdicCompletion.quotient l E X n)
            ).mapHomotopyCategory (.up ℤ)).unit.app P) ≫
        (Mod.comap (AdicCompletion.quotient l E X n)).mapDerivedCategoryFactorsh.inv.app
          (((Mod.extendScalars (AdicCompletion.quotient l E X n)
            ).mapHomotopyCategory (.up ℤ)).obj P) :=
  Mod.derivedExtendMapDerivedCategoryAdjunction_unit_app_Qh _ P

/-- The canonical derived scalar Hom equivalence has the specified scalar-unit formula.
Source: blueprint `def-pe-derived-complete`, derived tensor reduction.
Proof: use the derived extension--restriction adjunction for the actual quotient ring
objects, and its defining Hom-equivalence unit formula.
(blueprint: lem-weil-pbc-adic-reduction-adjunction-hom-equiv). -/
theorem adicReductionAdjunction_homEquiv_exists (n : ℕ)
    (K : DerivedCategory (AdicCompletion.Modules l E X))
    (H : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (AdicCompletion.finiteRing l E X n))) :
    ∃ e : ((AdicCompletion.derivedReduction l E X n).obj K ⟶ H) ≃
      (K ⟶ (adicDerivedRestrict l E X n).obj H),
      ∀ f, e f = adicReductionDerivedUnit l E X n K ≫
        (adicDerivedRestrict l E X n).map f := by
  let adj := Mod.derivedExtendMapDerivedCategoryAdjunction (AdicCompletion.quotient l E X n)
  exact ⟨adj.homEquiv K H, fun f ↦ adj.homEquiv_unit K H f⟩

/-- The specified unit formula is bijective.
Source: blueprint `def-pe-derived-complete`, scalar adjunction.
Proof: identify the formula pointwise with the preceding Hom equivalence.
(blueprint: lem-weil-pbc-adic-reduction-adjunction-hom-equiv). -/
theorem adicReductionAdjunction_bijective (n : ℕ)
    (K : DerivedCategory (AdicCompletion.Modules l E X))
    (H : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (AdicCompletion.finiteRing l E X n))) :
    Function.Bijective (fun f : (AdicCompletion.derivedReduction l E X n).obj K ⟶ H ↦
      adicReductionDerivedUnit l E X n K ≫ (adicDerivedRestrict l E X n).map f) := by
  obtain ⟨e, he⟩ := adicReductionAdjunction_homEquiv_exists l E X n K H
  have h : (fun f ↦ adicReductionDerivedUnit l E X n K ≫
      (adicDerivedRestrict l E X n).map f) = e := funext fun f ↦ (he f).symm
  rw [h]
  exact e.bijective

/-- The Hom equivalence with the scalar-unit formula as its forward function.
Source: blueprint `def-pe-derived-complete`, scalar adjunction.
(blueprint: lem-weil-pbc-adic-reduction-adjunction-hom-equiv). -/
def adicReductionHomEquiv (n : ℕ) (K : DerivedCategory (AdicCompletion.Modules l E X))
    (H : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (AdicCompletion.finiteRing l E X n))) :
    ((AdicCompletion.derivedReduction l E X n).obj K ⟶ H) ≃
      (K ⟶ (adicDerivedRestrict l E X n).obj H) :=
  Equiv.ofBijective _ (adicReductionAdjunction_bijective l E X n K H)

/-- Reduction of a morphism, characterized by its scalar-unit square.
Source: blueprint `def-pe-derived-complete`, functoriality of tensor reduction.
(blueprint: lem-weil-pbc-adic-reduction-adjunction-hom-equiv). -/
def adicReductionMap (n : ℕ) {K L : DerivedCategory (AdicCompletion.Modules l E X)}
    (f : K ⟶ L) :
    (AdicCompletion.derivedReduction l E X n).obj K ⟶
      (AdicCompletion.derivedReduction l E X n).obj L :=
  (adicReductionHomEquiv l E X n K _).symm (f ≫ adicReductionDerivedUnit l E X n L)

/-- The defining scalar-unit square for reduction on morphisms.
Source: blueprint `def-pe-derived-complete`, functoriality.
Proof: apply the canonical Hom equivalence to its inverse.
(blueprint: lem-weil-pbc-adic-reduction-adjunction-hom-equiv). -/
theorem adicReductionMap_unit (n : ℕ) {K L : DerivedCategory (AdicCompletion.Modules l E X)}
    (f : K ⟶ L) :
    adicReductionDerivedUnit l E X n K ≫
        (adicDerivedRestrict l E X n).map (adicReductionMap l E X n f) =
      f ≫ adicReductionDerivedUnit l E X n L :=
  (adicReductionHomEquiv l E X n K _).apply_symm_apply _

/-- The adjunction construction is the actual derived reduction on morphisms.
Source: blueprint `def-pe-derived-complete`, specified tensor reduction.
Proof: unit naturality identifies its transpose with the defining transpose.
(blueprint: lem-weil-pbc-adic-reduction-adjunction-hom-equiv). -/
theorem adicReductionMap_eq (n : ℕ) {K L : DerivedCategory (AdicCompletion.Modules l E X)}
    (f : K ⟶ L) : adicReductionMap l E X n f =
      (AdicCompletion.derivedReduction l E X n).map f := by
  apply (adicReductionHomEquiv l E X n K _).injective
  exact (adicReductionMap_unit l E X n f).trans
    ((Mod.derivedExtendMapDerivedCategoryAdjunction
      (AdicCompletion.quotient l E X n)).unit.naturality f)

/-- Reduction respects composition.
Source: blueprint `def-pe-derived-complete`, functoriality.
Proof: apply injectivity of the Hom equivalence and its unit square twice.
(blueprint: lem-weil-pbc-adic-reduction-adjunction-hom-equiv). -/
theorem adicReductionMap_comp (n : ℕ)
    {K L H : DerivedCategory (AdicCompletion.Modules l E X)} (f : K ⟶ L) (g : L ⟶ H) :
    adicReductionMap l E X n (f ≫ g) =
      adicReductionMap l E X n f ≫ adicReductionMap l E X n g := by
  apply (adicReductionHomEquiv l E X n K _).injective
  change adicReductionDerivedUnit l E X n K ≫ (adicDerivedRestrict l E X n).map _ =
    adicReductionDerivedUnit l E X n K ≫ (adicDerivedRestrict l E X n).map _
  rw [adicReductionMap_unit, Functor.map_comp, ← Category.assoc, adicReductionMap_unit]
  simp only [Category.assoc]
  rw [adicReductionMap_unit]

/-- Reduction respects identities.
Source: blueprint `def-pe-derived-complete`, functoriality.
Proof: the identity satisfies the defining unit square.
(blueprint: lem-weil-pbc-adic-reduction-adjunction-hom-equiv). -/
theorem adicReductionMap_id (n : ℕ) (K : DerivedCategory (AdicCompletion.Modules l E X)) :
    adicReductionMap l E X n (𝟙 K) = 𝟙 _ := by
  rw [adicReductionMap_eq, CategoryTheory.Functor.map_id]

/-- Reduction takes isomorphisms to isomorphisms.
Source: blueprint `def-pe-derived-complete`, functoriality.
Proof: reduce an inverse and use the proved composition and identity laws.
(blueprint: lem-weil-pbc-adic-reduction-adjunction-hom-equiv). -/
theorem adicReductionMap_isIso (n : ℕ)
    {K L : DerivedCategory (AdicCompletion.Modules l E X)} (f : K ⟶ L) [IsIso f] :
    IsIso (adicReductionMap l E X n f) := by
  refine ⟨⟨adicReductionMap l E X n (inv f), ?_, ?_⟩⟩
  · rw [← adicReductionMap_comp, IsIso.hom_inv_id, adicReductionMap_id]
  · rw [← adicReductionMap_comp, IsIso.inv_hom_id, adicReductionMap_id]

end AlgebraicGeometry.ProEtale
