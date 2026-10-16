/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtension
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-!
# Continuous coefficients and slice restrictions for lisse lattices

The coefficient constructions used by the etale-local lattice theorem.
Source: Bhatt--Scholze, Definitions 6.8.1 and 6.8.3.
(blueprint: def-weil-pbc-lisse-lattice-coefficients)
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.ProEtale

/-- The commutative-ring version of the existing continuous-function ring sheaf.
Source: Bhatt--Scholze, Definition 6.8.1
(blueprint: lem-weil-pbc-lisse-lattice-etale-local). -/
noncomputable def lisseContinuousCommRingSheaf (X : Scheme.{u}) (T : Type)
    [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] :
    Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1} :=
  ⟨{ obj := fun U ↦ CommRingCat.of (ULift.{u + 1} C(U.unop.left, T))
     map := fun f ↦ CommRingCat.ofHom ((continuousMapRingPresheaf X T).map f).hom
     map_id := fun _ ↦ rfl
     map_comp := fun _ _ ↦ rfl },
   Presheaf.isSheaf_of_isSheaf_comp _ _ (forget₂ CommRingCat RingCat)
     (isSheaf_continuousMapRingPresheaf X T)⟩

/-- The continuous coefficient sheaf, with the canonical extension of the p-adic norm.
Source: Bhatt--Scholze, Definition 6.8.1
(blueprint: lem-weil-pbc-lisse-lattice-etale-local). -/
noncomputable def lisseFieldSheaf (l : ℕ) [Fact l.Prime] (E : Type) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u}) :
    Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1} :=
  letI := spectralNorm.normedField ℚ_[l] E
  lisseContinuousCommRingSheaf X E

/-- The integral coefficient sheaf, with the topology induced from the coefficient field.
Source: Bhatt--Scholze, Definition 6.8.1
(blueprint: lem-weil-pbc-lisse-lattice-etale-local). -/
noncomputable def lisseIntegerSheaf (l : ℕ) [Fact l.Prime] (E : Type) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u}) :
    Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1} :=
  letI := spectralNorm.normedField ℚ_[l] E
  lisseContinuousCommRingSheaf X (Padic.coefficientExtensionIntegers l E)

/-- Postcomposition with the valuation-ring inclusion is the scalar extension map.
Source: Bhatt--Scholze, Proposition 6.8.4(6)
(blueprint: lem-weil-pbc-lisse-lattice-etale-local). -/
noncomputable def lisseIntegerToField (l : ℕ) [Fact l.Prime] (E : Type) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u}) :
    lisseIntegerSheaf l E X ⟶ lisseFieldSheaf l E X :=
  letI := spectralNorm.normedField ℚ_[l] E
  ⟨{ app := fun U ↦ CommRingCat.ofHom
       ((continuousMapRingPresheafMap X (Padic.coefficientExtensionIntegers l E).subtype
         continuous_subtype_val).app U).hom
     naturality := fun _ _ _ ↦ rfl }⟩

/-- Composition with an etale arrow embeds its small pro-etale site into the ambient site.
Source: Bhatt--Scholze, Proposition 6.8.4(6), slice-site restriction
(blueprint: lem-weil-pbc-lisse-lattice-etale-local). -/
noncomputable def lisseEtaleSiteInclusion {X Y : Scheme.{u}} (f : Y ⟶ X) [Etale f] :
    Y.ProEt ⥤ X.ProEt where
  obj V := Scheme.ProEt.mk (V.hom ≫ f)
  map {V W} a := MorphismProperty.Over.homMk a.left
    ((Category.assoc a.left W.hom f).symm.trans
      (congrArg (fun b : V.left ⟶ Y ↦ b ≫ f) a.w))

/-- The slice coefficient identification is the identity on continuous functions.
Source: Bhatt--Scholze, Proposition 6.8.4(6)
(blueprint: lem-weil-pbc-lisse-lattice-etale-local). -/
noncomputable def lisseEtaleCoefficientIdentification (l : ℕ) [Fact l.Prime]
    (E : Type) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (f : Y ⟶ X) [Etale f] :
    ((sheafCompose (Scheme.ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (lisseFieldSheaf l E Y)).obj ⟶
    (lisseEtaleSiteInclusion f).op ⋙
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (lisseFieldSheaf l E X)).obj :=
  { app := fun _ ↦ 𝟙 _
    naturality := fun _ _ _ ↦ rfl }

end AlgebraicGeometry.ProEtale
