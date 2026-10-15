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
import Sheaf.AlgebraicGeometry.ProEtaleLocallyClassicalEtaleCover
import Sheaf.Paper.LatticeSheafLocallyConstant

/-!
# Etale-local integral lattices in lisse coefficient sheaves

Source: Bhatt--Scholze, Proposition 6.8.4(6) and Definition 6.8.3
(blueprint: lem-weil-pbc-lisse-lattice-etale-local).
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

/-- A lisse coefficient sheaf admits lisse integral lattices after an etale cover.
The right-hand presheaf is the sectionwise slice-site presentation of `f⁻¹ L`, with
its coefficient action identified by the identity on continuous functions. An isomorphism
of these module presheaves is an isomorphism of module sheaves, since the forgetful
functor from module sheaves is fully faithful. Finite local freeness allows variable
ranks and rank zero. The empty scheme permits the empty etale covering.

Source: Bhatt--Scholze, Proposition 6.8.4(6), Definition 6.8.3
(blueprint: lem-weil-pbc-lisse-lattice-etale-local).

Proof plan:
1. Apply `lem-weil-pbc-lattice-sheaf-locally-constant` to the isomorphism classes of
   integral lattices with scalar-extension isomorphism. On each trivializing pro-etale
   member of rank n this is the constant sheaf GL_n(E)/GL_n(A). The identity coset gives
   a local section, also for n = 0.
2. Apply `lem-weil-pbc-proetale-locally-classical-etale-cover` to descend inhabitedness
   to an etale covering. No compatibility among its sections is required.
3. Choose lattice representatives on the members. Their defining isomorphisms are the
   required scalar-extension isomorphisms. Slice-site restriction is inverse image with
   the displayed coefficient identification. For the empty scheme use the empty family. -/
theorem exists_lisse_lattice_etale_local (l : ℕ) [Fact l.Prime] (E : Type) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})
    (L : ringedSiteModules.{u + 1} ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (lisseFieldSheaf l E X)))
    (hL : L.IsFiniteLocallyFree) :
    ∃ (I : Type (u + 1)) (Y : I → X.Etale),
      (X.smallEtaleTopology).CoversTop Y ∧
      ∀ i : I, ∃ M : ringedSiteModules.{u + 1}
        ((sheafCompose (Scheme.ProEt.topology (Y i).left)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (lisseIntegerSheaf l E (Y i).left)),
        M.IsFiniteLocallyFree ∧
        Nonempty ((SheafOfModules.changeOfRings
          (lisseIntegerToField l E (Y i).left) M).val ≅
          (PresheafOfModules.pushforward
            (lisseEtaleCoefficientIdentification l E (Y i).hom)).obj L.val) := by
  sorry

end AlgebraicGeometry.ProEtale
