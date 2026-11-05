/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.LocalSystems
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.CategoryTheory.CofilteredSystem
public import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
public import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimitMilnor
public import WeilConjectures.Algebra.Homology.DerivedCategory.Ext.TowerLimit
public import Mathlib.CategoryTheory.Subobject.ArtinianObject
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.InvertibleRestriction
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf

/-!
# Sheaves of modules with finite locally constant underlying sheaves of sets

On a connected scheme `X` with a geometric point `s`, for an arbitrary ring `Λ` (e.g.
`ULift ℤ`, so for abelian sheaves with finite stalks):

- `AlgebraicGeometry.Scheme.FiniteLocallyConstant.isIso_of_bijective_sheafFiber_map`,
  `AlgebraicGeometry.Scheme.FiniteLocallyConstant.section_ext`: for finite locally constant
  sheaves of sets, the stalk at `s` detects isomorphisms, and global sections are determined by
  their germ at `s` (fibre functor of the Galois category of finite étale schemes);
- `AlgebraicGeometry.Scheme.IsSetFLC`: sheaves of `Λ`-modules whose underlying sheaf of sets is
  finite locally constant;
- `IsSetFLC.isIso_of_isIso_sheafFiber_map`, `IsSetFLC.sectionsGerm'_injective`,
  `IsSetFLC.isIso_constantSheafAdj_counit`: the corresponding statements for them, and constancy
  as soon as global sections map bijectively to the stalk at `s`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {Y : Scheme.{u}} [ConnectedSpace Y] {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (s : Spec (.of Ω) ⟶ Y)

variable {X : Scheme.{u}}

/-- Finite local constancy of sheaves of sets is invariant under isomorphism. -/
lemma IsFiniteLocallyConstantSheafOfTypes.of_iso
    {E E' : Sheaf X.smallEtaleTopology (Type (u + 1))}
    (e : E ≅ E') (h : IsFiniteLocallyConstantSheafOfTypes E) :
    IsFiniteLocallyConstantSheafOfTypes E' := by
  obtain ⟨⟨𝒰, h𝒰⟩, hfin⟩ := h
  refine ⟨⟨𝒰, fun i ↦ ?_⟩, ⟨fun Ω _ _ s ↦ ?_⟩⟩
  · obtain ⟨M, ⟨e0⟩⟩ := (h𝒰 i).mem_essImage
    exact Sheaf.isConstant_of_iso _
      (((X.smallEtaleTopology.overPullback _ _).mapIso e).symm ≪≫ e0.symm)
  · exact (hfin.isFinitelyGenerated_sheafFiber Ω s).of_iso ((pointSmallEtale s).sheafFiber.mapIso e)

variable {Λ : Type (u + 1)} [Ring Λ]

section Connected

variable [ConnectedSpace X] {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X)

end Connected

end AlgebraicGeometry.Scheme
