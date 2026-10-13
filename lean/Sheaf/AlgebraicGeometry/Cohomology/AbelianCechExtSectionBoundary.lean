/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C2
-/
module

public import Sheaf.AlgebraicGeometry.Cohomology.AbelianCechComparisonConstruction
public import Mathlib.Algebra.Homology.HomologySequence

/-! # Ext boundary equals the horseshoe section boundary

Source: Stacks Project, Tags 01EQ and 0117.
(blueprint: lem-pc-abelian-cech-ext-section-boundary)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] cohomologyHasSheafify cohomologyHasExt

/-- The cocycle-compatible Ext/section identifications preserve the boundary.
Source: Stacks 0117 (lift-differentiate-lift) and 01EQ (resolution sections).
(blueprint: lem-pc-abelian-cech-ext-section-boundary)

Proof: Fix an Ext class t in degree q of the last sheaf and use he₃ to
represent it by a cocycle c and section cycle z₃. Split the horseshoe row
in degree q and compose c with its section to obtain b in the middle
resolution. Its differential maps to zero in the last resolution, hence
factors uniquely through the first inclusion in degree q+1 as a. The
next differential of a is zero because its composite with the monic first
inclusion is the square of the middle differential. The injective-resolution
formula for the Ext boundary sends extMk(c) to extMk(a). Under the
constant-sheaf adjunction evaluated at 1, b lifts the section represented
by c, and its differential is the image of the section represented by a:
the adjunction is natural in each row map and differential. The concrete
homology boundary formula for hS therefore sends homologyπ(z₃) to the
homology class y of this latter section. To identify its Ext class using
he₁ without choosing a preferred representative, apply he₁ to e₁.inv(y).
Its section class is y by the isomorphism equation. The section-homology
injectivity lemma therefore identifies its Ext class with extMk(a).
Applying e₁.hom gives e₁.hom(extMk(a)) = y. Substitute the he₃ class
equation and use extensionality of additive maps. The Ext boundary formula
may first be computed in the standard large Ext universe; transport through
the canonical change-of-universe equivalence, which preserves cocycle
classes and composition with the short-exact extension class.
The lift formula also holds for q=0, with no negative-degree terms. No
cover, tuple set, or total complex is involved in this assertion. -/
theorem abelianCechExtSection_boundary
    {X : Scheme.{u}}
    (T : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}))
    (hT : T.ShortExact)
    (I₁ : InjectiveResolution T.X₁) (I₂ : InjectiveResolution T.X₂)
    (I₃ : InjectiveResolution T.X₃)
    (α : I₁.cocomplex ⟶ I₂.cocomplex) (β : I₂.cocomplex ⟶ I₃.cocomplex)
    (hαβ : α ≫ β = 0)
    (hα : I₁.ι ≫ α = (CochainComplex.single₀ _).map T.f ≫ I₂.ι)
    (hβ : I₂.ι ≫ β = (CochainComplex.single₀ _).map T.g ≫ I₃.ι)
    (hrows : ∀ n : ℕ, ((ShortComplex.mk α β hαβ).map
      (HomologicalComplex.eval _ (.up ℕ) n)).ShortExact)
    (hS : ((ShortComplex.mk α β hαβ).map
      ((sheafToPresheaf _ _ ⋙ (CategoryTheory.evaluation _ _).obj
        (op (⊤ : X.Opens))).mapHomologicalComplex (.up ℕ))).ShortExact)
    (q : ℕ)
    (e₁ : (Sheaf.functorH (Opens.grothendieckTopology X) (q + 1)).obj T.X₁ ≅
      (abelianCechSections I₁).homology (q + 1))
    (e₃ : (Sheaf.functorH (Opens.grothendieckTopology X) q).obj T.X₃ ≅
      (abelianCechSections I₃).homology q)
    (he₁ : ∀ (t : (Sheaf.functorH (Opens.grothendieckTopology X) (q + 1)).obj T.X₁),
      ∃ (a : (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶ I₁.cocomplex.X (q + 1))
        (ha : a ≫ I₁.cocomplex.d (q + 1) ((q + 1) + 1) = 0)
        (z : (abelianCechSections I₁).cycles (q + 1)),
        I₁.extMk a ((q + 1) + 1) rfl ha = t ∧
        ((constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
          isTerminalTop).homEquiv _ _ a) (ULift.up 1) =
            (abelianCechSections I₁).iCycles (q + 1) z ∧
        e₁.hom t = (abelianCechSections I₁).homologyπ (q + 1) z)
    (he₃ : ∀ (t : (Sheaf.functorH (Opens.grothendieckTopology X) q).obj T.X₃),
      ∃ (a : (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶ I₃.cocomplex.X q)
        (ha : a ≫ I₃.cocomplex.d q (q + 1) = 0)
        (z : (abelianCechSections I₃).cycles q),
        I₃.extMk a (q + 1) rfl ha = t ∧
        ((constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
          isTerminalTop).homEquiv _ _ a) (ULift.up 1) =
            (abelianCechSections I₃).iCycles q z ∧
        e₃.hom t = (abelianCechSections I₃).homologyπ q z) :
    Sheaf.functorHδ hT q ≫ e₁.hom = e₃.hom ≫ hS.δ q (q + 1) rfl  := by sorry

end AlgebraicGeometry.Scheme.Modules
