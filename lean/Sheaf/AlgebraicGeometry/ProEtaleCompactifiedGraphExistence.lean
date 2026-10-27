/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H3
-/
module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.Compactification.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs

/-! # Existence and uniqueness of the pro-etale compactification graph map

Source: Stacks Project, Tag 0F4L, the clopen graph construction.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- The clopen graph construction gives a unique map for any specified left adjoint
of restriction. This separates graph existence from comparison of the two sites.

Source: Stacks Project, etale-cohomology.tex, Tag 0F4L,
lemma-shriek-into-star-separated-etale; proetale.tex, Tag 09AF.
(blueprint: lem-sp-proetale-compactified-graph-existence).

Proof: for each weakly etale object b over U, the two projections specify the
map b -> Z times_T b uniquely by the fibre-product universal property. Its image
is open because the graph is a section of the etale map U times_T b -> b, and
closed because Z -> T is separated. The open-extension unit supplies the value
of a section m on this graph. Glue that value with zero on the complementary
open. The disjoint-open sheaf condition gives existence and uniqueness, including
for the empty test scheme. Restriction and linear maps preserve both prescribed
values, so uniqueness makes this construction linear and natural in b and M.
Direct-sum elimination followed by sheafification gives the map from the usual
sum extension. Transport along the unique unit-preserving isomorphism from F
to that sum extension. Finally, transpose any other graph map under adj: its
values on every b and m are the same unique glued sections, so its transpose,
and hence the map itself, agrees with the constructed map. -/
theorem compactified_graph_existsUnique
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] [IsSeparated e]
    [LocallyOfFiniteType e] [QuasiCompact e] (c : Compactification e)
    (F : Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} A) ⥤
      Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))
    (adj : F ⊣ localizationRestriction (ModuleCat.{u + 1} A) e inferInstance)
    : ∃! G : F ⟶
      openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i ⋙
        lowerStar (ModuleCat.{u + 1} A) c.g,
  ∀ (M : Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} A)) (b : U.ProEt),
    ∃ γ :
      (MorphismProperty.Over.map (P := @WeaklyEtale) ⊤
        (inferInstance : WeaklyEtale c.i)).obj b ⟶
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ c.g).obj
        ((MorphismProperty.Over.map (P := @WeaklyEtale) ⊤
          (inferInstance : WeaklyEtale e)).obj b),
      γ.left ≫ pullback.fst (b.hom ≫ e) c.g = 𝟙 b.left ∧
      γ.left ≫ pullback.snd (b.hom ≫ e) c.g = b.hom ≫ c.i ∧
      IsOpenImmersion γ.left ∧ IsClosedImmersion γ.left ∧
      ∀ m : M.obj.obj (op b),
        (((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).obj M).obj.map γ.op)
          (((G.app M).hom.app
            (op ((MorphismProperty.Over.map (P := @WeaklyEtale) ⊤
              (inferInstance : WeaklyEtale e)).obj b)))
            ((adj.unit.app M).hom.app (op b) m)) =
          (((openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} A) c.i).unit.app M).hom.app
            (op b) m) ∧
        ∀ (D : c.Z.ProEt)
          (k : D ⟶ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ c.g).obj
            ((MorphismProperty.Over.map (P := @WeaklyEtale) ⊤
              (inferInstance : WeaklyEtale e)).obj b)),
          IsOpenImmersion k.left → Set.range k.left = (Set.range γ.left)ᶜ →
          (((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).obj M).obj.map k.op)
            (((G.app M).hom.app
              (op ((MorphismProperty.Over.map (P := @WeaklyEtale) ⊤
                (inferInstance : WeaklyEtale e)).obj b)))
              ((adj.unit.app M).hom.app (op b) m)) = 0 := by
  sorry

end AlgebraicGeometry.ProEtale
