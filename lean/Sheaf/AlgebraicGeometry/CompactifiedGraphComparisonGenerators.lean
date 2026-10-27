/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H3
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMapProjection
public import Sheaf.AlgebraicGeometry.EtaleCompactificationGraphMap
public import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
public import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison

/-! # Comparing compactified graph values on lift generators -/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- A graph map commutes with site comparison whenever the sum comparison preserves
its actual lift generators. The assertion concerns a given graph map, and does
not construct it or assert exactness of either sum extension.

Source: Stacks Project, proetale.tex, Tag 09AF and the comparison morphism square;
etale-cohomology.tex, Tag 0F4L, the clopen graph construction.
(blueprint: lem-sp-compactified-graph-comparison-generators).

Proof: transpose both maps under the comparison adjunction on T. Expand the
specified mate d of the inverse pullback comparison. The conjugate unit equation
for the canonical pullback comparison cancels its inverse, and naturality of the
comparison unit followed by the direct-image triangle identity gives
R_T(d) eta_T = p_* eta_Z. Thus the right transpose is the etale graph map followed
by p_*(R_Z(o) eta_Z), where o is the canonical open comparison. The open-comparison
unit normalization and the open-restriction equation for the comparison unit
identify the restriction of R_Z(o) eta_Z with eta_U. On every raw lift generator,
the right transpose therefore has graph value eta_U(m) and complementary value
zero. The canonical etale graph map has exactly its construction's values m and
zero; expand its base-change factor, the map from q^* to s_!, and the
unit-preserving comparison s_! v_! = i_!. Base change keeps the lift, the clopen
open-to-star isomorphism makes the middle factor extension of m by zero, and
unit preservation keeps that value under composition. Thus this adjunction
formula has the graph values of Tag 0F4L.
The assumed generator equation for sigma and the graph hypothesis for G give
the same two values for the left transpose. Uniqueness of disjoint-open gluing
identifies these sections. The direct-sum and sheafification universal properties
then identify the transposes; injectivity of the adjunction Hom equivalence gives
the displayed equality. This argument is natural in M and uses no invertibility
of d. Empty tests, the zero coefficient ring, and identity compactifications obey
the same gluing and adjunction identities. -/
theorem compactified_graph_comparison_of_generators
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] [IsSeparated e]
    [LocallyOfFiniteType e] [QuasiCompact e] (c : Compactification e)
    (F : Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} A) ⥤
      Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))
    (adj : F ⊣ localizationRestriction (ModuleCat.{u + 1} A) e inferInstance)
    (σ : Etale.etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance ⋙
      comparisonUpperStar (ModuleCat.{u + 1} A) T ≅
        comparisonUpperStar (ModuleCat.{u + 1} A) U ⋙ F)
    (hσ : ∀ (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) (b : U.Etale)
      (m : M.obj.obj (op b)),
      (((comparisonLowerStar (ModuleCat.{u + 1} A) T).map
        (σ.hom.app M)).hom.app
          (op ((MorphismProperty.Over.map (P := @Etale) ⊤
            (inferInstance : Etale e)).obj b)))
        ((((comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app
          ((Etale.etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).obj M)).hom.app
            (op ((MorphismProperty.Over.map (P := @Etale) ⊤
              (inferInstance : Etale e)).obj b)))
          ((((Etale.etaleLowerShriekAdjunction (ModuleCat.{u + 1} A) e
            inferInstance).unit.app M).hom.app (op b)) m)) =
        ((adj.unit.app
          ((comparisonUpperStar (ModuleCat.{u + 1} A) U).obj M)).hom.app
            (op ((Scheme.toProEt U).obj b)))
          ((((comparisonAdjunction (ModuleCat.{u + 1} A) U).unit.app M).hom.app (op b)) m))
    (G : F ⟶
      openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i ⋙
        lowerStar (ModuleCat.{u + 1} A) c.g)
    (hG :
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
              ((adj.unit.app M).hom.app (op b) m)) = 0) :
    ∀ M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A),
        σ.hom.app M ≫
          G.app ((comparisonUpperStar (ModuleCat.{u + 1} A) U).obj M) =
        (comparisonUpperStar (ModuleCat.{u + 1} A) T).map
            ((Etale.etaleCompactificationGraphMap A e c).app M) ≫
          ((mateEquiv
            (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) c.g)
            (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) c.g)
            (TwoSquare.mk (comparisonUpperStar (ModuleCat.{u + 1} A) T)
              (Etale.upperStar (ModuleCat.{u + 1} A) c.g)
              (upperStar (ModuleCat.{u + 1} A) c.g)
              (comparisonUpperStar (ModuleCat.{u + 1} A) c.Z)
              (comparisonCoefficientPullbackIso (ModuleCat.{u + 1} A) c.g).inv)).natTrans).app
            ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).obj M) ≫
          (lowerStar (ModuleCat.{u + 1} A) c.g).map
            ((openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} A)
              c.i).hom.app M) := by
  sorry

end AlgebraicGeometry.ProEtale
