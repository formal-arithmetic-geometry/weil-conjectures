/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Sheaf.AlgebraicGeometry.EtaleSetInverseImageStalkGerm
import Sheaf.AlgebraicGeometry.FinitePushforwardSetStalk
import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.GeometricFiber

/-! # Finite surjective descent of global sections for étale sheaves of sets

Source: literature/stacks-project/etale-cohomology.tex, Remark 09Z3
(blueprint: lem-weil-pbc-sets-finite-surjective-descent).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Section pullback along the adjunction unit. Source: Stacks, Remark 09Z3
(blueprint: lem-weil-pbc-sets-finite-surjective-descent). -/
noncomputable def etaleSetDescentUnit {S T : Scheme.{u}} (e : T ⟶ S)
    (G : Sheaf S.smallEtaleTopology (Type (u + 1))) (U : S.Etale) :=
  ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.pullback @Etale ⊤ e) (Type (u + 1))
    (S.smallGrothendieckTopology @Etale)
    (T.smallGrothendieckTopology @Etale)).unit.app G).hom.app (op U)

/-- Pull back a section and apply the unit-compatible composition comparison, then
identify the iterated fibre product with the composite fibre product.
Source: Stacks, Remark 09Z3 (blueprint: lem-weil-pbc-sets-finite-surjective-descent). -/
noncomputable def etaleSetDescentComparison {X Y W : Scheme.{u}}
    (f : Y ⟶ X) (g : W ⟶ Y)
    (G : Sheaf X.smallEtaleTopology (Type (u + 1))) (U : X.Etale)
    (s : ((Scheme.etaleSetPullback f).obj G).obj.obj
      (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U))) :=
  ((Scheme.etaleSetPullback (g ≫ f)).obj G).obj.map
    ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) g f).hom.app U).op
    ((((Classical.choose etaleSetInverseImageCompositionUnits.2.2) X Y W f g).hom.app G).hom.app
       (op ((MorphismProperty.Over.pullback @Etale ⊤ g).obj
        ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U)))
      (etaleSetDescentUnit g ((Scheme.etaleSetPullback f).obj G)
        ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U) s))

/-- Source: Stacks Project, Étale Cohomology, Remark 09Z3, following Lemma 09Z2.
(blueprint: lem-weil-pbc-sets-finite-surjective-descent)
The unit on global sections is injective with image exactly the equalizer of the
projection pullbacks, composed with the inverse-image composition comparisons.

Proof:
1. The first projection is finite by lem-weil-pbc-finite-morphism-permanence;
   its composite with f is finite by lem-weil-pbc-finite-composition.
2. Construct A = f_* f⁻¹G and B = f₁* f₁⁻¹G, their unit and the two projection
   maps, using lem-weil-pbc-sets-etale-inverse-image-composition-units and the
   natural fibre-product pasting isomorphisms of def-pc-fibre-product.
3. The composition unit equation makes the unit equalize these maps. The
   sectionwise equalizer E is a sheaf by lem-weil-pbc-site-sheaf-sets-limits-sectionwise.
4. At a geometric point the lifts P are nonempty by surjectivity and
   lem-weil-pbc-finite-geometric-point-lift. The double-fibre lifts are P × P.
5. By lem-weil-pbc-sets-finite-pushforward-stalk and
   lem-weil-pbc-sets-etale-inverse-image-stalk-germ, the stalks of A and B are
   products of G's stalk over P and P × P respectively.
6. The unit becomes the diagonal: check on germs using the germ formula of
   lem-weil-pbc-sets-etale-inverse-image-stalk-germ and def-weil-pbc-category-colimit.
7. The composition comparisons respect stalk identifications: check on the
   locally generating pulled-back germs using the composition unit equation.
8. Thus the two maps on stalks become the two coordinate projections; verify
   on germs of sections of A using the canonical pointed fibre-product isomorphisms.
9. By lem-weil-pbc-sets-etale-stalk-finite-limits, E's stalk is the equalizer,
   hence exactly the constant families. Nonemptiness of P makes its diagonal bijective.
10. The geometric stalk criterion lem-weil-pbc-sets-etale-iso-on-geometric-stalks
    gives G ≅ E. Evaluate at the identity étale neighbourhood to get the claim. -/
theorem finiteSurjectiveSetDescent
    {X X' : Scheme.{u}} (f : X' ⟶ X) [IsFinite f] [Surjective f]
    (G : Sheaf X.smallEtaleTopology (Type (u + 1))) :
    Function.Injective (etaleSetDescentUnit f G (Scheme.Etale.mk (𝟙 X))) ∧
      ∀ s' : ((Scheme.etaleSetPullback f).obj G).obj.obj
          (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj
            (Scheme.Etale.mk (𝟙 X)))),
        etaleSetDescentComparison f (pullback.fst f f) G (Scheme.Etale.mk (𝟙 X)) s' =
          eqToHom (congrArg
            (fun k : pullback f f ⟶ X ↦ ((Scheme.etaleSetPullback k).obj G).obj.obj
              (op ((MorphismProperty.Over.pullback @Etale ⊤ k).obj
                (Scheme.Etale.mk (𝟙 X))))) (pullback.condition (f := f) (g := f)).symm)
            (etaleSetDescentComparison f (pullback.snd f f) G
              (Scheme.Etale.mk (𝟙 X)) s') ↔
          ∃ s : G.obj.obj (op (Scheme.Etale.mk (𝟙 X))),
            etaleSetDescentUnit f G (Scheme.Etale.mk (𝟙 X)) s = s' := by
  sorry

end AlgebraicGeometry
