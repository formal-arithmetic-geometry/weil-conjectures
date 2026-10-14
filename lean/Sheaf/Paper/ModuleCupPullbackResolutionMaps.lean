/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Sheaf.Paper.ModuleCupResolutionData
public import Sheaf.AlgebraicGeometry.ModulePullbackTensor
public import Sheaf.AlgebraicGeometry.ModuleCohomologyFMap
import Sheaf.Paper.ModuleCupPullbackAugmentedPairings
import Sheaf.AlgebraicGeometry.ModuleCohomologyFMapFunctorial

/-! # Pullback maps between computing cup resolutions

Source: Stacks Project, Tags 0FKS, 0FKU and 01FD.
(blueprint: lem-sc-module-cup-pullback-resolution-maps).
-/

@[expose] public section

universe v
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

attribute [local irreducible] CupAcyclicResolution.class moduleCohomologyFMap
  cupResolutionGlobalMap tensorPullback

/-- There are computing pairings and additive maps of their global section complexes
that realize pullback in the three coefficients and preserve the section pairing.
No cohomological cup product is specified or assumed here.
Source: Stacks Project, Tag 0FKS (functorial Godement resolutions), Tag 0FKU
(naive cup product and Lemma 20.31.3), and Tag 01FD (resolution pullback diagram).
(blueprint: lem-sc-module-cup-pullback-resolution-maps).

Proof: use the Godement resolution on X and X' for F, G, F tensor G and their
pulled-back coefficients. For an open V, the map from the product of stalks on V
to the product on f-inverse V has at x' the component at f(x') followed by the
stalk map induced by the pullback unit. This commutes with the germ unit and stalk
evaluation. Iterate it to a map of cosimplicial Godement resolutions. Coordinatewise
tensor pairing is preserved: at each x' this is the tensor-pullback section equation.
The Alexander--Whitney pairing uses the same front and back faces on both schemes,
so the cosimplicial maps preserve it in every bidegree. Compose the tensor-coefficient
map with the canonical comparison f-star(F tensor G) to f-star F tensor f-star G.
The section normalization of this comparison gives the asserted pairing identity.
Godement terms are flasque and the augmented stalk complexes are contractible;
therefore they are computing resolutions. Equip them with injective comparisons.
The three maps extend respectively the pullback units of F, G and F tensor G
followed in the last case by the tensor comparison. Compare these diagrams with
the injective diagrams defining moduleCohomologyFMap. Resolution comparison and
homotopy independence identify their maps on global homology. The canonical
forgetting-scalars homology isomorphisms and the injective-resolution class
identifications give the three displayed class equations. At V=top the maps are
additive maps of global section complexes, even though their rings differ.
Neither exactness of tensor pullback nor acyclicity of a chosen open cover is used.
For the empty scheme all products and maps have zero sections. Zero coefficients
and degree zero obey the same additive and augmentation formulas. -/
theorem moduleCup_pullback_resolution_maps (X X' : Scheme.{v}) (f : X' ⟶ X)
    (F G : X.Modules) :
    ∃ (D : CupResolutionPairing F G)
      (E : CupResolutionPairing ((tensorPullback f).obj F) ((tensorPullback f).obj G))
      (l : ((RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙
        forget₂ _ AddCommGrpCat.{v}).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D.left.K ⟶
      ((RingedSpace.globalSectionsFunctor X'.toRingedSpace ⋙
        forget₂ _ AddCommGrpCat.{v}).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj E.left.K)
      (r : ((RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙
        forget₂ _ AddCommGrpCat.{v}).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D.right.K ⟶
      ((RingedSpace.globalSectionsFunctor X'.toRingedSpace ⋙
        forget₂ _ AddCommGrpCat.{v}).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj E.right.K)
      (t : ((RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙
        forget₂ _ AddCommGrpCat.{v}).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D.target.K ⟶
      ((RingedSpace.globalSectionsFunctor X'.toRingedSpace ⋙
        forget₂ _ AddCommGrpCat.{v}).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj E.target.K),
      (∀ (n : ℕ)
        (a : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D.left.K).sc n).moduleCatLeftHomologyData.K)
        (a' : ((((RingedSpace.globalSectionsFunctor X'.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj E.left.K).sc n).moduleCatLeftHomologyData.K),
        a'.val = l.f n a.val →
          E.left.class n a' =
            moduleCohomologyPullback f F n (D.left.class n a)) ∧
      (∀ (n : ℕ)
        (b : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D.right.K).sc n).moduleCatLeftHomologyData.K)
        (b' : ((((RingedSpace.globalSectionsFunctor X'.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj E.right.K).sc n).moduleCatLeftHomologyData.K),
        b'.val = r.f n b.val →
          E.right.class n b' =
            moduleCohomologyPullback f G n (D.right.class n b)) ∧
      (∀ (n : ℕ)
        (c : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D.target.K).sc n).moduleCatLeftHomologyData.K)
        (c' : ((((RingedSpace.globalSectionsFunctor X'.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj E.target.K).sc n).moduleCatLeftHomologyData.K),
        c'.val = t.f n c.val →
          E.target.class n c' =
            (RingedSpace.moduleCohomology X'.toRingedSpace n).map
              ((Classical.choose (module_pullback_tensor f)) F G).hom
              (moduleCohomologyPullback f (@id X.Modules (F ⊗ G)) n
                (D.target.class n c))) ∧
      (∀ (p q : ℕ) (a : Γ(D.left.K.X p, ⊤)) (b : Γ(D.right.K.X q, ⊤)),
        t.f (p + q) (D.pair p q ⊤ a b) =
          E.pair p q ⊤ (l.f p a) (r.f q b)) := by
  obtain ⟨D, E, l, r, t, hl, hr, ht, hpair⟩ :=
    moduleCup_pullback_augmented_pairings X X' f F G
  refine ⟨D, E, cupResolutionGlobalMap f l, cupResolutionGlobalMap f r,
    cupResolutionGlobalMap f t, ?_, ?_, ?_, hpair⟩
  · intro n a a' ha
    simpa only [moduleCohomologyPullback] using
      cupResolution_class_fmap f D.left E.left
        ((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app F) l hl n a a' ha
  · intro n b b' hb
    simpa only [moduleCohomologyPullback] using
      cupResolution_class_fmap f D.right E.right
        ((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app G) r hr n b b' hb
  · intro n c c' hc
    let η : F ⊗ G ⟶ (pushforward f).obj ((tensorPullback f).obj (F ⊗ G)) :=
      (Classical.choose (exists_tensorPullbackAdjunction f)).unit.app (F ⊗ G)
    let τ : (tensorPullback f).obj (F ⊗ G) ⟶
        (tensorPullback f).obj F ⊗ (tensorPullback f).obj G :=
      (Classical.choose (module_pullback_tensor f) F G).hom
    have hover : D.target.augmentation.f 0 ≫ t.f 0 =
        (η ≫ (pushforward f).map τ) ≫ (pushforward f).map (E.target.augmentation.f 0) :=
      ht.trans (Category.assoc _ _ _).symm
    have hclass := cupResolution_class_fmap f D.target E.target
      (η ≫ (pushforward f).map τ) t hover n c c' hc
    have hnat := moduleCohomologyFMap_target_naturality f τ η n
    exact hclass.trans (ConcreteCategory.congr_hom hnat (D.target.class n c)).symm

end
end AlgebraicGeometry.Scheme.Modules
