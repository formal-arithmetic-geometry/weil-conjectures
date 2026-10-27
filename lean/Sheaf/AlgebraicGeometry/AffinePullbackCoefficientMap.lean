/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.CoherentHigherImageClasses
public import Sheaf.AlgebraicGeometry.TensorCompositeCohomologyRestriction
public import WeilConjectures.AlgebraicGeometry.EtaleTensorSections

/-! # The canonical coefficient morphism on affine-chart pullbacks -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option autoImplicit false
attribute [local instance] Etale.RawRestrictedComparison.etaleComposition
  Etale.RawRestrictedComparison.etaleIdentities Etale.RawRestrictedComparison.etalePullbacks
  Etale.RawRestrictedComparison.etaleBaseChange
attribute [local irreducible] tensorPullback tensorPullbackObj tensorSectionsComp
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

/-- The canonical tensor-composition map, with a named coefficient-object transport.
Source: Stacks Project, Tags 03DR and 01FD.
(blueprint: def-weil-pbc-affine-pullback-coefficient-map). -/
@[irreducible] def tensorCompositeCoefficientMap {A B C : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ C) (c : A ⟶ C) (w : a ≫ b = c) (G : C.Modules) :
    (tensorPullback a).obj ((tensorPullback b).obj G) ⟶ (tensorPullback c).obj G :=
  (tensorSectionsComp a b).hom.app G ≫
    eqToHom (tensorCompositeCoefficient_eq a b c w G)

private theorem tensorCompositeCoefficientMap_eq_named {A B C : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ C) (c : A ⟶ C) (w : a ≫ b = c) (G : C.Modules) :
    tensorCompositeCoefficientMap a b c w G =
      (tensorSectionsComp a b).hom.app G ≫
        eqToHom (tensorCompositeCoefficient_eq a b c w G) := by
  unfold tensorCompositeCoefficientMap
  rfl

/-- The generic coefficient map uses the prescribed tensor composite.
Source: Stacks Project, Tag 03DR.
(blueprint: def-weil-pbc-affine-pullback-coefficient-map).
Proof: use the defining equation, then apply congruence to proof irrelevance for
its coefficient-object equality. This avoids unfolding the tensor construction. -/
theorem tensorCompositeCoefficientMap_eq {A B C : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ C) (c : A ⟶ C) (w : a ≫ b = c) (G : C.Modules) :
    tensorCompositeCoefficientMap a b c w G =
      (tensorSectionsComp a b).hom.app G ≫
        eqToHom (congrArg (fun j ↦ (tensorPullback j).obj G) w) := by
  exact (tensorCompositeCoefficientMap_eq_named a b c w G).trans
    (congrArg (fun p : (tensorPullback (a ≫ b)).obj G = (tensorPullback c).obj G ↦
      (tensorSectionsComp a b).hom.app G ≫ eqToHom p) (Subsingleton.elim _ _))

/-- The generic cohomology restriction is the adjunct of the named coefficient map.
Source: Stacks Project, Tags 01F8 and 01FB.
(blueprint: def-weil-pbc-affine-pullback-coefficient-map).
Proof: compose the existing cohomology restriction formula with the coefficient equation. -/
theorem tensorCompositeCohomologyRestriction_eq_coefficient {A B C : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ C) (c : A ⟶ C) (w : a ≫ b = c)
    (G : C.Modules) (q : ℕ) :
    tensorCompositeCohomologyRestriction a b c w G q =
      moduleCohomologyFMap a
        ((Classical.choose (exists_tensorPullbackAdjunction a)).homEquiv _ _
          (tensorCompositeCoefficientMap a b c w G)) q := by
  exact (tensorCompositeCohomologyRestriction_eq a b c w G q).trans
    (congrArg (fun ψ ↦ moduleCohomologyFMap a
      ((Classical.choose (exists_tensorPullbackAdjunction a)).homEquiv _ _ ψ) q)
      (tensorCompositeCoefficientMap_eq a b c w G).symm)

/-- The map of the actual fibre products induced by a map of etale charts.
Source: Stacks Project, Tag 03Q8.
(blueprint: def-weil-pbc-affine-pullback-coefficient-map). -/
@[irreducible] def affineRealizationChartMap {X S : Scheme.{u}} (f : X ⟶ S)
    {V V' : S.Etale} (h : V' ⟶ V) :
    Limits.pullback V'.hom f ⟶ Limits.pullback V.hom f :=
  ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f).map h).left

/-- The typed chart map commutes with the projections to X.
Source: Stacks Project, Tag 03Q8.
(blueprint: def-weil-pbc-affine-pullback-coefficient-map).
Proof: this is the commutative-square property of the base-change morphism. -/
theorem affineRealizationChartMap_w {X S : Scheme.{u}} (f : X ⟶ S)
    {V V' : S.Etale} (h : V' ⟶ V) :
    affineRealizationChartMap f h ≫ Limits.pullback.snd V.hom f =
      Limits.pullback.snd V'.hom f := by
  unfold affineRealizationChartMap
  exact ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f).map h).w

/-- The tensor-composition coefficient morphism, followed by base-change transport.
Source: Stacks Project, Tags 03Q8 and 01FD.
(blueprint: def-weil-pbc-affine-pullback-coefficient-map). -/
@[irreducible] def affineRealizationCoefficientMap {X S : Scheme.{u}} (f : X ⟶ S)
    (G : X.Modules) {V V' : S.Etale} (h : V' ⟶ V) :
    (tensorPullback (affineRealizationChartMap f h)).obj
      (affineRealizationCoefficient f G V) ⟶ affineRealizationCoefficient f G V' :=
  tensorCompositeCoefficientMap (affineRealizationChartMap f h)
    (pullback.snd V.hom f) (pullback.snd V'.hom f) (affineRealizationChartMap_w f h) G

/-- The named coefficient morphism is the prescribed tensor composite.
Source: Stacks Project, Tags 03Q8 and 01FD.
(blueprint: def-weil-pbc-affine-pullback-coefficient-map).
Proof: this is the defining equation of the constructed coefficient morphism. -/
theorem affineRealizationCoefficientMap_eq {X S : Scheme.{u}} (f : X ⟶ S)
    (G : X.Modules) {V V' : S.Etale} (h : V' ⟶ V) :
    affineRealizationCoefficientMap f G h =
      tensorCompositeCoefficientMap (affineRealizationChartMap f h)
        (pullback.snd V.hom f) (pullback.snd V'.hom f) (affineRealizationChartMap_w f h) G := by
  unfold affineRealizationCoefficientMap
  rfl

end
end AlgebraicGeometry.Scheme.Modules
