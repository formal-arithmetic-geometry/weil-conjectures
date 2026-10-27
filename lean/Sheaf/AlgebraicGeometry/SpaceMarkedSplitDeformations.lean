module

public import Sheaf.AlgebraicGeometry.SpaceSplitCoefficient
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties

/-! # Marked flat algebraic-space deformations over split square-zero bases

Source: Stacks Project, defos.tex, Tag 0D17; quot.tex, Tag 0D1K;
artin.tex, sections tangent-spaces and inf
(blueprint: def-sfb-space-marked-split-deformations).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace.SplitSpace

variable {K : Type u} [Field K]

/-- The right action is the given left action, using commutativity of K.
Source: Stacks, artin.tex, section-inf
(blueprint: def-sfb-space-marked-split-deformations). -/
instance directionOpposite (M : ModuleCat.{u} K) : Module Kᵐᵒᵖ M :=
  Module.compHom M ((RingHom.id K).fromOpposite (fun a b ↦ mul_comm a b))

/-- These two actions agree, so this adds no bimodule hypothesis.
Source: Stacks, artin.tex, section-inf
(blueprint: def-sfb-space-marked-split-deformations). -/
instance directionCentral (M : ModuleCat.{u} K) : IsCentralScalar K M where
  op_smul_eq_smul := fun _ _ ↦ rfl

variable (X : AlgebraicSpace (Spec (.of K))) (M : ModuleCat.{u} K)

/-- A flat family with a cartesian special-fibre marking by X.
Source: Stacks 0D17 (blueprint: def-sfb-space-marked-split-deformations). -/
structure Marked where
  space : AlgebraicSpace (Spec (.of K))
  projection : space ⟶ SplitModule.base (k := K) (M : Type u)
  flat : MapIsFlat projection
  marking : X ⟶ space
  cartesian : IsPullback marking (structureMap X) projection
    (ObjectProperty.homMk (SplitModule.baseZero (k := K) (M : Type u)))

variable {M}

/-- Isomorphisms fix the base and the specified marking.
Source: Stacks 0D17 (blueprint: def-sfb-space-marked-split-deformations). -/
def Related (D E : Marked X M) : Prop :=
  ∃ e : D.space ≅ E.space,
    e.hom ≫ E.projection = D.projection ∧ D.marking ≫ e.hom = E.marking

/-- Isomorphism classes; marked isomorphism is already an equivalence relation.
Source: Stacks 0D17 (blueprint: def-sfb-space-marked-split-deformations). -/
def Classes (M : ModuleCat.{u} K) := Quot (Related X (M := M))

/-- The class of the actual marked geometric family.
Source: Stacks 0D17 (blueprint: def-sfb-space-marked-split-deformations). -/
def classOf (D : Marked X M) : Classes X M := Quot.mk _ D

/-- Triviality is a marked isomorphism to the actual product with Y_M.
Source: Stacks 0D17 (blueprint: def-sfb-space-marked-split-deformations). -/
def IsTrivial (D : Marked X M) : Prop :=
  ∃ e : D.space ≅ SplitModule.space X (M : Type u),
    e.hom ≫ SplitModule.toBase X (M : Type u) = D.projection ∧
      D.marking ≫ e.hom = SplitModule.fibre X (M : Type u)

/-- A specified linear map induces the actual contravariant affine base map.
Source: Stacks, artin.tex, section-inf
(blueprint: def-sfb-space-marked-split-deformations). -/
def baseChangeMap {M N : ModuleCat.{u} K} (h : M ⟶ N) :
    SplitModule.base (k := K) (N : Type u) ⟶ SplitModule.base (k := K) (M : Type u) :=
  ObjectProperty.homMk ((Scheme.fppfTopology.over (Spec (.of K))).yoneda.map
    (ProperCurveFamily.directionMap K (𝟙 (Spec (.of K))) h.hom))

/-- Base change is a cartesian square compatible with the marked special fibre.
Source: Stacks 0D17, 0GQ8 (blueprint: def-sfb-space-marked-split-deformations). -/
def PullsBack {M N : ModuleCat.{u} K} (h : M ⟶ N)
    (D : Marked X M) (E : Marked X N) : Prop :=
  ∃ q : E.space ⟶ D.space,
    IsPullback q E.projection D.projection (baseChangeMap h) ∧ E.marking ≫ q = D.marking

/-- Gluing is a geometric pushout along X, with the two standard base projections.
Source: Stacks 0D17; artin.tex, section-inf
(blueprint: def-sfb-space-marked-split-deformations). -/
def IsGluing (D E : Marked X M) (G : Marked X (ModuleCat.of K (M × M))) : Prop :=
  ∃ (i : D.space ⟶ G.space) (j : E.space ⟶ G.space),
    IsPushout D.marking E.marking i j ∧
      i ≫ G.projection = D.projection ≫
        baseChangeMap (ModuleCat.ofHom (LinearMap.fst K M M)) ∧
      j ≫ G.projection = E.projection ≫
        baseChangeMap (ModuleCat.ofHom (LinearMap.snd K M M)) ∧
      D.marking ≫ i = G.marking

/-- Automorphisms of the actual trivial family, over Y_M and fixing X.
Source: Stacks 0D17, 08UG (blueprint: def-sfb-space-marked-split-deformations). -/
def AutZero (M : ModuleCat.{u} K) :=
  {g : Aut (SplitModule.space X (M : Type u)) //
    g.hom ≫ SplitModule.toBase X (M : Type u) = SplitModule.toBase X (M : Type u) ∧
      SplitModule.fibre X (M : Type u) ≫ g.hom = SplitModule.fibre X (M : Type u)}

/-- Pullback of automorphisms: the canonical product map intertwines them.
Source: Stacks 0D17, 0GQ8 (blueprint: def-sfb-space-marked-split-deformations). -/
def AutPullsBack {M N : ModuleCat.{u} K} (h : M ⟶ N)
    (g : AutZero X M) (t : AutZero X N) : Prop :=
  t.val.hom ≫ SplitModule.change X h.hom = SplitModule.change X h.hom ≫ g.val.hom

end AlgebraicGeometry.AlgebraicSpace.SplitSpace
