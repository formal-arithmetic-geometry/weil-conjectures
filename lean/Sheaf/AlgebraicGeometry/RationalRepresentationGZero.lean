/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q60
-/
module

public import Sheaf.AlgebraicGeometry.EquivariantCoherentGZero
public import Sheaf.AlgebraicGeometry.HopfCoactionLinearization
public import WeilConjectures.AlgebraicGeometry.ScalarGlobalSectionsComparison

/-! # Integral Grothendieck group of rational representations

Source: Stacks 03LF (affine linearization), 022S (group inverse), and
Milne, Algebraic Groups, Section 4 (representations via coordinate coactions).
(blueprint: def-sfb-rational-representation-gzero)

The group is a quotient on actual finite-dimensional counital coassociative
comodules. Associated bundles are pinned on constant generators using the inverse
of the linearization, hence give the geometric action from y to gy.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped TensorProduct

namespace AlgebraicGeometry.EquivariantCoherent

/-- Finite-dimensional rational modules as actual coordinate comodules.
Source: Milne, Algebraic Groups, Section 4
(blueprint: def-sfb-rational-representation-gzero). -/
structure RationalModule (F C : Type u) [Field F] [CommRing C] [HopfAlgebra F C] where
  space : ModuleCat.{u} F
  finite : Module.Finite F space
  coaction : space →ₗ[F] space ⊗[F] C
  counit : HopfAction.Counital F C space coaction
  coassoc : HopfAction.Coassociative F C space coaction

/-- The canonical coordinate Hopf structure, retaining the given scheme group law.
Source: Mathlib Group/Affine and Milne Section 4
(blueprint: def-sfb-rational-representation-gzero). -/
instance coordinateHopf (F : Type u) [Field F] (G : Over (Spec (.of F)))
    [GrpObj G] [IsAffine G.left] : HopfAlgebra F Γ(G.left, ⊤) :=
  @HopfAction.affineCoordinateHopfAlgebra (.of F) G.left ⟨G.hom⟩
    (inferInstanceAs (GrpObj G)) inferInstance

/-- Rational representations of the given affine group scheme.
Source: Milne Section 4 (blueprint: def-sfb-rational-representation-gzero). -/
abbrev Representation (F : Type u) [Field F] (G : Over (Spec (.of F)))
    [GrpObj G] [IsAffine G.left] :=
  letI := coordinateHopf F G
  RationalModule F Γ(G.left, ⊤)

variable {F C : Type u} [Field F] [CommRing C] [HopfAlgebra F C]

/-- A map of rational modules is a linear map commuting with coactions.
Source: Milne Section 4 (blueprint: def-sfb-rational-representation-gzero). -/
def IsRepresentationMap (V W : RationalModule F C) (f : V.space →ₗ[F] W.space) : Prop :=
  f.rTensor C ∘ₗ V.coaction = W.coaction ∘ₗ f

/-- The actual isomorphism and exact-sequence relations of rational representations.
Source: Milne Section 4 and the item's integral representation-ring convention
(blueprint: def-sfb-rational-representation-gzero). -/
def IsRepresentationRelation (z : FreeAbelianGroup (RationalModule F C)) : Prop :=
  (∃ (V W : RationalModule F C) (e : V.space ≃ₗ[F] W.space),
    IsRepresentationMap V W e.toLinearMap ∧
      z = FreeAbelianGroup.of V - FreeAbelianGroup.of W) ∨
  (∃ (A B D : RationalModule F C) (f : A.space →ₗ[F] B.space)
    (g : B.space →ₗ[F] D.space),
    IsRepresentationMap A B f ∧ IsRepresentationMap B D g ∧
      Function.Injective f ∧ Function.Surjective g ∧ LinearMap.range f = LinearMap.ker g ∧
      z = FreeAbelianGroup.of B - FreeAbelianGroup.of A - FreeAbelianGroup.of D)

/-- The integral representation Grothendieck group, before specifying tensor multiplication.
Source: the item's integral representation-ring convention
(blueprint: def-sfb-rational-representation-gzero). -/
abbrev RepresentationGZero (F C : Type u) [Field F] [CommRing C] [HopfAlgebra F C] :=
  FreeAbelianGroup (RationalModule F C) ⧸
    AddSubgroup.closure {z | IsRepresentationRelation z}

/-- The class of a rational module.
Source: the item's integral representation-ring convention
(blueprint: def-sfb-rational-representation-gzero). -/
def representationClass (V : RationalModule F C) : RepresentationGZero F C :=
  QuotientAddGroup.mk (FreeAbelianGroup.of V)

/-- The rational tensor product, pinned by multiplication of its Hopf coefficients.
Source: Stacks 03LF and Milne Section 4
(blueprint: def-sfb-rational-representation-gzero). -/
def IsRepresentationTensor (V W T : RationalModule F C) : Prop :=
  ∃ e : T.space ≃ₗ[F] V.space ⊗[F] W.space,
    ∀ (v : V.space) (w : W.space),
      e.toLinearMap.rTensor C (T.coaction (e.symm (v ⊗ₜ[F] w))) =
        HopfAction.tensorCoefficients F C F V.space W.space
          (V.coaction v ⊗ₜ[F] W.coaction w)

/-- The tensor unit is the trivial one-dimensional rational representation.
Source: Stacks 03LF and Milne Section 4
(blueprint: def-sfb-rational-representation-gzero). -/
def IsRepresentationUnit (V : RationalModule F C) : Prop :=
  ∃ e : V.space ≃ₗ[F] F,
    ∀ v : V.space, e.toLinearMap.rTensor C (V.coaction v) = e v ⊗ₜ[F] (1 : C)

/-- Tensor multiplication and unit on the already constructed additive quotient.
Source: the item's integral representation-ring convention
(blueprint: def-sfb-rational-representation-gzero). -/
def IsRepresentationRing (r : CommRing (RepresentationGZero F C)) : Prop :=
  r.toAddCommGroup = (inferInstance : AddCommGroup (RepresentationGZero F C)) ∧
    (∀ V W : RationalModule F C, ∃ T, IsRepresentationTensor V W T) ∧
    (∃ U : RationalModule F C, IsRepresentationUnit U) ∧
    (∀ V W T : RationalModule F C, IsRepresentationTensor V W T →
      r.mul (representationClass V) (representationClass W) = representationClass T) ∧
    ∀ U : RationalModule F C, IsRepresentationUnit U → r.one = representationClass U

/-- The constant section of the ordinary trivial vector bundle associated to V.
Source: Stacks 01I6 and 0096
(blueprint: def-sfb-rational-representation-gzero). -/
def constantSection (F : Type u) [Field F] {G Y : Over (Spec (.of F))}
    [GrpObj G] [ModObj G Y] [IsAffine G.left]
    {D : ActionGroupoidModel G Y} (V : Representation F G) (E : Coherent D)
    (e : underlying E ≅ (Scheme.Modules.tensorPullback Y.hom).obj
      (tilde (R := .of F) (ModuleCat.of F V.space)))
    (v : V.space) : Γ(underlying E, ⊤) :=
  e.inv.app ⊤ (Scheme.Modules.tensorPullbackTopSection Y.hom
    (tilde (R := .of F) (ModuleCat.of F V.space))
    ((tilde.toOpen (R := .of F) (ModuleCat.of F V.space) ⊤).hom v))

/-- The associated trivial bundle with exactly the given rational action. The
formula is required for every finite tensor presentation of each coaction value.
Source: Stacks 03LF, affine coaction translation, and Milne Section 4
(blueprint: def-sfb-rational-representation-gzero). -/
def IsAssociated (F : Type u) [Field F] {G Y : Over (Spec (.of F))}
    [GrpObj G] [ModObj G Y] [IsAffine G.left]
    {D : ActionGroupoidModel G Y} (V : Representation F G) (E : Coherent D) : Prop :=
  ∃ e : underlying E ≅ (Scheme.Modules.tensorPullback Y.hom).obj
      (tilde (R := .of F) (ModuleCat.of F V.space)),
    ∀ (v : V.space) (n : ℕ) (vi : Fin n → V.space) (ci : Fin n → Γ(G.left, ⊤)),
      V.coaction v = ∑ k, vi k ⊗ₜ[F] ci k →
      (linearization E).inv.app ⊤
          (Scheme.Modules.tensorPullbackTopSection (source G Y) (underlying E)
            (constantSection F V E e v)) =
        ∑ k, ((fst G Y).left.appTop.hom (ci k)) •
          Scheme.Modules.tensorPullbackTopSection (target G Y) (underlying E)
            (constantSection F V E e (vi k))

/-- Scalar multiplication normalized by tensoring with the associated trivial bundle.
Source: the item's representation-ring action
(blueprint: def-sfb-rational-representation-gzero). -/
def IsRepresentationAction (F : Type u) [Field F] {G Y : Over (Spec (.of F))}
    [GrpObj G] [ModObj G Y] [IsAffine G.left]
    (D : ActionGroupoidModel G Y)
    (r : CommRing (@RepresentationGZero F Γ(G.left, ⊤) _ _ (coordinateHopf F G)))
    (m : @Module (@RepresentationGZero F Γ(G.left, ⊤) _ _ (coordinateHopf F G))
      (GZero D) r.toSemiring inferInstance) : Prop :=
  (∀ V : Representation F G, ∃ E : Coherent D, IsAssociated F V E) ∧
    (∀ M N : Coherent D, ∃ P : Coherent D, IsTensor M N P) ∧
    ∀ (V : Representation F G) (E M P : Coherent D),
      IsAssociated F V E → IsTensor E M P →
        m.smul (representationClass V) (classOf M) = classOf P

end AlgebraicGeometry.EquivariantCoherent
