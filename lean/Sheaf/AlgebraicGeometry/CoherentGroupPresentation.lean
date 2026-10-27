/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q35
-/
module

public import Sheaf.AlgebraicGeometry.TrivialTorusCoherentData
public import Mathlib.LinearAlgebra.Finsupp.Defs
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Presentations of ordinary and equivariant coherent groups

Source: the presentations in lem-sfb-trivial-torus-coherent-weight-decomposition;
Stacks Project, Groupoids, Tags 03LF and 0EKL
(blueprint: def-sfb-coherent-group-presentation).

The equivariant presentation is an R-module presentation: in addition to the
isomorphism and short exact sequence relations, twisting by χ is identified with
multiplication by e^χ. Thus its R-action is the specified character-twist action.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

namespace AlgebraicGeometry.TrivialTorusCoherent

variable {F : Type u} [Field F]

/-- Coherent sheaves on the actual scheme.
Source: Stacks, Tag 01BV (blueprint: def-sfb-coherent-group-presentation). -/
abbrev Coherent (Z : Over (Spec (.of F))) :=
  {M : Z.left.Modules // RingedSpace.IsCoherent Z.left.toRingedSpace M}

/-- Short exactness is short exactness in the ambient abelian category of sheaves.
Source: Stacks, Tag 01BV (blueprint: def-sfb-coherent-group-presentation). -/
def ExactTriple {Z : Over (Spec (.of F))} (A B C : Z.left.Modules)
    (f : A ⟶ B) (g : B ⟶ C) : Prop :=
  ∃ h : f ≫ g = 0, (ShortComplex.mk f g h).ShortExact

/-- Ordinary relations, including isomorphisms and every short exact sequence.
Source: the node's G₀ presentation (blueprint: def-sfb-coherent-group-presentation). -/
def ordinaryRelations (Z : Over (Spec (.of F))) : Submodule ℤ (Coherent Z →₀ ℤ) :=
  Submodule.span ℤ {x |
    (∃ A B : Coherent Z, Nonempty (A.val ≅ B.val) ∧
      x = Finsupp.single B 1 - Finsupp.single A 1) ∨
    (∃ A B C : Coherent Z, ∃ (f : A.val ⟶ B.val) (g : B.val ⟶ C.val),
      ExactTriple A.val B.val C.val f g ∧
      x = Finsupp.single B 1 - Finsupp.single A 1 - Finsupp.single C 1)}

/-- The coherent group is the quotient by its stated relations.
Source: the node's G₀ presentation (blueprint: def-sfb-coherent-group-presentation). -/
abbrev OrdinaryGroup (Z : Over (Spec (.of F))) :=
  (Coherent Z →₀ ℤ) ⧸ ordinaryRelations Z

/-- The generator represented by a coherent sheaf.
Source: the node's G₀ presentation (blueprint: def-sfb-coherent-group-presentation). -/
def ordinaryClass {Z : Over (Spec (.of F))} (A : Coherent Z) : OrdinaryGroup Z :=
  (ordinaryRelations Z).mkQ (Finsupp.single A 1)

/-- An isomorphism intertwining the forward linearizations.
Source: Stacks, Tag 03LF (blueprint: def-sfb-coherent-group-presentation). -/
def IsEquivariantlyIsomorphic {T : Grp (Over (Spec (.of F)))}
    {Z : Over (Spec (.of F))} (M N : Linearized T Z) : Prop :=
  ∃ e : M.moduleObj ≅ N.moduleObj, Equivariant M N e.hom

/-- Twisting adds χ to the forward action, on every test scheme.
Source: Milne, Theorem 12.12 (blueprint: def-sfb-coherent-group-presentation). -/
def IsTwist {T : Grp (Over (Spec (.of F)))} {Z : Over (Spec (.of F))}
    (χ : Character T) (M N : Linearized T Z) : Prop :=
  ∃ e : M.moduleObj ≅ N.moduleObj,
    ∀ (W : Over (Spec (.of F))) (z : W ⟶ Z) (t : W ⟶ T.X),
      atMap e.hom z ≫ (N.linearization.action W z t).hom =
        (testModule M.moduleObj z).smulHom (characterValue T χ W t) ≫
          (M.linearization.action W z t).hom ≫ atMap e.hom z

/-- The equivariant relations; the last relation implements the character-ring action.
Source: the node's G₀ᵀ presentation (blueprint: def-sfb-coherent-group-presentation). -/
def equivariantRelations (T : Grp (Over (Spec (.of F))))
    (Z : Over (Spec (.of F))) :
    Submodule (CharacterRing T) (Linearized T Z →₀ CharacterRing T) :=
  Submodule.span (CharacterRing T) {x |
    (∃ M N : Linearized T Z, IsEquivariantlyIsomorphic M N ∧
      x = Finsupp.single N 1 - Finsupp.single M 1) ∨
    (∃ A B C : Linearized T Z,
      ∃ (f : A.moduleObj ⟶ B.moduleObj) (g : B.moduleObj ⟶ C.moduleObj),
      Equivariant A B f ∧ Equivariant B C g ∧
      ExactTriple A.moduleObj B.moduleObj C.moduleObj f g ∧
      x = Finsupp.single B 1 - Finsupp.single A 1 - Finsupp.single C 1) ∨
    (∃ (χ : Character T) (M N : Linearized T Z), IsTwist χ M N ∧
      x = Finsupp.single N 1 - Finsupp.single M (AddMonoidAlgebra.single χ 1))}

/-- The equivariant coherent group, with its prescribed R-module structure.
Source: the node's G₀ᵀ presentation (blueprint: def-sfb-coherent-group-presentation). -/
abbrev EquivariantGroup (T : Grp (Over (Spec (.of F)))) (Z : Over (Spec (.of F))) :=
  (Linearized T Z →₀ CharacterRing T) ⧸ equivariantRelations T Z

/-- The class of a coherent linearized module.
Source: the node's G₀ᵀ presentation (blueprint: def-sfb-coherent-group-presentation). -/
def equivariantClass {T : Grp (Over (Spec (.of F)))} {Z : Over (Spec (.of F))}
    (M : Linearized T Z) : EquivariantGroup T Z :=
  (equivariantRelations T Z).mkQ (Finsupp.single M 1)

/-- Tensoring by a finite locally free module, characterized on every generator.
Source: the node's tensor operators (blueprint: def-sfb-coherent-group-presentation). -/
def IsOrdinaryTensorOperator {Z : Over (Spec (.of F))} (E : Z.left.Modules)
    (op : OrdinaryGroup Z →+ OrdinaryGroup Z) : Prop :=
  ∀ A B : Coherent Z, Nonempty (B.val ≅ E ⊗ A.val) →
    op (ordinaryClass A) = ordinaryClass B

/-- An equivariant tensor product, characterized on pulled-back pure tensors.
The comparison is the canonical tensor comparison characterized on local sections.
Source: Stacks, Tag 03LF (blueprint: def-sfb-coherent-group-presentation). -/
def IsTensorWith {T : Grp (Over (Spec (.of F)))} {Z : Over (Spec (.of F))}
    (M N P : Linearized T Z) (e : P.moduleObj ≅ M.moduleObj ⊗ N.moduleObj) : Prop :=
  ∀ (W : Over (Spec (.of F))) (z : W ⟶ Z),
      ∃ c : testModule P.moduleObj z ≅
          testModule M.moduleObj z ⊗ testModule N.moduleObj z,
        (∀ (U : Z.left.Opens) (m : Γ(M.moduleObj, U)) (n : Γ(N.moduleObj, U)),
          c.hom.app (z.left ⁻¹ᵁ U)
            (Scheme.Modules.tensorPullbackSection z.left P.moduleObj U
              (e.inv.app U (Scheme.Modules.tmulSection m n))) =
          Scheme.Modules.tmulSection
            (Scheme.Modules.tensorPullbackSection z.left M.moduleObj U m)
            (Scheme.Modules.tensorPullbackSection z.left N.moduleObj U n)) ∧
        (∀ t : W ⟶ T.X,
          (P.linearization.action W z t).hom ≫ c.hom = c.hom ≫
            ((M.linearization.action W z t).hom ⊗ₘ (N.linearization.action W z t).hom))

/-- The actual tensor product linearization, up to equivariant isomorphism.
Source: Stacks, Tag 03LF (blueprint: def-sfb-coherent-group-presentation). -/
def IsTensor {T : Grp (Over (Spec (.of F)))} {Z : Over (Spec (.of F))}
    (M N P : Linearized T Z) : Prop :=
  ∃ e : P.moduleObj ≅ M.moduleObj ⊗ N.moduleObj, IsTensorWith M N P e

/-- An equivariant exterior power, normalized on pullbacks of wedge sections.
Source: Stacks, exterior algebra, Tag 00DM
(blueprint: def-sfb-coherent-group-presentation). -/
def IsExterior {T : Grp (Over (Spec (.of F)))} {Z : Over (Spec (.of F))}
    (M : Linearized T Z) (q : ℕ) (N : Linearized T Z) : Prop :=
  ∃ e : N.moduleObj ≅ Scheme.Modules.exteriorSheaf M.moduleObj q,
    ∀ (W : Over (Spec (.of F))) (z : W ⟶ Z),
      ∃ c : testModule N.moduleObj z ≅ Scheme.Modules.exteriorSheaf
          (testModule M.moduleObj z) q,
        (∀ (U : Z.left.Opens) (m : Fin q → Γ(M.moduleObj, U)),
          c.hom.app (z.left ⁻¹ᵁ U)
            (Scheme.Modules.tensorPullbackSection z.left N.moduleObj U
              (e.inv.app U (Scheme.Modules.exteriorSheafSection M.moduleObj q U m))) =
          Scheme.Modules.exteriorSheafSection (testModule M.moduleObj z) q (z.left ⁻¹ᵁ U)
            (fun i => Scheme.Modules.tensorPullbackSection z.left M.moduleObj U (m i))) ∧
        (∀ (t : W ⟶ T.X) (U : W.left.Opens)
          (m : Fin q → Γ(testModule M.moduleObj z, U)),
          c.hom.app U
            ((N.linearization.action W z t).hom.app U (c.inv.app U
              (Scheme.Modules.exteriorSheafSection (testModule M.moduleObj z) q U m))) =
            Scheme.Modules.exteriorSheafSection (testModule M.moduleObj z) q U
              (fun i => (M.linearization.action W z t).hom.app U (m i)))

/-- An exact equivariant tensor operator, characterized on all generators.
Source: the node's tensor action (blueprint: def-sfb-coherent-group-presentation). -/
def IsEquivariantTensorOperator {T : Grp (Over (Spec (.of F)))}
    {Z : Over (Spec (.of F))} (E : Linearized T Z)
    (op : Module.End (CharacterRing T) (EquivariantGroup T Z)) : Prop :=
  ∀ A B : Linearized T Z, IsTensor E A B → op (equivariantClass A) = equivariantClass B

/-- Pullback of a decomposition, expressed by its pulled-back inclusions. This
makes sense even when a field extension of a Noetherian scheme is not Noetherian.
Source: Stacks, Tag 0EKL (blueprint: def-sfb-coherent-group-presentation). -/
def IsPulledBackDecomposition {T : Grp (Over (Spec (.of F)))}
    {Z : Over (Spec (.of F))} (M : Linearized T Z)
    (P : Character T → Subobject M.moduleObj) {W : Over (Spec (.of F))}
    (f : W ⟶ Z) : Prop :=
  (∀ χ, Mono (atMap (P χ).arrow f)) ∧
    Nonempty (IsColimit (Cofan.mk (testModule M.moduleObj f)
      (fun χ => atMap (P χ).arrow f))) ∧
    (∀ (V : Over (Spec (.of F))) (z : V ⟶ W) (t : V ⟶ T.X) (χ : Character T),
      atMap (P χ).arrow (z ≫ f) ≫ (M.linearization.action V (z ≫ f) t).hom =
        (testModule (P χ : Z.left.Modules) (z ≫ f)).smulHom
          (characterValue T χ V t) ≫ atMap (P χ).arrow (z ≫ f))

/-- Restriction of a linearized coherent module along a base-scheme morphism,
using the canonical composition comparison, with no arbitrary transport.
Source: Stacks, Tag 03LF (blueprint: def-sfb-coherent-group-presentation). -/
def IsRestriction {T : Grp (Over (Spec (.of F)))}
    {Z W : Over (Spec (.of F))} (f : W ⟶ Z)
    (M : Linearized T Z) (N : Linearized T W) : Prop :=
  ∃ e : N.moduleObj ≅ testModule M.moduleObj f,
    ∀ (V : Over (Spec (.of F))) (z : V ⟶ W) (t : V ⟶ T.X),
      atMap e.hom z ≫ (atComp M.moduleObj z f).inv ≫
          (M.linearization.action V (z ≫ f) t).hom =
        (N.linearization.action V z t).hom ≫
          atMap e.hom z ≫ (atComp M.moduleObj z f).inv

/-- A clopen piece as a scheme over the same field.
Source: Stacks, Tags 01C6 and 01IA (blueprint: def-sfb-coherent-group-presentation). -/
abbrev openBase (Z : Over (Spec (.of F))) (U : Z.left.Opens) : Over (Spec (.of F)) :=
  Over.mk (U.ι ≫ Z.hom)

/-- The inclusion of a clopen piece over the base field.
Source: Stacks, Tags 01C6 and 01IA (blueprint: def-sfb-coherent-group-presentation). -/
def openInclusion (Z : Over (Spec (.of F))) (U : Z.left.Opens) : openBase Z U ⟶ Z :=
  Over.homMk U.ι

/-- The scheme obtained by extending the base field, kept as an F-scheme.
Source: Stacks, Tag 01IA (blueprint: def-sfb-coherent-group-presentation). -/
abbrev fieldBase (Z : Over (Spec (.of F))) (K : Type u) [Field K] [Algebra F K] :
    Over (Spec (.of F)) :=
  Over.mk (pullback.snd Z.hom (Spec.map (CommRingCat.ofHom (algebraMap F K))) ≫
    Spec.map (CommRingCat.ofHom (algebraMap F K)))

/-- The canonical projection from a field extension of the scheme.
Source: Stacks, Tag 01IA (blueprint: def-sfb-coherent-group-presentation). -/
def fieldProjection (Z : Over (Spec (.of F))) (K : Type u) [Field K] [Algebra F K] :
    fieldBase Z K ⟶ Z :=
  Over.homMk (pullback.fst Z.hom (Spec.map (CommRingCat.ofHom (algebraMap F K))))
    pullback.condition

/-- The canonical character comparison, specified on all pure-character generators.
The tensor symmetry rewrites its domain as the source G₀ ⊗ℤ R in the node.
Source: Stacks, Tag 0EKL (blueprint: def-sfb-coherent-group-presentation). -/
def IsCharacterComparison {T : Grp (Over (Spec (.of F)))}
    {Z : Over (Spec (.of F))}
    (φ : CharacterRing T ⊗[ℤ] OrdinaryGroup Z ≃ₗ[CharacterRing T] EquivariantGroup T Z) :
    Prop :=
  ∀ (A : Coherent Z) (χ : Character T) (M : Linearized T Z),
    Nonempty (M.moduleObj ≅ A.val) → IsPure M χ →
      φ (AddMonoidAlgebra.single χ 1 ⊗ₜ[ℤ] ordinaryClass A) = equivariantClass M

end AlgebraicGeometry.TrivialTorusCoherent
