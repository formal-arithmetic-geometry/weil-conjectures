/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F4
-/
module

public import Sheaf.AlgebraicGeometry.QcqsQuasicoherentAcyclicEmbedding
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel
import WeilConjectures.AlgebraicGeometry.Cohomology.QuasicoherentExtension

/-! # Effacing a coefficient morphism across arbitrary scheme pullback

Source: Stacks Project, Tags 0BDY, 01E7 and 010T.
-/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
attribute [local irreducible] tensorPullback tensorPullbackObj
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A morphism of short exact sequences with acyclic source middle term. -/
structure PullbackEffacingSquare {X Y : Scheme.{u}} (g : Y ⟶ X)
    (F : X.Modules) (G : Y.Modules) (ψ : (tensorPullback g).obj F ⟶ G) where
  E : X.Modules
  Q : X.Modules
  qcE : E.IsQuasicoherent
  qcQ : Q.IsQuasicoherent
  i : F ⟶ E
  p : E ⟶ Q
  zero : i ≫ p = 0
  exact : (ShortComplex.mk i p zero).ShortExact
  E' : Y.Modules
  Q' : Y.Modules
  qcE' : E'.IsQuasicoherent
  qcQ' : Q'.IsQuasicoherent
  i' : G ⟶ E'
  p' : E' ⟶ Q'
  zero' : i' ≫ p' = 0
  exact' : (ShortComplex.mk i' p' zero').ShortExact
  middle : (tensorPullback g).obj E ⟶ E'
  last : (tensorPullback g).obj Q ⟶ Q'
  first_comm : (tensorPullback g).map i ≫ middle = ψ ≫ i'
  second_comm : (tensorPullback g).map p ≫ last = middle ≫ p'
  acyclic : ∀ n : ℕ, 1 ≤ n →
    IsZero ((RingedSpace.moduleCohomology X.toRingedSpace n).obj E)

private theorem tensorPullback_qcoh {X Y : Scheme.{u}} (g : Y ⟶ X)
    (F : X.Modules) [F.IsQuasicoherent] : ((tensorPullback g).obj F).IsQuasicoherent := by
  let e := (Classical.choose (exists_tensorPullbackAdjunction g)).leftAdjointUniq
    (pullbackPushforwardAdjunction g)
  exact (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso
    (e.app F).symm (isQuasicoherent_pullback g F)

private theorem tensorPullback_mono {X Y : Scheme.{u}} (g : Y ⟶ X)
    {F E : X.Modules} (i : F ⟶ E) (h : Mono ((pullback g).map i)) :
    Mono ((tensorPullback g).map i) := by
  let e := (Classical.choose (exists_tensorPullbackAdjunction g)).leftAdjointUniq
    (pullbackPushforwardAdjunction g)
  have : Mono ((pullback g).map i) := h
  have : Mono ((tensorPullback g).map i ≫ e.hom.app E) := by
    rw [e.hom.naturality i]
    infer_instance
  exact mono_of_mono _ (e.hom.app E)

private theorem pushout_qcoh {X : Scheme.{u}} {A B C : X.Modules}
    [A.IsQuasicoherent] [B.IsQuasicoherent] [C.IsQuasicoherent]
    (f : A ⟶ B) (g : A ⟶ C) : (pushout f g).IsQuasicoherent := by
  have : (B ⊞ C).IsQuasicoherent := isQuasicoherent_biprod B C
  have h := isQuasicoherent_cokernel (biprod.lift f (-g))
  let e : cokernel (biprod.lift f (-g)) ≅ pushout f g :=
    (cokernelIsCokernel _).coconePointUniqueUpToIso
      (Abelian.BiproductToPushoutIsCokernel.isColimitBiproductToPushout f g)
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso e h

/-- Any structural coefficient map extends to an acyclic effacing square.
Source: Stacks Project, Tags 0BDY, 01E7 and 010T.
(blueprint: lem-weil-pbc-qcoherent-pullback-effacing-square)

Proof: Choose the universally monic affine-cover acyclic embedding i:F into E.
Set Q=coker(i). Tensor pullback is a left adjoint and preserves cokernels,
and its image of i is monic by the embedding's universal property. Push this
image out along psi, obtaining G into E'. Pushouts of monomorphisms are monic
in an abelian category. Set Q'=coker(G into E'). The pushout is quasi-coherent:
it is the cokernel of the map from g*F to g*E direct sum G. Its cokernel Q'
is quasi-coherent too. The cokernel comparison for tensor pullback and the
universal property of cokernels provide g*Q into Q'. These choices give both
commuting squares and the two short exact sequences. Acyclicity of E is the
one supplied by the finite affine cover, including an empty cover. -/
theorem exists_pullbackEffacingSquare (X Y : Scheme.{u})
    [CompactSpace X] [X.IsSeparated] (g : Y ⟶ X)
    (F : X.Modules) (G : Y.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    (ψ : (tensorPullback g).obj F ⟶ G) : Nonempty (PullbackEffacingSquare g F G ψ) := by
  classical
  obtain ⟨E, hE, i, hi, hpure, hacyclic⟩ :=
    exists_qcqs_quasicoherent_pure_acyclic_embedding X F
  let : E.IsQuasicoherent := hE
  let : Mono i := hi
  let Q := cokernel i
  have hQ : Q.IsQuasicoherent := isQuasicoherent_cokernel i
  let : Q.IsQuasicoherent := hQ
  let T := tensorPullback g
  let : T.IsLeftAdjoint := ⟨_, ⟨Classical.choose (exists_tensorPullbackAdjunction g)⟩⟩
  let : PreservesColimits T := inferInstance
  let : Mono (T.map i) := tensorPullback_mono g i (hpure Y g)
  let : (T.obj F).IsQuasicoherent := tensorPullback_qcoh g F
  let : (T.obj E).IsQuasicoherent := tensorPullback_qcoh g E
  let P := pushout (T.map i) ψ
  have hP : P.IsQuasicoherent := pushout_qcoh (T.map i) ψ
  let : P.IsQuasicoherent := hP
  let j : G ⟶ P := pushout.inr (T.map i) ψ
  let b : T.obj E ⟶ P := pushout.inl (T.map i) ψ
  have hj : Mono j := inferInstance
  let R := cokernel j
  have hR : R.IsQuasicoherent := isQuasicoherent_cokernel j
  let c : T.obj Q ⟶ R := inv (cokernelComparison i T) ≫
    cokernel.map (T.map i) j ψ b ((pushout.condition (f := T.map i) (g := ψ)))
  have hc : T.map (cokernel.π i) ≫ c = b ≫ cokernel.π j := by
    dsimp only [c]
    rw [← π_comp_cokernelComparison, Category.assoc,
      IsIso.hom_inv_id_assoc, cokernel.π_desc]
  exact ⟨{
    E := E, Q := Q, qcE := hE, qcQ := hQ, i := i, p := cokernel.π i
    zero := cokernel.condition i
    exact := ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact i)
      hi inferInstance
    E' := P, Q' := R, qcE' := hP, qcQ' := hR, i' := j, p' := cokernel.π j
    zero' := cokernel.condition j
    exact' := ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact j)
      hj inferInstance
    middle := b, last := c, first_comm := (pushout.condition (f := T.map i) (g := ψ))
    second_comm := hc, acyclic := hacyclic }⟩

end
end AlgebraicGeometry.Scheme.Modules
