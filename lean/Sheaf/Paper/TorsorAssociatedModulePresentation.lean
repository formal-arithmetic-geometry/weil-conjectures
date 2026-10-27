/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q145
-/
module

public import Sheaf.Paper.CompletedFrameGenericComparison
public import Sheaf.Paper.GenericLisseScalarComparison

/-! # Associated-module presentations of continuous right torsors

Source: Bhatt--Scholze, Lemma 7.4.7, pp. 70--71, and Stacks Tags 04TR and 04TQ.
(blueprint: def-sfb-torsor-associated-module-presentation).

The frames are actual slice module isomorphisms. Their columns specify restriction,
the associated-module relation, uniqueness, and normalization by the chosen fibre point.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.TorsorAssociatedModule
open CompletedFrameGeneric

variable {X : Scheme.{u}} {A : Type u} [NormedField A]
  {H : TorsorCoefficientGroup.{u}} {n : ℕ}

set_option genSizeOfSpec false in
set_option genInjectivity false in
/-- Frames indexed by all local torsor sections, satisfying e_(ph) = e_p r(h).
Coefficient matrices are fixed by the canonical continuous-ring comparison.
Source: Bhatt--Scholze, Lemma 7.4.7; Stacks Tag 04TR.
(blueprint: def-sfb-torsor-associated-module-presentation). -/
structure Presentation (r : H.carrier →ₜ* Matrix.GeneralLinearGroup (Fin n) A)
    (P : ContinuousRightTorsor X H) (L : NormContinuousLisse A X) where
  frame (U : X.ProEt) : P.sheaf.obj.obj (op U) → Frame X A L.obj n U
  natural : ∀ (U V : X.ProEt) (f : V ⟶ U) (s : P.sheaf.obj.obj (op U))
      (i : Fin n) (W : Over V),
    column X A (frame V (P.sheaf.obj.map f.op s)) i W =
      column X A (frame U s) i ((Over.map f).obj W)
  balanced : ∀ (U : X.ProEt) (s : P.sheaf.obj.obj (op U)) (h : C(U.left, H.carrier))
      (V : Over U) (c : Matrix (Fin n) (Fin n) ((ring X A).obj.obj (op V.left))),
    (∀ (i j : Fin n) (z : V.left.left),
      ((ContinuousRingUniverse.comparison X A).hom.app (op V.left) (c i j)).down z =
        (r (h (V.hom.left.base z)) : Matrix (Fin n) (Fin n) A) i j) →
    ∀ j : Fin n,
      column X A (frame U (P.act (op U) s h)) j V =
        ∑ i : Fin n, scale X A L.obj V.left (c i j) (column X A (frame U s) i V)

/-- An isomorphism respecting the associated-module charts on every slice.
Source: Stacks Tag 04TQ; Bhatt--Scholze, Lemma 7.4.7.
(blueprint: def-sfb-torsor-associated-module-presentation). -/
def Respects {r : H.carrier →ₜ* Matrix.GeneralLinearGroup (Fin n) A}
    {P : ContinuousRightTorsor X H} {L M : NormContinuousLisse A X}
    (a : Presentation r P L) (b : Presentation r P M) (e : L.obj ≅ M.obj) : Prop :=
  ∀ (U : X.ProEt) (s : P.sheaf.obj.obj (op U)) (i : Fin n) (V : Over U),
    e.hom.hom.hom.app (op V.left) (column X A (a.frame U s) i V) =
      column X A (b.frame U s) i V

/-- The generic columns are those of a chart whose geometric specialization is p.
HEq compares two definitionally identical presentations of the actual section group;
it introduces no transport choice or additional field identification.
Source: Bhatt--Scholze, Lemmas 7.4.7 and 7.4.10.
(blueprint: def-sfb-torsor-associated-module-presentation). -/
def IsPointedBasis [IsIntegral X]
    (ks : Type u) [Field ks] [Algebra X.functionField ks]
    [IsSepClosure X.functionField ks]
    (K : Type u) [Field K] (i : ks →+* K) (x : Spec (.of K) ⟶ X)
    {r : H.carrier →ₜ* Matrix.GeneralLinearGroup (Fin n) A}
    {P : ContinuousRightTorsor X H} {L : NormContinuousLisse A X}
    (a : Presentation r P L) (p : P.fibre x)
    (b : Fin n → NormalGenericLisse.geometricSections X A ks L) : Prop :=
  ∃ (U : X.ProEt) (s : P.sheaf.obj.obj (op U)) (t : Spec (.of ks) ⟶ U.left)
    (ht : t ≫ U.hom = Spec.map (CommRingCat.ofHom (algebraMap X.functionField ks)) ≫
      NormalGenericLisse.genericMap X)
    (tbar : Spec (.of K) ⟶ U.left) (htbar : tbar ≫ U.hom = x),
    tbar = Spec.map (CommRingCat.ofHom i) ≫ t ∧
    P.sectionToFibre x U tbar htbar s = p ∧
    ∀ j : Fin n,
      HEq (toGeneric X (normContinuousRing A).X ks L.obj U t ht
        (column X A (a.frame U s) j (Over.mk (𝟙 U)))) (b j)

end AlgebraicGeometry.ProEtale.TorsorAssociatedModule
