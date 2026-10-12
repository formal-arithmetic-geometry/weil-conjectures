/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Sheaf.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

public import Mathlib.Algebra.Category.ModuleCat.Limits

/-! # Affine annihilation of the canonical formal push-pull comparison

Source: Stacks Project, Cohomology of Schemes, Lemma 088B, second half of the proof.
(blueprint: lem-weil-pbc-formal-systems-push-pull-affine-annihilation)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The canonical comparison, specified by its quotient and adjunction equations,
has affine limit kernel and cokernel killed by a positive power of K.

Source: Stacks Project, Lemma 088B, proof from the base change to Spec(B-completion)
to its last paragraph; Remark 0888, condition (2).
(blueprint: lem-weil-pbc-formal-systems-push-pull-affine-annihilation)

Proof: Restrict to an affine open U = Spec B. The quotient equation determines
κ uniquely because the quotient projections are epimorphisms. Formal functions
and the affine formal-module equivalence then show that the adjunction equation
determines α uniquely. Replace B by its J-adic completion B'; it is Noetherian
and flat over B, and B/J^n = B'/(JB')^n. Flat base change identifies the
pushforward sections, the quotient maps, and the adjunction units; uniqueness
therefore identifies the pulled-back comparison with the comparison over B'.
The affine formal-module equivalence algebraizes G over B'. Full faithfulness
of completion on coherent modules proper over a complete base algebraizes β
to an isomorphism b: f*G -> F. The comparison is now the completion of the
adjunction map G -> f_*f*G followed by f_*b, by its defining equations.
Over the complement of V(K) this is an isomorphism, since f is an isomorphism
there. Its coherent kernel and cokernel are supported on V(K); Tag 01Y9
annihilates both by a common positive power K^s. Exactness of completion on
finite modules carries this annihilation to the affine limit kernel and
cokernel. Since the two affine limit modules are already complete modules,
the original and completed limit maps coincide under the canonical equivalences;
restricting scalars carries annihilation by (KB')^s back to K^s. This yields
one exponent for each U. For K = 0 choose exponent 1; on an empty affine
all modules vanish, so exponent 1 also works.
-/
theorem formalSystemsPushPull_affine_annihilation
    {X Y : Scheme.{u}} [IsNoetherian Y]
    (J K : Y.IdealSheafData) (f : X ⟶ Y) [IsProper f]
    (hV : IsIso (pullback.snd f (Scheme.Opens.ι K.support.compl)))
    (adj : Scheme.Modules.tensorPullback f ⊣ Scheme.Modules.pushforward f)
    (G : CoherentFormalModule Y J) (F : CoherentModules X)
    (β : G.obj ⋙ Scheme.Modules.tensorPullback f ≅
      formalCompletionSystem (J.comap f) F.obj)
    (h : RingedSpace.IsCoherent Y.toRingedSpace
      ((Scheme.Modules.pushforward f).obj F.obj))
    (κ : formalCompletionSystem J ((Scheme.Modules.pushforward f).obj F.obj) ⟶
      formalCompletionSystem (J.comap f) F.obj ⋙ Scheme.Modules.pushforward f)
    (α : G ⟶ (completion Y J).obj ⟨(Scheme.Modules.pushforward f).obj F.obj, h⟩)
    (hκ : ∀ n : ℕ,
      formalModuleQuotientπ J (n + 1) ((Scheme.Modules.pushforward f).obj F.obj) ≫
        κ.app (op n) =
      (Scheme.Modules.pushforward f).map
        (formalModuleQuotientπ (J.comap f) (n + 1) F.obj))
    (hα : ∀ n : ℕ, α.hom.app (op n) ≫ κ.app (op n) =
      adj.unit.app (G.obj.obj (op n)) ≫
        (Scheme.Modules.pushforward f).map (β.hom.app (op n))) :
    ∀ U : Y.affineOpens, ∃ t : ℕ, 1 ≤ t ∧
      K.ideal U ^ t ≤ Module.annihilator Γ(Y, U.1) (LinearMap.ker
        (lim.map (Functor.whiskerRight α.hom
          (SheafOfModules.evaluation Y.ringCatSheaf (op U.1)))).hom) ∧
      K.ideal U ^ t ≤ Module.annihilator Γ(Y, U.1)
        (↥(limit (((completion Y J).obj
          ⟨(Scheme.Modules.pushforward f).obj F.obj, h⟩).obj ⋙
          SheafOfModules.evaluation Y.ringCatSheaf (op U.1)) :
          ModuleCat Γ(Y, U.1)) ⧸ LinearMap.range
          (lim.map (Functor.whiskerRight α.hom
            (SheafOfModules.evaluation Y.ringCatSheaf (op U.1)))).hom) := by
  sorry

end AlgebraicGeometry
