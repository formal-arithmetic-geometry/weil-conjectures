/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T3
-/
module

public import Sheaf.CategoryTheory.InternalHomogeneousCochainCoordinateData

/-! # Empty-tuple evaluation of internal bar cochains

Source: the internal sheaf adaptation of the displayed bar differential of Stacks 0DVG.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.CondensedBar

/-- In degree zero the bar term is the coefficient module, with the actual empty-tuple
evaluation on every slice.
Source: Stacks 0DVG, degree-zero internal evaluation calculation
(blueprint: lem-sfb-internal-bar-zero-evaluation).

Proof: compose the recorded degree-zero bar-term isomorphism with evaluation of an
internal function on the unique empty tuple. On sections over S, the latter sends a
natural family c to c(S,id,empty). Its inverse sends m to the family (T,f,empty) ↦ f* m.
Naturality of c shows these operations are inverse: the parameter power J⁰ is terminal,
so every parameter map is the empty tuple. Evaluation additivity and scalar compatibility
show linearity; the restriction law shows naturality in S. Lift these mutually inverse
linear section maps through the section-module equivalence. This proves both the internal
isomorphism and the evaluation identity on the whole slice, including empty test objects. -/
theorem exists_internalBarZeroEvaluation {A : Ring.{u}} (F : InternalFunctions A)
    (J : ProfiniteGrp.{u}) (B : BarDiagram (G := J) F) (M : Equivariant A J) :
    ∃ z : ((cochains B).obj M).X 0 ≅ M.module,
      ∀ (S : Profinite.{u}) (c : sections A (((cochains B).obj M).X 0) S)
        (T : Profinite.{u}) (f : T ⟶ S) (g : Fin 0 → C(T, J)),
        inhomogeneousCoordinateValue B M 0 S c T f g =
          M.module.X.obj.map f.op (z.hom.hom.hom.app (op S) c) := by
  let P := power J 0
  let E := (F.functor P).obj M.module
  let empty (S : Profinite.{u}) : C(S, P) := tupleMap Fin.elim0
  let ev (S : Profinite.{u}) (x : sections A E S) : sections A M.module S :=
    (F.evaluate P S M.module x).val S (𝟙 S) (empty S)
  have hev (S T : Profinite.{u}) (f : T ⟶ S) (x : sections A E S) :
      (F.evaluate P S M.module x).val T f (empty T) =
        M.module.X.obj.map f.op (ev S x) := by
    have h := (F.evaluate P S M.module x).property S T (𝟙 S) f (empty S)
    simpa only [Category.comp_id,
      show (empty S).comp f.hom.hom = empty T from Subsingleton.elim _ _] using h.symm
  let theta : E ⟶ M.module :=
    (InternalAbelianSheafModule.sectionModuleFunctor_fullyFaithful
      (coherentTopology Profinite.{u}) A.X).preimage
      ⟨PresheafOfModules.homMk
        { app Z := AddCommGrpCat.ofHom
            { toFun := ev Z.unop
              map_zero' := by
                apply add_left_cancel (a := ev Z.unop 0)
                simpa only [add_zero] using
                  (F.add P Z.unop M.module 0 0 Z.unop (𝟙 Z.unop) (empty Z.unop)).symm
              map_add' := fun x y ↦ F.add P Z.unop M.module x y Z.unop
                (𝟙 Z.unop) (empty Z.unop) }
          naturality Z W f := by
            apply ConcreteCategory.hom_ext
            intro x
            change ev W.unop (E.X.obj.map f x) =
              M.module.X.obj.map f (ev Z.unop x)
            exact (F.restriction P Z.unop W.unop f.unop M.module x W.unop
              (𝟙 W.unop) (empty W.unop)).trans
                (by simpa only [Category.id_comp, Quiver.Hom.op_unop] using
                  hev Z.unop W.unop f.unop x) }
        (by
          intro Z r x
          let r' : sectionRing A Z.unop := r
          let x' : sections A E Z.unop := x
          change ev Z.unop (r' • x') = r' • ev Z.unop x'
          simpa [ev] using F.smul P Z.unop M.module r' x' Z.unop
            (𝟙 Z.unop) (empty Z.unop))⟩
  have htheta (S : Profinite.{u}) (x : sections A E S) :
      theta.hom.hom.app (op S) x = ev S x := rfl
  have hbij (S : Profinite.{u}) : Function.Bijective (theta.hom.hom.app (op S)) := by
    constructor
    · intro x y hxy
      apply (F.evaluate P S M.module).injective
      apply Subtype.ext
      funext T f g
      rw [show g = empty T from Subsingleton.elim _ _]
      rw [hev S T f x, hev S T f y]
      exact congrArg (fun m ↦ M.module.X.obj.map f.op m) hxy
    · intro m
      let c : {c : FunctionFamily M.module P S // c.IsNatural} :=
        ⟨fun T f _ ↦ M.module.X.obj.map f.op m, by
          intro T V f k g
          change M.module.X.obj.map k.op (M.module.X.obj.map f.op m) =
            M.module.X.obj.map (k ≫ f).op m
          rw [op_comp, M.module.X.obj.map_comp]
          rfl⟩
      refine ⟨(F.evaluate P S M.module).symm c, ?_⟩
      rw [htheta]
      dsimp only [ev]
      rw [Equiv.apply_symm_apply]
      change M.module.X.obj.map (𝟙 S).op m = m
      simp
  have : ∀ S, IsIso (theta.hom.hom.app S) := fun S ↦
    (ConcreteCategory.isIso_iff_bijective _).2 (hbij S.unop)
  have : IsIso theta.hom.hom := NatIso.isIso_of_isIso_app _
  have : IsIso ((sheafToPresheaf (coherentTopology Profinite.{u})
      AddCommGrpCat.{u + 1}).map theta.hom) := by
    change IsIso theta.hom.hom
    infer_instance
  have : IsIso theta.hom := isIso_of_reflects_iso _
    (sheafToPresheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
  have : IsIso ((Mod.forget A.toMon.X).map theta) := by
    change IsIso theta.hom
    infer_instance
  have : IsIso theta := isIso_of_reflects_iso _ (Mod.forget A.toMon.X)
  refine ⟨B.term M 0 ≪≫ asIso theta, ?_⟩
  intro S c T f g
  change (F.evaluate P S M.module ((B.term M 0).hom.hom.hom.app (op S) c)).val
    T f (tupleMap g) =
      M.module.X.obj.map f.op
        (theta.hom.hom.app (op S) ((B.term M 0).hom.hom.hom.app (op S) c))
  rw [htheta, show tupleMap g = empty T from Subsingleton.elim _ _]
  exact hev S T f _

end CategoryTheory.CondensedBar
