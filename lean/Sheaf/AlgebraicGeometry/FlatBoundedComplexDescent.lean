/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.RingTheory.Noetherian.Basic
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage
public import Sheaf.AlgebraicGeometry.BaseChangeConventions
import Sheaf.AlgebraicGeometry.FinitelyPresentedComplexDescent
import Sheaf.AlgebraicGeometry.StagedModuleEventualFlatness
import Sheaf.AlgebraicGeometry.PullbackModelFlatnessComparison
import Sheaf.AlgebraicGeometry.BoundedComplexBaseChangeEnlargement
import Mathlib.Data.Int.Interval
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-!
# Descent of bounded finitely presented flat complexes

Source: Stacks Project, `literature/stacks-project/limits.tex`, Lemmas 32.10.2
and 32.10.4 (Tags 01ZR and 05LY) (blueprint: lem-pc-flat-bounded-complex-descent).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private theorem flatOver_of_isZero
    {X S : Scheme.{u}} (f : X ⟶ S) (M : X.Modules) (hM : IsZero M) :
    M.IsFlatOver f := by
  intro V U e
  let : Module Γ(S, V.1) Γ(M, U.1) := Module.compHom _ (f.appLE V.1 U.1 e).hom
  have hz : IsZero (ModuleCat.of Γ(X, U.1) Γ(M, U.1)) := by
    rw [IsZero.iff_id_eq_zero]
    have hh := congrArg (fun t : M ⟶ M ↦ t.val.app (op U.1))
      (hM.eq_of_src (𝟙 M) 0)
    exact hh
  have : Subsingleton Γ(M, U.1) := ModuleCat.subsingleton_of_isZero hz
  infer_instance

private theorem exists_common_stage
    {I : Type u} [PartialOrder I] [IsDirectedOrder I]
    (j : I) (s : Finset ℤ) (l : ℤ → I) :
    ∃ k : I, j ≤ k ∧ ∀ n ∈ s, l n ≤ k := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨j, le_rfl, by simp⟩
  | @insert n s _ ih =>
    obtain ⟨k, hjk, hk⟩ := ih
    obtain ⟨k', hkk', hnk'⟩ := exists_ge_ge k (l n)
    refine ⟨k', hjk.trans hkk', ?_⟩
    intro m hm
    rcases Finset.mem_insert.mp hm with rfl | hm
    · exact hnk'
    · exact (hk m hm).trans hkk'

private theorem termwise_iso_comp
    {C D E : Type*} [Category C] [Category D] [Category E]
    [HasZeroMorphisms C] [HasZeroMorphisms D] [HasZeroMorphisms E]
    (F : C ⥤ E) (B B' : D ⥤ E)
    (K : CochainComplex C ℤ) (H : CochainComplex D ℤ) (G : CochainComplex E ℤ)
    (β : B ≅ B')
    (eK : ∀ n : ℤ, F.obj (K.X n) ≅ B.obj (H.X n))
    (heK : ∀ n m : ℤ, F.map (K.d n m) ≫ (eK m).hom =
      (eK n).hom ≫ B.map (H.d n m))
    (e : ∀ n : ℤ, B'.obj (H.X n) ≅ G.X n)
    (he : ∀ n m : ℤ, B'.map (H.d n m) ≫ (e m).hom = (e n).hom ≫ G.d n m) :
    ∃ e' : ∀ n : ℤ, F.obj (K.X n) ≅ G.X n,
      ∀ n m : ℤ, F.map (K.d n m) ≫ (e' m).hom = (e' n).hom ≫ G.d n m := by
  refine ⟨fun n ↦ eK n ≪≫ β.app (H.X n) ≪≫ e n, ?_⟩
  intro n m
  simp only [Iso.trans_hom, Iso.app_hom]
  rw [← Category.assoc, heK]
  simp only [Category.assoc]
  rw [β.hom.naturality_assoc, he]

/-- A bounded complex of finitely presented modules flat over the limit base descends to a
bounded complex of finitely presented modules flat over some stage.

Source: Stacks Project, `limits.tex`, Lemmas 32.10.2 and 32.10.4, Tags 01ZR
and 05LY (blueprint: lem-pc-flat-bounded-complex-descent).

The ring functor presents the affine inverse system `S_k = Spec R_k` contravariantly; the
limit cone `c` is `S = Spec R` (`IsAffine c.pt`), and `X = X_i ×_{S_i} S`,
`X_j = X_i ×_{S_i} S_j`. The base change of a module on `X_j` to `X` is `moduleBaseChange`
along the cone projection `S → S_j` over `S_i` (def-pc-base-change); the isomorphism of
complexes is a family of termwise isomorphisms commuting with the differentials.

Proof:
1. Apply bounded finite-presentation descent (`lem-pc-fp-complex-descent`, Tag 01ZR) to the
   finitely many terms of `G`, its differentials and their relations: after increasing the
   stage, this gives a bounded complex `H_j` of finitely presented modules on `X_j` whose
   base change to `X` is isomorphic to `G`.
2. Each term `H_j^r` is finitely presented with flat pullback to `X`; eventual flatness
   descent (`lem-pc-flat-module-descent`, Tag 05LY) gives `j_r ≥ j` beyond which its pullback
   is flat over the stage; zero terms are already flat. Directedness gives one stage `j'`
   above the finitely many `j_r`; base-changing `H_j` to `j'` keeps differentials,
   boundedness, finite presentation and the identification with `G`.
3. Rename `j'` as `j` and the base-changed complex as `G_j`. -/
theorem flat_bounded_complex_descent
    {I : Type u} [PartialOrder I] [IsDirectedOrder I]
    (R : I ⥤ CommRingCat.{u}) [∀ k : I, IsNoetherianRing (R.obj k)]
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (G : CochainComplex (pullback f (c.π.app (op i))).Modules ℤ)
    (hG_bounded : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (G.X n))
    (hG_fp : ∀ n : ℤ, (G.X n).IsFinitePresentation)
    (hG_flat : ∀ n : ℤ, (G.X n).IsFlatOver (pullback.snd f (c.π.app (op i)))) :
    ∃ (j : I) (hij : i ≤ j)
      (Gj : CochainComplex (pullback f (Spec.map (R.map (homOfLE hij)))).Modules ℤ),
      (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (Gj.X n)) ∧
      (∀ n : ℤ, (Gj.X n).IsFinitePresentation) ∧
      (∀ n : ℤ, (Gj.X n).IsFlatOver (pullback.snd f (Spec.map (R.map (homOfLE hij))))) ∧
      ∃ e : ∀ n : ℤ,
          (Scheme.Modules.moduleBaseChange f
            (T := Over.mk (Spec.map (R.map (homOfLE hij))))
            (T' := Over.mk (c.π.app (op i)))
            (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))).obj (Gj.X n) ≅ G.X n,
        ∀ n m : ℤ,
          (Scheme.Modules.moduleBaseChange f
            (T := Over.mk (Spec.map (R.map (homOfLE hij))))
            (T' := Over.mk (c.π.app (op i)))
            (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))).map (Gj.d n m) ≫
              (e m).hom = (e n).hom ≫ G.d n m := by
  classical
  have hG_qc : ∀ n : ℤ, (G.X n).IsQuasicoherent := fun n ↦ by
    let := hG_fp n
    infer_instance
  obtain ⟨j, hij, H, hH_bounded, hH_fp, _, e, he⟩ :=
    exists_finitelyPresented_complex_of_limit R c hc i f G hG_bounded hG_fp hG_qc
  have hHflat : ∀ n : ℤ,
      ((Scheme.Modules.moduleBaseChange f
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (c.π.app (op i)))
        (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))).obj (H.X n)).IsFlatOver
          (pullback.snd f (c.π.app (op i))) := fun n ↦
    flatOver_of_iso _ (e n) (hG_flat n)
  have hstage (n : ℤ) := by
    let := hH_fp n
    exact exists_eventually_isFlatOver_staged_module R c hc i f j hij (H.X n) (hHflat n)
  choose l hjl hl using hstage
  obtain ⟨a, b, hab⟩ := hH_bounded
  obtain ⟨k, hjk, hk⟩ := exists_common_stage j (Finset.Icc a b) l
  let g : Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))) ⟶
      Over.mk (Spec.map (R.map (homOfLE hij))) :=
    Over.homMk (Spec.map (R.map (homOfLE hjk)))
      (by simp [← Spec.map_comp, ← R.map_comp])
  let h : Over.mk (c.π.app (op i)) ⟶
      Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))) :=
    Over.homMk (c.π.app (op k)) (c.w (homOfLE (hij.trans hjk)).op)
  have hcomp : h ≫ g = Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op) := by
    apply Over.OverMorphism.ext
    exact c.w (homOfLE hjk).op
  have htermflat : ∀ n : ℤ,
      ((Scheme.Modules.moduleBaseChange f g).obj (H.X n)).IsFlatOver
        (pullback.snd f (Spec.map (R.map (homOfLE (hij.trans hjk))))) := by
    intro n
    by_cases hn : n ∈ Finset.Icc a b
    · exact hl n k (hk n hn)
    · have hz : IsZero (H.X n) := hab n (by
        simp only [Finset.mem_Icc, not_and_or, not_le] at hn
        exact hn)
      let : (Scheme.Modules.tensorPullback (baseChangeMap f g)).IsLeftAdjoint :=
        ⟨_, Scheme.Modules.nonempty_tensorPullbackAdjunction (baseChangeMap f g)⟩
      exact flatOver_of_isZero _ _
        ((Scheme.Modules.tensorPullback (baseChangeMap f g)).map_isZero hz)
  obtain ⟨K, hK_bounded, hK_fp, ⟨q⟩, eK, heK⟩ :=
    exists_bounded_complex_baseChange_enlargement f g h H ⟨a, b, hab⟩ hH_fp
  refine ⟨k, hij.trans hjk, K, hK_bounded, hK_fp,
    fun n ↦ flatOver_of_iso _ (q n) (htermflat n), ?_⟩
  let β : Scheme.Modules.moduleBaseChange f (h ≫ g) ≅
      Scheme.Modules.moduleBaseChange f
        (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op)) :=
    eqToIso (congrArg (fun t ↦ Scheme.Modules.moduleBaseChange f t) hcomp)
  exact termwise_iso_comp (Scheme.Modules.moduleBaseChange f h)
    (Scheme.Modules.moduleBaseChange f (h ≫ g))
    (Scheme.Modules.moduleBaseChange f
      (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))) K H G β eK heK e he

end AlgebraicGeometry
