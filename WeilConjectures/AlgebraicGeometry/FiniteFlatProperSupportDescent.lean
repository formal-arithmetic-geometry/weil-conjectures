/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.RingTheory.Noetherian.Basic
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.IsFlatOver
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase
import WeilConjectures.AlgebraicGeometry.FinitelyPresentedComplexDescent
import WeilConjectures.AlgebraicGeometry.ChosenComplexFlatProperRefinement

/-!
# Descent of bounded flat complexes with proper support

## References

Stacks Project, Limits of Schemes, Tags 01ZR, 05LY and 081G;
Cohomology of Schemes, Lemma 30.26.7 (Tag 0CYS).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private theorem supportProper_of_iso {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] {M N : X.Modules} (e : M ≅ N)
    (hN : Scheme.Modules.HasSupportProperOver f N) :
    Scheme.Modules.HasSupportProperOver f M := by
  obtain ⟨Z, hZ, hp⟩ := hN
  refine ⟨Z, hZ.trans ?_, hp⟩
  ext x
  let es := ((Scheme.Modules.toPresheaf X) ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} x).mapIso e
  have hs : Subsingleton (M.presheaf.stalk x) ↔ Subsingleton (N.presheaf.stalk x) := by
    constructor
    · intro h
      have : Subsingleton (((Scheme.Modules.toPresheaf X) ⋙
          TopCat.Presheaf.stalkFunctor Ab.{u} x).obj M) := h
      exact Function.Surjective.subsingleton
        ((ConcreteCategory.bijective_of_isIso es.hom).2)
    · intro h
      have : Subsingleton (((Scheme.Modules.toPresheaf X) ⋙
          TopCat.Presheaf.stalkFunctor Ab.{u} x).obj N) := h
      exact Function.Injective.subsingleton
        ((ConcreteCategory.bijective_of_isIso es.hom).1)
  exact not_congr hs.symm

/-- A bounded complex of finitely presented modules flat over the limit base and with
termwise proper support descends with all these properties to a later stage.
(Stacks, Tags 01ZR, 05LY, 081G and 0CYS.) -/
theorem finite_flat_proper_support_descent
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) [∀ k : I, IsNoetherianRing (R.obj k)]
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (G : CochainComplex (pullback f (c.π.app (op i))).Modules ℤ)
    (hG_bounded : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (G.X n))
    (hG_fp : ∀ n : ℤ, (G.X n).IsFinitePresentation)
    (hG_flat : ∀ n : ℤ, (G.X n).IsFlatOver (pullback.snd f (c.π.app (op i))))
    (hG_support : ∀ n : ℤ,
      Scheme.Modules.HasSupportProperOver (pullback.snd f (c.π.app (op i))) (G.X n)) :
    ∃ (j : I) (hij : i ≤ j)
      (Gj : CochainComplex (pullback f (Spec.map (R.map (homOfLE hij)))).Modules ℤ),
      (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (Gj.X n)) ∧
      (∀ n : ℤ, (Gj.X n).IsFinitePresentation) ∧
      (∀ n : ℤ, (Gj.X n).IsFlatOver (pullback.snd f (Spec.map (R.map (homOfLE hij))))) ∧
      (∀ n : ℤ, Scheme.Modules.HasSupportProperOver
        (pullback.snd f (Spec.map (R.map (homOfLE hij)))) (Gj.X n)) ∧
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
  have hG_qc : ∀ n : ℤ, (G.X n).IsQuasicoherent := by
    intro n
    have := hG_fp n
    infer_instance
  obtain ⟨j, hij, H, hH_bounded, hH_fp, _, e, he⟩ :=
    exists_finitelyPresented_complex_of_limit R c hc i f G hG_bounded hG_fp hG_qc
  have hH_flat : ∀ n : ℤ,
      ((Scheme.Modules.moduleBaseChange f
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (c.π.app (op i)))
        (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))).obj (H.X n)).IsFlatOver
        (pullback.snd f (c.π.app (op i))) := by
    intro n
    exact (hG_flat n).of_iso (e n).symm
  have hH_support : ∀ n : ℤ, Scheme.Modules.HasSupportProperOver
      (pullback.snd f (c.π.app (op i)))
      ((Scheme.Modules.moduleBaseChange f
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (c.π.app (op i)))
        (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))).obj (H.X n)) := by
    intro n
    exact supportProper_of_iso _ (e n) (hG_support n)
  obtain ⟨k, hjk, K, hK_bounded, hK_fp, hK_flat, hK_support, e', he'⟩ :=
    exists_chosen_complex_flat_proper_refinement R c hc i f j hij H
      hH_bounded hH_fp hH_flat hH_support
  refine ⟨k, hij.trans hjk, K, hK_bounded, hK_fp, hK_flat, hK_support,
    (fun n ↦ e' n ≪≫ e n), ?_⟩
  intro n m
  change _ ≫ ((e' m).hom ≫ (e m).hom) = ((e' n).hom ≫ (e n).hom) ≫ _
  rw [← Category.assoc, he', Category.assoc, he, ← Category.assoc]

end AlgebraicGeometry
