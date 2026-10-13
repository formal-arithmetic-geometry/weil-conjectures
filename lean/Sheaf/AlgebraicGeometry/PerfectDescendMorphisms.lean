/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.DerivedPullbackComposition
public import Sheaf.AlgebraicGeometry.PerfectHomTransport
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.AlgebraicGeometry.Picard.TwistedDescent
import Sheaf.AlgebraicGeometry.PerfectHomContinuity
import Mathlib.Data.Finset.Order

/-!
# Descent of morphisms between perfect complexes

Source: Stacks Project, Derived Categories of Schemes, Lemma 36.29.2, Tag 09RE,
used in Lemma 36.29.3, Tag 09RF (blueprint: lem-pc-perfect-descend-morphisms).

The shared coherent derived-pullback composition comparisons transport the stage map
to the direct pullbacks of both objects. The equality clause uses a common starting stage for the
finite list of morphisms; directedness puts any finite list of starting stages in this form.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The recorded canonical composition comparison along a base-change map.
This specializes the shared counit-pinned comparisons of
`exists_derivedPullbackComposition`; it introduces no new pullback functor.
Source: Stacks Project, Derived Categories of Schemes, Tag 09RE; Cohomology, Tag 0D5S
(blueprint: lem-pc-perfect-descend-morphisms). -/
noncomputable abbrev perfectDescentComparison
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X S : Scheme.{u}} (s : X ⟶ S) {T T' : Over S} (g : T' ⟶ T) :
    derivedPullback (pullback.fst s T'.hom) ≅
      derivedPullback (pullback.fst s T.hom) ⋙ derivedPullback (baseChangeMap s g) :=
  perfectHomComparison s g

private theorem homMap_eq_iff
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X S : Scheme.{u}} (s : X ⟶ S) {T T' : Over S} (g : T' ⟶ T)
    {P Q : schemeDerivedCategory X}
    (f : (derivedPullback (pullback.fst s T.hom)).obj P ⟶
      (derivedPullback (pullback.fst s T.hom)).obj Q)
    (φ : (derivedPullback (pullback.fst s T'.hom)).obj P ⟶
      (derivedPullback (pullback.fst s T'.hom)).obj Q) :
    (perfectDescentComparison s g).hom.app P ≫
      (derivedPullback (baseChangeMap s g)).map f =
        φ ≫ (perfectDescentComparison s g).hom.app Q ↔ perfectHomMap s g f = φ := by
  rw [← cancel_mono ((perfectDescentComparison s g).inv.app Q)]
  simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  rfl

/-- Morphisms between perfect complexes descend, isomorphisms descend as isomorphisms,
and finitely many equalities are eventually true at one common stage.
Source: Stacks Project, Derived Categories of Schemes, Tag 09RE, used in Tag 09RF
(blueprint: lem-pc-perfect-descend-morphisms).

Proof: `perfect_hom_continuity` isolates the affine calculation and quasi-compact-open
induction of Tag 09RE. Apply its surjectivity clause to lift a morphism. If the morphism
is invertible, apply the same clause to its inverse on a tail above the first lift, and
transport the first lift to that stage. `perfectLimitMap_stage` preserves its limit image.
Composition and identity preservation show the two composites have limit images equal
to the identities. Apply the equality clause separately to these two relations, choose
an upper bound of their stabilization stages, and obtain mutually inverse stage maps.
For a finite family of equalities, apply the equality clause to each pair and take an
upper bound of the finite set of stabilization stages and the initial stage. The empty
family is covered too because the initial stage witnesses nonemptiness of the index set.
Finally cancel the invertible comparison components to obtain exactly the unconjugated
pullback equations in the statement. -/
theorem perfect_descend_morphisms
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (hc : IsColimit c)
    (i : I) (Xi : Scheme.{u}) (s : Xi ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation s] [QuasiCompact s] [QuasiSeparated s]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ U : Xi.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Xi.toRingedSpace).over U))]
    (Pi Qi : schemeDerivedCategory Xi) (hP : Xi.IsPerfect Pi) (hQ : Xi.IsPerfect Qi)
    :
    (∀ φ : (derivedPullback (pullback.fst s (Spec.map (c.ι.app i)))).obj Pi ⟶
        (derivedPullback (pullback.fst s (Spec.map (c.ι.app i)))).obj Qi,
      ∃ (j : I) (hij : i ≤ j)
        (φj : (derivedPullback
            (pullback.fst s (Spec.map (R.map (homOfLE hij))))).obj Pi ⟶
          (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE hij))))).obj Qi),
        (perfectDescentComparison s
            (T := Over.mk (Spec.map (R.map (homOfLE hij))))
            (T' := Over.mk (Spec.map (c.ι.app i)))
            (Over.homMk (Spec.map (c.ι.app j))
              (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)]))).hom.app Pi ≫
          (derivedPullback (baseChangeMap s
            (T := Over.mk (Spec.map (R.map (homOfLE hij))))
            (T' := Over.mk (Spec.map (c.ι.app i)))
            (Over.homMk (Spec.map (c.ι.app j))
              (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)])))).map φj =
            φ ≫ (perfectDescentComparison s
            (T := Over.mk (Spec.map (R.map (homOfLE hij))))
            (T' := Over.mk (Spec.map (c.ι.app i)))
            (Over.homMk (Spec.map (c.ι.app j))
              (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)]))).hom.app Qi ∧
          (IsIso φ → IsIso φj)) ∧
    (∀ (j : I) (hij : i ≤ j) (n : ℕ)
      (a b : Fin n →
        ((derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE hij))))).obj Pi ⟶
          (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE hij))))).obj Qi)),
      (∀ t : Fin n,
        (derivedPullback (baseChangeMap s
          (T := Over.mk (Spec.map (R.map (homOfLE hij))))
          (T' := Over.mk (Spec.map (c.ι.app i)))
          (Over.homMk (Spec.map (c.ι.app j))
            (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)])))).map (a t) =
        (derivedPullback (baseChangeMap s
          (T := Over.mk (Spec.map (R.map (homOfLE hij))))
          (T' := Over.mk (Spec.map (c.ι.app i)))
          (Over.homMk (Spec.map (c.ι.app j))
            (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)])))).map (b t)) →
      ∃ (k : I) (hjk : j ≤ k), ∀ t : Fin n,
        (derivedPullback (baseChangeMap s
          (T := Over.mk (Spec.map (R.map (homOfLE hij))))
          (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
          (Over.homMk (Spec.map (R.map (homOfLE hjk)))
            (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl)))).map (a t) =
        (derivedPullback (baseChangeMap s
          (T := Over.mk (Spec.map (R.map (homOfLE hij))))
          (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
          (Over.homMk (Spec.map (R.map (homOfLE hjk)))
            (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl)))).map (b t)) := by
  classical
  have cont := fun P Q hP hQ ↦ perfect_hom_continuity R c hc i Xi s P Q hP hQ
  have surj := (cont Pi Qi hP hQ).1
  have eqs := (cont Pi Qi hP hQ).2
  constructor
  · intro φ
    by_cases hφ : IsIso φ
    · let := hφ
      obtain ⟨j, hij, f, hf⟩ := surj i le_rfl φ
      obtain ⟨k, hjk, g, hg⟩ := (cont Qi Pi hQ hP).1 j hij (inv φ)
      let f' := perfectStageMap R s hij hjk f
      have hf' : perfectLimitMap R c s (hij.trans hjk) f' = φ := by
        rw [perfectLimitMap_stage, hf]
      have hfg : perfectLimitMap R c s (hij.trans hjk) (f' ≫ g) =
          perfectLimitMap R c s (hij.trans hjk) (𝟙 _) := by
        have h := congrArg₂ (fun a b ↦ a ≫ b) hf' hg
        rw [perfectLimitMap_id]
        simp only [perfectLimitMap] at h ⊢
        rw [perfectHomMap_comp]
        simpa only [IsIso.hom_inv_id] using h
      have hgf : perfectLimitMap R c s (hij.trans hjk) (g ≫ f') =
          perfectLimitMap R c s (hij.trans hjk) (𝟙 _) := by
        have h := congrArg₂ (fun a b ↦ a ≫ b) hg hf'
        rw [perfectLimitMap_id]
        simp only [perfectLimitMap] at h ⊢
        rw [perfectHomMap_comp]
        simpa only [IsIso.inv_hom_id] using h
      obtain ⟨l₁, hkl₁, hl₁⟩ := (cont Pi Pi hP hP).2 k (hij.trans hjk) _ _ hfg
      obtain ⟨l₂, hkl₂, hl₂⟩ := (cont Qi Qi hQ hQ).2 k (hij.trans hjk) _ _ hgf
      obtain ⟨l, hl₁l, hl₂l⟩ := directed_of (· ≤ ·) l₁ l₂
      let fl := perfectStageMap R s (hij.trans hjk) (hkl₁.trans hl₁l) f'
      let gl := perfectStageMap R s (hij.trans hjk) (hkl₁.trans hl₁l) g
      have hflgl : fl ≫ gl = 𝟙 _ := by
        have h := hl₁ l hl₁l
        dsimp only [fl, gl]
        rw [perfectStageMap_id] at h
        simp only [perfectStageMap] at h ⊢
        rw [perfectHomMap_comp] at h
        exact h
      have hglfl : gl ≫ fl = 𝟙 _ := by
        have h := hl₂ l hl₂l
        dsimp only [fl, gl]
        rw [perfectStageMap_id] at h
        simp only [perfectStageMap] at h ⊢
        rw [perfectHomMap_comp] at h
        exact h
      have : IsIso fl := ⟨⟨gl, hflgl, hglfl⟩⟩
      refine ⟨l, (hij.trans hjk).trans (hkl₁.trans hl₁l), fl, ?_, fun _ ↦ inferInstance⟩
      have hfl : perfectLimitMap R c s _ fl = φ := by
        rw [perfectLimitMap_stage, hf']
      exact (homMap_eq_iff _ _ _ _).2 hfl
    · obtain ⟨j, hij, f, hf⟩ := surj i le_rfl φ
      refine ⟨j, hij, f, ?_, fun h ↦ (hφ h).elim⟩
      exact (homMap_eq_iff _ _ _ _).2 hf
  · intro j hij n a b hab
    have hab' : ∀ t, perfectLimitMap R c s hij (a t) =
        perfectLimitMap R c s hij (b t) := by
      intro t
      exact (perfectHomMap_eq_iff _ _ _ _).2 (hab t)
    choose k hjk hk using fun t ↦ eqs j hij (a t) (b t) (hab' t)
    let : Nonempty I := ⟨j⟩
    obtain ⟨l, hl⟩ := (Finset.univ.image k).exists_le
    obtain ⟨m, hjm, hlm⟩ := directed_of (· ≤ ·) j l
    refine ⟨m, hjm, fun t ↦ ?_⟩
    have hkt : k t ≤ m := (hl _ (Finset.mem_image.mpr ⟨t, Finset.mem_univ t, rfl⟩)).trans hlm
    exact (perfectHomMap_eq_iff _ _ _ _).1 (hk t m hkt)

end AlgebraicGeometry
