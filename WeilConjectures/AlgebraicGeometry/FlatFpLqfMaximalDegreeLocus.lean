/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FiberDegreeBound
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
import WeilConjectures.AlgebraicGeometry.FlatFpLqfMaximalDegreeEtaleNeighborhood
import WeilConjectures.AlgebraicGeometry.FiniteFiberDegreeBaseChange
import WeilConjectures.AlgebraicGeometry.IsFiniteLocallyFreeOfDegreeOfEtaleCover
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# The maximal fibre degree locus

The geometric claim in the proof of Stacks Project, More on Morphisms, Tag 07RY.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Hom

/-- The maximal fibre degree locus is open, and the restriction to it is finite
(Stacks, Tag 07RY). -/
theorem exists_isFinite_morphismRestrict_maximal_fiber_degree {X S : Scheme.{u}}
    (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f] [IsSeparated f]
    (h_lqf : IsLocallyQuasiFinite f) (m : ℕ) (hm : BoundsFiberDegrees f m) :
    ∃ U : S.Opens,
      (∀ s : S, s ∈ U ↔ (f.fiberToSpecResidueField s).finrankΓ = m) ∧ IsFinite (f ∣_ U) := by
  classical
  let δ : S → ℕ := fun s ↦ (f.fiberToSpecResidueField s).finrankΓ
  let E := {s : S // δ s = m}
  choose T φ t hφ ht hdeg using fun s : E ↦
    exists_etale_isFiniteLocallyFreeOfDegree_of_maximal_fiber_degree
      f h_lqf m hm s.val s.property
  have himage (s : E) : Set.range (φ s) ⊆ {s : S | δ s = m} := by
    rintro y ⟨z, rfl⟩
    have := hdeg s
    exact ((finite_fiber_degree_pullback f (φ s) z (hm ((φ s) z)).1).2).symm.trans
      ((hdeg s).fiberDegree_eq z)
  have hopen : IsOpen {s : S | δ s = m} := by
    rw [isOpen_iff_forall_mem_open]
    intro s hs
    let e : E := ⟨s, hs⟩
    have := hφ e
    exact ⟨Set.range (φ e), himage e, (φ e).isOpenMap.isOpen_range, ⟨t e, ht e⟩⟩
  let U : S.Opens := ⟨_, hopen⟩
  have hfactor (s : E) : Set.range (φ s) ⊆ Set.range U.ι := by
    simpa [U] using himage s
  let ψ (s : E) : T s ⟶ U := IsOpenImmersion.lift U.ι (φ s) (hfactor s)
  have hfac (s : E) : ψ s ≫ U.ι = φ s := IsOpenImmersion.lift_fac _ _ _
  have hψ (s : E) : Etale (ψ s) := by
    have := hφ s
    have : Etale (ψ s ≫ U.ι) := by rw [hfac]; infer_instance
    exact Etale.of_comp (ψ s) U.ι
  have hcover : ∀ z : U, ∃ (s : E) (w : T s), ψ s w = z := by
    intro z
    let s : E := ⟨z.val, z.property⟩
    refine ⟨s, t s, U.ι.isOpenEmbedding.injective ?_⟩
    change (ψ s ≫ U.ι) (t s) = z.val
    rw [hfac]
    exact ht s
  have hdegree (s : E) : (pullback.snd (f ∣_ U) (ψ s)).IsFiniteLocallyFreeOfDegree m := by
    have := hdeg s
    let p := pullback.snd (f ∣_ U) (ψ s)
    have H := (IsPullback.of_hasPullback (f ∣_ U) (ψ s)).paste_horiz
      (isPullback_morphismRestrict f U).flip
    rw [hfac] at H
    have : IsFinite p := by
      have : IsFinite (H.isoPullback.hom ≫ pullback.snd f (φ s)) := inferInstance
      rwa [H.isoPullback_hom_snd] at this
    have : p.IsFiniteLocallyFree := {}
    refine { fiberDegree_eq := ?_ }
    intro w
    have heq : p = H.isoPullback.hom ≫ pullback.snd f (φ s) :=
      H.isoPullback_hom_snd.symm
    have hd := fiberDegree_comp_left_of_isIso
      H.isoPullback.hom (pullback.snd f (φ s)) w
    rw [← heq] at hd
    exact hd.trans ((hdeg s).fiberDegree_eq w)
  have hfree := isFiniteLocallyFreeOfDegree_of_etale_cover (f ∣_ U) m T ψ hψ hcover hdegree
  exact ⟨U, fun s ↦ Iff.rfl, hfree.toIsFiniteLocallyFree.toIsFinite⟩

end AlgebraicGeometry.Scheme.Hom
