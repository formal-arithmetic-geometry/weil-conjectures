/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import WeilConjectures.AlgebraicGeometry.HenselianConnectedness
import WeilConjectures.RingTheory.HenselianOfEtaleNeighbourhoodSection
import WeilConjectures.Mathlib.CategoryTheory.Sites.Subcanonical

/-! # Stein connectedness over a closed-specializing pro-etale test

Source: Steps 1--2 of `lem-sp-proetale-proper-closed-overlap-chains`.
(blueprint: lem-sp-proetale-proper-test-closed-fibre-connectedness).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- Every irreducible closed subset of the proper pullback meets its closed fibre
in a nonempty connected set. This is a topological assertion, without coefficients,
free sheaves, augmentation maps, or choices of overlap arrows.

Source: Steps 1--2 of `lem-sp-proetale-proper-closed-overlap-chains`;
Stein connectedness for a henselian pair, Stacks Tag 0A0B.
(blueprint: lem-sp-proetale-proper-test-closed-fibre-connectedness).

Proof: write the affine scheme W as Spec R and its closed fibre as V(J).
Every maximal point of Spec R specializes into V(J), hence belongs to V(J), so
J is contained in the Jacobson radical. Evaluation at W splits epimorphisms of
set sheaves. In particular an etale neighbourhood of V(J) admits a section:
its image contains V(J), and is open, so the specialization assumption makes
it surjective over W. To lift a specified section over V(J), first remove the
closed complement of that section in the etale closed fibre. The remaining
etale neighbourhood is still surjective and its section lifts the specified
one. The etale section-lifting characterization of henselian pairs therefore
makes (R,J) henselian. The projection B times_D W to W is proper by base
change. Apply Stein connectedness to this proper morphism over Spec R and
transport V(J) back to the inverse image of the closed complement in B.
This proves both nonemptiness and connectedness, including nonreduced closed
fibres. If W or the proper pullback is empty there is no irreducible C. -/
theorem proper_test_closed_fibre_connectedness
    {B D E : Scheme.{u}} (p : B ⟶ D) (i : E ⟶ D)
    [IsProper p] [IsOpenImmersion i] [QuasiCompact i]
    (W : D.ProEt) [IsAffine W.left]
    (hW : ∀ (F G : Sheaf (ProEt.topology D) (Type (u + 1))) (e : F ⟶ G),
      Epi e → Function.Surjective (e.hom.app (op W)))
    (hspecializes : ∀ x : W.left, ∃ z : ↥(pullback W.hom i.closedComplement),
      Specializes x ((pullback.fst W.hom i.closedComplement) z)) :
    let z := (pullback.fst p i).closedComplement
    let P := (proEtaleBaseChange p).obj W
    ∀ C : Set P.left, IsClosed C → IsIrreducible C →
      IsConnected (C ∩ P.hom ⁻¹' Set.range z) := by
  intro z P C hC hCirr
  let X := W.left
  let R := Γ(X, ⊤)
  let Z : Set (Spec R) :=
    X.isoSpec.hom '' Set.range (pullback.fst W.hom i.closedComplement)
  have hZ : IsClosed Z := by
    refine (X.isoSpec.hom.homeomorph.isClosedMap _ ?_)
    exact (pullback.fst W.hom i.closedComplement).isClosedEmbedding.isClosed_range
  let I : Ideal R := PrimeSpectrum.vanishingIdeal Z
  have hIZ : PrimeSpectrum.zeroLocus (I : Set R) = Z := by
    rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hZ.closure_eq]
  have : HenselianRing R I := by
    apply Algebra.henselianRing_of_etale_surjective_zeroLocus_section
    intro A' _ _ _ hsurj
    let φ : Spec (.of A') ⟶ Spec R := Spec.map (CommRingCat.ofHom (algebraMap R A'))
    have : Etale φ := HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr ‹_›)
    let g : Spec (.of A') ⟶ X := φ ≫ X.isoSpec.inv
    have : Surjective g := by
      refine ⟨fun x ↦ ?_⟩
      obtain ⟨y, hy⟩ := hspecializes x
      have hmem : (pullback.fst W.hom i.closedComplement) y ∈ Set.range g := by
        have hy' : X.isoSpec.hom ((pullback.fst W.hom i.closedComplement) y) ∈
            PrimeSpectrum.zeroLocus (I : Set R) := hIZ ▸ ⟨_, ⟨y, rfl⟩, rfl⟩
        obtain ⟨q', hq'⟩ := hsurj _ hy'
        have hφq : φ q' = X.isoSpec.hom ((pullback.fst W.hom i.closedComplement) y) := hq'
        refine ⟨q', ?_⟩
        change (φ ≫ X.isoSpec.inv) q' = _
        rw [Scheme.Hom.comp_apply, hφq]
        change (X.isoSpec.hom ≫ X.isoSpec.inv) _ = _
        simp
      exact hy.mem_open g.isOpenMap.isOpen_range hmem
    let V : D.ProEt := ProEt.mk (g ≫ W.hom)
    let f : V ⟶ W := MorphismProperty.Over.homMk g
    have hf : Sieve.generate (Presieve.singleton f) ∈ ProEt.topology D W := by
      apply Precoverage.generate_mem_toGrothendieck
      change (Presieve.singleton f).map (ProEt.forget D ⋙ Over.forget D) ∈
        Scheme.proetalePrecoverage W.left
      rw [Presieve.map_singleton]
      exact Scheme.Hom.singleton_mem_propQCPrecoverage (P := @WeaklyEtale) (f := g)
        inferInstance
    obtain ⟨s, hs⟩ := GrothendieckTopology.exists_comp_eq_id_of_surjective_app.{u + 1} f hf hW
    have hs' : s.left ≫ g = 𝟙 X := congrArg (fun k : W ⟶ W ↦ k.left) hs
    let σ := Spec.preimage (X.isoSpec.inv ≫ s.left)
    have hσ : CommRingCat.ofHom (algebraMap R A') ≫ σ = 𝟙 R := by
      apply Spec.map_injective
      simp only [Spec.map_comp, σ, Spec.map_preimage]
      have hφ : φ = g ≫ X.isoSpec.hom := by simp [g]
      have h : (X.isoSpec.inv ≫ s.left) ≫ φ = 𝟙 _ := by
        rw [hφ, Category.assoc, reassoc_of% hs', Category.id_comp, Iso.inv_hom_id]
      exact h.trans (Spec.map_id _).symm
    exact ⟨{ toRingHom := σ.hom, commutes' := fun r ↦ congrArg (fun k ↦ k.hom r) hσ }⟩
  let q : P.left ⟶ X := pullback.fst W.hom p
  have hset : P.hom ⁻¹' Set.range z =
      (q ≫ X.isoSpec.hom) ⁻¹' PrimeSpectrum.zeroLocus (I : Set R) := by
    ext x
    have hcond : W.hom (q x) = p (P.hom x) := by
      change (q ≫ W.hom) x = (pullback.snd W.hom p ≫ p) x
      rw [pullback.condition]
      rfl
    have hinj : Function.Injective X.isoSpec.hom := X.isoSpec.hom.homeomorph.injective
    rw [Set.mem_preimage, Set.mem_preimage, hIZ, Scheme.Hom.comp_apply, hinj.mem_set_image]
    simp only [z, Scheme.Hom.range_closedComplement, Scheme.Pullback.range_fst, Set.mem_preimage,
      Set.mem_compl_iff, hcond]
    exact Iff.rfl
  rw [hset]
  exact (q ≫ X.isoSpec.hom).isConnected_inter_preimage_zeroLocus I hC hCirr

end AlgebraicGeometry.Scheme
