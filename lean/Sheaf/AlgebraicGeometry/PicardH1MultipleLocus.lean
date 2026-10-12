/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.AlgebraicGeometry.PicardDiagonalLocallyClosed
public import Sheaf.AlgebraicGeometry.BaseChangeConventions
public import Sheaf.AlgebraicGeometry.StructureSheafCohomologyPullback
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import Sheaf.AlgebraicGeometry.PicardH1IntersectionSection
import Sheaf.AlgebraicGeometry.ProperFibreGeneratorPullbackLocus

/-!
# H¹ injectivity and the multiple Picard triviality locus

Source: Stacks Project, More on Morphisms, Lemma H1-O-multiple-picard-flat-proper,
Tag 0BF2 (blueprint: lem-sc-picard-h1-multiple-locus).
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The Picard locus agrees locally with the intersection of the pullback Picard loci.
Source: Stacks Project, Tag 0BF2 (blueprint: lem-sc-picard-h1-multiple-locus).
The universal factorization equivalence in the conclusion expresses equality of subschemes,
including their nilpotent structure, rather than just equality of their underlying points.

Proof:
1. Replace the base by the scheme-theoretic intersection of the Zᵢ. By
   lem-sc-picard-diagonal-locally-closed, its universal property preserves all the loci.
   Shrink to an affine neighbourhood on which the pulled-back invertible modules are trivial.
2. Put E = Rf_* L and Eᵢ = Rfᵢ_* O_Xᵢ. By lem-pc-rf-perfect-base-change these are perfect
   and commute with arbitrary base change. Since s lies in Z, E has fibre RΓ(X_s, O_X_s).
3. By lem-sc-perfect-finite-free-residue-model choose bounded finite free models with ranks
   equal to the fibre cohomology dimensions. They vanish in negative degrees and have rank
   one in degree zero by the universal pushforward assumptions. On the affine base the
   derived maps E → Eᵢ are represented by chain maps between these fixed models. Their
   degree-zero residue maps are isomorphisms because fibre trivializing sections pull back.
4. H¹ injectivity gives a nonzero maximal minor of the joint degree-one map. Shrinking makes
   this minor invertible and the map injective. If H¹ is zero this is vacuous. Each target
   degree-zero differential vanishes because Lᵢ is trivial. The chain-map identity then
   forces the source degree-zero differential to vanish too.
5. The fibre trivializing section therefore lifts to a section of L. Its zero locus is
   closed and has closed image by lem-weil-pbc-proper-closed-image. Remove this image near s;
   the section now trivializes L. The universal property of Z gives the required equality.
-/
theorem picard_h1_multiple_locus {X S : Scheme.{v}} (f : X ⟶ S) {n : ℕ}
    (Xi : Fin n → Scheme.{v}) (fi : ∀ i, Xi i ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    [∀ i, Flat (fi i)] [∀ i, IsProper (fi i)] [∀ i, LocallyOfFinitePresentation (fi i)]
    (ui : ∀ i, Xi i ⟶ X) (hui : ∀ i, ui i ≫ f = fi i)
    (hO : ∀ {T : Scheme.{v}} (g : T ⟶ S),
      IsIso ((Classical.choose
        (Scheme.Modules.exists_tensorPullbackAdjunction (pullback.snd f g))).unit.app
          (SheafOfModules.unit T.ringCatSheaf)))
    (hOi : ∀ i, ∀ {T : Scheme.{v}} (g : T ⟶ S),
      IsIso ((Classical.choose
        (Scheme.Modules.exists_tensorPullbackAdjunction (pullback.snd (fi i) g))).unit.app
          (SheafOfModules.unit T.ringCatSheaf)))
    (L : X.Modules) [L.IsInvertible]
    (Z : Scheme.{v}) (j : Z ⟶ S) [IsImmersion j]
    (Zi : Fin n → Scheme.{v}) (ji : ∀ i, Zi i ⟶ S) [∀ i, IsImmersion (ji i)]
    (hZ : ∀ {T : Scheme.{v}} (g : T ⟶ S),
      (∃ h : T ⟶ Z, h ≫ j = g) ↔
        ∃ (N : T.Modules) (_ : N.IsFiniteLocallyFree),
          Nonempty ((Modules.tensorPullback (pullback.fst f g)).obj L ≅
            (Modules.tensorPullback (pullback.snd f g)).obj N))
    (hZi : ∀ i, ∀ {T : Scheme.{v}} (g : T ⟶ S),
      (∃ h : T ⟶ Zi i, h ≫ ji i = g) ↔
        ∃ (N : T.Modules) (_ : N.IsFiniteLocallyFree),
          Nonempty ((Modules.tensorPullback (pullback.fst (fi i) g)).obj
            ((Modules.tensorPullback (ui i)).obj L) ≅
            (Modules.tensorPullback (pullback.snd (fi i) g)).obj N))
    (hsub : ∀ {T : Scheme.{v}} (g : T ⟶ S),
      (∃ h : T ⟶ Z, h ≫ j = g) → ∀ i, ∃ h : T ⟶ Zi i, h ≫ ji i = g)
    (s : S) (hs : s ∈ Set.range j)
    (hH : Function.Injective (fun x :
        Sheaf.H (structureSheafAb (pullback f (S.fromSpecResidueField s))) 1 ↦ fun i ↦
      structureSheafCohomologyPullback
        (((Over.pullback (S.fromSpecResidueField s)).map
          (Over.homMk (U := Over.mk (fi i)) (V := Over.mk f) (ui i) (hui i))).left) 1 x)) :
    ∃ U : S.Opens, s ∈ U ∧ ∀ {T : Scheme.{v}} (g : T ⟶ U.toScheme),
      (∃ h : T ⟶ Z, h ≫ j = g ≫ U.ι) ↔
        ∀ i, ∃ h : T ⟶ Zi i, h ≫ ji i = g ≫ U.ι := by
  classical
  have hsi : ∀ i, s ∈ Set.range (ji i) := by
    obtain ⟨z, hz⟩ := hs
    intro i
    obtain ⟨a, ha⟩ := hsub j ⟨𝟙 Z, by simp⟩ i
    refine ⟨a z, ?_⟩
    change (a ≫ ji i) z = s
    rw [ha]
    exact hz
  obtain ⟨U, hsU, W, k, hk, w, hw, hW, σ, hσ⟩ :=
    picard_h1_intersection_section f Xi fi ui hui hO hOi L Z j Zi ji hZ hZi s hs hsi hH
  let : IsImmersion k := hk
  obtain ⟨V, hwV, hV⟩ := proper_fibre_generator_pullback_locus f L k w σ hσ
  obtain ⟨O, hOopen, hOV⟩ := k.isEmbedding.isInducing.isOpen_iff.mp V.isOpen
  let O' : S.Opens := ⟨O, hOopen⟩
  have hsO : s ∈ O' := by
    rw [← hw]
    change w ∈ k ⁻¹' O
    rw [hOV]
    exact hwV
  refine ⟨U ⊓ O', ⟨hsU, hsO⟩, ?_⟩
  intro T g
  constructor
  · exact hsub (g ≫ (U ⊓ O').ι)
  · intro hgi
    have hgU : Set.range (g ≫ (U ⊓ O').ι) ⊆ U := by
      rintro _ ⟨t, rfl⟩
      exact (g t).property.1
    obtain ⟨h, hh⟩ := (hW (g ≫ (U ⊓ O').ι) hgU).mpr hgi
    have hhV : Set.range h ⊆ V := by
      rintro _ ⟨t, rfl⟩
      rw [← hOV]
      change k (h t) ∈ O'
      change (h ≫ k) t ∈ O'
      rw [hh]
      exact (g t).property.2
    have hL := hV h hhV
    rw [hh] at hL
    exact (hZ (g ≫ (U ⊓ O').ι)).mpr hL

end AlgebraicGeometry.Scheme
