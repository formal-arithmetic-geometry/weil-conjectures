/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import Sheaf.AlgebraicGeometry.FlatTelescopeStageMap
import Sheaf.AlgebraicGeometry.CompactFlatGeneratorCover
import Sheaf.Algebra.Homology.RelativeBiprodConeExtension
import Sheaf.Algebra.Homology.CyclePullbackResolution
import Mathlib.Algebra.Homology.Refinements

/-! # One relative compact flat generator resolution step

Source: Stacks Project Tags 03EW, 077J and the cone induction in Tag 06XX.
(blueprint: lem-sc-compact-flat-generator-relative-extension).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

private abbrev GeneratorSum (Y : Scheme.{u})
    (M : SheafOfModules.{u} (moduleRings Y.toRingedSpace)) : Prop :=
  ∃ (I : Type u)
        (G : I → SheafOfModules.{u} (moduleRings Y.toRingedSpace)),
        Nonempty (M ≅ ∐ G) ∧
        (∀ j : I, SheafOfModules.IsFlat (G j)) ∧
        ∀ (j : I) (K : Type u)
          (H : K → SheafOfModules.{u} (moduleRings Y.toRingedSpace))
          (f : G j ⟶ ∐ H),
          ∃ (S : Finset K) (g : G j ⟶ ∐ (fun k : {k // k ∈ S} ↦ H k.1)),
            g ≫ Sigma.desc (fun k : {k // k ∈ S} ↦ Sigma.ι H k.1) = f

private theorem generatorSum_biprod (Y : Scheme.{u})
    (M N : SheafOfModules.{u} (moduleRings Y.toRingedSpace))
    (hM : GeneratorSum Y M) (hN : GeneratorSum Y N) :
    GeneratorSum Y (M ⊞ N) := by
  classical
  obtain ⟨I, G, ⟨eM⟩, hG, hcG⟩ := hM
  obtain ⟨J, H, ⟨eN⟩, hH, hcH⟩ := hN
  let K : I ⊕ J → SheafOfModules.{u} (moduleRings Y.toRingedSpace) := Sum.elim G H
  let e : (∐ G) ⊞ (∐ H) ≅ ∐ K :=
    { hom := biprod.desc (Sigma.desc (fun i ↦ Sigma.ι K (.inl i)))
        (Sigma.desc (fun j ↦ Sigma.ι K (.inr j)))
      inv := Sigma.desc (fun k ↦ match k with
        | .inl i => Sigma.ι G i ≫ biprod.inl
        | .inr j => Sigma.ι H j ≫ biprod.inr)
      hom_inv_id := by
        apply biprod.hom_ext'
        all_goals apply Sigma.hom_ext; intro i; simp [K]
      inv_hom_id := by
        apply Sigma.hom_ext
        intro i
        cases i <;> simp [K, Category.assoc] }
  refine ⟨I ⊕ J, K, ⟨biprod.mapIso eM eN ≪≫ e⟩, ?_, ?_⟩
  · intro i
    cases i with
    | inl i => exact hG i
    | inr j => exact hH j
  · intro i
    cases i with
    | inl i => exact hcG i
    | inr j => exact hcH j

/-- Extend a bounded-above generator complex along an arbitrary map into a
bounded-above complex, keeping its inclusion split in each degree.

Source: Stacks Project Tag 06XX, the induction step before the final
termwise-surjectivity addition; Tags 03EW and 077J supply generator resolutions.
This is the finite extension in the first paragraph of the original proof of
`lem-sc-flat-telescope-target-refinement`.

Proof. Use the affine-open sheaves j_! O_U. Their stalks are either zero or the
local ring, so they are flat. Adjunction identifies maps from them with sections
on U. A section of a sheaf coproduct locally comes from a finite subsum; an affine
open is quasi-compact, so finitely many such neighborhoods suffice. The union of
their finite supports gives the required factorization, with uniqueness and
gluing supplied by the monic inclusion of a subsum. Every module sheaf is covered
by a sum of these sheaves: for every local section choose an affine neighborhood
and its corresponding adjunction map. Resolve the bounded-above mapping cone of
a by these generators, downward from its upper bound, choosing generator covers
of the successive pullbacks of cycles as in the bounded resolution construction
underlying 077J. This gives a bounded-above complex Q and a quasi-isomorphism
Q -> Cone(a). Compose with Cone(a) -> L[1]. Its shifted cone gives L', with the
termwise split inclusion L -> L' and terms the direct sums of terms of L and Q.
The triangle comparison gives L' -> E. Its composite with L -> L' equals a up to
homotopy. Extend the comparison homotopy degreewise along the split inclusion,
and subtract its boundary; this makes the equality strict without changing the
homotopy class. The map is a quasi-isomorphism by comparison of the two triangles,
since the other vertical maps are the identity of L and Q -> Cone(a).
Finite direct sums of generator coproducts are reindexed by disjoint union, so
all terms of L' have the required generator description. The maximum of the
bounds, with the shift accounted for, bounds L'. There is no assumption on a:
a zero map, a zero target, and an acyclic target are covered by the same argument.
Empty coproducts represent zero terms. No projective lifting is used.
(blueprint: lem-sc-compact-flat-generator-relative-extension). -/
theorem exists_compact_flat_generator_relative_extension (Y : Scheme.{u})
    (L E : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (a : L ⟶ E)
    (hL : ∃ z : ℤ, ∀ i : ℤ, z < i → IsZero (L.X i))
    (hE : ∃ z : ℤ, ∀ i : ℤ, z < i → IsZero (E.X i))
    (hgen : ∀ i : ℤ, ∃ (I : Type u)
        (G : I → SheafOfModules.{u} (moduleRings Y.toRingedSpace)),
        Nonempty (L.X i ≅ ∐ G) ∧
        (∀ j : I, SheafOfModules.IsFlat (G j)) ∧
        ∀ (j : I) (K : Type u)
          (H : K → SheafOfModules.{u} (moduleRings Y.toRingedSpace))
          (f : G j ⟶ ∐ H),
          ∃ (S : Finset K) (g : G j ⟶ ∐ (fun k : {k // k ∈ S} ↦ H k.1)),
            g ≫ Sigma.desc (fun k : {k // k ∈ S} ↦ Sigma.ι H k.1) = f) :
    ∃ (L' : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
      (l : L ⟶ L') (v : L' ⟶ E),
      (∃ z : ℤ, ∀ i : ℤ, z < i → IsZero (L'.X i)) ∧
      QuasiIso v ∧ (l ≫ v = a) ∧ (∀ i : ℤ, IsSplitMono (l.f i)) ∧
    ∀ i : ℤ, ∃ (I : Type u)
        (G : I → SheafOfModules.{u} (moduleRings Y.toRingedSpace)),
        Nonempty (L'.X i ≅ ∐ G) ∧
        (∀ j : I, SheafOfModules.IsFlat (G j)) ∧
        ∀ (j : I) (K : Type u)
          (H : K → SheafOfModules.{u} (moduleRings Y.toRingedSpace))
          (f : G j ⟶ ∐ H),
          ∃ (S : Finset K) (g : G j ⟶ ∐ (fun k : {k // k ∈ S} ↦ H k.1)),
            g ≫ Sigma.desc (fun k : {k // k ∈ S} ↦ Sigma.ι H k.1) = f := by
  classical
  let A := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  let S : ObjectProperty A := GeneratorSum Y
  have hzero (M : A) (hM : IsZero M) : S M := by
    let G : PEmpty.{u + 1} → A := PEmpty.elim
    have hG : IsZero (∐ G) := by
      rw [IsZero.iff_id_eq_zero]
      apply Sigma.hom_ext
      intro j
      exact PEmpty.elim j
    exact ⟨PEmpty.{u + 1}, G, ⟨hM.iso hG⟩, fun j ↦ PEmpty.elim j,
      fun j ↦ PEmpty.elim j⟩
  obtain ⟨T, π, hT⟩ := exists_functorial_compact_flat_generator_cover Y
  obtain ⟨bL, hbL⟩ := hL
  obtain ⟨bE, hbE⟩ := hE
  let N := max bL bE
  have hc : ∀ i : ℤ, N < i → IsZero ((CochainComplex.mappingCone a).X i) := by
    intro i hi
    apply (CochainComplex.mappingCone.isZero_X_iff a i).2
    exact ⟨hbL (i + 1) (by dsimp [N] at hi; omega),
      hbE i (by dsimp [N] at hi; omega)⟩
  let P : ObjectProperty (CochainComplex A ℤ) :=
    fun F ↦ ∀ i : ℤ, N < i → IsZero (F.X i)
  let F : P.FullSubcategory := ⟨CochainComplex.mappingCone a, hc⟩
  obtain ⟨Q, ε, hQ⟩ := CochainComplex.exists_functorial_cyclePullback_construction
    S hzero T π (fun M ↦ (hT M).2) (fun M ↦ (hT M).1) N
  have hr : QuasiIso (ε.app F) := by
    rw [quasiIso_iff]
    intro i
    rw [quasiIsoAt_iff_isIso_homologyMap, isIso_iff_mono_and_epi]
    constructor
    · rw [HomologicalComplex.mono_homologyMap_iff_up_to_refinements
        (ε.app F) (i - 1) i (i + 1) (by simp) (by simp)]
      intro B x hx y hy
      have hlift := (hQ F).2.2 (i - 1)
      rw [show i - 1 + 1 = i by omega] at hlift
      obtain ⟨B', p, hp, z, _, hz⟩ := hlift B x y hx hy
      exact ⟨B', p, hp, z, by simpa using hz.symm⟩
    · rw [HomologicalComplex.epi_homologyMap_iff_up_to_refinements
        (ε.app F) (i - 1) i (i + 1) (by simp) (by simp)]
      intro B y hy
      obtain ⟨B', p, hp, z, hz, hd⟩ :=
        (hQ F).2.2 i B 0 y (by simp) (by simpa using hy.symm)
      exact ⟨B', p, hp, z, by simpa using hd, 0, by simpa using hz.symm⟩
  obtain ⟨L', l, v, hb, hv, hlv, hs, ht⟩ :=
    CochainComplex.exists_relative_biprod_cone_extension L E a ⟨bL, hbL⟩
      (Q.obj F) (ε.app F) ⟨N, (hQ F).2.1⟩ hr
  refine ⟨L', l, v, hb, hv, hlv, hs, ?_⟩
  intro i
  obtain ⟨e⟩ := ht i
  obtain ⟨I, G, ⟨eG⟩, hg, hcompact⟩ :=
    generatorSum_biprod Y (L.X i) ((Q.obj F).X i) (hgen i) ((hQ F).1 i)
  exact ⟨I, G, ⟨e ≪≫ eG⟩, hg, hcompact⟩

end AlgebraicGeometry
