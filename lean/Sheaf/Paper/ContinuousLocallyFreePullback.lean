/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.ContinuousIntegralCoefficients
import all Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality

/-! # Pullback and coefficient transport for locally free internal modules

The reusable local-freeness API formerly private to the stratified lattice proof.
Source: Bhatt--Scholze, Section 6.8; Stacks Project, Tag 03DO.
(blueprint: lem-weil-pbc-continuous-locally-free-pullback)
-/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- An internal module is locally finite free when a pro-etale scheme cover makes it finite free.
Source: Bhatt--Scholze, Section 6.8; Stacks Project, Modules on Sites, Tag 03DO.
(blueprint: lem-weil-pbc-continuous-locally-free-pullback)

This is exactly the scheme-cover predicate used by the lattice statements. -/
abbrev LocallyFree {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R]
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) : Prop :=
  ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ s : C.I₀,
    Mod.IsFree ((ProEtale.upperStar Ab.{u + 1} (C.f s)).obj R)
      (((ProEtale.upperStar Ab.{u + 1} (C.f s)).mapMod R).obj P)

/-- Local finite freeness is invariant under an isomorphism of internal modules.
Source: Bhatt--Scholze, Section 6.8; Stacks Project, Modules on Sites, Tag 03DO.
(blueprint: lem-weil-pbc-continuous-locally-free-pullback)

Use the same cover and apply the existing free_of_iso to its pulled-back
module isomorphisms. -/
lemma locallyFree_of_iso {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R]
    {P Q : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (e : P ≅ Q) (hP : LocallyFree R P) : LocallyFree R Q := by
  obtain ⟨C, hC⟩ := hP
  exact ⟨C, fun s ↦ ProEtale.free_of_iso (hC s)
    (((ProEtale.upperStar Ab.{u + 1} (C.f s)).mapMod R).mapIso e)⟩

/-- Restriction along an invertible coefficient map preserves local finite freeness.
Source: Bhatt--Scholze, Section 6.8; Stacks Project, Modules on Sites, Tag 03DO.
(blueprint: lem-weil-pbc-continuous-locally-free-pullback)

Use the same cover. On each member apply the existing free_comap and
free_of_iso to the mapModComapIso comparison. -/
lemma locallyFree_comap {X : Scheme.{u}}
    {R T : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R] [MonObj T]
    (φ : R ⟶ T) [IsMonHom φ] [IsIso φ]
    {P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) T}
    (hP : LocallyFree T P) : LocallyFree R ((Mod.comap φ).obj P) := by
  obtain ⟨C, hC⟩ := hP
  refine ⟨C, fun s ↦ ?_⟩
  let G := ProEtale.upperStar Ab.{u + 1} (C.f s)
  exact ProEtale.free_of_iso (ProEtale.free_comap (G.map φ) (hC s))
    ((G.mapModComapIso φ).app P).symm

/-- Inverse image preserves finite free internal modules.
Source: Bhatt--Scholze, Section 6.8; Stacks Project, Modules on Sites, Tag 03DO.
(blueprint: lem-weil-pbc-continuous-locally-free-pullback)

Map the chosen finite biproduct presentation. Additivity preserves this
biproduct, and strong monoidality identifies the image of the regular module. -/
lemma free_map {X Y : Scheme.{u}} (g : Y ⟶ X)
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R]
    {P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (hP : Mod.IsFree R P) : Mod.IsFree ((ProEtale.upperStar Ab.{u + 1} g).obj R)
      (((ProEtale.upperStar Ab.{u + 1} g).mapMod R).obj P) := by
  let G := ProEtale.upperStar Ab.{u + 1} g
  obtain ⟨n, ⟨e⟩⟩ := hP
  exact ⟨n, ⟨(G.mapMod R).mapIso e ≪≫ (G.mapMod R).mapBiproduct _ ≪≫
    Limits.biproduct.mapIso (fun _ ↦ Mod.isoMk (Iso.refl _) (by simp [Mod.act]))⟩⟩

/-- Inverse image preserves local finite freeness over its pulled-back coefficient ring.
Source: Bhatt--Scholze, Section 6.8; Stacks Project, Modules on Sites, Tag 03DO.
(blueprint: lem-weil-pbc-continuous-locally-free-pullback)

Base change the trivializing cover. Freeness is preserved by inverse image;
the pullback-square equation and mapMod composition isomorphism identify the
resulting modules with the restrictions of the pulled-back module. -/
lemma locallyFree_map {X Y : Scheme.{u}} (g : Y ⟶ X)
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R]
    {P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (hP : LocallyFree R P) : LocallyFree ((ProEtale.upperStar Ab.{u + 1} g).obj R)
      (((ProEtale.upperStar Ab.{u + 1} g).mapMod R).obj P) := by
  obtain ⟨C, hC⟩ := hP
  refine ⟨C.pullback₂ g, fun s ↦ ?_⟩
  have h := (ProEtale.free_pullback_comp_iff (Limits.pullback.fst (C.f s) g) (C.f s) P).mpr
    (free_map _ (hC s))
  rw [Limits.pullback.condition] at h
  exact (ProEtale.free_pullback_comp_iff (Limits.pullback.snd (C.f s) g) g P).mp h

/-- Canonical condensed-coefficient inverse image preserves local finite freeness.
Source: Bhatt--Scholze, Section 6.8; Stacks Project, Modules on Sites, Tag 03DO.
(blueprint: lem-weil-pbc-continuous-locally-free-pullback)

First pull back over the inverse-image coefficient ring. Restriction along
the inverse condensed coefficient comparison preserves freeness, and the
extension-of-scalars comparison gives the canonical pullback module. -/
lemma locallyFree_upperStar
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    {P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hP : LocallyFree (condensedRingObj Λ X) P) :
    LocallyFree (condensedRingObj Λ Y) ((CondensedRing.upperStar Λ g).obj P) := by
  let φ := condensedPullbackHom Λ g
  let Q := ((ProEtale.upperStar Ab.{u + 1} g).mapMod _).obj P
  exact locallyFree_of_iso ((Mod.extendScalarsIsoComapInv φ).app Q).symm
    (locallyFree_comap (inv φ) (locallyFree_map g hP))

end AlgebraicGeometry.ProEtale.CondensedRing
