# AlgebraicGeometry.ProEtale.CondensedRing local-freeness helper sharing

## Reason

The returned delivery duplicated four already-proved private free-module helpers
and five private local-freeness helpers. Reuse the first four via `import all`
of `Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality`. Move the other five,
with their exact predicate, from the unclaimed stratified-lattice module to the
new shared API `Sheaf.Paper.ContinuousLocallyFreePullback`; remove the originals
and the two consumers' copies. This avoids importing the stratification module
from its own dependency. A broader duplicate scan also found the coproduct module's copied
`openUnitIsIso`; that copy is removed and the existing private theorem from
`Sheaf.Paper.CondensedOpenClosedRecollement` is imported instead.
No public theorem statement changes, and no target uses
a changed notion: the predicate is the same abbreviation of the raw cover formula.

## Old

In `Sheaf.Paper.ContinuousLisseStratifiedLattices`:

```lean
private abbrev LocallyFree {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R]
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) : Prop :=
  ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ s : C.I₀,
    Mod.IsFree ((ProEtale.upperStar Ab.{u + 1} (C.f s)).obj R)
      (((ProEtale.upperStar Ab.{u + 1} (C.f s)).mapMod R).obj P)

private lemma locallyFree_of_iso {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R]
    {P Q : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (e : P ≅ Q) (hP : LocallyFree R P) : LocallyFree R Q := by
  obtain ⟨C, hC⟩ := hP
  exact ⟨C, fun s ↦ ProEtale.free_of_iso (hC s)
    (((ProEtale.upperStar Ab.{u + 1} (C.f s)).mapMod R).mapIso e)⟩

private lemma locallyFree_comap {X : Scheme.{u}}
    {R T : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R] [MonObj T]
    (φ : R ⟶ T) [IsMonHom φ] [IsIso φ]
    {P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) T}
    (hP : LocallyFree T P) : LocallyFree R ((Mod.comap φ).obj P) := by
  obtain ⟨C, hC⟩ := hP
  refine ⟨C, fun s ↦ ?_⟩
  let G := ProEtale.upperStar Ab.{u + 1} (C.f s)
  exact ProEtale.free_of_iso (ProEtale.free_comap (G.map φ) (hC s))
    ((G.mapModComapIso φ).app P).symm

private lemma free_map {X Y : Scheme.{u}} (g : Y ⟶ X)
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R]
    {P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (hP : Mod.IsFree R P) : Mod.IsFree ((ProEtale.upperStar Ab.{u + 1} g).obj R)
      (((ProEtale.upperStar Ab.{u + 1} g).mapMod R).obj P) := by
  let G := ProEtale.upperStar Ab.{u + 1} g
  obtain ⟨n, ⟨e⟩⟩ := hP
  exact ⟨n, ⟨(G.mapMod R).mapIso e ≪≫ (G.mapMod R).mapBiproduct _ ≪≫
    Limits.biproduct.mapIso (fun _ ↦ Mod.isoMk (Iso.refl _) (by simp [Mod.act]))⟩⟩

private lemma locallyFree_map {X Y : Scheme.{u}} (g : Y ⟶ X)
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

private lemma locallyFree_upperStar
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    {P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hP : LocallyFree (condensedRingObj Λ X) P) :
    LocallyFree (condensedRingObj Λ Y) ((CondensedRing.upperStar Λ g).obj P) := by
  let φ := condensedPullbackHom Λ g
  let Q := ((ProEtale.upperStar Ab.{u + 1} g).mapMod _).obj P
  exact locallyFree_of_iso ((Mod.extendScalarsIsoComapInv φ).app Q).symm
    (locallyFree_comap (inv φ) (locallyFree_map g hP))
```

## New

In `Sheaf.Paper.ContinuousLocallyFreePullback` (the old implementations are removed):

```lean
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
```

The original module replaces its proof-only `import all
Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality` by the ordinary proof
import `Sheaf.Paper.ContinuousLocallyFreePullback`. Its remaining declarations,
including its public stratification theorem, are byte-for-byte unchanged.

## Users

`tools/downstream.py Sheaf.Paper.ContinuousLisseStratifiedLattices --uses
LocallyFree locallyFree_of_iso locallyFree_comap free_map locallyFree_map
locallyFree_upperStar` lists eight downstream modules and no uses of these
private helpers outside their defining module. No consumer adaptation is needed.
The new API is imported only for proofs, so downstream public interfaces stay.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.ContinuousLisseStratifiedLattices | unclaimed | Removes moved private helpers; imports the shared API; public theorem unchanged. |
| Sheaf.Paper.ContinuousAffineEtaleLattice | B2 (new delivery module) | Removes duplicate helpers; imports shared API. |
| Sheaf.Paper.ContinuousLatticeFiniteCoproduct | B2 (new delivery module) | Removes duplicate helpers; imports shared API and existing raw free-module helpers. |
| Sheaf.Paper.ContinuousLocallyFreePullback | B2 (new delivery module) | Sole owner of the five moved proofs and the identical predicate. |
| Sheaf.Paper.ContinuousConstructibleIntegralModel | unclaimed | No adaptation; existing public theorem and coefficient definitions unchanged. |
| Sheaf.Paper.ContinuousConstructibleIntegralSingle | unclaimed | No adaptation; existing public theorem and coefficient definitions unchanged. |
| Sheaf.Paper.ContinuousConstructibleIntegralStratum | unclaimed | No adaptation; existing public theorem and coefficient definitions unchanged. |
| Sheaf.Paper.ContinuousExchangeIntegralModel | unclaimed | No adaptation; existing public theorem and coefficient definitions unchanged. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | No adaptation; existing public theorem and coefficient definitions unchanged. |
| TargetsCheck | unclaimed | No adaptation; existing public theorem and coefficient definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | No adaptation; existing public theorem and coefficient definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | No adaptation; existing public theorem and coefficient definitions unchanged. |

## Status

landed 20261016T093725-L-2050642 2026-10-16 (merge of deliver/B2/Sheaf.Paper.ContinuousEtaleLocalLattices)
