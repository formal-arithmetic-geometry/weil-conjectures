## What changed

Replaced the single `sorry` in `AlgebraicGeometry.Etale.FiniteSmoothPurity.specialization_normalExchange` by an explicit proof. It constructs the Rees map of the Cartesian pair, builds an `ExceptionalFamilyBaseChange` with the actual one and zero fibres, applies normalized-family uniqueness and fibre coherence, and identifies the supplied normal lift with the canonical one at the level of section comparisons.

Restored the source hypothesis `hS : IsUnit (N : Γ(S, ⊤))` in this intermediate statement. The existing caller `Sheaf.Paper.FiniteSectionIntegratedSpecialization` is unclaimed in the current server claim records. Its only change supplies its already available `hS`; its public statement is unchanged. No target, definition, instance, attribute, adopted-source declaration or public import changes. The complete signature/consumer audit is in `coord/changes/J3-specialization-invertible-exponent.md`.

Added three modules. `SectionReesCartesianPair` proves the arbitrary-presentation Rees pullback square by transporting the existing canonical local extended-Rees pushouts along `cart.isoPullback`. `SmoothSectionExchangeIndependence` proves comparison independence by expressing the quotient of two Cartesian lifts as an automorphism, applying comparison composition, and cancelling the identity compositor. `SmoothSectionAutomorphism` states the remaining local fundamental-class calculation.

All five modules compile cleanly through the remote compiler, in import order: Rees geometry 7.2 s, automorphism statement 7.3 s, comparison independence 7.8 s, assigned item 8.7 s, adapted parent 36.3 s. There are no debug options or unfinished tactic blocks.

## Proved and sorry left

The repaired `AlgebraicGeometry.Etale.FiniteSmoothPurity.specialization_normalExchange` has no `sorry` in its proof. This does not claim a proof of its old signature without invertibility of N.

The following new declarations have complete proofs:

- `AlgebraicGeometry.SectionReesBaseChange.pairMap_isPullback` (`lem-sp-section-rees-cartesian-pair`).
- `AlgebraicGeometry.Etale.NoetherianSectionSpecialization.sectionMap_eq_of_cartesian` (`lem-sp-smooth-section-exchange-independence`), conditional on the next lemma.

Exactly one new `sorry` remains: `AlgebraicGeometry.Etale.NoetherianSectionSpecialization.sectionMap_automorphism`, node `lem-sp-smooth-section-automorphism`, in `Sheaf.Paper.SmoothSectionAutomorphism`. It says that an ambient automorphism over the identity, fixing a smooth section, acts trivially on its dualizing line. It contains no deformation space, normalization, specialization, arbitrary base change, or normal-cone choice. Its docstring gives the local trace-normalized fundamental-class argument. It is a strict part of the argument, not the original specialization equation renamed. The Rees construction, pullback transport, normalized-family comparison, automorphism factorization, and identity-coherence cancellation are all proved here.

Counts: the original item had one hole and now has zero; one strictly smaller hole is added. This is a decomposition (net zero holes), together with a recorded source-hypothesis repair, not a claimed net proof or proof of the old all-characteristics statement. No other existing holes or theorem bodies are replaced by `sorry`. All imported finite-ring deformation and exceptional-family coherence results used in the Lean proof already have complete proofs.

## No longer needed

Removed the item's direct proof import `WeilConjectures.EtaleCohomology.Purity.Smooth.SmoothBaseChange`. Retained its two original public imports because they provide the public statement's data.

The item's old proof dependency `lem-sp-finite-section-integrated-specialization-normal-exchange` supplies existence of a normal lift only; it supplies neither the Rees-family comparison nor the desired specialization equality. The new proof constructs its canonical normal lift from the Rees pair map and therefore does not use that dependency. Its parent still uses `normalExchange_exists`, so this is a dependency removal for this item only. No module is globally pruned or withdrawn; no upstream declaration is removed.

The canonical-pullback-only `FiniteRingSectionDeformation.baseChange_compatibility` is not imported separately or used as a substitute for the arbitrary-presentation square. The new geometry proof uses the existing local Rees pushouts directly; the specialization proof uses the existing normalized-family theorem. No smooth-orientation base-change theorem, diagonal restriction or integrated-specialization result is used to prove its own factor.

## Where the brief, the DAG or earlier work was wrong

The original strict-factor signature omitted the invertibility hypothesis present in the finite-coefficient DNC source, in `lem-trf-finite-ring-section-deformation`, in normalized-family uniqueness, and in the sole parent theorem. This delivery records the correction with all citers and adapts that parent's proof call. It does not assert that the omitted-hypothesis statement is false: no counterexample to that stronger statement is claimed. The statement being delivered is the source formulation actually needed by the parent, and the change is explicit for independent review.

The old node's one proof step cited only existence of a normal exchange. Existence alone cannot establish its equation. The updated steps distinguish the Cartesian Rees construction, uniqueness of the normalized trivializations, fibre coherence, and comparison independence. The original docstring also pointed at the parent node rather than this factor; its blueprint reference is corrected.

Tools from another unit used here are `lem-trf-section-rees-base-change-etale`, `lem-trf-finite-ring-section-deformation`, and `lem-trf-section-exceptional-fibre-coherence`: these give the actual canonical Rees chart pushouts, normalized-family uniqueness, and counit-defined comparison composition. They implement precisely the DNC part of proof (1) in the current unit; no node of this unit gives those constructions. No maintainer `tool_uses` approval is added or altered. The unit's orientation/integration route is retained.

The new statements were checked mathematically in relative dimension zero, on an empty base, and with the zero coefficient ring. The Rees transport uses no flatness of b. For Cartesian-lift independence the quotient is an actual isomorphism over the base fixing the section; it is not an arbitrary endomorphism. Invertibility pulls back to the new base. For the remaining automorphism lemma the local fundamental class has degree one, so no Jacobian determinant scalar appears in etale Tate orientation.

The search commands (LeanSearch, LeanFinder, Loogle and grep) found only basic scheme-isomorphism and pullback facts, not the dualizing-line automorphism statement. The current blueprint search for automorphism/section and Rees/Cartesian-pair phrases found no matching imported statement. Existing local Rees pushouts and normalized comparison coherence were used instead of restated.

## New nodes

`lem-sp-section-rees-cartesian-pair`: the arbitrary-presentation Cartesian Rees square, with a complete Lean proof in `Sheaf.Paper.SectionReesCartesianPair`.

`lem-sp-smooth-section-exchange-independence`: the equality of section comparisons for two Cartesian ambient lifts over the same base map, proved in `Sheaf.Paper.SmoothSectionExchangeIndependence` using the quotient automorphism and actual counit-composition coherence.

`lem-sp-smooth-section-automorphism`: the one remaining local trace-normalization calculation, with its full source-based proof in words and a single public named `sorry` in `Sheaf.Paper.SmoothSectionAutomorphism`.

Change record: `coord/changes/J3-specialization-invertible-exponent.md`.

## Forced adaptations

The original `Sheaf.Paper.FiniteSectionIntegratedSpecialization`, compiled against the changed item and its dependencies, fails at line 187: `Application type mismatch: The argument d has type ℕ but is expected to have type IsUnit ↑N in the application specialization_normalExchange A N hN hA d`. The sole changed line adds the caller's existing `hS` before `d`; the adapted module compiles in 36.3 s. The caller is unclaimed. No declaration signature or visibility in that module changes.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.FiniteSectionIntegratedSpecialization": "798d00db4f4eb72447ffc1c83147a59af95f2d0e", "Sheaf.Paper.FiniteSectionIntegratedSpecializationSpecializationBaseChange": "880c6632b5c62a9dc4d831848cf7e4de1c0f4c07", "Sheaf.Paper.SectionReesCartesianPair": "5e4346698436fde0ed3ffe559a38dc7fcd45439e", "Sheaf.Paper.SmoothSectionAutomorphism": "b011b0a25358cb372586ab085400bc4d833a317d", "Sheaf.Paper.SmoothSectionExchangeIndependence": "3c6e2f527d7320d09421ecd6e68663b7fd6c0df0"}, "results": {}, "time": "2026-10-28T03:40:46+0800", "transitive": 0, "version": 1}
```

## Second reading by J3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
