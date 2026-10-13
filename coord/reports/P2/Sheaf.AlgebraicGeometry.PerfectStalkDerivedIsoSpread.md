## What changed

The target theorem `AlgebraicGeometry.Scheme.exists_affine_restriction_iso_of_perfect_stalk_iso` now has a complete reduction proof, conditional on two split theorems. Its proof chooses a common affine neighbourhood, restricts the existing strictly perfect models, lifts the stalk morphism to a chain map, detects that chain map as a quasi-isomorphism on a smaller affine open, and composes the restricted derived comparison isomorphisms. The two new proof-only imports isolate the two genuinely missing arguments; all existing public signatures are unchanged.

The delivery also adds `PerfectStalkDerivedHomLift.lean` and `PerfectStalkQuasiIsoDetection.lean`, each with one named intermediate theorem whose proof is intentionally left for a subsequent worker. The existing target node records the revised proof route and its two new dependencies.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.exists_affine_restriction_iso_of_perfect_stalk_iso` (the one `sorry` in the held target module). The private restriction helpers in that module are proved directly from restriction functor preservation of zero objects and finite-free retracts.

Split off: `AlgebraicGeometry.Scheme.exists_affine_perfect_stalk_hom_lift` in node `lem-sc-perfect-stalk-derived-hom-lift`, and `AlgebraicGeometry.Scheme.exists_affine_restriction_quasiIso_of_perfect_stalk_quasiIso` in node `lem-sc-perfect-stalk-quasi-iso-detection`. These are strictly smaller: the first lifts an arbitrary stalk morphism, while the second handles a fixed chain map and only detects its quasi-isomorphism.

## No longer needed

Removed direct target imports: `Sheaf.AlgebraicGeometry.AffinePerfectHomColimit`, `Sheaf.RingTheory.LocalizationColimitPrincipalLocalizations`, `Sheaf.Algebra.Homology.ModuleStalkExact`, and `Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence`. The corresponding old dependencies `lem-pc-affine-perfect-hom-colimit`, `lem-weil-pbc-localization-colimit-principal-localizations`, `lem-weil-pbc-module-stalk-exact`, and `lem-pc-affine-qcoh-derived-equivalence` remain in the split lemmas’ route. `def-pc-perfect-complex` remains a direct dependency.

No DAG node is pruned: the target's original affine localization and Hom-colimit nodes remain dependencies of the two split lemmas. The target file no longer imports those implementation modules directly; they are imported by the split modules, so the public dependency route remains available. No statement, definition, or existing interface was changed.

## Where the brief, the DAG or earlier work was wrong

The original three-step route bundled affine model construction, descent of a morphism and inverse identities, and quasi-isomorphism detection into one target-sized argument. The usable Lean route separates the latter two into the two strictly smaller statements above. The existing `OpenModuleStalkFunctor` module already provides the needed stalk functor and zero-morphism instance; a duplicate local definition was removed before delivery. The cone argument in the detection statement uses injectivity of perfect Hom comparison, so it does not assume coherence or Noetherian support hypotheses.

## New nodes

`lem-sc-perfect-stalk-derived-hom-lift` records the local derived Hom lifting statement and its Stacks Project source. `lem-sc-perfect-stalk-quasi-iso-detection` records the cone-based local quasi-isomorphism detection statement. Both node files are under `dag/nodes/sec-abelian-varieties/` in this sandbox.

## Second reading by P2

1. Compared the delivered target module against the repository version. The theorem signatures and all existing declarations are byte-for-byte unchanged; only proof code and proof-only imports differ. Verdict: pass.
2. Compiled the target and both split modules with `lcompile.py`; all compile cleanly. The target proof has no `sorry`; the only remaining `sorry`s are the two named split theorems, each public and documented with source and proof plans. No prohibited axioms or unsafe declarations were added. Verdict: pass.
3. Checked the two split statements and their DAG nodes. They are strictly smaller reductions (derived Hom lifting and quasi-isomorphism detection), carry source/docstring proofs, and are not duplicates found in the existing library. Verdict: pass.
4. The proof follows the unit route through affine restriction, local model comparisons, Hom lifting, and quasi-isomorphism detection. The target's original implementation imports are moved into the split modules; no unused target imports remain. Verdict: pass.
5. Compared the target node's proof and proof dependencies with the Lean proof: both split nodes are used exactly where recorded, and the unit `sk-prop-av-cube` route is preserved. Verdict: pass.

Changed during second reading: corrected the target node’s step 2 to match the proof (no inverse is lifted); added the missing proof-dependency imports for the affine chain-map representative and exact stalks; removed the unused chain-map representative dependency from the detection node. No existing signature or definition changed. Explicit axiom probes show only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` for all three declarations. This is a decomposition (one hole closed, two holes added), not an unconditional proof. Independent LeanFinder search for a bounded-projective quasi-isomorphism spreading theorem returned general quasi-isomorphism lemmas only; source search found no replacement. The unit’s `realized` fields are empty in the baseline and are unchanged.

Second-reader edge cases: zero complexes and zero maps cause no failure; with x ∈ U the affine neighbourhood is nonempty, and for a field the principal localization argument already works on the original chart. Over an arbitrary non-Noetherian ring, the bounded finite-projective cone argument uses Hom-colimit injectivity rather than finite generation of cohomology. The two holes are not restatements of the target: Hom lifting makes no invertibility conclusion, and detection has a fixed chain map and no derived comparison to global complexes. The local Stacks sources are absent on this machine; checked the official [09RE](https://stacks.math.columbia.edu/tag/09RE) and [0BC7 (2)](https://stacks.math.columbia.edu/tag/0BC7) statements and affine proofs online. No new definition chooses data from an unproved existence theorem. Net holes for this decomposition are −1 (one closed minus two added), before any downstream pruning ledger calculation.
