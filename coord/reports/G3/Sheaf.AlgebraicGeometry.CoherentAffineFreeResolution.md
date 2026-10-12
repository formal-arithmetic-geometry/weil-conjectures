## What changed

`Sheaf.AlgebraicGeometry.CoherentAffineFreeResolution` now constructs the affine
neighbourhood, its Noetherian coordinate ring, finite section module, and tilde
identification. It applies the existing module-resolution theorem and the new
`Sheaf.AlgebraicGeometry.FiniteFreeResolutionSheafification` theorem, then transports
the augmentation to `F.over U`. Existing declaration signatures and definitions are unchanged.
The new theorem takes prescribed exact algebraic resolution data; it has no coherence,
Noetherian, or neighbourhood-selection hypotheses. All imports added to the item are proof-only.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.coherent_affine_free_resolution` (1 of 1 original holes).
Hole added: `AlgebraicGeometry.finite_free_resolution_sheafification`, node
`lem-sc-finite-free-resolution-sheafification` (1 split off). The delivered modules
contain exactly this one direct sorry, the entire proof of its named public theorem.
This is a decomposition, not a net hole reduction: one upper hole is replaced by one
strictly lower sheafification hole. The existing theorem
`Module.exists_finite_free_resolution` remains an imported open dependency.
Both delivered declarations print only `propext`, `Classical.choice`, `Quot.sound`,
and `sorryAx`; neither is claimed to be independent of open statements.

## No longer needed

The item removes direct imports of
`Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine` and
`Sheaf.Algebra.Homology.ModuleStalkExact`. The former bundled criterion is replaced
by the proved source-level `Scheme.Modules.finite_sections_top_of_isIso_fromTildeΓ`
in `WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel`.

Compared with the old item's proof_deps:
- `def-weil-pbc-quasi-compact-scheme` is unused: local Noetherianness suffices.
- `lem-weil-pbc-quasi-coherent-finite-type-affine` is no longer used by this proof.
- `lem-weil-pbc-spec-tilde-stalk-localization` and
  `lem-weil-pbc-module-stalk-exact` move to the new sheafification node; they remain
  needed there, together with `lem-weil-pbc-localization-module-exact`.

No whole module is certified pruned from the targets' import closure: other users
and transitive imports may retain these modules. The maintainer's ledger decides that.

## Where the brief, the DAG or earlier work was wrong

The original plan left implicit the construction converting the exact sequence of
module maps into an augmented integer-indexed sheaf complex. This is the remaining
strict intermediate theorem. The first worker's new node omitted the localization
and stalk dependencies its own written argument uses. Its recorded searches were
not the actual sandbox search queries. Its report also failed to call the one-for-one
hole replacement a decomposition, and omitted the complete old-dependency comparison.
These record faults are repaired without rewriting the working Lean proof.

## New nodes

`lem-sc-finite-free-resolution-sheafification`, in
`lean/Sheaf/AlgebraicGeometry/FiniteFreeResolutionSheafification.lean`, records the
termwise tilde construction and equivalence transport. Its statement specifies the
actual ranks, augmentation, differentials and exactness hypotheses. Its node now
cites the existing localization, tilde-stalk and stalk-exactness results, has explicit
statement dependencies, and records the searches actually run. No change record
is needed: no existing signature or definition changed.

## Second reading by G3

1. Compared the delivered item against its repository version with `diff -u`.
   Its sole existing theorem's signature and docstring are byte-for-byte unchanged;
   only proof text and plain imports differ. The additional module is new and has
   one theorem, no data definitions. Verdict: pass; no accidental interface change.
2. Compiled both modules in import order using `lcompile.py --all`; no errors or
   warnings. Scanned for sorry and forbidden declarations. Compiled scratch copies
   with `#print axioms` for both declarations: exactly the three permitted axioms
   plus `sorryAx`. All witnesses from open existence statements are eliminated
   inside the theorem proof, never used to define an arbitrary data object.
   Verdict: pass as a partial proof with one named split-off hole.
3. Read the complete new statement and its docstring argument. Kernel-range equalities
   imply consecutive composites vanish; surjectivity identifies degree-zero homology
   with M. Functorial tilde stalk localization preserves this exactness, detected
   on stalks, and the two equivalences preserve zero objects, finite free terms and
   homology. Bound zero is valid; positive terms have rank zero. Checked zero module,
   zero ring, empty chart, and zero ranks: the hypotheses and construction still work.
   The statement is a strict part of the original argument, not its restatement.
   LeanFinder, Loogle and Mathlib grep with fresh queries found no complete match;
   LeanSearch was attempted separately and returned Internal Server Error;
   searched both project roots for alternative sheafified-resolution declarations.
   Existing affine RHom results require a larger argument and are still open.
   Verified the sources at https://stacks.math.columbia.edu/tag/01HV,
   https://stacks.math.columbia.edu/tag/01AG and
   https://stacks.math.columbia.edu/tag/00LP. Verdict: pass; closing the remaining
   categorical construction is substantial, not a few-minute repair.
4. The affine proof uses proved Mathlib/source declarations for local generators,
   affine shrinking, finite sections and the tilde counit, then the existing module
   resolution and the new sheafification lemma. Imports needed only for proofs stay
   plain. Public imports provide signature notation, types or `moduleRings`.
   The new theorem retains stalk exactness as a plain planned-proof import; added
   the plain localization-exactness import matching its repaired plan. The unit
   `dag/units/sk-thm-picard-duality.json` is unchanged (its existing realized arrays
   are empty); this item is below the unit, and the affine-resolution route is kept.
   Verdict: pass; full old-dependency comparison is now listed above.
5. Read both node records against the Lean. The item retains coherence, finite-free
   module resolution and tilde identification, and now depends on the sheafification
   node. Removed the unused bundled finite-type criterion from its proof_deps and
   named the actual source theorem in the proof step. Repaired the new node's
   proof_deps as the union of its cited steps and replaced its unsupported search
   records with logged searches, including the unavailable LeanSearch attempt. Verdict: pass after record repairs.

Second reading changed: dependency and search metadata, decomposition/pruning report,
and the new module's plain localization-exactness import. The original Lean proof and
all existing statements remain unchanged.
