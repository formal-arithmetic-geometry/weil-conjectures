## What changed

Replaced the sole sorry in Sheaf.RingTheory.RegularLocalMaximal by a complete Lean reduction,
without changing its signature or public imports. Added proof-only imports of RegularComposition,
RegularThroughLocalization, LocalizationRegular, FibreRingNoetherian, and the new
GeometricallyRegularFibersOfMaximal module. Updated the item's DAG proof to match the Lean.

The forward direction uses regular composition with the target localization and regularity
through source localization. For the maximal-local converse, flatness is proved directly using
Module.flat_of_isLocalized_maximal, the flatness of source localization, and transitivity.
Regular composition with the source localization gives geometrically regular fibres for
R -> S_m. A new theorem descends a single fixed fibre from these target localizations.
Prime-local hypotheses specialize to maximal-local hypotheses, completing both equivalences.

## Proved and sorry left

Closed: RingHom.isRegular_iff_localRingHom_prime_and_maximal
(lem-weil-pbc-regular-local-maximal). No sorry remains in the assigned module.

Added and left: Algebra.isGeometricallyRegular_fiber_of_localizations_maximal
(lem-weil-pbc-geometrically-regular-fiber-of-maximal), in
Sheaf.RingTheory.GeometricallyRegularFibersOfMaximal. Its proof is exactly `by sorry`.
The statement concerns one fibre and has no flatness or regular-ring-map hypothesis/conclusion.
Its docstring supplies the source and full localization argument; zero targets, empty fibres,
and a maximal ideal whose contraction does not contain p are harmless (zero localized fibres
are allowed).

This is a decomposition: one hole closed, one hole added, net zero for these declarations.
The proof also uses the pre-existing, still holed
RingHom.IsRegular.comp_of_fiber_noetherian and
RingHom.isRegular_of_comp_algebraMap_localization; their modules are imported, not proved here.
IsLocalization.isRegular_and_fiber and Ideal.isNoetherianRing_fiber are already proved.
Local compilation succeeds without warnings. deliver3.py --no-push printed OK: the delivery
compiles locally and on the server and passes preflight except for the second reading,
which the second reader supplies. Nothing was pushed.

## No longer needed

No existing import was removed: the original sole import, Sheaf.RingTheory.GRing, supplies the
statement and stays public. The regular-ring local criterion node
lem-weil-pbc-regular-ring-local-criterion is no longer a direct dependency of the assigned
node; it remains necessary in the new fixed-fibre descent node. The flat local criterion,
localization definitions, and regularity definitions remain used. No original dependency is
claimed globally unreachable. No new forward-localization helper is delivered: the existing
regular-composition, regular-localization, and regular-through-localization nodes suffice.
No complete module is pruned.

## Where the brief, the DAG or earlier work was wrong

The original DAG step 3 described prime-local to maximal-local as another localization;
that implication is simply specialization, since maximal ideals are prime. Its reverse
localization explanation did not specify the single-fibre geometric descent argument, which
is now stated explicitly. The target statement itself is unchanged and no dispute is raised.

Mathlib's RingHom.Flat.ofLocalizationPrime is formulated with the same universe for the two
rings and handles prime localizations. The direct Module.flat_of_isLocalized_maximal argument
handles the target's independent universes and maximal-only hypothesis without a new hole.
Fibre Noetherianity is a proved project theorem, not an available automatic instance; the
composition arguments explicitly supply Ideal.isNoetherianRing_fiber.

## New nodes

lem-weil-pbc-geometrically-regular-fiber-of-maximal: fixed-source-prime geometric fibre descent
from all maximal localizations of a Noetherian target. This is the remaining fibre part of
Stacks 07C0, independent of flatness. The new node and its module supply the complete intended
proof and all three search records. No definition or existing statement was changed, and no
change record is required. The unit route is preserved.


## Second reading by C3

1. Compared the delivered existing module with the repository using diff. The only Lean
   changes are five plain proof-only imports and the body of
   RingHom.isRegular_iff_localRingHom_prime_and_maximal. Its existing signature and
   docstrings are byte-for-byte unchanged, and its public import stays unchanged.
   The other module is new; there are no changed definitions, adapted modules, or
   statement changes requiring a change record. Verdict: pass.
2. Compiled both modules in import order with lcompile.py: no errors or warnings.
   Scanned the delivered sources: the sole sorry is the whole proof of the named new
   fibre-descent theorem; there are no forbidden declarations or hollow definitions.
   Scratch copies with #print axioms for both delivered theorems compiled and reported
   only propext, Classical.choice, Quot.sound, and sorryAx. The upper theorem still
   depends on the new hole and the two reported pre-existing holes, so it is a valid
   reduction, not an axiom-free proof of the item. Verdict: pass as a decomposition.
3. Read the new theorem, its complete docstring argument, and its node. Checked the
   live Stacks 07C0 source and the definition of IsGeometricallyRegular. For each finite
   purely inseparable extension the extended fibre is finite over a Noetherian fibre.
   Every prime contracts to a prime of S contained in some maximal m, and avoids all
   denominators outside m. The hypothesized regular extended local fibre therefore
   controls that prime localization. This gives precisely the regularity needed.
   For zero S there are no such primes and the fibres are zero; when the fibre is empty
   the same reasoning is vacuous. Contractions of m need not contain the fixed p: the
   corresponding zero local fibres cause no problem. The hypothesis has neither
   flatness nor regularity of ring maps, and the conclusion concerns one fixed fibre,
   so this is strictly smaller than the original two-equivalence theorem, not a
   renamed restatement. Independent LeanFinder (localizations covering a spectrum),
   Loogle (IsRegularRing), and grep (geometric regularity and maximal locality)
   searches, plus rg over Sheaf and WeilConjectures, found only ring-level criteria,
   regular-sequence results, and other geometric regularity theorems; no duplicate
   or immediate proof of this fibre descent was found. Verdict: pass; retained hole.
4. Read all five imported proof modules and checked their uses in the Lean argument.
   The composition and source-localization reductions are correctly specialized;
   maximal flat descent is proved directly with Mathlib rather than split off.
   All plain imports serve the proof, and GRing serves the signature. The only old
   proof dependency removed is lem-weil-pbc-regular-ring-local-criterion; the report
   names it and explains its retained role in the new node. The localization definition
   is still used and has been restored as a direct dependency. Read sk-thm-p1.json's
   realized statement and steps: none is bypassed or changed by this reduction below
   unit level. No entire module is pruned. Verdict: pass after the metadata repair.
5. Compared the existing node changes and read the new node in full: existing fields
   change only in proof, proof_deps, and proof_origin. The new node's signature agrees
   with Lean; source, proof steps, dependency union, origin, searches, creation,
   blueprint ancestry, chapter, unit, and Lean record are present. Both proof routes
   describe the delivered reduction and remaining localization argument. Verdict:
   pass after restoring def-weil-pbc-localization-at-prime to step 1 and proof_deps.

Second-reading changes: restored that localization-definition dependency in the existing
node, and added this review. No Lean proof or statement needed repair. Holes closed and
added remain one and one respectively; net zero, counted as a decomposition.
