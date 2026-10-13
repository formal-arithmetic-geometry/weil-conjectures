## What changed

Completed and checked the existing sandbox proof of
`Submodule.length_quotSMulTop_lt_top_of_ringKrullDim_eq_one` in
`Sheaf.RingTheory.FiniteLengthGlobalSubmodule`, keeping its signature and visibility unchanged.
The proof takes the finite set of maximal ideals containing x, shows the quotient vanishes
outside this set, and applies the existing local finite-length theorem inside it.
The localized fraction-field algebra is constructed with `IsLocalization.liftAlgHom`;
the localized submodule and quotient comparison are actual Mathlib constructions.
No arbitrary object is chosen from an unproved existence theorem.

Added the fully proved module `Sheaf.RingTheory.FiniteLengthOfFiniteMaximalSupport`, with
`Module.length_lt_top_of_finite_maximal_support`. Its localization order embedding transfers
both chain conditions from a finite product of local submodule lattices. This implements the
last local-to-global part of the argument without a new hole. Updated the item's node proof,
proof_deps and proof_origin and supplied the new helper's node.
The pointwise scalar actions on submodules are installed only inside the proof, avoiding
a file-wide scope command that would change the public interface.
All new imports are proof-only. The helper publicly imports only its statement's Mathlib
interfaces; no existing public imports or signatures change.

Both modules compile cleanly with lcompile.py --all. The helper includes arbitrary universes,
the zero module, the empty support set and a non-Noetherian base ring. For empty support the
localization test embeds the submodule lattice in a singleton, forcing the module to be zero.
For unit x the support is empty and every localization vanishes; no unit case is omitted.
For r = 0 or M = 0 the same proof applies. No definition or dependent module was adapted.

## Proved and sorry left

Closed the item's one hole:
`Submodule.length_quotSMulTop_lt_top_of_ringKrullDim_eq_one`
(node `lem-sc-finite-length-global-submodule`).

Also proved the new theorem `Module.length_lt_top_of_finite_maximal_support`
(node `lem-sc-finite-length-finite-maximal-support`). Zero holes added or split off;
no sorry remains in either delivered module. The item is proved from existing dependencies,
not asserted to be transitively sorry-free: the imported
`Submodule.length_quotSMulTop_le_of_ringKrullDim_eq_one_of_isLocalRing`
(node `lem-weil-pbc-dim-one-submodule-quotient-finite-length`) still contains its existing sorry.
`Ring.finite_maximalIdeals_containing_nonzero` is already proved in the current library.

## No longer needed

No original imports, dependency nodes or dependency modules are pruned. Both original Sheaf
proof dependencies are used. All added Mathlib imports are needed: Ideal.Height supplies the
localized dimension computation; LocalizationLocalization supplies the fraction-ring instance;
Localization.Submodule supplies IsLocalization.isNoetherianRing. Testing removal of the last
import gave an unknown-constant error for that declaration, so it was retained.
The helper uses LocalProperties.Submodule for inclusion detection and DFinsupp.WellFounded
for finite products of lattices with chain conditions.

The separate unit reduction and the numerical sum of local lengths in the old node plan are
unnecessary proof steps. They are replaced by the finite-support order-embedding argument;
no module attached to those steps becomes unused. The unit's realized statement and steps
are unchanged, and the existing local theorem remains used as the recorded tool of that route.

## Where the brief, the DAG or earlier work was wrong

The previous attempt left compiling proofs and node records, but no report or successful dry
run. Those files were inspected rather than replaced. The DAG's final numerical chain-bound
argument was a plan; the proof instead transfers Noetherian and Artinian conditions along an
order embedding. This remains below the unit level: sk-thm-curveestimate realizes only its
cohomology statement and has no realized steps at this algebra node.

The local algebra.tex cited in the nodes is absent on this machine. Read the primary source
[Stacks Tag 00PF](https://stacks.math.columbia.edu/tag/00PF) directly. It proves the same global
statement using a product decomposition. The general finite-support lattice proof is written
by K4, as the helper's proof_origin records, and is fully proved in Lean. The historical lemma
number in the item's source is outdated; the stable tag 00PF identifies the intended statement.
No source statement, target, or existing definition was changed.

## New nodes

`lem-sc-finite-length-finite-maximal-support`, in sec-curve-estimates and sk-thm-curveestimate,
states precisely the helper's criterion: finite maximal support and finite lengths of the
supported localizations imply global finite length. The helper and the item's final application
both compile; this node creates no further proof task. Its prior search log records LeanFinder,
Loogle, grep and an unavailable LeanSearch service; no unavailable search is counted as a
negative result. There are no change records.

## Second reading by K4

1. Compared the entire target module against the repository with `diff -u`. Its only
   changes are four plain proof imports and the replacement of its one `sorry`. The
   existing signature, universe parameters, visibility, public imports, and docstrings
   are byte-for-byte unchanged. The other module is new; no definition was changed.
   Verdict: pass; no change record or forced adaptation is needed.
2. Compiled both modules with `lcompile.py --all`, without errors or warnings. Checked
   both complete sources for forbidden declarations and holes: neither has any. Scratch
   copies with `#print axioms` show only `propext`, `Classical.choice`, and `Quot.sound`
   for `Module.length_lt_top_of_finite_maximal_support`; the target additionally has
   `sorryAx`, inherited from the explicitly reported existing local theorem. The maps,
   localized submodules, and quotient equivalence are actual constructions, with no
   witness chosen from an unproved existence theorem. Verdict: pass.
3. No statement was split off with `sorry`. Read the new helper's statement and proof:
   maximal localization detects inclusion, giving an order embedding into finitely
   many local submodule lattices, which transfers both chain conditions. Empty support
   makes that product a singleton; the zero module and zero ring are covered. In the
   target, unit x yields empty support, and r=0 or M=0 introduces no exception. A
   supported maximal ideal is nonzero because it contains the nonzero x, so its height
   is exactly one. Independently searched LeanFinder for Artinian/Noetherian detection
   at finitely many maximal localizations, Loogle for `IsFiniteLength`, grep for local
   Artinian/Noetherian criteria, and the upstream/project RingTheory sources for local
   length results. No theorem replacing this helper was found; the semilocal ring
   criterion concerns rings, not this arbitrary module. Verdict: pass.
4. The target first uses the existing finite-maximals theorem and the existing local
   length theorem, with Mathlib localization constructions and inclusion detection.
   Both original Sheaf dependencies and the original length definition node remain
   used; hence the list of pruned nodes is empty. Added imports serve the height,
   fraction-field, Noetherian-localization, inclusion-detection and finite-product
   arguments. Inspected `dag/units/sk-thm-curveestimate.json`: its realized statement
   is `thm-sc-proper-cohomology`, and its realized steps are empty. This algebra
   reduction changes no unit route. Read Stacks Tag 00PF directly: the target matches
   it, while the helper's lattice argument is correctly attributed to K4 rather than
   claimed as the source's product-decomposition proof. Verdict: pass.
5. Compared the old and delivered target node: only `proof`, `proof_deps`, and
   `proof_origin` change. Each new step matches the Lean proof, and the dependency list
   is the union of its step uses. The helper's node records its full statement,
   localization/length dependencies, complete lattice proof, source, searches,
   creation record, blueprint ancestry, chapter/unit, and exact Lean declaration.
   Verdict: pass.

Second reading changed only this report by adding the independent checks and verdicts.
No Lean or node repair was necessary. One original hole closed; zero holes added,
zero split off; no imports or modules pruned.
