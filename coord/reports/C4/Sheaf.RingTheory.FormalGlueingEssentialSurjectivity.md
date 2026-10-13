## What changed

Replaced the sole hole in `Sheaf.RingTheory.FormalGlueingEssentialSurjectivity`
with a compiling reduction. Its existing signature, universes, visibility, and
public imports are unchanged. The proof constructs the prime cokernel, proves
its multiplication comparison with scalar extension is an S-linear equivalence,
applies `LinearMap.exists_torsion_extension_flat_descent`, proves the descended
injection is bijective on every localization, and constructs the inverse glueing
morphism componentwise. All private helpers are proved.

Added two modules, each with one strictly intermediate theorem:
`Sheaf.RingTheory.FormalGlueingInjectiveApproximation` handles construction of
an injective approximation with torsion cokernel (original steps 7–9), and
`Sheaf.RingTheory.FormalGlueingExtensionTransport` handles compatibility of maps
transported across localized injections (the compatibility portion of step 11).
Neither asserts essential surjectivity. The second has no flatness or quotient
hypothesis and does not assume anything about Can on morphisms. Actual extension
descent, localization bijectivity, and componentwise inversion are in the assigned
module, not in either new hole. Updated the assigned node's proof route accordingly.

The source read was [Stacks Tag 05ER](https://stacks.math.columbia.edu/tag/05ER),
`proposition-equivalence`, especially its short exact sequence and reconstruction
of Can(E). The source TeX is not installed in this clone. The unit `sk-thm-p1`
and its realized route are preserved; this reduction is below the unit level.

Validated all three modules with `lcompile.py --all`, with no errors or warnings.
The new statements were checked on an empty chart family, zero generators,
zero modules, and the unit ideal: empty chart conditions are vacuous, torsion
fractions vanish without cancellation in R, and the unit-ideal torsion cokernel
is zero. The transported prime equivalence covers the empty chart family.

## Proved and sorry left

Closed `FormalGlueing.canonical_essentially_surjective`, the assigned module's
only direct hole, by a complete proof from named dependencies. No direct hole
remains in the assigned module.

Added two direct holes:

- `FormalGlueing.exists_injective_approximation`, node
  `lem-weil-pbc-formal-glueing-injective-approximation`, in
  `Sheaf.RingTheory.FormalGlueingInjectiveApproximation`.
- `FormalGlueing.exists_extension_transport`, node
  `lem-weil-pbc-formal-glueing-extension-transport`, in
  `Sheaf.RingTheory.FormalGlueingExtensionTransport`.

This is a decomposition, not a sorry-free proof or a net hole reduction: one
upper hole closed, two lower holes added, direct net minus one. The approximation
asserts injectivity and torsion cokernel, not prime surjectivity. The transport
lemma takes an already constructed E, j, and prime equivalence, and only verifies
the gluing maps; it does not produce the extension. The proof combining them
constructs the extension and the final isomorphism in Lean.

Existing named dependencies, including torsion-module comparison and extension
descent, are used as stated. No axiom, forbidden implementation feature, or data
definition with a hole was introduced. The existential witnesses are used inside
a theorem proof; no definition chooses arbitrary data from an unproved theorem.

## No longer needed

Removed direct proof imports from the assigned module:

- `Sheaf.RingTheory.FormalGlueingH0Localization`.
- `Sheaf.Algebra.Module.TorsionSubmoduleFlatBaseChangeIso`.
- `Sheaf.Paper.FormalGlueingCanonicalMaps`.

The first two are needed by the new approximation node; canonical maps are needed
by both new intermediate nodes. They therefore remain in those modules' planned
proof imports. The assigned node no longer directly uses these old proof dependencies:
`lem-weil-pbc-formal-glueing-H0-localization`,
`lem-weil-pbc-torsion-submodule-flat-base-change-iso`, and
`lem-weil-pbc-formal-glueing-canonical-maps`. They are retained below the new
intermediate nodes. Removed the unnecessary newly added proof import
`Mathlib.RingTheory.Finiteness.Ideal`; single-file compilation still succeeds.
There are no globally pruned nodes or modules. Nothing in the
original mathematical route is claimed unnecessary; its difficult portions are
isolated as independently provable items.

## Where the brief, the DAG or earlier work was wrong

No existing statement was found false and no existing interface was changed.
The dependency signatures do not directly state construction of the approximation
morphism or transport of its chart maps. These are the two new nodes.

Searches were run through `msearch.py` and are recorded in `searches.jsonl`:
LeanSearch was unavailable (HTTP internal server error); LeanFinder returned
cotangent/localization and general sheaf-gluing results rather than these claims;
Loogle supplied `LinearEquiv.ofBijective` and `IsLocalizedModule.map_injective`,
which the complete proof uses; the Mathlib grep searches found no corresponding
formal-glueing theorem. Library searches found no alternative algebraization in
WeilConjectures. Existing map-to/from-algebraization modules depend on
FormalGlueingEquivalence and would create a cycle, so they are not imported.
Blueprint searches for glueing, compatible sections, and torsion cokernel found
no matching blueprint node for either new intermediate assertion.

An optional route through `FormalGlueingCanonicalFunctor` was investigated, but
its compiled artifact is absent from the shared build; no duplicate was written
and the final delivery does not import it. The direct transport argument is left
as its own named intermediate theorem. The main proof's bundled prime casts are
handled by proved equality-transport lemmas.

## New nodes

`lem-weil-pbc-formal-glueing-injective-approximation` isolates construction of the
compatible-section morphism, torsion of its prime cokernel, and injectivity of
its prime map. Its source, full natural-language proof, existing proof dependencies,
search records, and exact Lean signature are in its node and module. Its conclusion
is strictly weaker than essential surjectivity because prime surjectivity is absent.

`lem-weil-pbc-formal-glueing-extension-transport` isolates the two compatibility
squares after extension descent. Its hypotheses include the actual E, j, theta,
localized bijectivity, and the equation with the original approximation. Its source,
full natural-language proof, exact Lean signature, and search records are in its
node and module. It needs canonical-map naturality, not extension descent.

No change records or forced adaptations are required: no existing definition,
statement, signature, visibility, or public import changed.


## Second reading by C4

1. **Interface preservation: pass.** Compared the assigned module with the
   repository using diff and the stage-3 declaration reader. The sole existing
   theorem's full signature is byte-for-byte identical, as are its docstring,
   universes, visibility, and public imports. There are no removed declarations
   or changed definitions. Both additional modules are new statements, not
   forced adaptations. Only proof, proof_deps, and proof_origin differ in the
   existing node; no change record is needed.
2. **Proof and trust: pass as a decomposition.** Independently compiled all
   three modules with lcompile.py. The two reported public theorems are the
   only direct sorries, each the whole proof. No forbidden implementation
   feature or hollow definition occurs. A scratch copy with #print axioms
   for the main theorem and both intermediate theorems reports only propext,
   Classical.choice, Quot.sound, and sorryAx. Read every private helper and
   the main proof: quotient exactness, the S-linear multiplication inverse,
   extension descent, localized surjectivity, equality transport, and both
   inverse compatibility squares all have the required direction and types.
   Existential data is eliminated within a theorem proof; no definition
   chooses an arbitrary witness from an unproved existence claim.
3. **Intermediate statements: pass.** Read the actual proof of Stacks Tag
   05ER and the imported H0-localization, torsion-submodule comparison,
   canonical-map, and extension-descent signatures. Approximation is the
   compatible-section construction and kernel/cokernel argument of the
   first two paragraphs. Transport is the compatibility verification in
   the final paragraph for an already supplied E, j, and theta; it neither
   constructs the extension nor assumes Can's action on morphisms.
   Both are strictly proper parts of the original argument, have full
   docstring proofs and matching nodes, and are used with precisely the
   needed hypotheses. Checked empty charts (I=0 and exponent one suffices),
   zero generators (their localizations are zero), zero modules, and I=R
   (positive ideal-power torsion forces zero). No cancellation in R is
   required. Independent LeanFinder search for compatible sections,
   patching, injection and torsion cokernels found general injectivity
   lemmas, not these statements. Loogle verified baseChange_comp; grep
   searches for patching, reconstruction, and transport in Mathlib and
   local Lean found no substitute. The canonical-functor theorem remains
   unproved and supplies no shorter proved route. Neither remaining hole
   has a short closing proof: both require bundled object transports and
   naturality, and approximation additionally requires the torsion argument.
4. **Route and pruning: pass after report correction.** Read the proof from
   the main theorem downward and checked the old dependency list against
   the new one. The report now explicitly names all three removed direct
   dependency nodes, which remain reachable through the intermediate
   modules; no global pruning or net hole reduction is claimed. The unit
   sk-thm-p1 realized fields are untouched. The reduction follows the
   existing below-unit steps. Public imports serve the statements; the
   additional imports are private proof imports. The remaining holes keep
   the imports of their documented proof plans, as the contract requires.
5. **DAG agreement: pass.** Checked every node's recorded Lean statement
   against its actual signature and checked that proof_deps is exactly the
   union of proof-step uses. The main node describes the construction that
   Lean performs; each new node has its source, searches, provenance,
   blueprint ancestry, chapter/unit, split status, and exact Lean record.

Second reading changed the report's explicit direct-dependency accounting and
removed the unused proof import Mathlib.RingTheory.Finiteness.Ideal. No existing
statement, definition, public import, proof argument, or new hole was changed.
The result remains one upper hole closed and two strictly intermediate holes
added (a decomposition, direct net minus one).
