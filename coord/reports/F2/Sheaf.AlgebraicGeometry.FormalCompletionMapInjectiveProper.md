## What changed

Replaced the initial factorization application with a direct reduction from the existing
`completion_internal_hom_bijective`, `globalSections_formalFunctions_complete_base`, and
`Scheme.Modules.isCoherent_homObj`. The proof constructs the compatible reductions of the
actual internal Hom section. It proves componentwise that the internal Hom comparison sends
these reductions to the completion of the original morphism, using its factorization equation
and cancellation of the source cokernel projection. Injectivity of that comparison gives
equality of reductions. The canonical formal-functions isomorphism then gives equality of
top sections, and restriction identifies the original morphisms.

Added one proved private implementation helper, `AlgebraicGeometry.homSections_map`, whose
naturality identity is `rfl`. This adds no public interface. Removed the proposed auxiliary
module `Sheaf.AlgebraicGeometry.FormalCompletionMapInjectiveProperAux` and its proposed node
`aux-formal-completion-map-factorization`: they restated the entire injectivity problem.
Updated the item's proof steps and dependencies, including internal Hom coherence, to match
this reduction. All existing signatures, docstrings, definitions and public imports remain
byte-for-byte unchanged. No change record is needed.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.formalCompletion_map_injective_of_proper`, node
`lem-weil-pbc-formal-completion-map-injective-proper` (1 of 1 holes of the original module).
New private helper proved: `AlgebraicGeometry.homSections_map`.
Holes added: none. Split-off statements delivered: none. No `sorry` remains in the module.
The proposed `AlgebraicGeometry.formalCompletion_map_factorization` and its hole were removed
before delivery; they were never part of the library baseline.

This is a proved reduction to existing open dependencies, not an axiom-free completion of
the whole formal-functions argument. The main theorem's `#print axioms` reports exactly
`propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` from imported open comparisons and
coherence results. The private helper reports only the three allowed axioms. Relative to the
item's supplied baseline, one existing hole is closed and zero new holes are introduced;
the maintainer's pinned sorry ledger decides the import-closure totals.

## No longer needed

Removed unused original proof-only imports:
- `Sheaf.AlgebraicGeometry.Coherent`
- `Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`

Coherence definitions and internal Hom remain available through the retained public
imports of the comparison modules. None of the four original `proof_deps` is unused:
`lem-weil-pbc-completion-internal-hom`, `lem-weil-pbc-formal-functions-complete-base`,
`def-pur-sheaf-hom`, and `def-weil-pbc-coherent-formal-module` are all used. No unit-level
node or route is pruned, and no claim is made that these modules disappear from the whole
target import closure. The proposed auxiliary import, module and node are also removed.

## Where the brief, the DAG or earlier work was wrong

The initial auxiliary claimed an injective function with exactly the same domain and
codomain as completion, together with equality to completion on every morphism. This is
equivalent to the item's injectivity claim, not a strictly simpler intermediate statement.
Its alleged factorization added no intermediate object. The initial report's claim of a
strict decomposition was therefore wrong; the auxiliary is removed rather than accepted.
The existing comparison statements already specify all component identities needed for a
real reduction. The original DAG omitted the direct use of internal Hom coherence; it is
now recorded as a proof dependency.

Source checked against [Stacks 0883](https://stacks.math.columbia.edu/tag/0883),
[0882](https://stacks.math.columbia.edu/tag/0882), and
[087U](https://stacks.math.columbia.edu/tag/087U). The final proof follows their comparisons.

## Second reading by F2

1. Compared the delivered module against the repository using `diff`, and separately compared
   the existing theorem's raw signature up to `:= by`: byte-for-byte identical. No existing
   definition, docstring, target statement or public import changed. Verdict: pass.
2. Compiled the final module with `lcompile.py` at the normal heartbeat limit: no errors or
   warnings, under 11 seconds. Scanned for `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, and
   `implemented_by`: none. Compiled a scratch copy with `#print axioms` for both declarations;
   only the permitted axioms and the main theorem's inherited `sorryAx` occur. The internal
   Hom object and reductions are actual constructions; the isomorphisms and comparison maps
   are specified canonically by their projections/components. No arbitrary existential
   witness is used as data in a definition. Verdict: pass as a reduction to open dependencies.
3. Rejected and removed the sole proposed split, since it is equivalent to the item.
   No split remains. The private naturality helper is definitional and works for arbitrary
   module maps, including zero maps and zero objects. Searched the repository and Mathlib by
   `rg`, and used `msearch.py` Loogle for sections and Lean Finder for global internal Hom
   naturality; no existing lemma directly states this particular definitional identity.
   The theorem adds no nonzero-ideal, nonempty-scheme, or nonzero-module assumption; its proof
   uses positive levels uniformly, so zero ideal/zero module cases require no exception.
   Verdict: pass after removing the restatement.
4. Read from the target downward through the comparison interfaces. The final proof uses
   their specified equations directly, and introduces zero holes. Removed four unused
   original proof imports and the proposed auxiliary import. Compared all old `proof_deps`
   with the proof: all remain used. Read `dag/units/sk-thm-p1.json`, including its `realized`
   statement and four step groups: the formal-completion reduction stays below that unit;
   no realized step or chapter route is bypassed. The cited blueprint `_section.md` is not
   present in this machine's literature tree; its text and steps are recorded in the unit
   JSON and were read there. Verdict: pass.
5. Updated the existing item's `proof`, `proof_deps`, and `proof_origin` to the actual
   reduction. Their dependencies are exactly the union of the proof-step uses, with
   `lem-weil-pbc-coherent-sheaf-hom-coherent` added. All other node fields stay unchanged.
   No new node remains. Verdict: pass.

Second reading changed the proof to a real reduction, removed the restatement and its
node/module, pruned four original unused imports, kept the original file-level `open` command by
qualifying new proof references, corrected the DAG, and rewrote the report
with the actual holes closed and added.
