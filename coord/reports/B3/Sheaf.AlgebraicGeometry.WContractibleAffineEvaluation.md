## What changed

Proved `AlgebraicGeometry.Scheme.ProEt.surjective_app_of_affine_ring_retractions`
in `Sheaf.AlgebraicGeometry.WContractibleAffineEvaluation` with its signature unchanged.
Retained the existing proof-only import
`Sheaf.AlgebraicGeometry.Sites.WContractibleCoverSection` and added a proved private
helper `exists_glue_of_disjoint`. The four original public imports are unchanged.

The proof extracts a small covering subfamily from the locally surjective image
sieve, applies the existing covering-section theorem, glues the lifts on its
scheme coproduct, and pulls the glued lift back along the section. Gluing before
pullback avoids constructing a finite clopen refinement of the affine target.
The copied DAG node records this route and the existing Mathlib source-locality
node that it uses. No unit statement or unit proof step is bypassed.

Read the source arguments at
[Stacks 098F](https://stacks.math.columbia.edu/tag/098F) and
[Stacks 098H](https://stacks.math.columbia.edu/tag/098H), including the empty-family
case. The source `.tex` file is absent from this machine, so these official pages
were read instead. Mathlib's smallness/comap and disjoint-cover sheaf APIs were
read directly from the pinned local sources.

Validation: the final Lean file compiles cleanly with `lcompile.py` in about
three seconds. A temporary `#print axioms` check showed only `propext`,
`Classical.choice`, and `Quot.sound` for the private gluing helper. The main
theorem additionally depends on `sorryAx` through the existing imported geometric
cover-section theorem, as intended for this stage. The temporary audit commands
were removed. No new definitions, public signatures, or modules were added.

## Proved and sorry left

Closed one existing hole:
`AlgebraicGeometry.Scheme.ProEt.surjective_app_of_affine_ring_retractions`
(node `lem-weil-pbc-wcontractible-affine-weakly-contractible`).

No `sorry` remains in the item module. No holes were added or split off.
The private helper `exists_glue_of_disjoint` is proved entirely from Mathlib.

The proof uses the existing unproved statement
`AlgebraicGeometry.exists_section_proetaleCover_of_ring_retractions`
(node `lem-weil-pbc-wcontractible-cover-section`, module
`Sheaf.AlgebraicGeometry.Sites.WContractibleCoverSection`), which is unchanged.
This delivery closes the upper hole from that existing dependency; it does not
claim to remove that dependency's remaining hole.

## No longer needed

Removed five unused proof imports:

- `Mathlib.AlgebraicGeometry.Limits`
- `Mathlib.RingTheory.Spectrum.Prime.Topology`
- `Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale`
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`
- `Mathlib.AlgebraicGeometry.OpenImmersion`

The coproduct, weak-etaleness, and open-immersion APIs are available through the
required imports. Their corresponding geometric nodes remain used where the
proof needs them; removing redundant direct imports does not prune those facts.

Removed these direct DAG proof dependencies, because the target-side finite
clopen refinement is unnecessary:

- `lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact`
- `def-weil-flat-morphism`

In particular, prime-spectrum compactness and a separate verification of
flatness of the clopen inclusions are not needed by this proof. Other modules may
still reach these nodes. No library module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The mathematical statement is unchanged and no false statement was found.
The original plan's target-side finite clopen refinement is unnecessary: the
coproduct of the small covering subfamily is already a weakly etale site object,
so disjoint-cover gluing may happen there before pullback along its section.

The size issue needs an explicit step. A locally surjective image sieve initially
gives a cover indexed in the larger site universe, whereas the covering-section
theorem takes an index type in `Type u`. Mathlib's smallness instance for
`propQCPrecoverage` and its preservation by `comap` allow
`ZeroHypercover.restrictIndexOfSmall.{u}` to resolve this without changing any
statement or introducing a new hole.

## Second reading by B3

1. **Signatures and accidental changes.** Compared the delivered module and node with the repository baseline. The public theorem signature is byte-for-byte unchanged; only its proof, proof-only imports, and the recorded proof route/dependencies changed. No target statement or definition changed.

2. **Proof and axioms.** Compiled the module with `python3 /home/ubuntu/weil-launcher/lcompile.py`; it compiles without errors or warnings and contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`. The private gluing helper uses only `propext`, `Classical.choice`, and `Quot.sound`; the main theorem's remaining `sorryAx` comes only through the existing cover-section theorem.

3. **Statements and searches.** The delivery adds no split-off statement or node. I checked the helper is private and fully proved, and searched the library and Mathlib declarations for an existing theorem that directly supplies this evaluation-surjectivity argument; none replaces the proof.

4. **Route and pruning.** The proof follows the item route through local surjectivity, the covering-section theorem, the coproduct cover, and sheaf gluing. I read `dag/units/sk-thm-properbasechange.json`; this is a subordinate tool, and no node realizing a unit statement or step is bypassed. It uses the shorter valid route of gluing on the coproduct before pulling back, so the target-side finite clopen refinement is unnecessary. The five unused proof imports and the two obsolete direct DAG dependencies are recorded above; the unit's realized route is retained.

5. **DAG agreement.** The item's `proof`, `proof_deps`, and `proof_origin` match the Lean proof. The removed compactness/flatness dependencies are no longer used, while the coproduct, source-locality, weak-etale composition, open-immersion, site, local-surjectivity, and cover-section dependencies remain recorded.

I added this second-reading record and corrected the import description: the freshly read repository baseline already has the proof-only cover-section import. The delivered Lean proof and node changes otherwise needed no repair. The helper and main theorem were independently audited with `#print axioms` in a scratch copy. Edge cases checked: an empty covering family glues uniquely over the empty coproduct; the zero ring needs no nontriviality assumption; same-index overlaps use monomorphy, and distinct-index overlaps force the test scheme to be empty.
