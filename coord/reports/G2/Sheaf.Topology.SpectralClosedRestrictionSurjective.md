## What changed

Proved `TopCat.spectral_closed_restriction_surjective` without changing its signature.
Adapted the complete source-library germ-and-gluing proof in
`WeilConjectures.Topology.Sheaves.SpectralRestriction` from abelian sheaves to sheaves of
sets. Its only connectedness uses concern closures of individual points, exactly as
assumed here. The private helper proves the compatible-stalk-bijection criterion in
full; the public proof constructs the stalk comparison, applies the criterion, and
transfers through uniqueness of left adjoints. The source theorem itself cannot be
applied directly because its coefficient category is `AddCommGrpCat`.

Added proof imports `Mathlib.Topology.Sheaves.Sheafify` and
`WeilConjectures.Topology.SpectralSpace.Constructible`. Stalks and unique gluing are
already available through these imports; trial removal of redundant direct imports
compiled successfully. Updated the existing node's proof, proof_deps, and proof_origin
for this route. The original docstring records the previous finite-constant plan;
an inline comment explicitly identifies the alternative proof implemented here.

## Proved and sorry left

Proved `TopCat.spectral_closed_restriction_surjective` (one of one original sorries).
No sorries remain or were introduced. The private `restriction_bijective_of_stalk` is
also completely proved. Local compilation is clean, and `#print axioms` for the public
theorem reports exactly `propext`, `Classical.choice`, and `Quot.sound`.

The proof covers empty spaces: the connectedness hypothesis forces X empty if Z is
empty; the finite family and gluing arguments allow an empty index set. No finite or
nonempty assumption is imposed on the sheaf's sets. Closedness is used to make Z
compact, and spectrality supplies compact open representatives and the constructible
closure-specialization theorem. The unit's route is preserved: the item is below the
unit's realized statements/steps in `dag/units/sk-thm-p1.json`, none of which is bypassed.

## No longer needed

Removed all five previous proof imports:

- `Sheaf.Topology.ClosedPushforwardConstantRestriction`
- `Sheaf.Topology.SheavesDirectedColimitSections`
- `Sheaf.Topology.SpectralClosedClopenDecompositionLift`
- `Sheaf.Topology.SpectralClosedSubspace`
- `Sheaf.Topology.SpectralSheafColimitConstantEmbeddings`

Their finite-constant, finite-product, subsheaf, and directed-colimit route is unnecessary
for this proof. The following former proof dependencies are removed (they may still be
needed by other callers):

- `lem-weil-pbc-spectral-closed-clopen-decomposition-lift`
- `lem-weil-pbc-spectral-closed-subspace`
- `lem-weil-pbc-sets-inverse-image-colimits-finite-products`
- `lem-weil-pbc-closed-pushforward-constant-restriction`
- `lem-weil-pbc-filtered-colimit-sets-elementwise`
- `lem-weil-pbc-spectral-sheaf-colimit-constant-embeddings`
- `lem-weil-pbc-sheaves-directed-colimit-sections`

The generalizations and constructible closure-specialization facts are used through
already proved source-library implementations, not the admitted Sheaf wrapper modules.
No claim is made that their nodes are globally unreachable. No new module is introduced.

## Second reading by G2

1. Compared the delivered module with the repository version. The theorem signature and
all existing declarations are unchanged byte for byte; only proof imports, the proof body,
the author line, and the existing node's proof metadata changed.

2. Compiled the module with `lcompile.py`; it is clean and contains no `sorry`, `axiom`,
`unsafe`, `opaque`, `extern`, or `implemented_by`. The proof uses only the permitted
constructible-topology and stalk results; its declarations have no unintended axioms.

3. The proof introduces no public split-off statement. The private germ-and-gluing helper
is fully proved, so no new node or admitted theorem is needed. Searches found no shorter
Mathlib or upstream declaration matching the target.

4. The source-library germ-and-gluing route is a shorter valid route below the unit level.
The unit route is preserved, while the seven finite-constant/colimit dependencies and their
imports are pruned because the proof does not use them.

5. Updated node proof steps, `proof_deps`, and `proof_origin` match the Lean proof. The
unit's realized statements and steps remain untouched.

Changed: replaced the admitted proof with the complete set-valued germ-and-constructible
proof, minimized imports, and recorded the corresponding DAG pruning and proof metadata.

## Where the brief, the DAG or earlier work was wrong

The existing source library has a complete proof with a different coefficient category;
its actual argument uses no additive operations and only point-closure connectedness.
Thus the planned directed-colimit presentation is avoidable below the unit level.
Searches: ripgrep found `WeilConjectures.Topology.Sheaves.SpectralRestriction` and its
complete proofs; Loogle query `SpectralSpace, TopCat.Sheaf` returned zero hits. All
underlying constructible and stalk lemmas were checked by their source signatures and
by compilation; no assumption of a missing Mathlib theorem is made.
