## What changed

Proved `etaleSection_zero_neighbourhood` with its signature and public imports unchanged.
Added a proved private helper `etaleSection_zero_pointed_witness` and two proof imports:
`WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint` and
`Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen`.

The helper uses the algebraic-closure point over each source point, the comap stalk
comparison, its proved unit/germ formula, and uniqueness of left adjoints. The filtered
colimit equality criterion gives a pointed etale refinement on which the section is zero.
The final proof takes the union of their open images, factors the refinements through that
union, and applies sheaf separatedness to the resulting jointly surjective family.
This retains the node's stalk/open-image route and changes no unit realization.

Updated the node's proof, proof_deps and proof_origin to describe this implementation.
LeanFinder found only structure-sheaf analogues, Loogle's `Presheaf.stalk` query was an
unknown identifier, and the logged grep found no arbitrary-etale-sheaf theorem.
The shorter assembly was found by reading the proved general-site germ API.

## Proved and sorry left

Closed the one original hole: `etaleSection_zero_neighbourhood`
(node `lem-weil-pbc-etale-section-zero-neighbourhood`).
The private helper `etaleSection_zero_pointed_witness` is also fully proved.
No sorry remains in the delivered module; no holes or modules were added.
This is a proof, not a decomposition. Local compilation checks the empty-source case
through the empty cover without requiring any inhabitant of T.

## No longer needed

No original imports were removed: both public imports serve the unchanged statement.
The specialized `Sheaf.Paper.InverseImageStalkGerm` module and
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk` module are not imported.
Their nodes `lem-weil-pbc-inverse-image-stalk-germ` and
`lemma-openclosed-stalk-upperstar`, and the standard-inverse-image node
`def-weil-pbc-inverse-image`, are removed from this node's proof_deps.
The already proved general-site comap comparison and germ formula suffice directly.
The filtered-colimit and open-map dependencies remain. No maximal zero locus or separate
single-neighbourhood descent lemma is needed: one cover of the union suffices.
These are local pruning claims; they do not assert that other targets cease to use those
modules.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error was found. The planned specialized inverse-image-stalk
lemma is stated for Scheme.{v} with AddCommGrpCat.{v+1}, whereas this item's unchanged
statement uses Scheme.{u+1} with AddCommGrpCat.{u+1}. The general-site comap API handles
these exact universes and uses only the supplied adjunction, so no interface change or
forced adaptation is necessary. Empty T yields the empty union; when s=0 all chosen
restrictions are zero, and the proof still applies without needing a maximal zero locus.

## Second reading by G2

1. Compared the delivered module with the repository version. The theorem signature and all existing declarations are byte-for-byte unchanged; only proof imports, a private helper, and proof bodies differ. Verdict: pass.
2. Compiled the module with `lcompile.py`; it succeeds with no errors or warnings. The delivered file contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`; the private helper and target are ordinary proved declarations. Verdict: pass.
3. Checked the helper and target against the imported general-site stalk/comap API and searched Mathlib and `lean/`; no duplicate theorem or weaker replacement was found. The helper is private and introduces no split-off hole. Verdict: pass.
4. The proof follows the planned pointed-stalk route, then takes the union of open images and uses sheaf separatedness. The two added imports are proof-only; no removable original public import was found. The listed specialized inverse-image dependencies are absent and correctly pruned. Verdict: pass.
5. Checked the node proof, proof dependencies, and proof origin against the Lean proof; they describe the helper, germ comparison, filtered-colimit witness, and open-cover descent. The unit route and realized steps are retained. Verdict: pass.

Changed after this reading: no Lean or DAG changes; appended this review record only.
