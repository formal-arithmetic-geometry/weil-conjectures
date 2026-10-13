## What changed

Replaced the invalid earlier split with a compiling decomposition of
`affineOpenSections_inverse_image_finite_local_lifts`. Its existing signature and
public imports are unchanged. The only new imports are proof-only imports of
`Sheaf.Paper.EtaleAbelianLocalUnitRepresentatives` and
`Sheaf.Paper.AffineOpenRepresentingCoverDescent`.

The local lemma produces a cover together with representing objects, arrows and
sections, before choosing a finite stage cover. The geometric lemma refines this
particular cover, selects finitely many members (allowing repetitions), and
provides stage models and representing maps. It contains no sheaf, section or
adjunction. The main proof explicitly restricts each representative along the
stage representing map and proves its unit equation by naturality and
contravariant functoriality. This final calculation is proved in Lean.

Deleted the two never-delivered sandbox lemmas and nodes from the earlier attempt,
`exists_affine_open_finite_cover_data` and `exists_affine_open_local_sections`.
They were not repository declarations. Replaced the previous report, including
its obsolete second-reading section; the new delivery still needs its independent
second reading. No existing definition or statement was changed or adapted. The new local
representative module omits the affine-morphism import, which its statement does
not need.

## Proved and sorry left

Original holes closed: `affineOpenSections_inverse_image_finite_local_lifts`
(node `lem-weil-pbc-affine-open-inverse-image-finite-local-lifts`), 1 of 1.

New holes, each a public theorem with a source and complete proof in words:

- `etaleAbelian_local_unit_representatives`, in
  `Sheaf.Paper.EtaleAbelianLocalUnitRepresentatives`, node
  `lem-weil-pbc-etale-abelian-local-unit-representatives`.
- `affineOpen_representing_cover_descent`, in
  `Sheaf.Paper.AffineOpenRepresentingCoverDescent`, node
  `lem-weil-pbc-affine-open-representing-cover-descent`.

This is a decomposition into two strictly separate parts, not a complete
sorry-free proof or positive net hole progress: one hole closed and two added.
The item's module contains no sorry. No data definition was introduced.
All three delivered modules compile together with the prescribed launcher.

Edge-case checks: the local lemma needs neither an affine target nor a diagram;
its cover may be empty. The geometric lemma permits an arbitrary initial cover,
non-affine sources, non-quasi-compact representing objects, refinements,
repeated indices and an empty final index. Empty limits require eventual empty
stages through finite covering descent. A singleton system reduces to affine
refinement and composing its representing maps. For zero coefficients the
local representative sections are zero. The final Lean calculation does not
assume a nonempty index and requires no overlap compatibility.

## No longer needed

Removed the earlier sandbox proof imports
`Sheaf.Paper.AffineOpenFiniteCoverData` and
`Sheaf.Paper.AffineOpenLocalSections`, and discarded their never-landed nodes
`new-affine-open-finite-cover-data` and `new-affine-open-local-sections`.
The invalid prescribed-cover local-section statement is not used.

The parent node's nine old direct proof dependencies are replaced by the two
new nodes. Cofiltered directed reindexing, local inverse-image description,
abelian comparison, finite affine refinement, geometric descent and canonical
pullback comparisons remain work under those nodes, not claimed as globally
pruned. In the geometric node, the existing
`lem-weil-pbc-etale-finite-cover-factorization-descent` packages finite object,
arrow and covering descent; its arbitrary auxiliary targets avoid duplicating
that theory. The original direct spreading-out and finite-diagram dependencies
remain within this existing geometric result's dependency tree.

The original localization-restriction dependency
`lem-weil-pbc-etale-inverse-image-restriction` (module
`WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`) is unnecessary
for this argument: naturality of the specified hH unit supplies the equation
directly. No import of that module was present in the repository item and none
is added. No whole module is claimed to leave the global targets' closure.

## Where the brief, the DAG or earlier work was wrong

The earlier split was false: a section of the inverse image need not lie in
the unit image on each member of an arbitrary prescribed cover. Representatives
must be obtained first; their particular covering may then be refined and
descended. The replacement geometric statement explicitly allows that
refinement and retains the representing-arrow equation needed by naturality.

The earlier reader suggested `affineOpenSections_descent` as a shortcut. Its
module imports `AffineOpenInverseImageUnitRepresentatives`, which imports this
item, so that shortcut would create a cycle and is not used.

The recorded inverse-image section description and algebraic-structure lemmas
have schemes in universe u and coefficients in universe u+1. Instantiating them
at this item's scheme universe u+1 gives coefficients in u+2, whereas this
item's coefficients are in u+1. They do not apply unchanged. The new local lemma
records the needed same-universe, supplied-adjunction version. Its proof plan
requires the underlying-set comparison at this universe, via an essentially
small site or universe transport; it does not silently change the original
statement's coefficients or invoke the mismatched signature.

Searches used LeanFinder, Loogle and Mathlib grep; LeanSearch returned Internal
Server Error. Results and queries are recorded in the new nodes. The existing
geometric descent lemmas and relevant signatures were read. Stacks Tags 09XN,
00YV, 0EYL and 03Q6 were read online; the sources support the local representation,
algebraic-structure compatibility and finite-descent steps. The unit route
`sk-thm-p1` is unchanged: this is a below-unit decomposition of the same
finite-local-lift step, without global gluing or bypassing a realized unit node.

## New nodes

`lem-weil-pbc-etale-abelian-local-unit-representatives` records the local
sheaf-theoretic part for an arbitrary morphism and specified abelian adjunction,
with no diagram or finite stage claim. Its module is
`lean/Sheaf/Paper/EtaleAbelianLocalUnitRepresentatives.lean`.

`lem-weil-pbc-affine-open-representing-cover-descent` records only geometric
refinement and stage descent, with a selection map and factorization equations.
Its module is `lean/Sheaf/Paper/AffineOpenRepresentingCoverDescent.lean`.

Both node files are in `dag/nodes/sec-proper-base-change/`. The existing parent's
proof, proof_deps and proof_origin now record the actual Lean reduction. No
change record is needed because existing interfaces did not change.

## Second reading by R4

1. **Interfaces and accidental changes.** Compared the delivered item module with the repository version. The target theorem signature and all existing declarations are byte-for-byte unchanged; only proof-only imports and the proof body changed. The two added modules contain new split-off declarations only, and no existing definition or interface was adapted. Verdict: pass.

2. **Compilation and proof hygiene.** Compiled all three sandbox modules with `lcompile.py --all`; compilation succeeds. The item theorem contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`. The two split-off public theorems intentionally contain exactly their named `sorry`s, as listed above and represented by their DAG nodes. Verdict: pass subject to those declared split holes.

3. **Truth and strength of split statements.** Read both new statements against the proof and source references. `etaleAbelian_local_unit_representatives` asserts only local unit representatives for an arbitrary supplied abelian adjunction, with no finiteness or stage claim. `affineOpen_representing_cover_descent` asserts only geometric finite refinement, stage descent, covering, and factorization, with no sheaf data. Both permit empty/repeated families and impose no extra hypotheses; they are strictly smaller than the target and their docstrings record the intended proofs. Searches recorded in the node files found no existing equivalent declarations. Verdict: pass.

4. **Pruning and route.** The item proof uses exactly the two new split nodes followed by a direct naturality/functoriality calculation. Removed unused earlier sandbox imports and the obsolete prescribed-cover split. The parent node's proof, proof dependencies, and proof origin match the Lean proof. The unit route `sk-thm-p1` remains recorded and the geometric/local representative work stays below the unit. Verdict: pass.

5. **DAG and report consistency.** Checked both new node files, the updated parent node, and this report. Statements, declaration names, modules, proof steps, dependencies, source notes, and split status agree with the delivered Lean files. Verdict: pass.

Changed during second reading: added this required independent review section only; no Lean proof or statement changes were needed.
