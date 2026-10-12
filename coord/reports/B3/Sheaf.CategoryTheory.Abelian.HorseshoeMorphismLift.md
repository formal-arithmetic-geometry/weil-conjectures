## What changed

Proved `CategoryTheory.InjectiveResolution.horseshoe_preliminary_data` in
`Sheaf.CategoryTheory.Abelian.HorseshoeMorphismLift` with its signature unchanged.
Added two proof-only imports, `Sheaf.CategoryTheory.Abelian.HorseshoeGradedDefects` and
`Sheaf.CategoryTheory.Abelian.HorseshoeDefectHomotopy`, each containing one fully proved
public theorem and no definitions or sorries. All existing public imports and signatures stay
unchanged; no change record is needed.

The construction splits the source and target rows degreewise, factors the differential and
augmentation errors using Mathlib's `ShortComplex.Exact.desc` and `lift`, and proves the
compatibility identities by cancellation. A dependent recursion extends the correction maps
using `Injective.factorThru`, `InjectiveResolution.exact₀`, `exact_succ` and
`ShortComplex.Exact.descToInjective`. The item constructs the corrected chain map componentwise
and checks its differential, augmentation and both outer squares. It then supplies this map as
`χ` and the zero chain map as `q` to the existing preliminary-data interface.

Updated the preliminary-data and final-lift nodes so their proof dependencies follow the actual
Lean assembly. The unit `sk-thm-p1` and all its realized statements and steps are retained.
The three modules compile with the local single-file compiler in dependency order.

## Proved and sorry left

Closed the sole original sorry:
`CategoryTheory.InjectiveResolution.horseshoe_preliminary_data`
(`lem-weil-pbc-horseshoe-preliminary-data`).

Also fully proved:
`CategoryTheory.InjectiveResolution.horseshoe_graded_defects`
(`lem-weil-pbc-horseshoe-graded-defects`) and
`CategoryTheory.InjectiveResolution.horseshoe_defect_homotopy`
(`lem-weil-pbc-horseshoe-defect-homotopy`).

The already proved `corrected_middle_map` and `exists_horseshoe_morphism_lift` retain their
proofs and signatures. No sorry remains in the item or either new module. The two new nodes are
proved auxiliary results, not postponed obligations: zero sorries were split off.

## No longer needed

No existing import was removed: the original public import of
`Mathlib.CategoryTheory.Abelian.Injective.Resolution` supplies the statements and the Mathlib
proof tools. Both new imports are used and proof-only.

`lem-weil-pbc-acyclic-map-to-injective-nullhomotopy` is no longer needed by this proof.
In particular, no import of `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`, construction
of a Z-indexed augmented complex, shifted target complex or signed chain map is needed. Its
role is replaced by the completely proved componentwise theorem
`horseshoe_defect_homotopy`, which performs the same injective-extension induction directly
on natural-number indices. No associated Sheaf module exists to remove.

`lem-weil-pbc-ses-injective-kernel-splits` remains used by `horseshoe_graded_defects` through
Mathlib's `ShortExact.splittingOfInjective`. The two definition nodes `def-sp-abelian` and
`def-sp-injective-resolutions` remain needed. The corrected-middle-map and preliminary-data
nodes remain used by the final theorem. In the final-lift node the old direct dependencies
`lem-weil-pbc-ses-injective-kernel-splits` and `def-sp-abelian` are replaced by the
preliminary-data and correction nodes, but remain used transitively in the graded-defect
construction. In the preliminary-data node the splitting dependency likewise moves to
`horseshoe_graded_defects`. These are changes in dependency placement, not abandoned
lemmas. The only abandoned mathematical dependency is
`lem-weil-pbc-acyclic-map-to-injective-nullhomotopy`; no module is pruned.

## Where the brief, the DAG or earlier work was wrong

The old preliminary-data interface already requires `χ` and `q` to be chain maps. In the
classical splitting step, the initial `χ` is only a graded family and generally fails the
chain-map identity. Thus that interface had combined nearly the entire construction into one
sorry. The delivery retains its exact statement but exposes the actual graded maps and their
errors separately, proves the correction, and returns the corrected chain map with `q = 0`.

The old final-lift node still listed the splitting and generic null-homotopy lemmas directly,
although its already landed Lean proof used preliminary-data and correction. Its dependencies
now match that assembly. No mathematical statement is disputed or weakened.

The target base row's `hT : T.ShortExact` is unnecessary for the graded construction: exactness
of the target rows of complexes and the target augmentation squares suffice. It is retained in both
interfaces, with the unused binder named `_hT` in the new helper; the existing signature stays
unchanged.

LeanSearch returned HTTP 500 for both new-node queries. These searches are recorded as
unavailable, not as empty successful searches. LeanFinder/Loogle and source grep were run and
provided the component lemmas. The new statements were checked at degree zero, for zero
outer objects and for resolutions concentrated in degree zero; the full Lean proofs also
cover those cases without additional assumptions.

## New nodes

`lem-weil-pbc-horseshoe-graded-defects`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-horseshoe-graded-defects.json`, records
`Sheaf.CategoryTheory.Abelian.HorseshoeGradedDefects`. It states the graded middle-map
construction and both error factorizations, with their cocycle and augmentation compatibility.
It is fully proved using injective row splittings and exact factorization; its source is the
classical horseshoe calculation of Weibel Theorem 2.4.6 and Stacks Tags 0136 and 013T.

`lem-weil-pbc-horseshoe-defect-homotopy`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-horseshoe-defect-homotopy.json`, records
`Sheaf.CategoryTheory.Abelian.HorseshoeDefectHomotopy`. It states the signed coboundary identity
for a compatible degree-one cocycle on an augmented resolution. It is fully proved by
injective extension and dependent recursion, following the induction behind Stacks Tag 013R.

## Second reading by B3

1. **Public contract: pass after a whitespace repair.** Read the diff of the item against
   the repository. Its only substantive changes are two ordinary proof-only imports and
   replacement of the preliminary-data proof. Restored the space before `:=` in the
   already proved final theorem, so all three existing declaration signatures are byte
   for byte unchanged. The declaration comparison reports no statement changes. No
   existing definition or public import changed; there is no change record to require.

2. **Proof and axioms: pass.** Read all three modules and compiled them together through
   `lcompile.py --all` in dependency order, without errors or warnings. There is no
   `sorry`, axiom declaration, unsafe code, opaque declaration, implementation override
   or external implementation in any delivered Lean file, and no new definitions.
   Scratch copies with `#print axioms` for `corrected_middle_map`,
   `horseshoe_preliminary_data`, `exists_horseshoe_morphism_lift`,
   `horseshoe_graded_defects` and `horseshoe_defect_homotopy` each show exactly
   `propext`, `Classical.choice` and `Quot.sound`; the scratch copies were removed.
   The graded proof cancels only the epic source row maps and monic target row maps,
   supplied by degreewise short exactness. Its augmentation descent uses `hS`, and the
   two squares of `F` and both prescribed outer augmentation equations are used.
   In the homotopy proof, augmentation monicity supplies the initial extension;
   `exact₀` supplies the first differential extension, and `exact_succ n` supplies the
   inductive extension. Each codomain is a term of `JA`, hence injective. The recursion
   retains two consecutive maps and their equation, so its extracted components agree
   at successive indices. In the item, the signed defect identity proves `comm'`, the
   two zero composites preserve the outer squares, and extensionality from `single₀`
   reduces the augmentation equality to degree zero. Choosing the already corrected
   map as `chi` and zero as `q` satisfies the original five equations.

3. **Auxiliary statements: pass; no postponed statements.** Matched every hypothesis
   and conclusion of each new node with its Lean signature. The graded helper provides
   a family, not a chain map, and records both defect factorizations and their two
   compatibility identities. The homotopy helper requires precisely the cocycle and
   augmentation compatibility needed to construct `k`; neither is a renamed copy of
   the item. Both are fully proved. At zero outer objects the corresponding errors are
   zero; when the resolutions are concentrated in degree zero, `E` is zero and the
   only required construction is extension of `e` across the monic augmentation.
   The degree-zero compatibility is checked separately before induction, so there is
   no negative-index assumption or missing initial case. The unused target-base
   short-exactness hypothesis in the graded helper is retained, matching its node.
   Fresh LeanFinder search for compatible augmentation and anticommuting degree-one
   maps returned resolution comparison and ordinary null-homotopy tools, not the
   signed augmented statement. Loogle's unqualified query was rejected as an unknown
   identifier; the qualified query and source inspection identify the component
   extension tool. Inspected Mathlib `Injective/Resolution.lean` lines 114--172:
   `descHomotopyZero` starts from a chain map with zero augmentation, whereas here
   `E` has degree one, anticommutes, and has a possibly nonzero augmentation `e`.
   Inspected `ShortComplex/Exact.lean` lines 937--950 (`descToInjective` and its
   equation) and `ShortComplex/ShortExact.lean` lines 203--210 (injective splitting).
   Searched `lean/Sheaf/CategoryTheory/Abelian` and upstream category-theory sources
   using defect, graded map, coboundary and horseshoe keywords. The exact-source
   horseshoe statement is still sorry and imports this item, so it is not a usable
   shorter route. No existing proved declaration states either new helper.

4. **Route and pruning: pass after report clarification.** Read the source ingredients
   at [Stacks Tag 0136](https://stacks.math.columbia.edu/tag/0136),
   [Tag 013R](https://stacks.math.columbia.edu/tag/013R) and
   [Tag 013T](https://stacks.math.columbia.edu/tag/013T); the local literature text is
   absent on this machine. Tag 0136 supplies injective row splitting, and the extension
   induction in Tag 013R is exactly the argument used for the signed coboundary.
   Tag 013T supplies horseshoe context, rather than a statement of this naturality
   calculation. Weibel is listed as wanted in the original node and was not available
   to read; the checked Stacks ingredients and the explicit algebra justify the proof.
   The two new imports are both used only by the item proof. Each helper's sole public
   Mathlib import supplies the categories, resolutions and types in its signature.
   The componentwise induction avoids constructing augmented integer-indexed complexes
   or importing K-injective machinery, so no shorter available route was found.
   Compared both old dependency lists: the generic acyclic-to-injective null-homotopy
   node is abandoned; row splitting and abelian-category tools remain used transitively.
   Clarified those placements under `No longer needed`. Read `sk-thm-p1.json`, including
   all four `realized.steps` and `realized.statement`: none is altered or bypassed.

5. **DAG agreement: pass.** Read all four delivered node records. The two existing nodes
   change only `proof`, `proof_deps` and `proof_origin`; their statements and Lean
   signatures remain unchanged. The preliminary node now applies the graded-defect
   and signed-homotopy helpers, then performs the explicit correction. The final node
   accurately records its applications of preliminary data and `corrected_middle_map`.
   The graded helper's four steps match splitting, differential factorization,
   augmentation factorization and cancellation identities in its code. The homotopy
   helper's three steps match the initial injective extension, degree-zero extension
   and dependent recursion. Each `proof_deps` list is the union of step citations.
   Both new records carry sources, statement dependencies, actual search records
   (including unavailable LeanSearch), creation data, blueprint ancestry, chapter,
   unit and Lean declaration records. Their declaration docstrings give complete
   mathematical proofs. Added their node labels to the new module docstrings.

Changes by this second reader: restored existing-signature whitespace, added two module
blueprint labels, clarified direct versus transitive pruning in the report, and recorded
this independent reading. No mathematical statement or proof needed repair.
