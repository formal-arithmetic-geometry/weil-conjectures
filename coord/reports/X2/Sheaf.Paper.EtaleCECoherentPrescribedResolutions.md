## What changed

Proved the assembly in `Sheaf.Paper.EtaleCECoherentPrescribedResolutions` without
changing its declaration signature or existing docstring. Its proof obtains
prescribed presentations and conditional page descent, applies augmented CE
comparison, totalizes the comparison, invokes descent with the resulting summand
and filtration equations, and chooses the sequence maps simultaneously.

Added one module, `Sheaf.Paper.EtaleCEPrescribedQuotientPageDescent`, containing the
remaining presentation/page-descent step. This is the prescribed-resolution
counterpart of the existing `EtaleCEQuotientPageDescent`; that existing theorem
cannot enforce `D.I = I` for externally supplied bicomplexes. The new statement
requires a supplied augmented bicomplex comparison, a supplied sheaf-total map
satisfying its summand equations, and supplied filtration restrictions. It constructs
none of these. The item's proof constructs those inputs using existing theorems,
so this is a strict reduction of the argument, not a renamed complete conclusion.

Added proof-only imports of `CartanEilenbergAugmentedComparison`,
`EtaleCEPrescribedQuotientPageDescent` and `EtaleCETotalizeAugmentedComparison`.
Updated the original DAG node's proof, proof dependencies and proof origin to
match the assembly. No existing definitions, statements or other modules changed.

## Proved and sorry left

Closed the item's one hole:
`AlgebraicGeometry.Etale.exists_etaleCE_coherent_prescribed_resolutions`
(node `lem-weil-pbc-ce-coherent-prescribed-resolutions`).

Added one hole:
`AlgebraicGeometry.Etale.exists_etaleCE_prescribed_quotient_page_descent`
(node `lem-weil-pbc-ce-prescribed-quotient-page-descent`).
Its whole proof is `:= by sorry`; its docstring and node give the componentwise
quotient construction, normalized successor comparisons, and computation of the
signed first-page map. There are no holes in the item's assembly and no new data
definitions. This delivery is a decomposition: one upper hole closed, one lower
hole added; it does not claim a net reduction in holes or a proof free of sorry.

The existing imported theorems
`CategoryTheory.exists_cartanEilenberg_augmented_comparison` and
`AlgebraicGeometry.Etale.etaleCE_totalize_augmented_comparison` remain dependencies;
the delivery neither modifies nor proves them.

Checked edge cases before stating the new conclusion: zero bicomplexes and empty
schemes give zero quotients and the same universal-property maps; empty diagonals
are handled by finite empty coproducts; p=0 uses the same augmented resolution;
negative complex degree q is allowed and the sign (-1)^(pq) remains defined.
A complex unbounded above has only degreewise finite diagonals, which suffices
for the componentwise construction. No globally finite filtration is assumed.

## No longer needed

No imports were removed, and no modules are claimed pruned. The existing public
import of `EtaleCEStationaryPageNaturality` is required by the statement's quotient
realizations and representative predicate. Every added proof import is used.

The original node no longer directly invokes `thm-sp-if-e1`,
`lem-sp-filtered-complex-page-differential`,
`lem-sp-filtered-complex-page-homology`,
`lem-weil-pbc-sheafH-ext-derived-comparison`, or
`lem-weil-pbc-ce-total-sections-comparison`. Presentation and page construction are
recorded in the new node, whose plan uses the normalized homology comparison
instead of a bare existence isomorphism. The total-sections comparison is part
of the totalization interface. These dependencies still occur transitively;
removing them from the whole target closure would be incorrect.

The non-prescribed `EtaleCEQuotientPageDescent` and CE-existence modules are not
imported for this proof: resolutions are inputs, not constructed here.
The globally finite `FilteredQuotientCanonicalFunctor` is not imported either.
The unit `sk-prop-h2` has no realized nodes; its statement and route were untouched.

## Where the brief, the DAG or earlier work was wrong

The original plan combines page construction, normalized successor compatibility
and first-page comparison in prose, but none of its listed declarations provides
this package for externally prescribed resolutions. The existing quotient descent
theorem chooses its own resolutions and has no prescribed-I equality. This missing
interface is the single new node; augmented comparison and totalization already
have matching interfaces and are used directly.

A bare `Nonempty` successor homology isomorphism cannot justify naturality of
page maps. The remaining proof explicitly specifies the unique comparison on
successor cycles, using `filteredComplex_normalized_homology`. Also, the existing
canonical quotient functor is restricted to globally finite filtered complexes;
CE totals need componentwise construction, since their upper filtration bounds
depend on total degree.

The LeanSearch service returned Internal Server Error. LeanFinder, Loogle and
Mathlib grep were performed and found no exact prescribed CE construction.

## New nodes

`lem-weil-pbc-ce-prescribed-quotient-page-descent` is stated in
`lean/Sheaf/Paper/EtaleCEPrescribedQuotientPageDescent.lean`. It isolates steps 1
and 3 of the original plan, conditional on the comparison and filtered-total data
constructed by step 2. Its node records the exact Lean signature, all three
search kinds, sources, and a complete proof in words. No change records are
needed: existing public signatures, definitions and imports stay unchanged.

## Second reading by X2

1. Interface check: compared the delivered existing module with the repository
   by diff and compared its theorem signature byte for byte. PASS: only three
   plain proof imports, a scoped unused-variable linter option and the proof body
   differ; the existing docstring, signature and public import are unchanged.
   The existing node changes only proof, proof_deps and proof_origin. There are
   no changed definitions, target statements, forced adaptations or change records.
2. Proof check: compiled both modules in import order through lcompile.py.
   PASS: the assembly has no sorry; the new descent theorem has exactly its
   reported whole-theorem sorry. No axiom, unsafe, opaque, implemented_by, extern,
   skipped kernel check or data definition is introduced. Axiom probes of both
   declarations are recorded below. The choices of D,e and M occur inside the
   theorem proof, not inside definitions of arbitrary data.
3. Split check: read the complete new signature, docstring and node against
   Stacks Tags 015J (Lemma 13.21.3), 015K (Remark 13.21.4), and 012K
   (Lemmas 12.24.2 and 12.24.4). PASS: I,a and all six CE assumptions match the
   prescribed-resolution inputs; the new conclusion retains I, constructs actual
   quotient realizations, and descends only a supplied phi and u satisfying their
   augmentation/summand equations and filtration restrictions. It does not supply
   the augmented bicomplex comparison, strict total augmentation square or the
   filtration restrictions required by the item. Those are genuine separate steps,
   discharged in the assembly from existing declarations. Tested zero complexes,
   empty schemes/diagonals, p=0, negative q and complexes unbounded above: in total
   degree n, contributing rows satisfy b <= q <= n, so each sum is finite without
   a globally finite filtration. The signed first-page identification uses the
   same (-1)^(pq) on source and target. Read normalized successor homology's
   uniqueness statement: it supplies the representative normalization needed for
   compatibility, unlike bare Nonempty homology isomorphisms. The missing proof
   remains substantial and is not a few-minute closure.
   Independently searched LeanFinder for filtration-preserving cochain maps and
   quotient representatives, Loogle for spectral-sequence homs, and Mathlib grep
   for spectralSequence maps/filteredComplex naturality; no packaged match.
   Searched lean/Sheaf and upstream WeilConjectures with quotient-page and
   prescribed-resolution keywords. EtaleCEQuotientPageDescent does not retain an
   arbitrary supplied I; FilteredQuotientCanonicalFunctor and
   FilteredQuotientPageRealization require a globally finite filtration and hence
   cannot be specialized to arbitrary bounded-below CE totals. No duplicate new
   statement was found.
4. Route and pruning check: read both invoked comparison/totalization interfaces
   and the first-hypercohomology construction. PASS: augmented CE comparison
   accepts the presentation's below/rows/horizontal_quasi fields and the target
   injectivity fields; totalization returns exactly u, its strict square, hu and
   the filtration restrictions consumed by hpages. The final choice retains all
   these witnesses. All three plain imports are used by name; the public import
   provides statement types. Compared old/new proof_deps: the five old direct
   dependencies no longer invoked are all named under No longer needed. No whole
   module is claimed pruned. Read dag/units/sk-prop-h2.json: realized.statement
   and its sole realized step are empty, and the unit record is untouched.
5. Metadata check: PASS: both node proof_deps lists equal the unions of their
   proof-step uses; both recorded Lean signatures match their module text exactly.
   The original node follows descent, augmented comparison, totalization and
   choice. The new node records source, complete construction/descent proof,
   searches, created/item/group, blueprint provenance, chapter/unit and Lean
   location. The report explicitly counts one hole closed and one added, a
   decomposition with zero net reduction, and lists the remaining declaration.

Second-reading changes: reflowed the new theorem's docstring to remove broken
successor-cycle wording; added the missing unavailable verdict to its LeanSearch
record. No proof or signature was changed.

Axiom probes: both declarations compiled and reported exactly propext,
Classical.choice, Quot.sound and sorryAx. The assembly remains dependent on
the reported lower hole and existing open imports; it is not axiom-closed.
