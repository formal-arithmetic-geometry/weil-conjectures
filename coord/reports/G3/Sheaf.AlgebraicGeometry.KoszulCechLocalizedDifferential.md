## What changed

Proved `AlgebraicGeometry.koszulCechLocalizedDegreeMap_comm` by expanding
Mathlib `CochainComplex.HomComplex.δ_v`, distributing the evaluation over the two
summands, and combining their separate vertical and horizontal identities.
The vertical identity is completely proved, including naturality of scalar division
and the integer sign calculation. The horizontal identity is a new, strictly smaller
named theorem: it involves only precomposition with the Koszul boundary, with no
coefficient differential. The singleton horizontal component is proved directly in
the item, so the remaining boundary lemma is needed only for subsets of cardinality
at least two.

Relocated the existing `koszulCechScalarDivision` and `koszulCechLocalizedDegreeMap`
definitions verbatim to `Sheaf.AlgebraicGeometry.KoszulCechLocalizedEvaluation`.
The item publicly imports that module, preserving both names, signatures, bodies,
visibility and its former transitive public imports. This makes the horizontal lemma
importable without a cycle. No other existing module was edited. Change record:
`coord/changes/koszul-cech-localized-evaluation-relocation.md`.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.koszulCechLocalizedDegreeMap_comm`
(node `lem-sc-koszul-cech-localized-differential`), by a compiling proof from two
separate terms. Added one hole in `AlgebraicGeometry.koszulCechLocalized_boundary`
(node `lem-sc-koszul-cech-localized-boundary`). This is a decomposition: one original
hole closed, one strictly smaller hole added, net zero holes. The item itself has no
remaining sorry.

`AlgebraicGeometry.koszulCechLocalized_vertical` is fully proved (node
`lem-sc-koszul-cech-localized-vertical`). Its private scalar-cancellation and
scalar-division-naturality helpers are fully proved. No data definition has a hole.
The horizontal theorem, restricted to subsets of cardinality at least two, has whole proof `:= by sorry`; its docstring and node spell
out the contraction, denominator cancellation, degree transports and sign calculation.

## No longer needed

No node or dependency module is pruned. The item's three old direct public imports
(`Sheaf.Algebra.Homology.ModuleHomComplex`,
`Sheaf.AlgebraicGeometry.PrincipalOpenCechTotal`,
`Sheaf.AlgebraicGeometry.KoszulOpenSystem`) now occur in the public evaluation module
and remain visible transitively. They are still needed. No unused proof import remains.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The existing plan compressed the entire calculation into
one step; the delivery separates the coefficient and boundary terms explicitly.
For edge cases, a singleton has zero outgoing tail differential and no nonempty erased
subset. For r=0 there is no component J. Zero or nilpotent products give empty opens
and zero section modules. There is no cancellation in A or quasi-coherence assumption.
The two-element case checks the horizontal signs: its exponent with the negative tail
boundary and the Hom sign yields the usual plus/minus deletion pair. The vertical
statement is checked by Lean for arbitrary degree, including negative degrees.

Read Stacks Tags 08D0 and 08D1 on their official pages; the listed local perfect.tex is
absent on this machine. Search: LeanSearch returned Internal Server Error; LeanFinder
returned Hom differential tools but no localized identity; Loogle found `δ_v`, used in
the item. `msearch grep` and direct rg found no available localized comparison lemma.
The source library's contraction formula is private and concerns the exterior boundary,
not either complete localized identity. New node search records include these outcomes.

## New nodes

`lem-sc-koszul-cech-localized-vertical` records the fully proved coefficient identity
and the relocated concrete evaluation definitions, in
`Sheaf.AlgebraicGeometry.KoszulCechLocalizedEvaluation`.

`lem-sc-koszul-cech-localized-boundary` records just the horizontal precomposition
calculation, in `Sheaf.AlgebraicGeometry.KoszulCechLocalizedBoundary`. Its proof task
is independent of every coefficient differential and is strictly part of the original
argument. The original node now records the Lean combination of the two terms.

Change record: `coord/changes/koszul-cech-localized-evaluation-relocation.md`.

## Second reading by G3

1. Interface: PASS. Compared the item with the repository by diff and checked
   the original theorem signature byte for byte. Both relocated definitions have
   byte-identical signatures and bodies. Their universe, namespace, parameters and
   public visibility agree. The change record declares the relocation and lists
   downstream users; the original public imports remain available transitively.
   No target statement, hypothesis, conclusion or data construction was changed.
2. Proof: PASS. All three delivered modules compile locally through lcompile.py
   in import order. The only textual hole is the whole proof of the public named
   theorem `AlgebraicGeometry.koszulCechLocalized_boundary`. No axiom, unsafe,
   opaque, implemented_by, extern or definition hole is introduced. A separate
   scratch probe prints the axioms of both definitions and all three public
   theorems: both definitions and the vertical theorem use only propext,
   Classical.choice and Quot.sound. The boundary and original commutation theorem
   additionally use sorryAx, as expected from the one remaining boundary hole.
   The delivery tool also probes every newly declared constant.
3. Split statements: PASS. Read the horizontal statement, its docstring and node
   against the negative tail boundary and the actual Cech differential. It is only
   the precomposition summand and excludes the singleton case already proved in
   the item, rather than renaming the original chain-map identity. For p=1 the
   erased rows have p=0 and the sign difference is 2*n; for general p>0 it is
   2*(n-p+1). Empty covers have no components; empty principal opens have zero
   sections, and no cancellation in A is assumed. The division definition takes
   the inverse of a proved bijection, not an arbitrary unproved existence witness.
   Independently searched LeanFinder for exterior contraction, Loogle for
   contractLeft_ι_mul, and grep/rg for contraction and Koszul/Cech identities.
   Mathlib supplies the contraction recursion, and the library's
   koszul_differential supplies an exterior formula; neither proves the localized
   restriction and ordered-subset calculation. No duplicate or few-minute proof
   of the remaining boundary theorem was found. Read Stacks Tags
   [08D0](https://stacks.math.columbia.edu/tag/08D0) and
   [08D1](https://stacks.math.columbia.edu/tag/08D1).
4. Route and pruning: PASS. The item expands the Hom differential, proves the
   vertical summand and singleton boundary, and applies the remaining horizontal
   lemma only for card(J)>1. Public imports are required by signatures or concrete
   definitions; the boundary import is proof-only. All three old proof_deps are
   still used, so no old dependency is missing from No longer needed. Checked
   dag/units/sk-thm-picard-duality.json: its realized fields are unchanged, and
   this calculation bypasses none of the unit's stated steps. One original hole
   is closed and one smaller hole added: decomposition, net zero holes.
5. DAG: PASS. The original node records component extensionality, delta expansion,
   the vertical lemma and the singleton/general horizontal split. Its proof_deps
   are exactly the union of the proof steps' uses. The two new nodes name their
   Lean declarations, chapter/unit, source, origin, searches and creation data;
   the boundary node describes the one remaining proof obligation faithfully.

Changed in this reading: removed the unnecessary file-level
`backward.isDefEq.respectTransparency` and
`backward.isDefEq.respectTransparency.types` options from the evaluation module;
compilation succeeds without them. Corrected a report grammar error. No mathematical
statement, definition or proof was changed.
