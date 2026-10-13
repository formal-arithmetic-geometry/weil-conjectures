## What changed

Proved `AlgebraicGeometry.Scheme.Modules.moduleMapIsoLocus_inter_eq_basicOpen_of_free`
in `Sheaf.AlgebraicGeometry.FiniteFreeMapIsoLocusBasicOpen`, preserving its full public
signature and both original public imports. Added proof-only imports of
`Sheaf.AlgebraicGeometry.ModuleMapIsoLocusPullback`,
`Sheaf.AlgebraicGeometry.Modules.LocalInvertibleMinorBlockIso`,
`WeilConjectures.Mathlib.AlgebraicGeometry.Restrict`, and
`Mathlib.AlgebraicGeometry.ResidueField`.

The witness is the determinant of the framed square map, transferred by `U.topIso`,
when the finite ranks agree; it is zero otherwise. The forward inclusion uses the
existing proved square free-sheaf inverse lemma. The reverse inclusion and the
unequal-rank contradiction use the existing proved preservation of local invertibility
under pullback to a residue-field point. Eight proved private helpers supply the
restriction, image-open, matrix, and finite-dimensional linear algebra calculations.
No new public interface or unproved statement was introduced.

Updated the existing node's `proof`, `proof_deps`, and `proof_origin` to this argument.
The unit `sk-prop-av-cube` has no realization by this node; its statement and route are
unchanged. The determinant step of the original plan is retained.

## Proved and sorry left

Closed the module's sole hole:
`AlgebraicGeometry.Scheme.Modules.moduleMapIsoLocus_inter_eq_basicOpen_of_free`
(node `lem-sc-finite-free-map-iso-locus-basic-open`). Holes closed: 1. Holes added: 0.
No `sorry` remains in the delivered module, and there are no new modules.

The file compiles cleanly through `lcompile.py`. A separate temporary `#print axioms`
check of the theorem reported exactly `propext`, `Classical.choice`, and `Quot.sound`;
the diagnostic command was removed from the delivery. Thus this is a proof, not a
decomposition through lower holes. All private helpers are proved.

Edge cases are covered by the general proof: empty U contributes no point in the
reverse or unequal-rank branches, empty equal index types give determinant one, and
the unequal-rank contradiction is made only after obtaining an actual residue-field
point. Nonreduced schemes are allowed. Both finite index types remain in universe u.

## No longer needed

No original import was removed: both public imports are needed by the unchanged
statement. No module is claimed as pruned. `def-weil-affine-spectrum` is removed from
this node's proof-dependency list because affineness is unused by the argument; it
remains a statement dependency, since the existing affine hypothesis is retained.
The planned stalk-inverse/determinant calculation is replaced by a residue-field
calculation, so no stalk comparison or stalk inverse extension module is imported.

## Where the brief, the DAG or earlier work was wrong

No false statement or unusable interface was found. The planned converse can be
shortened using residue-field pullback, and the matrix proof works for every open U,
without affineness. The original affine hypothesis is retained verbatim. The source
was checked against Stacks Project Section 10.79 (Tag 05GD), Lemma 10.79.4(3), and
Tag 0BDP. No statement or definition was changed and no forced adaptation is needed.

## Second reading by J3

1. **Public interface: pass.** Read the entire delivered module and compared it with
   the repository file using `diff -u`. Independently compared the text from the existing
   theorem name through its type, before `:= by`: byte-for-byte identical. In particular
   `hU : IsAffineOpen U`, both `Finite` hypotheses, both unrestricted free frames, the
   universe `u`, and the existential basic-open equality are retained. The two public
   imports and visibility are unchanged. No definition or existing declaration besides
   the theorem proof was changed; the eight added helpers are private proved theorems.
   No interface change record is needed.

2. **Proof and axioms: pass.** Independently compiled the delivered file with
   `lcompile.py` (4.4 seconds, no warnings or errors). A scratch copy printed axioms for
   all eight helpers and the public theorem: each uses exactly `propext`,
   `Classical.choice`, and `Quot.sound`, with no `sorryAx`. Searched the delivered Lean
   for `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, and `extern`: none occur.
   The determinant is explicitly constructed from the given frames. Reindexing uses
   the proved finite-cardinality equivalence, not an unproved existence witness.
   The forward inclusion constructs invertibility on the determinant basic open;
   the converse evaluates the square matrix over the residue field. The unequal-rank
   branch obtains an actual point before using field finrank, so it also handles the
   empty scheme. For rank zero the square determinant is one. No reducedness or
   nonempty-index assumption is hidden in either branch.

3. **Split-off statements and shorter tools: pass.** There are no split-off statements,
   new nodes, or new holes. Read the imported square free-map inverse theorem and
   pullback-preservation theorem: their hypotheses supply exactly what the calls need.
   Searched Mathlib, upstream, and `lean/` for the principal-open identity and for
   determinant/free-matrix tools. The existing inverse theorem is reused; the similar
   `freeMatrix_restrict` in `LocalInvertibleMinorBlockData` is private and unavailable
   as a public tool. No existing public theorem was found that supplies the full
   basic-open equality. Read Stacks Tag 05GD, Lemma 10.79.4(3) and its matrix proof,
   and Tag 0BDP's final determinant paragraph: the finite-free determinant argument
   agrees with those sources. No new statement requires a source, search log, or node.

4. **Route and pruning: pass.** Followed the public proof through the equal-cardinality
   reindexing, the two subset lemmas, and the unequal-cardinality contradiction. This
   opens the original hole directly and uses proved tools rather than moving it into
   another statement. Both original public imports support the unchanged interface.
   The two added Sheaf imports supply the explicitly used preservation and inverse
   theorems. Scratch removal tests for the other added imports fail: removing
   `Restrict` loses `isUnit_ι_appTop_basicOpen` and `isField_Γ_Spec`; removing
   `ResidueField` loses `fromSpecResidueField`. Thus all four added imports are
   proof-only and needed. The only removed old proof dependency is
   `def-weil-affine-spectrum`, already listed under No longer needed; no imported
   module was pruned. Opened `dag/units/sk-prop-av-cube.json`: its realization lists
   do not name this node, and its fixed cube statement and step are untouched.

5. **Node agreement: pass.** Compared the old and delivered node JSON: precisely
   `proof`, `proof_deps`, and `proof_origin` differ. Checked that `proof_deps` is exactly
   the union of the steps' `uses`. The five steps match the concrete determinant
   construction, restriction inverse, image-open comparison, residue-field converse,
   and unequal-rank contradiction in the Lean. The statement, statement dependencies,
   Lean signature record, source, unit, and blueprint metadata are unchanged.

Second reading changed only this report by adding the independent review. No Lean or
node repair was needed. Confirmed holes closed: 1; holes added: 0; split off: 0.
