## What changed

The existing statement of
`AlgebraicGeometry.exists_affineBaseChangeTildeCanonicalGlobalComparison` is unchanged.
Its proof now establishes that the tensor-algebra structure map is an isomorphism by
comparing the cartesian spectrum square with Mathlib's `pullbackSpecIso`. The private,
proved helper `tensorAlgebraMap_isIso` reflects that isomorphism through the fully
faithful spectrum functor. Restriction along the resulting ring equivalence makes the
extension/restriction unit invertible.

The proof constructs the source transport `t` from this unit and the natural
restriction-of-scalars comparison. It proves `t ≫ restrictScalars.map a = c` using
naturality and the fixed model's `localized_eq`. Composing tilde of the inverse of `t`
with the ordinary source comparison and cancelling `t` proves the desired square.
Proof imports added: `Mathlib.AlgebraicGeometry.Pullbacks` and
`Sheaf.Algebra.Homology.AffineBaseChangeTildeOrdinaryComparison`. All original public
imports and declaration signatures remain intact. The parent node's proof and
proof-dependency fields now describe this argument.

The new module isolates the ordinary affine mate computation for a square that merely
commutes. Its source is tilde of the restriction of `m.cohomology i`, and its arrow is
built from `m.comparison`, homology of `m.ordinaryToLocalized`, and the exact-restriction
homology comparison. It does not use `affineBaseChangeTildeModule`,
`affineBaseChangeTildeModuleMap` or `m.localizedComparison` in its statement. The parent
proves the independent cartesian tensor-algebra and adjoint-localization steps needed
to recover its actual source and arrow.

Both delivered modules compile together in import order without errors or warnings
through `lcompile.py --all`.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.exists_affineBaseChangeTildeCanonicalGlobalComparison`
(node `lem-pc-affine-base-change-tilde-canonical-global-comparison`). Its Lean proof is
complete from the ordinary-mate statement below.

Added one hole:
`AlgebraicGeometry.exists_affineBaseChangeTildeOrdinaryComparison`
(node `lem-pc-affine-base-change-tilde-ordinary-comparison`), in its own module, with
proof exactly `:= by sorry`, source, and complete proof in words in its docstring and
node. No sorry remains in the item's module; the new theorem is the only sorry in the
delivery. This is a decomposition: one hole closed and one added, net zero, not a
claim of an axiom-free proof of the mathematical theorem.

## No longer needed

No original imports were removed, and no globally pruned modules are claimed.
The parent's former direct proof dependencies
`lem-pc-affine-derived-cohomology-presentation`,
`lem-pc-affine-derived-pullback-tensor-tilde`, `lem-pc-affine-morphism-hi`,
`lem-sc-qcoh-acyclic-derived-pushforward-cohomology`,
`lem-weil-pbc-tilde-pullback-base-change`, and `def-pc-derived-base-change-map`
are needed by the new ordinary-mate lemma and are recorded there. They are delegated,
not pruned. The parent retains the tensor-model and coordinate nodes and adds the
Mathlib affine fibre-product node and the ordinary-mate node.

The earlier sandbox-only helper modules
`AffineBaseChangeTildeCanonicalGlobalComparisonD` and
`AffineBaseChangeTildeCanonicalGlobalComparisonE` were removed; neither had a DAG node
or an admissible finished delivery. They are not library pruning.

## Where the brief, the DAG or earlier work was wrong

The previous sandbox inserted `obtain` and `exact` into the theorem's type, before
its existential conclusion, and left the original `sorry`. Its new helper modules
lacked source/proof docstrings and DAG nodes. Its D helper redundantly assumed the
whole cartesian setup just to assert existence of d with `True`; its E helper assumed
an arbitrary natural d without a normalization justifying its mate equation. The
previous report's assertion that the target had been proved was inaccurate. These
files were replaced, not preserved as a delivery.

The remaining ordinary-mate lemma does not assume cartesianness. Edge cases were
checked conceptually: zero complexes make all displayed arrows zero; zero rings and
empty spectra use the same functors. For a noncartesian example, take
R=A=B a field and D the zero ring. The ordinary source is still the cohomology over B,
and its map to the zero target is legitimate; extension of that source to D would
be zero and would not identify the source sheaf. Thus the new lemma does not simply
repackage the original source comparison: cartesianness is precisely what the
parent's proved ring-isomorphism argument adds. No boundedness, Tor independence,
flatness of A over R, or invertibility of the base-change map is assumed.

The source proof uses the existing generic module K-flat resolution node
`lem-pc-source-module-kflat-resolution` as a tool; its source declaration in
`WeilConjectures.CategoryTheory.DerivedCategory.FlatModel` is already proved. No unit's
own statement or realized proof step is bypassed. The unit's realized lists are empty.
The nearest blueprint ancestor was traced through the parent and global-comparison
nodes to `lem-pc-rf-perfect-base-change`; its current proof's affine input is recorded
in the new node's blueprint field. Blueprint searches for `affine base change` and
`0DJ8` found no duplicate; the broader tensor search was also read.

A read-only dependency-graph check also found ten cycles already reachable from the
original parent node, including the sheaf-algebraic-structures object/component cycle
and the horseshoe/derived-long-exact cycle. Comparing the baseline with the delivered
node overlay found no newly introduced cycle. These inherited DAG issues are reported
for the maintainer; this delivery does not edit their nodes.

## New nodes

`lem-pc-affine-base-change-tilde-ordinary-comparison`, at
`dag/nodes/sec-picard-framework/lem-pc-affine-base-change-tilde-ordinary-comparison.json`,
records the ordinary affine derived mate calculation before source scalar extension.
Its module is
`lean/Sheaf/Algebra/Homology/AffineBaseChangeTildeOrdinaryComparison.lean`.
Sources read: Stacks Tag 0DJ8, `perfect.tex`,
`lemma-single-complex-base-change-condition`, its affine proof and `equation-bc`;
Tag 06Y6, `more-algebra.tex`, `lemma-derived-base-change`; and the pinned mate
construction of Tag 08HY, `cohomology.tex`, `remark-base-change`. The latter is exposed
by the existing `derivedBaseChange_unit_compatibility` statement. The new node cites
that statement, the source resolution theorem, the affine pullback and natural
pushforward comparisons, and the fixed tensor-model equations.

Actual Mathlib searches are logged in `searches.jsonl`: LeanSearch was unavailable
(Internal Server Error); LeanFinder returned cotangent/ordinary-flat-base-change
results, none matching this mate calculation; grep returned the generic
`leftDerived_fac_app` declarations, not an affine mate theorem. Local library searches
also found the already existing affine extension/sections unit-mate result, which
concerns a different adjunction and does not state this direct-image comparison.
No change record is needed: no existing definition, statement or visibility changed.

## Second reading by J4

1. Interface preservation: PASS. Compared the only existing delivered module with
   the repository using diff. Its existing theorem signature is byte-for-byte
   identical, including the existential conclusion and all hypotheses. No existing
   definition, visibility, public import or file-level option changes. The only
   existing node changes are proof, proof_deps and proof_origin. No change record
   or forced adaptation is needed.
2. Proof and trust: PASS as a decomposition. Both delivered modules compile through
   lcompile.py in import order without errors or warnings. A scratch-copy
   #print axioms check gives only propext, Classical.choice and Quot.sound for
   tensorAlgebraMap_isIso; the parent and ordinary lemma additionally have sorryAx.
   The only new direct hole is the public named ordinary theorem with whole proof
   `by sorry`. No definition or private helper has a hole, and no prohibited trust
   mechanism occurs. The parent constructs t explicitly from an adjunction unit;
   it does not define data by choosing a witness of the new existence theorem.
3. Split statement: PASS. Read the ordinary theorem, its complete proof docstring,
   node, fixed model comparison_eq/localized_eq, target coordinate, unit-normalized
   tensor-pullback theorem and derived mate unit-compatibility theorem. Read Stacks
   Tags 0DJ8, 06Y6 and 08HY. The ordinary lemma is the source identification and
   ordinary mate step before scalar extension; the parent independently proves
   coefficient invertibility, adjunction transport and cancellation. Tested zero
   complexes, identity squares, zero-ring spectra and the noncartesian field-to-zero
   square conceptually. The source is independent of the upper-left coefficient
   ring; no assertion of source-extension invertibility is made by the new lemma.
   Searched again with different terms using LeanFinder, grep and Loogle, and rg
   on the library: ordinary sheafification/pullback and adjunction-unit results
   were found, but no existing affine derived mate formula closes this hole.
   The remaining calculation requires derived-functor/counit coherence and is not
   a few-minute theorem closure. One upper hole closed, one lower hole added:
   net zero, counted as decomposition, not an axiom-free proof.
4. Route and pruning: PASS. The parent takes Mathlib's pullbackSpecIso and fully
   faithful spectrum reflection directly, and uses the ordinary mate only for the
   remaining affine computation. Added imports are proof-only plain imports.
   Existing public imports supply the signature's coordinates, scheme mate and
   K-flat predicate. Each public import in the new module supplies its statement.
   Checked all eight old proof dependencies: the two coordinate/model dependencies
   remain direct, and the six listed under No longer needed move to the ordinary
   lemma's plan; none is globally pruned. The unit sk-thm-picard-semicon has
   realized = {statement: [], steps: [[]]}; no realized unit node is bypassed.
5. Node agreement: PASS. The parent node records the ring-isomorphism argument,
   the ordinary comparison application and localized_eq cancellation, exactly as
   the proof does. The ordinary node has its source, self-contained statement,
   dependency union, proof steps, search records, creation and blueprint ancestry,
   chapter/unit and verbatim Lean statement. Its dependencies describe the pending
   ordinary calculation rather than claiming it has been proved.

Second-reader changes: removed the unused local f and g in the private helper;
restored exact whitespace before the existing theorem's proof delimiter; appended
independent search evidence to the ordinary node and this review to the report.
No mathematical statement changed. No additional hole was closed or added.
