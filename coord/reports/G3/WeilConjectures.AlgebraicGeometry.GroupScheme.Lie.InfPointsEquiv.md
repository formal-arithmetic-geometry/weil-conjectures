## What changed

Replaced the sole sorry in
`WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.InfPointsEquiv`,
`AlgebraicGeometry.GrpObj.lieEquiv_mul`, by a complete Lean reduction.
The product map on two dual-number thickenings restricts on its diagonal to
`v * w`. Its axis restrictions are `v` and `w`, proved using the two unit laws
and the defining kernel condition. A private, proved equality-transport helper
handles the dependent pullback domains without unfolding the scheme constructions.
The original signatures, visibility, definitions, and docstrings are unchanged.

Added two modules:
`Sheaf.AlgebraicGeometry.GroupScheme.DiagonalTangentAddition` and
`Sheaf.AlgebraicGeometry.GroupScheme.DiagonalDerivationCoefficients`.
The former proves `omegaHom_diagonal_add` from the latter's sectionwise
coefficient identity. The universal-differential factorization equations prove
that `desc` preserves these coefficient sums; additive sheafification and
pullback-pushforward adjunctions then prove additivity of `homOfDerivation`.
Equality induction identifies transported `omegaHom` with this construction.
The sole unfinished step is now the geometric diagonal coefficient calculation.
It applies to arbitrary schemes over a base and contains no group structure,
Lie equivalence, differential universal property, or adjunction in its conclusion.

The item adds one proof-only import of `DiagonalTangentAddition`; that module
imports `DiagonalDerivationCoefficients`, `PointOfDerivation`, and the Mathlib
additive-adjunction module for its proofs only. The new modules publicly import
`InfPoints`, which supplies their statement types. No existing interface changes
or forced adaptations are made. Local compilation of all three modules succeeds.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.GrpObj.lieEquiv_mul`
(node `lem-ag-lie-equivalence-multiplication`).
There are no sorries left in the item's module.

Proved `AlgebraicGeometry.GrpObj.omegaHom_diagonal_add`
(node `lem-ag-dual-numbers-diagonal-tangent-addition`) from the coefficient identity,
including the additive universal-property and adjunction glue in Lean.
All private helpers in the delivery are proved.

Added exactly one hole:
`AlgebraicGeometry.GrpObj.infDerivation_diagonal_coefficients`
(node `lem-ag-dual-numbers-diagonal-coefficients`), in its own module.
Its whole proof is `:= by sorry`; its docstring contains the source and a complete
sectionwise argument, including the product comparison and equality transports.
This is a decomposition, not a sorry-free proof of the original theorem.
Holes closed: 1; holes added: 1; net: 0.

Edge cases checked mathematically before stating the new lemma: empty base and
zero section rings, constant maps (both coefficients vanish), restriction to
one factor (the other coefficient vanishes), arbitrary characteristic including
2, and nonsmooth schemes. The proof needs neither reducedness nor smoothness.

## No longer needed

No original imports, modules, or DAG nodes were removed. No unrelated planned
lemmas were imported. In the new coefficient module, `PointOfDerivation` is not
needed and its public import was reduced to `InfPoints`. In the new tangent
addition module, `PointOfDerivation` is proof-only; `InfPoints` alone supplies
the public statement interface. This does not prune an existing target-closure
module, because the original item still needs `PointOfDerivation`.

## Where the brief, the DAG or earlier work was wrong

The files matched by a text search for the item's module mention it in their
`lean_audit` open lists, but none records `lieEquiv_mul` as its main `lean`
declaration. Consequently there is no numbered DAG proof plan for this hole.
The delivery attaches a new node to the existing declaration and records the
actual two-step group-unit-law and diagonal-addition argument there. The unit
`sk-d-tangent` is retained, with no bypass of a realized unit step.

`DualNumbersDiagonal` proves equality on the diagonal from equality on the
axes; it does not provide a statement relating the three derivation coefficients.
`LieIdentityTangentEquiv` imports `Lie.Ring` and depends on this item, so using it
would create a cycle. Mathlib search found no scheme-level shortcut; its additive
adjunction lemmas are used in the proved glue. LeanSearch returned Internal Server
Error; this is recorded as unavailable, not as evidence of no match.

## New nodes

`lem-ag-lie-equivalence-multiplication` attaches the original, now reduced theorem
to a DAG node. Its proof depends on tangent addition and explicitly proves both
axis restrictions from the group unit laws. No existing node is changed.

`lem-ag-dual-numbers-diagonal-tangent-addition` records the proved passage from
sectionwise coefficient addition to addition of pulled-back cotangent morphisms.
Its only proof dependency is the coefficient node.

`lem-ag-dual-numbers-diagonal-coefficients` states the remaining square-zero
coefficient identity for an arbitrary morphism from the product of thickenings.
Its proof in words follows the sectionwise version of Stacks Project Tag 0B2B,
whose source text was read. Each new node is in
`dag/nodes/sec-algebraic-groups-lie-algebras/`, belongs to `sk-d-tangent`, and
names its Lean declaration and exact signature. No change record is needed.

## Second reading by G3

1. Interface preservation: PASS. Read the complete diff of the existing item
   against the repository version. Every existing declaration signature,
   definition body, visibility, and docstring is byte-for-byte unchanged.
   The changes are one proof-only import, a proved private transport helper,
   and the proof of `AlgebraicGeometry.GrpObj.lieEquiv_mul`. The two other
   delivered modules are new. No target, change record, or forced adaptation
   is involved.

2. Proof and trust: PASS as a decomposition. Independently compiled all three
   modules in import order through `lcompile.py`, without errors or warnings.
   Scratch copies with `#print axioms` checked all public declarations of the
   item, all three private helpers, and both new public theorems. The helpers,
   the bijection, and `lieEquiv` use only `propext`, `Classical.choice`, and
   `Quot.sound`. The coefficient theorem, tangent-addition theorem,
   `lieEquiv_mul`, and its two consequences additionally use `sorryAx`, as
   expected from the one explicitly reported coefficient hole. There is no
   forbidden declaration or annotation, hollow definition, or new data choice.
   The sole remaining `sorry` is the whole proof of the named public theorem
   `AlgebraicGeometry.GrpObj.infDerivation_diagonal_coefficients`.

3. Split statement: PASS. Read the coefficient theorem, its complete docstring
   argument, its node, and the definition of `infDerivation`. For a section of
   the iterated thickening write the four coefficients as a,b,c,d. The axis
   coefficients are b and c; substituting both infinitesimals by epsilon gives
   a+(b+c)epsilon, with d killed by epsilon squared. This verifies constants,
   either axis, characteristic 2, zero rings, empty schemes, and arbitrary
   nonsmooth bases. The equations of reductions supply the necessary dependent
   transports; proof irrelevance makes their witnesses immaterial. This is a
   geometric section calculation with no group or Lie-equivalence conclusion,
   strictly a part of the original argument. The supplied Lean proof already
   closes the group-unit-law and differential/adjunction parts. Read the
   [Stacks source](https://stacks.math.columbia.edu/tag/0B2B): it gives the
   square-zero addition calculation over a residue field; the node and proof
   explicitly explain its sectionwise arbitrary-base extension.
   Independent searches used Loogle `TrivSqZeroExt.snd, HAdd.hAdd`, LeanFinder
   with an arbitrary-base diagonal-coefficient query, and `rg` for derivation,
   diagonal, and tangent-addition variants in both library roots. The returned
   ring coefficient and affine diagonal lemmas do not prove the stated scheme
   coefficient identity. The upstream item also leaves `lieEquiv_mul` open.
   No existing replacement was found; completing the remaining scheme-section
   transports is not a short repair, so the reported single hole is retained.

4. Route and pruning: PASS. Read `DualNumbersDiagonal`, `InfPoints`, and
   `PointOfDerivation`, and checked each delivered import against its uses.
   The existing diagonal lemma compares maps with equal axes; it does not
   assert coefficient addition. The proof uses the two group unit laws before
   applying the new tangent-addition theorem, whose universal-property and
   additive-adjunction glue is fully proved. Proof-only imports are plain
   `import`; public imports supply the public statement types. There were no
   old recorded `proof_deps` for this hole to prune, and no original imports
   were removed, as `## No longer needed` records. The `sk-d-tangent` unit has
   empty `realized.statement` and `realized.steps`; no realized unit route is
   bypassed or changed.

5. DAG consistency: PASS. Read all three new nodes and their Lean declarations.
   Their signatures match; the item depends on tangent addition, which depends
   on the coefficient identity. The coefficient node records the iterated
   thickening calculation and transports rather than an application of the
   original theorem. Their proof steps, dependency unions, proof origins,
   source citations, searches, creation metadata, chapter, unit, and Lean
   records describe the delivered argument. Existing DAG nodes are untouched.

Second reading changed only this report: added the independent checks, axiom
results, fresh searches, source qualification, and explicit decomposition
verdict. No Lean or node repair was needed. The delivery still closes one
original hole and adds one strictly intermediate hole, with net zero holes.
