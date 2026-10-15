## What changed

Current second reading: removed six further copied private helpers from the main
module (`resolutionHomotopyZero`, `resolutionHomotopy`, `map_cycle`,
`map_cycle_val`, `map_cycle_class`, `computingClass_naturality`). Reuse the
existing `computingClass_naturality` through a proof-only `import all
Sheaf.Paper.ModuleCupCoefficientResolutionMaps`. Its hypotheses concern only the
supplied computing resolutions and coefficient map; this use assumes no Godement
existence theorem. Removed the now-redundant direct proof import of
`WeilConjectures.Mathlib.CategoryTheory.Abelian.Injective.Resolution`. Updated the
main node's proof route and proof dependencies. All signatures in the submitted
set are unchanged by this second reading.

Latest landing return repaired: both comparison modules had identical private
`d_transport` theorems. Removed both copies. `pairRightMap` now uses Mathlib's
`HomologicalComplex.d_comp_eqToHom`; `leftZeroMap` uses Mathlib's
`CategoryTheory.eqToHom_naturality`. Both files compile without warnings
(9.9 seconds and 39.2 seconds). This repair changes only the two transport
proofs and removes their duplicate helpers; it adds no declarations, imports,
statements, nodes or holes. The prior second reading is saved in scratchpad
because it predates this repair; the next reader supplies the current review.

Repair of the returned scalar cup sign delivery. The scalar resolution comparison
retains the corrected factor `(-1 : ℤ) ^ (p * q)` on its target resolution class.
The scalar/module cup, scalar external/module cup, and both canonical scalar Cech
comparison statements carry the corresponding factor. Their proofs and the
constructive proofs of both degree-zero axes are retained.

This repair changes where the factor stops propagating. In
`PicardRightCechCupCycleComparison`, the factor and product comparisons keep their
canonical normalization; its conclusion now explicitly multiplies the product
image by `(-1)^(p*q)`. Its direct caller `PicardRightCechCupGenerators` keeps its
entire original public signature. Its existential equivalence is precomposed
with the direct sum of the unit scalar automorphisms `(-1)^(p*q)` on the `(p,q)`
tensor-homology summands. `summandSignEquiv` constructs that equivalence using
`LinearEquiv.smulOfUnit` and `DirectSum.congrLinearEquiv`;
`summandSignEquiv_lof` proves its value on every summand inclusion. Moving the
integer scalar through the linear comparisons gives precisely the signed cycle
formula, so the generator conclusion remains unsigned. These two helpers are
private and fully proved. The sign is one on both degree-zero axes and in
characteristic two; zero factors and empty schemes need no special hypotheses.

The repaired set has seven Lean modules. No external-cup normalization definition
changes. In particular `IsPicardExternalCupCochain` and
`IsPicardExternalCupHomology` keep their original unsigned formulas. The higher
left generators and Kunneth theorem therefore retain their original statements
and proof bodies. No target statement, definition, universe or binder changes.
All adapted caller modules are unclaimed in the local claims snapshot. The unit
route remains the theorem-of-the-cube / Picard / Kunneth route.

The cycle-comparison node now records its corrected statement and its direct
citer; the generator node records the summand normalization proof. The other
node records retain the signed scalar comparison route. Change record:
`coord/changes/K1-scalar-cup-resolution-koszul-sign.md`, with all six changed
old/new signatures and every downstream user.

## Proved and sorry left

The corrected
`AlgebraicGeometry.Scheme.Modules.scalarCup_resolution_class_compatibility`
(node `new-sc-scalar-cup-resolution-class-compatibility`) has a complete case
proof. Its original unsigned statement is not claimed proved. The two boundary
cases are proved without holes by private helpers
`scalarCup_resolution_right_zero` and `scalarCup_resolution_left_zero`.
This remains the earlier decomposition: one original upper hole is closed and
one strictly positive-degree hole is added, net zero. This repair adds no further
holes or split modules.

The only delivered `sorry` is
`AlgebraicGeometry.Scheme.Modules.scalarCup_positive_resolution_class_compatibility`
in `Sheaf.AlgebraicGeometry.ScalarCupPositiveResolutionClassCompatibility`, node
`new-sc-scalar-cup-positive-resolution-class-compatibility`. It still needs the
localized tensor/Yoneda identification for two positive-degree classes. Its
private tail map, signed cochain, closedness proof and injective-cocycle class
formulas are actual constructions and complete proofs. The residual theorem's
source and full natural-language argument remain in its docstring and node.

All six direct caller theorems in this delivery have complete Lean proofs from
the corrected comparison, with no additional `sorry`:
`scalarCup_moduleCup_compatibility`, `scalarExternalCup_moduleComparison`,
`picardScalarCech_externalCup_core`, `picardScalarCech_externalCup`,
`picardRightCechCup_cycle_comparison`, and `picardRightCechCup_generators`.

Compiled all 26 modules in the affected chain in import order using only
`lcompile.py`, one file at a time. All passed with no warnings. This includes the
seven delivery modules and 19 temporarily copied, byte-identical caller/interface
modules. Both reported failing consumers, `PicardExternalCupLeftCechGenerators`
and `PicardKunnethCechModels`, compile unchanged (3.8 and 3.4 seconds). The shared
cochain/homology predicates, both Cech homology ladders, quasi-isomorphism proof,
and upper quasi-coherent Kunneth modules also compile unchanged. The main file
takes 41.0 seconds, below the fixed 60-second limit. The unchanged copies have
been removed from the delivery. As a countercheck, the original
`PicardRightCechCupGenerators` fails against the signed cycle comparison at its
final `simpa`: the available formula has `(-1)^(p*q)` multiplying its left side,
while the unchanged goal is unsigned. The adapted proof compiles and preserves
the original signature. Nothing is pushed by this worker.

## No longer needed

Second reading also removes the six duplicate private naturality helpers listed
above and the main file's direct import of
`WeilConjectures.Mathlib.CategoryTheory.Abelian.Injective.Resolution`.
Their existing implementation in `ModuleCupCoefficientResolutionMaps` is reused;
that module is now a proof dependency, not a newly stated result.

The duplicate private `d_transport` declarations in
`ScalarCupResolutionClassCompatibility` and
`ScalarCupPositiveResolutionClassCompatibility` are removed. Existing Mathlib
transport lemmas supply both uses, so no shared helper module is required.

The main proof removes these original audit-only imports and nodes:

- `Sheaf.Paper.ModuleCupShiftedUnitChainTensor`,
  `lem-sc-module-cup-shifted-unit-chain-tensor`;
- `WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex`;
- `Mathlib.Algebra.Homology.BifunctorShift`, attached to
  `def-pc-tensor-complex-sheaves`.

The four obsolete private audit declarations are removed:
`scalarCup_yoneda_order`, `oddShiftTensor_component`,
`oddTensorSummand_ne_neg`, and `oddShiftTensor_not_unsigned`.
The audit remains in the repository baseline for review. These modules may still
be needed by other parts of the library.

This repair removes the previous cycle-comparison proof's imports of
`Sheaf.AlgebraicGeometry.ExternalCupScalarBalance` and
`Mathlib.Data.Nat.Choose.Vandermonde`, its six private degree-rescaling/bilinearity
helpers, and the proof dependency `lem-sc-external-cup-scalar-balance`.
The direct-sum unit equivalence replaces that rescaling argument. It uses the
existing DirectSum imports; no new proof import or module is needed.

In `lem-sc-scalar-external-cup-module-comparison`, the original proof dependencies
`def-sc-field-linear-module-cohomology-operations`,
`def-sc-module-cup-resolution-data`, and
`def-weil-pbc-module-cohomology-fmap` are not used by the proof; their public
imports remain necessary for the unchanged hypotheses and coefficient types.
The proof directly uses scalar/module cup compatibility and scalar/module
pullback comparison. No unit statement or proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The latest return correctly identified the two identical `d_transport` helpers.
A successful file compile did not detect that duplication. Both uses now invoke
the existing Mathlib API directly, resolving the reported landing refusal.

The original resolution statement and canonical scalar Cech formulas omitted the
Koszul factor under the library's left-then-right Yoneda convention. The route
note explicitly authorizes this correction. The original private audit proves
the product order and the chain-level `(1,1)` sign, including a nonzero rational
test; it does not establish the complete positive-degree localization comparison.
The remaining positive-degree obligation is therefore reported honestly.

The return reports two incompatible normalization expectations: the left Cech
generators expected a signed image from an unsigned homology predicate, and
`PicardKunnethCechModels` expected an unsigned image from a signed cochain
predicate. Propagating a bidegree factor into those shared predicates breaks
their unchanged callers. This repair absorbs the factor before either predicate
is reached, in the generator equivalence, and keeps both predicates unchanged.
The canonical cycle formula remains explicitly signed. This is an actual Lean
proof and interface repair, not an unchanged re-push.

The old cycle node's `lean.statement` accidentally included part of its proof.
It now records only the complete corrected signature. Search before proving
included LeanFinder, Loogle and local Mathlib/library searches; no existing
all-degree scalar resolution comparison was found. Loogle did not recognize the
unqualified `InjectiveResolution.extMk` query; no absence conclusion is inferred.

## New nodes

The inherited node
`new-sc-scalar-cup-positive-resolution-class-compatibility` states only `p>0`,
`q>0`; the parent proves both axes independently. It retains the constructive
tail map, signed closed cochain and injective-cocycle class formulas. Its remaining
step identifies the localized cochain with the right Ext class transported by
tensor and the coefficient morphism; composition then evaluates its degree-p
component. This repair creates no additional nodes or holes.

Change record: `coord/changes/K1-scalar-cup-resolution-koszul-sign.md`.

## Second reading by K1

1. Compared every delivered module with the read-only repository using `diff`
   and the declaration parser. Verdict: all six changed existing signatures are
   exactly the old/new signatures declared in the sign change record; every
   binder, hypothesis, coefficient, and degree is otherwise retained. The
   generator theorem's signature is unchanged. There are no changed definitions
   or target statements. The six callers' changes propagate the corrected sign
   and stop it at an explicitly constructed existential generator equivalence.
2. Read every delivered proof and construction and compiled the set in import
   order using only `lcompile.py`. The only direct hole is the named public
   positive-degree comparison listed above. No forbidden declaration mechanism
   or hollow definition is present. Explicit `#print axioms` checks on the two
   axes, positive cochain closedness and cocycle-to-Ext formula show only
   `propext`, `Classical.choice`, `Quot.sound`; the main comparison and callers
   additionally depend on `sorryAx`, as the report states. No all-degree proof
   is claimed independent of that remaining hole.
3. Read the positive-degree lemma's statement, docstring, node and constructions.
   Verdict: it is strictly the positive-bidegree remainder, since both zero axes
   have separate constructive proofs in the parent. Zero cycles or coefficients
   give zero; characteristic two makes the sign one. The closed cochain's
   component factor `(-1)^(n*q)` gives the required signed degree-p component.
   Exact tensoring of sheaves of k-vector spaces justifies the localization
   argument, with no flatness assumption on O-modules. Repeated searches with
   different LeanFinder and Loogle queries and local searches found only
   degree-zero extMk composition or generic exact-functor composition formulas,
   not the missing tensor/Yoneda comparison. The existing derived-module
   homology tensor API concerns ModuleCat complexes and does not identify these
   sheaf Ext classes. The remaining lemma cannot be closed by one of those
   APIs in a few minutes. The split has a source, full argument and matching
   node; it is a decomposition, not a net proof gain.
4. Followed the reduction from the target down through the degree split. Found
   six copied naturality helpers and replaced them with their existing theorem
   from `ModuleCupCoefficientResolutionMaps`; the main file compiles after
   removing the copied block. All new proof imports are ordinary imports,
   including the private-access imports. The original audit-only imports and
   removed dependencies are listed above. Read `dag/units/sk-prop-av-cube.json`:
   its statement and realized route are untouched, and the cube/Picard/Kunneth
   route is retained. No unit-level step is bypassed.
5. Compared all eight node records with their Lean declarations and proofs;
   checked that each `proof_deps` is exactly the union of step uses. Corrected
   the main node to record reuse of the existing resolution class naturality
   theorem. The new node has all required provenance, source, search, blueprint,
   Lean and status fields. Both the canonical cycle formula's sign and the
   generator's summand automorphism are reflected in their nodes. Verdict:
   metadata agrees with the delivered argument.

Changes by this reader: reuse the existing naturality implementation instead of
six private copies; remove its redundant direct Mathlib-wrapper import; update
the main node, search evidence and this report. No signature, definition, or hole
was added or changed by this second reading. The returned duplicate differential
transport helpers remain removed and use the existing Mathlib lemmas directly.

Source checks: [Stacks 0FKV](https://stacks.math.columbia.edu/tag/0FKV) supplies
the derived/Cech tensor comparison, and
[Stacks 01F7](https://stacks.math.columbia.edu/tag/01F7) describes comparison
functoriality. The bidegree sign is determined by this library's explicit
`scalarExtCup` order and Mathlib shift conventions, as audited in the original
module; neither Stacks page alone proves that convention-specific factor.

Final verification by this reader: all seven delivery modules compile cleanly
in import order (9.9, 35.3, 6.3, 6.0, 10.1, 19.0, 9.2 seconds).
Re-ran the explicit axiom checks against those freshly rebuilt sandbox artifacts;
the results above hold after the naturality reuse. Copied the original generator
and the two previously failing higher consumers into a scratch source root with
the final sandbox artifact overlay. The original generator fails exactly at its
unsigned final `simpa` against the signed cycle formula. The byte-identical
`PicardExternalCupLeftCechGenerators` and `PicardKunnethCechModels` compile
unchanged in 3.6 and 3.3 seconds. Scratch files are excluded from the delivery.
All old/new signatures in the change record were mechanically compared with the
actual declarations after whitespace normalization. No further signature change
or caller repair was necessary. No whole module is claimed globally pruned.
