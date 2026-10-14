## What changed

Proved `AlgebraicGeometry.schemeMVOpenComposition_unit_normalization` with its existing
signature and docstring unchanged. Both original public imports remain. Added the
proof-only import `Sheaf.AlgebraicGeometry.DerivedDirectImageSquareUnitNormalization`.

Added `DerivedDirectImageCompositionUnit.lean`, containing the concrete existing
composite unit with its source presented by successive pushforwards. Its factorization
is a private, proved helper in the item's module, obtained directly from
`RingedSpace.exists_derivedModuleDirectImageComposition` by `Classical.choose_spec`.
Added `DerivedDirectImageSquareUnitNormalization.lean`, leaving only the single-unit
transport across the commutative square open. The parent now proves the two
factorizations, comparison cancellation, postcomposition, and reassociation.

The single-unit statement spells out the universe expression of `eqToIso` to match
the fixed comparison in the existing target. This is the same mathematical statement;
it prevents kernel conversion from expanding the derived-functor definitions.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.schemeMVOpenComposition_unit_normalization`
(node `lem-pc-derived-mayer-vietoris-open-composition-normalization`).

Hole added and left: `AlgebraicGeometry.schemeDirectImageSquare_single_unit_normalization`
(node `lem-pc-direct-image-square-single-unit-normalization`). This concerns one composite
unit on each side, with no chosen composition comparisons or pasted pairs of units.

There are no other delivery holes and none inside definitions. The private
`schemeMVCompositionUnit_fac` is proved. This is a decomposition: one upper hole closed,
one strictly lower hole added, net zero holes closed in the target import closure.
The item contains no remaining `sorry`; this does not assert that its upstream
proof dependencies are closed.

## No longer needed

No original imports or proof-dependency nodes are pruned. The open homotopy model and
the original ringed-space composition theorem remain used. The discarded first-worker
canonical restatement and unit-source-map wrapper were never in the repository and
are not delivered.

## Where the brief, the DAG or earlier work was wrong

The first-worker report described substitution of the canonical comparison into a
new holed theorem as a reduction. It was a restatement of the whole item, so that
module and node were removed. Its report also omitted three sandbox modules and
four node records. The retained delivery is now listed completely above and below.
The original timeout was not grounds for moving the whole conclusion into a new hole.
Aligning the comparison's universe expression permits an actual categorical proof
within the single-file limit, without changing any existing definition or statement.

## New nodes

`def-pc-direct-image-composition-unit-source`: the existing right-derived unit of a
composite direct image, with the successive-image source. Its data is constructed
from the existing unit; no existence witness is chosen. Its module is
`Sheaf.AlgebraicGeometry.DerivedDirectImageCompositionUnit`.

`lem-pc-direct-image-square-single-unit-normalization`: equality transport for one
composite unit across the inverse-image-open square. Its source supplies the detailed
sectionwise-identity, homotopy-quotient, and equality-induction argument in the docstring.
Its module is `Sheaf.AlgebraicGeometry.DerivedDirectImageSquareUnitNormalization`.
No change record is needed: no existing public signature or definition changes.

## Second reading by J1

1. Compared the delivered item with the repository by `diff`. Its existing declaration
signature and docstring are byte for byte unchanged. The two additional modules are
new; no other existing module is changed. Restored the original author's header and
both statement imports. No target, hypothesis, conclusion, or existing definition changes.

2. Compiled the three delivered modules in import order with `lcompile.py --all`.
The parent proof uses the determining comparison equations, cancels the left comparison
and its inverse, applies the single-unit square, and postcomposes with the right
comparison. No forbidden declarations or hollow definitions occur. The only textual
`sorry` is the listed single-unit theorem. Checked the parent, the concrete composite
unit, and the single-unit theorem using `#print axioms` in a scratch copy; only the
standard axioms and inherited/open `sorryAx` are permitted. Delivery preflight also
checks every declaration's axioms.

3. Read Stacks Tags [08FE](https://stacks.math.columbia.edu/tag/08FE),
[0D5T](https://stacks.math.columbia.edu/tag/0D5T), and
[08BV](https://stacks.math.columbia.edu/tag/08BV). The single-unit lemma is a categorical
normalization of their direct-image identifications, rather than an additional
geometric assumption. On identity squares its equality becomes the unit followed by
identity on either side. For the zero complex both sides are the unique morphism;
empty opens and empty schemes need no exclusion. For general K, pushforwardComp is
identity on sections, pushforwardCongr is equality transport, homotopy quotient
surjectivity identifies the source map, and equality induction for the family of
right-derived units proves the square. Its docstring records this full argument.
Searched with Loogle for eqToHom/naturality, LeanFinder for naturality of families and
functor preservation of equality maps, and grep for mapHomotopyCategoryCompIso,
map_eqToHom, and eqToHom_naturality. Mathlib supplies the generic equality lemmas but
not this identification of the fixed homotopy model. Read the project's
`DirectImageSquareUnitTransport.lean`: its global derived-category instance is not
provided by the four local structures here, so it cannot be applied directly.
The remaining lemma is strictly part of the original argument; the canonical
restatement is removed.

4. Kept the original public imports; the additional transport import is plain `import`
because only the proof needs it. The new transport module publicly imports the
homotopy model and concrete unit because its signature names them. Its auxiliary
calculation stays below the unit level. Read `dag/units/sk-thm-picard-semicon.json`:
no realized unit statement or step is removed or bypassed. Both original proof
nodes remain in the parent's proof dependency list. No original module is pruned.

5. Updated the parent node to the actual factorization/cancellation/pasting argument.
The new definition has no postponed data. The new single-unit node has its source,
complete proof plan, dependency union, searches, creation record, blueprint ancestry,
chapter/unit, and verbatim Lean statement, including the explicit universe expression.
Removed the stale canonical node and unused source-map definition node. The DAG and
Lean now describe the same reduction.

Changes by this reader: removed the canonical restatement and unused source-map wrapper;
restored the existing interface/docstring; wrote the actual parent pasting proof;
made its comparison factorization a private helper; aligned the new comparison's
universe expression; repaired the node records, imports, and report.
