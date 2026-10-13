## What changed

The unchanged theorem `AlgebraicGeometry.Scheme.strictPerfect_relativeTensor_terms_flat`
is reduced to flatness of each base-flat module restricted to the localized open site.
The original module constructs the actual ring map, restricts the complex, extracts
finite free retractions from `IsStrictlyPerfect`, proves flatness of every tensor
summand, and assembles the total term using coproduct preservation and flatness.
Integer-pair indices are lifted to the sheaf universe and then canonically reindexed.

Added `RelativeFlatOpenScalarRestriction` for the remaining geometric comparison and
`ScalarRestrictedTensorRetractFlat` for the algebra step. The latter has a complete
proof: identify the tensor of a finite free module with copies of its second factor,
restrict scalars, apply coproduct flatness, and transfer through the given retraction.
Scalar restriction preserves coproducts by reflection through the forgetful functor
to abelian sheaves; its private proof is included in each module where it is used.
All new imports in the original module are proof-only imports. Existing signatures,
visibility, definitions, docstrings and public imports are unchanged.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.strictPerfect_relativeTensor_terms_flat` (node
`lem-pc-strict-perfect-relative-tensor-terms-flat`).

Proved the new auxiliary theorem
`SheafOfModules.isFlat_scalarRestricted_tensor_retract` (node
`lem-pc-scalar-restricted-tensor-retract-flat`), including its scalar-restriction
coproduct preservation helper. The original module's helper is also proved.

Added exactly one hole:
`AlgebraicGeometry.Scheme.relativeFlat_open_scalarRestriction` (node
`lem-pc-relative-flat-open-scalar-restriction`). Its entire proof body is `by sorry`;
its docstring supplies the stalk identification and exactness argument. It is a
single-module geometric statement, independent of complexes, totalization and finite
free retractions. It is strictly only the first step of the original argument.

This is a decomposition: one original hole closed, one strictly smaller hole added,
net zero holes among declarations changed by this delivery. The tensor and total-sum steps are fully formalized. No holes occur
inside definitions, private declarations or the original proof.

## No longer needed

No original imports or modules are removed. No original dependency node is claimed
pruned: relative stalk flatness and pullback remain needed through the open-site
lemma; the tensor, perfectness and flatness definitions remain used.

Only the boundedness component `hL.1` is unnecessary for this termwise-flatness
argument. The finite free retractions `hL.2` suffice; no statement is changed.

## Where the brief, the DAG or earlier work was wrong

The original DAG's second step grouped the finite free retract argument, scalar
restriction of the total coproduct and stalkwise exactness into one unstated glue
step. The new interfaces separate the geometric stalk comparison from the proved
algebraic and totalization calculations. Both retain the original route; the unit
record has no realization that this reduction bypasses.

The supplied topological flatness criterion (Stacks Tag 05NE) and coproduct criterion
(Tag 03EU) were read on the Stacks website because this clone has no Stacks source
checkout. Searches of the existing Lean library found a private stalk-to-flatness
helper but no applicable public open-site relative-flatness theorem. The broad
LeanSearch (unavailable), LeanFinder, Loogle and grep searches are recorded in `searches.jsonl`; none supplied
the needed complete geometric statement.

An accidental early write to the read-only clone was restored immediately, before
any delivery preparation. The final changes are all in this sandbox. An early
single-degree auxiliary proposal was discarded because it merely renamed the
original assertion; it is absent from this delivery.

## New nodes

`lem-pc-relative-flat-open-scalar-restriction` states the geometric first step for
one module on one open site, without quasi-coherence. Its proof uses the existing
relative module-stalk theorem and inverse-image/open-site stalk identifications,
then the tensor-stalk and stalk-exactness criteria. Zero modules and empty opens
were checked in its natural-language proof.

`lem-pc-scalar-restricted-tensor-retract-flat` states and proves the generic site
algebra step. It requires only a displayed finite free retraction and base-flatness
of the second factor; it assumes neither base-flatness of the algebra nor any
complex. Rank zero forces a retract of zero; the proof also includes a zero second
factor and the empty site. No arbitrary object is chosen from an existence theorem.

The original node's proof, proof dependencies and proof origin have been updated
to match the Lean assembly. No change record is needed because no existing interface
is changed.

## Second reading by D4

1. Interface check: compared all three delivered modules with the repository. Only
   StrictPerfectRelativeTensorTermsFlat already exists. Its theorem signature is now
   byte for byte identical, including whitespace before `:=`; its docstring, public
   imports, visibility and definitions are unchanged. The two auxiliary modules are
   new. The original node changes only `proof`, `proof_deps` and `proof_origin`.
   Verdict: pass; no change record or target-statement change is required.

2. Proof check: compiled the three-file set with lcompile.py in import order, and
   read both scalar-restriction colimit helpers, the tensor-retract proof and the
   total-term assembly. The helpers reflect colimits through the forgetful functor;
   the retract equation is preserved by both functors; the total coproduct is
   transported in the correct direction after ULift reindexing. Scratch-copy
   `#print axioms` checks cover both public proved theorems, the open theorem and
   both private helpers. The tensor-retract theorem and colimit helpers use only
   propext, Classical.choice and Quot.sound. The original theorem and geometric
   lemma additionally use the expected sorryAx. The sole textual sorry is the
   complete body of relativeFlat_open_scalarRestriction. There are no prohibited
   declarations, hollow definitions or arbitrary data choices. Verdict: pass as
   a decomposition, with one original hole closed and one smaller hole added.

3. Split-statement check: independently read Tags
   [05NE](https://stacks.math.columbia.edu/tag/05NE),
   [01U2](https://stacks.math.columbia.edu/tag/01U2),
   [0098](https://stacks.math.columbia.edu/tag/0098) and
   [03EU](https://stacks.math.columbia.edu/tag/03EU), together with the actual
   relative_flat_module_stalk, inverse-image stalk, tensor-stalk and exactness
   declarations. Tag 01U2 states its equivalence for quasi-coherent modules; here
   only the section-flat-to-stalk-flat implication is used, and its filtered
   affine-neighbourhood proof works without quasi-coherence, as the already
   proved relative_flat_module_stalk confirms. The open-site lemma restricts an
   existing module; it does not perform module pullback or extend scalars. Its
   docstring gives the scalar-action comparison, cofinality and exactness argument.
   It is a strictly smaller geometric step, independent of complexes and retracts.
   The algebra lemma is already fully proved, requires no flatness of A, and
   handles rank zero. Checked the zero module, zero base ring, empty open/site and
   identity morphism cases. Independent LeanFinder, Loogle and grep queries used
   stalk detection, open restriction and tensor/retract wording; also searched
   lean/Sheaf, upstream and Mathlib. The upstream site-point flatness theorem is
   for sheaves valued in one fixed monoidal category, not modules over this varying
   ring sheaf; FlatModuleTilde's applicable stalk criterion is private and is not
   the open-site scalar-action comparison. No duplicate complete statement or
   quick closure of the remaining geometric lemma was found. Verdict: pass.

4. Route and pruning check: read the explicit strictPerfectRelativeTensorComplex
   construction and IsStrictlyPerfect. The proof uses the actual structure map,
   G restricted termwise, finite free retractions from hL.2, and the signed total's
   direct-sum terms. No alternative representative is selected. Read the local
   calculation in [0DJQ](https://stacks.math.columbia.edu/tag/0DJQ) and
   [08CI](https://stacks.math.columbia.edu/tag/08CI). The tensor/coproduct/retract
   route matches that calculation. sk-thm-picard-semicon has empty `realized`
   statement and step lists; nothing realizing a unit step is bypassed. Every
   original proof dependency is still used, directly or through the geometric
   lemma: relative-flat-module-stalk, module-pullback, perfect-complex,
   tensor-complex-sheaves and flat-sheaf-modules. No module is claimed pruned.
   Each new public import supplies a signature dependency; in particular
   DerivedHomMayerVietoris defines moduleRings used in the open-site signature.
   New imports in the original module are proof-only. Verdict: pass.

5. DAG check: opened all three node records and checked their Lean names,
   statements, source/docstring arguments, proof steps and dependency unions.
   The geometric node records the stalk/action comparison followed by the
   exactness test; the algebra node records the free tensor isomorphism and
   actual source-library flat_of_retract application; the original records the
   three-step assembly. New nodes have creation, source, searches, blueprint,
   chapter/unit and verbatim Lean statement records. Added module-pullback to
   the original node's first step and flat-sheaf-modules to its last step, since
   its Lean explicitly uses those definitions; proof_deps remains exactly the
   union of step uses. Verdict: pass after this metadata correction.

Changes by the second reader: restored exact original signature whitespace and
completed the original node's proof dependency metadata. No proof argument,
statement, definition or import was changed in the final delivery.
