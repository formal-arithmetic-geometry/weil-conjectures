## What changed

Replaced the proof of `AlgebraicGeometry.strictlyPerfect_evaluation_local_model`
without changing its signature, visibility, or existing docstring. The proof takes
`F` from the essentially surjective derived localization (`objPreimage`), constructs
`f` from actual degree maps and their differential identity, proves its ordinary
component formula using coproduct and product universal properties, and combines
compatible comparison isomorphisms with these data.

Added `Sheaf.AlgebraicGeometry.OrdinaryEvaluationDifferential`: actual Hom-product
lifts and evaluation degree maps, with proved product and component formulas.
Only their differential identity remains a separate named proof obligation.
`HomComplexProjections` is the existing API used to expose the Hom products without
repeatedly expanding the large bifunctor existence statement. All data definitions
are real constructions; no definition uses an unproved existence theorem to choose
an arbitrary object.

Added `Sheaf.AlgebraicGeometry.StrictlyPerfectEvaluationComparisons`: comparison
isomorphisms for a supplied representative and a supplied ordinary evaluation map.
Its isomorphisms are existentially quantified. Its plan uses the bounded-exact-term
Hom computation on the localized site, which does not require U to be affine.

The parent uses two new proof-only imports and retains both original public imports.
The scoped elaboration settings accommodate conversions between the localized module
carrier and the carrier used by the internal Hom construction.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.strictlyPerfect_evaluation_local_model`
(node `lem-pc-strictly-perfect-evaluation-model`). This is a decomposition, not a
complete proof without sorry-dependent premises: one original hole closed, two new
holes added, net -1 hole.

The delivery leaves precisely these named theorem proofs as `sorry`:

- `AlgebraicGeometry.localEvaluationDegreeMap_comm`, node
  `lem-pc-ordinary-evaluation-differential`.
- `AlgebraicGeometry.exists_strictlyPerfect_evaluation_comparisons`, node
  `lem-pc-strictly-perfect-evaluation-comparisons`.

Proved helpers: `AlgebraicGeometry.homComplexProductLimit_exists`,
`AlgebraicGeometry.homComplexProductLift_proj`, and
`AlgebraicGeometry.localEvaluationDegreeMap_formula`. The parent has no direct sorry.
The two remaining obligations are strictly separate argument parts: the first is
an ordinary differential identity for arbitrary complexes and has no derived
category in its statement; the second assumes the representatives and actual
ordinary chain map already supplied and constructs compatible derived comparisons.

## No longer needed

Removed these direct proof imports from the parent:

- `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`
- `Sheaf.Algebra.Homology.DerivedInternalHom`
- `Sheaf.Algebra.Homology.HomComplex`
- `Sheaf.AlgebraicGeometry.DerivedTensorStructure`
- `Sheaf.AlgebraicGeometry.PerfectComplex`
- `Sheaf.AlgebraicGeometry.StrictlyPerfectDerivedInternalHom`
- `Sheaf.Paper.DerivedInternalHomRestrictOpen`

The first, last, and the definitions remain available through the new obligations
and existing public imports. The affine-only theorem
`AlgebraicGeometry.Scheme.isIso_homComplex_resolution_of_isStrictlyPerfect`, node
`lem-pc-rhom-strict-perfect-hom`, and its module
`Sheaf.AlgebraicGeometry.StrictlyPerfectDerivedInternalHom` are not used by this
local-model route. Instead the comparison obligation uses
`lem-pc-bounded-exact-term-hom-quasi-iso` and
`lem-sc-finite-free-internal-hom-exact` on the localized site. For clarity, all ten original parent `proof_deps` are removed as direct
proof dependencies of the parent assembly:

- `def-pc-canonical-derived-tensor-hom-bijection`
- `def-pc-perfect-complex`
- `def-pc-scheme-derived-tensor-structure`
- `def-pc-tensor-complex-sheaves`
- `def-pur-derived-internal-hom`
- `def-pur-hom-complex`
- `lem-pc-bounded-above-flat-kflat-site`
- `lem-pc-rhom-strict-perfect-hom`
- `lem-pc-strictly-perfect-ordinary-evaluation`
- `lem-sc-derived-internal-hom-restrict-open`

Only `lem-pc-rhom-strict-perfect-hom` is eliminated from the mathematical route.
The other nodes remain in the new obligations or supply definitions used in the
statements. In particular the ordinary-evaluation node supplies definitions;
its invertibility theorem is unused. This is direct-dependency pruning, not a
claim that all these nodes or modules leave the targets' import closure.
The ordinary-evaluation invertibility theorem is not needed: only its component
construction is used. Other targets may still reach the affine-only module; this
report does not assert that it leaves the whole target closure.

Discarded the two uncommitted modules and nodes of the previous attempt,
`StrictlyPerfectEvaluationModelData` and `StrictlyPerfectEvaluationModelComparison`.
They were never library nodes and are not delivered.

## Where the brief, the DAG or earlier work was wrong

The earlier comparison theorem asserted an equation for arbitrary f, a, and b,
without evaluation or compatibility hypotheses. That assertion is false: for
nonzero ordinary evaluation, choosing f to be zero already destroys the square.
The discarded data theorem ended in a vacuous True and did not fix the defect.
This delivery constructs the actual ordinary graded map, verifies its component
formula, and asserts existence of compatible comparisons for that fixed map.
It neither assumes nor asserts the comparison equation for arbitrary isomorphisms.

The earlier claim that no valid reduction was available was too strong. The
localization already supplies a representative of restricted N; the product and
coproduct APIs supply the graded evaluation maps. The unresolved differential and
derived comparison arguments can be stated separately with their source proofs.

The parent plan's strictly-perfect Hom lemma assumes an affine open, whereas the
parent has arbitrary U. The new comparison plan explicitly uses finite-free
internal Hom exactness and the bounded-exact-term Hom quasi-isomorphism theorem,
which give the needed computation without an affine hypothesis.

Edge cases checked in the mathematical statements: empty U, P=0, F=0, rank-zero
finite-free terms, and unbounded F. The graded construction needs no finiteness;
strict perfectness is required only to make the dual K-flat and the Hom comparison
invertible. In the differential check the two possibly nonzero projected cases
are r+q=0 and r+q=-1; their signs are (-1)^p times -(-1)^q=-(-1)^(p+q).
Arbitrary representative automorphisms can be absorbed in the existentially chosen
comparisons; no universal assertion about a or b is made.

The unit record `sk-thm-picard-duality` and its realized route are unchanged.
Searches used the registered msearch tool, the library sources, Mathlib sources,
and blueprint searches. LeanSearch returned Internal Server Error (unavailable),
not a mathematical no-match. LeanFinder returned underived evaluation and tensor
APIs; grep found the tensor coproduct API but no complete internal-sheaf evaluation
comparison theorem. The local literature checkout is absent; Stacks Tags 08DQ,
08DM and 08DL were read at their stable online pages. The detailed new-node proofs
are marked agent-written expansions of those sources.

## New nodes

`lem-pc-ordinary-evaluation-differential`, in
`dag/nodes/sec-picard-framework/lem-pc-ordinary-evaluation-differential.json`, records
the actual graded construction and the differential compatibility obligation. It
records all supplied helpers in its Lean declarations. It realizes step 4 of the
parent's source proof. The component formula and universal-property lemmas are
proved; the remaining equation is the sign calculation.

`lem-pc-strictly-perfect-evaluation-comparisons`, in
`dag/nodes/sec-picard-framework/lem-pc-strictly-perfect-evaluation-comparisons.json`,
records compatible comparisons for supplied P, F, their representatives, and an
ordinary evaluation chain map. It realizes steps 2, 3 and 5 of the parent proof.
Its complete proof plan explicitly preserves compatibility when passing through
the K-injective resolutions. No existing statement or definition is changed, and
no forced adaptation or change record is needed.


## Second reading by H3

1. Interface preservation: compared the sole existing delivered module with its
   repository version using `diff -u`, and checked the theorem signature byte for
   byte through `:= by`. Verdict: unchanged hypotheses, conclusion, universes,
   visibility, and docstring. Both existing public imports remain. The other two
   modules and their nodes are new; there are no changed definitions or signatures
   of existing declarations and no forced adaptations.

2. Proof and data: compiled all three modules in import order with `lcompile.py`;
   no errors or non-sorry warnings. Inspected every delivered declaration for
   forbidden constructs and definition holes. The only direct sorries are
   `localEvaluationDegreeMap_comm` and
   `exists_strictlyPerfect_evaluation_comparisons`, both named and reported.
   An appended `#print axioms` scratch copy checked all eight public declarations.
   The product-limit theorem, product lift, lift-projection theorem, degree map,
   and degree-map formula use only `propext`, `Classical.choice`, `Quot.sound`.
   The parent and the two open theorems additionally use `sorryAx` as expected.
   The product lift chooses an IsLimit proof, not arbitrary object data; the
   graded maps are explicit descents of these lifts. The representative F comes
   from the existing localization's proved essential surjectivity. Verdict: real
   construction and valid reduction, with no claimed axiom-free proof of the parent.

3. Split statements: read the full new Lean statements and nodes, the internal
   Hom projections/differential, the ordinary evaluation components, and the
   canonical derived tensor-Hom representative predicate. Read Stacks
   [08DQ](https://stacks.math.columbia.edu/tag/08DQ),
   [08DM](https://stacks.math.columbia.edu/tag/08DM), and
   [08DL](https://stacks.math.columbia.edu/tag/08DL).
   The differential assertion uses arbitrary P,F and no strict perfectness; on
   (p,q), the F contribution occurs at r+q=0 and the P contribution at r+q=-1.
   The dual sign -(-1)^q times the tensor sign (-1)^p is -(-1)^(p+q), exactly
   the Hom sign. All other projected contributions vanish. Zero differentials,
   odd and negative degrees, zero complexes and the empty open fit the formula.
   The comparison statement takes the actual chain map and its component formula
   as inputs and existentially chooses a,b. Strict perfectness gives bounded
   source terms that retract from finite free sheaves. Read
   `finiteFreeInternalHomExact` and
   `quasiIso_homComplex_map_of_bounded_exact_terms`: the former's exactness passes
   to retracts and supplies the latter's termwise hypothesis. Thus no affine or
   bounded-F assumption is needed. Verdict: true obligations, respectively the
   differential check and derived comparison; neither simply renames the parent.
   The parent actually constructs F and the degree maps and proves hf.
   Fresh registered LeanFinder searches for cochain evaluation compatibility and
   derived restriction/evaluation comparisons found ordinary morphism cochains
   and exact-functor localization APIs, not replacements. Registered grep and
   local/upstream source searches found the termwise right-dual `evalPQ_comm`
   and Hom/tensor currying comparison. Read them: the first uses specified
   right duals rather than the actual Hom-product dual here; the second has a
   different map and its differential theorem is itself open. Neither closes
   these obligations in a few lines. No additional statements were split off.

4. Route and pruning: inspected the parent proof from its existential conclusion
   downward. `objPreimage`, actual graded-map construction, the proved formula,
   and application of the comparison obligation account for every step.
   The public imports in the new files are used by signatures or definitions;
   comparison proof imports supply its recorded open proof plan. The old
   affine-only Hom lemma is unused, and its replacements apply to arbitrary U.
   The report now enumerates every old parent proof dependency removed directly
   and distinguishes their transitive use from actual pruning. Inspected
   `dag/units/sk-thm-picard-duality.json`: its existing realized value is
   `{"statement": [], "steps": [[]]}`; this delivery leaves it and the finite
   duality ancestor route unchanged. Verdict: no unit route bypass and no
   assertion of whole-closure pruning unsupported by the import graph.

5. Node agreement: compared the parent JSON with the repository version; only
   `proof`, `proof_deps`, and `proof_origin` differ. Checked that every proof_deps
   set equals the union of its steps' uses and every referenced node exists.
   Both new nodes have source, full proof plan, actual search records (including
   the unavailable LeanSearch result), creation, blueprint ancestry, chapter,
   unit, and matching Lean records. Their declared primary theorems and helper
   lists agree with the delivered modules. Verdict: DAG and Lean agree.

Second-reading changes: clarified `## No longer needed` with the complete old
parent proof-dependency list and direct-versus-transitive distinctions, and added
this independent reading. No Lean proof, statement, definition, import, or node
repair was necessary. One original hole is closed by decomposition, two holes
are added, net -1; the five proved construction declarations have no sorry axioms.
