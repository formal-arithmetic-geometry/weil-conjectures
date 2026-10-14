## What changed

Replaced the proof of
`AlgebraicGeometry.Scheme.Modules.tensorGradedAlgebraData_exists` in
`Sheaf.AlgebraicGeometry.TensorGradedAlgebraData` by a compiling reduction.
Every existing declaration, signature, definition body and visibility is unchanged.
All original public imports remain necessary for the statements and definitions.
Added four proof-only imports:

- `Sheaf.AlgebraicGeometry.TensorPowerAlgebraCoproduct`;
- `Sheaf.AlgebraicGeometry.AlgebraTensorPullbackComparison`;
- `Sheaf.AlgebraicGeometry.ClosedImmersionUnitQuotient`;
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed`.

The first lemma constructs only B and its homogeneous coproduct maps and multiplication.
The second is a general algebra base-change comparison for an arbitrary algebra B and
arbitrary supplied tensor-pullback adjunction. It has no tensor powers, grading,
coproduct hypothesis, local freeness hypothesis, or closed-immersion hypothesis.
These are independent parts of the construction, not copies of the item's statement.
Neither new theorem is used to define any data-valued declaration by choice.
Their witnesses are eliminated inside the proposition-valued existence proof only.

The fully proved private helper `restrictionCofanIsColimit` supplies the remaining
coproduct argument. The closed-immersion unit identifies F(M)=j_*j^*M with M/JM.
Given a cofan from F(D_d), descend its composites with the units along the source
coproduct. Tensoring with J preserves this coproduct by the tensor-Hom adjunction.
Naturality of J-multiplication shows that the descended map kills JM; use the cokernel
universal property and the unit-quotient isomorphism to descend again. Epi units give
factorization and uniqueness. Thus the proof does not leave coproduct preservation as
a third hole or assume that a right adjoint preserves coproducts.

Finally c_d is F(b_d) followed by the algebra comparison isomorphism. Transport the
colimit along that isomorphism. Unit naturality proves the required quotient square
for exactly `tensorGradedUnit`, and the source construction supplies `b_multiply`.

## Proved and sorry left

Closed the single original hole:

- `AlgebraicGeometry.Scheme.Modules.tensorGradedAlgebraData_exists`
  (`lem-sc-tensor-graded-algebra-data`).

Added two holes, each the entire proof of one public named theorem in a new module:

- `AlgebraicGeometry.Scheme.Modules.exists_tensorPowerAlgebraCoproduct`
  (`lem-sc-tensor-power-algebra-coproduct`);
- `AlgebraicGeometry.Scheme.Modules.exists_algebraTensorPullbackComparison`
  (`lem-sc-algebra-tensor-pullback-comparison`).

This is a decomposition: one original hole closed, two lower holes added (local net -1),
not a sorry-free proof of the algebra constructions. No sorry remains in the item's module.
The private `restrictionCofanIsColimit` has a complete Lean proof from the existing
`closedImmersion_unit_quotient` and tensor-Hom adjunction; it adds no hole.
Existing imported theorems retain their own recorded proof dependencies and holes.

All three modules compile individually/with the sandbox import overlay, with no errors
or non-sorry warnings. The compiler checked the colimit transport, chosen-unit
naturality equation and homogeneous multiplication field. New Lean lines are at most
100 characters, and the existing interfaces have been compared with the originals.

The mathematical edge cases were checked before stating the two lemmas: degree zero
is the constant polynomial term; empty opens satisfy the same sheaf equations; the
zero algebra and empty schemes are admitted; no nonzero-unit hypothesis is used.
The source coproduct is a coproduct of sheaves, not an assertion that taking sections
on every open commutes with infinite direct sums. The comparison e is a module
isomorphism, so arbitrary changes of the adjunction do not impose spurious algebra
compatibility. The original node's lack of a multiplication condition on c is respected.

## No longer needed

No original imports or modules were removed, and no original node is claimed pruned.
The old direct proof dependencies `def-sc-invertible-module` and
`def-weil-pbc-comm-algebra-sheaf` are no longer direct proof dependencies of the item:
the source-algebra lemma now uses them. They remain statement dependencies and are
used transitively; their modules are not pruned.
The definition nodes for invertibility and algebra sheaves remain needed by the new
source construction and the item's statement. TensorPullbackAdjunction remains needed
for the original chosen unit and the algebra base-change comparison.

No import of `QuasiCoherentSymmetricAlgebra` is needed: its universal degree-one map
does not provide the tensor-power coproduct and homogeneous multiplication comparison.
No separate gluing of C by polynomial frames, independent construction of c, or
separate sorry for preservation of coproducts is needed in the new route. Algebra
base change produces C, and the cokernel argument proves the coproduct property.
These were implicit steps, not existing modules removed from the import closure.

## Where the brief, the DAG or earlier work was wrong

No false statement or forced adaptation was found. The two original proof steps hid
substantial algebra-sheaf constructions behind definition-only dependencies. Their
signatures do not construct a polynomial algebra sheaf or compare an algebra pullback
with module tensor pullback. The delivery isolates these two genuinely missing parts
and proves the quotient-square and coproduct glue in Lean.

The actual proof of coproduct preservation uses the existing closed-immersion
unit-quotient theorem and tensor-Hom adjunction, rather than an unsupported claim
that pushforward, being a right adjoint, preserves coproducts. The item node is updated
to match these dependencies. The unit's realized statement and route are unchanged.

LeanSearch returned Internal Server Error for both new statements; successful
LeanFinder/Loogle and local grep searches are recorded separately, without treating
the unavailable service as evidence of absence. Whole-DAG and blueprint searches
found no duplicate sheaf-level construction. The source files are absent from this
machine's literature cache, so the corresponding canonical Stacks pages were read:
https://stacks.math.columbia.edu/tag/09MS,
https://stacks.math.columbia.edu/tag/0095 and
https://stacks.math.columbia.edu/tag/0096.
The expanded construction arguments are marked as agent-written in proof_origin.

## New nodes

`lem-sc-tensor-power-algebra-coproduct`, in
`dag/nodes/sec-curve-estimates/lem-sc-tensor-power-algebra-coproduct.json`, states the
source algebra half of the original construction. Its module is
`Sheaf.AlgebraicGeometry.TensorPowerAlgebraCoproduct`. Its docstring gives the local
polynomial-frame construction, descent, sheaf coproduct universal property and
multiplication check.

`lem-sc-algebra-tensor-pullback-comparison`, in
`dag/nodes/sec-curve-estimates/lem-sc-algebra-tensor-pullback-comparison.json`, states
algebra base change and comparison with the supplied module adjunction unit. Its module
is `Sheaf.AlgebraicGeometry.AlgebraTensorPullbackComparison`. Its docstring describes
inverse image, extension of scalars, forgetting multiplication, and the comparison of
adjunctions. This lemma applies independently to every algebra sheaf and every scheme
morphism, and asserts no graded or coproduct data.

No existing definition or public interface was changed; no change record or forced
consumer adaptation is required.

## Second reading by Q3

1. **Interfaces: pass.** Read the repository and sandbox modules in full and compared
   them with `diff -u` and the declaration scanner. The four existing declarations
   `tensorGradedAlgebraMap`, `tensorGradedAlgebraSection`, `tensorGradedUnit`, and
   `TensorGradedAlgebraData` retain their exact signatures and definition bodies;
   `tensorGradedAlgebraData_exists` retains its exact signature. The diff adds only
   four private imports, a proved private helper and the theorem proof. No change
   record or forced adaptation is needed. In particular, the theorem still assumes
   only a closed immersion and invertibility, with the same universes and fields.

2. **Proof and axioms: pass as a decomposition.** Compiled all three modules against
   the sandbox overlay, with no errors or non-sorry warnings. Scratch copies printed
   axioms for the helper, original definitions and three public theorems. The helper
   and the original definitions use only `propext`, `Classical.choice`, `Quot.sound`.
   The main theorem additionally uses `sorryAx`, as do precisely the two reported
   split theorems. No forbidden declaration, hidden sorry, or new data-valued choice
   was found. The existential algebra witnesses are eliminated inside a proposition
   proof; no public definition chooses an arbitrary algebra from an open existence
   theorem. The helper's choice of a colimit proof is proof-valued and is sorry-free.
   Read its cancellation argument: tensor-Hom preserves the source coproduct;
   naturality makes J-multiplication vanish on every summand, hence on the whole
   source. Image-epi cancellation and cokernel descent produce the factor map.
   Epi units prove factorization and uniqueness. No preservation property of a
   general right adjoint is assumed.

3. **Split statements and sources: pass.** Read
   [Stacks 09MS](https://stacks.math.columbia.edu/tag/09MS), specifically the graded
   direct-sum sequence after coherent-equation-ses, and
   [0095](https://stacks.math.columbia.edu/tag/0095) and
   [0096](https://stacks.math.columbia.edu/tag/0096), the tensor formula and adjunction.
   The construction, unlike the surrounding ampleness theorem, does not use
   Noetherianity, a topological homeomorphism, or square-zero: polynomial frames
   construct B on any scheme; inverse image and scalar extension construct the
   coefficient algebra for any morphism. The first split has only X,L and constructs
   B,b with coproduct and multiplication. It omits C,p,c and the quotient square.
   The second has arbitrary B,j,a, constructs C,p,e, and has no grading or coproduct
   clause. Thus neither restates the item. On Spec R with a trivial line, the first
   is R[T] with the monomial basis, including the constant degree-zero summand.
   The second is the underlying-module comparison for extension of scalars. A
   different adjunction unit is absorbed by a module automorphism in e; e is not
   required to preserve algebra multiplication. Empty schemes, empty opens, and
   the zero algebra introduce no excluded case. Both complete docstring arguments
   agree with the nodes, including sheafification of local finite sums rather than
   an incorrect sectionwise infinite-direct-sum formula.

   Independent LeanFinder queries used 'sheaf of polynomial algebras associated to
   a locally trivial rank one module homogeneous direct sum' and 'extension of
   scalars of a sheaf of commutative rings underlying module adjunction unit'. Hits
   were Proj structure sheaves, tilde modules, module sheafification and free-module
   unit comparisons, not these algebra-sheaf constructions. Loogle on
   `CategoryTheory.Adjunction.leftAdjointUniq` confirms the unit comparison used in
   the second split's argument, but supplies no algebra pullback. Local searches
   covered Lean, the DAG and blueprint notes with polynomial-sheaf, algebra-base-
   change and tensor-power-algebra wording. Read `QuasiCoherentSymmetricAlgebra`:
   its degree-one universal property and affine comparisons do not give the
   tensor-power coproduct identification without another argument. Read
   `StructureAlgebraPullbackTransport`: it assumes a structure-algebra realization
   and an invertible base-change map, rather than constructing arbitrary algebra
   pullback. `GradedModuleRelativeSpecRealization` assumes properness, Noetherianity
   and finite generation. Ring-level symmetric/tensor algebra grading nodes do not
   provide the sheaf-level comparison. Neither split can be closed by a short
   application of these results; both remain explicitly open.

4. **Route and pruning: pass after report correction.** The main proof uses the two
   genuine parts, proves the closed-immersion coproduct passage, transports along e,
   and uses naturality for the exact `Classical.choose` unit in `tensorGradedUnit`.
   All original public imports support existing statements or definitions; all four
   added imports support proofs and are private. The original two definition nodes
   removed from direct `proof_deps` are now explicitly accounted for under
   'No longer needed'; they remain needed transitively and no module is pruned.
   Opened `dag/units/sk-thm-curveestimate.json`: its realized statement is
   `thm-sc-proper-cohomology`, with no realized steps. This lower construction
   changes neither that record nor the chapter's route through the Picard argument.

5. **DAG agreement: pass.** The original node changes exactly `proof`, `proof_deps`
   and `proof_origin`. Its steps name the source construction, algebra comparison,
   chosen adjunction, quotient theorem and tensor-Hom theorem actually used.
   Both new nodes have distinct IDs, self-contained matching Lean statements,
   sources, docstring proofs, dependency unions, searches, provenance, creation
   records, chapter/unit and blueprint ancestry. Their statements make exactly
   the module assertions: the first's coproduct proof is `Nonempty IsColimit`,
   and the second's comparison is only a module isomorphism. No unit record or
   existing target statement is changed.

Changes from this reading: added the missing blueprint IDs to both new module
headers, corrected the new comparison module's source chapter from 'Modules' to
'Sheaves on Spaces', and completed the pruning report with the two removed direct
DAG dependencies. The mathematical proof and all statement signatures were kept.
One original hole is closed by reduction; two lower holes remain added, so this
remains a decomposition with local net -1, not a sorry-free result.
