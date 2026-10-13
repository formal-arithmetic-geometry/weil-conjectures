## What changed

The assigned module reduces `exists_moduleExtEquiv` to the new fixed-resolution lemma
`moduleResolutionHomologyExtEquiv`. The proof chooses one resolution, transports its homology
comparison to the derived-functor object, and proves compatibility with every resolution using
`desc`, naturality of cycles and homology, and the Ext representative comparison. Existing public
signatures remain unchanged. The additive-equivalence constructor is reformulated with the same
function and inverse; its equality to the old constructor is checked by reflexivity.

The finite-colimit forgetful helper uses the restriction/coextension adjunction followed by the
sheafification adjunction. The existing additive comparison proof uses the composed additive
homomorphisms. Local transparency controls keep comparison definitions folded when elaborating
later declarations. Added proof-only imports: `ModuleResolutionHomologyExt`,
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`, and
`Mathlib.CategoryTheory.Sites.Adjunction`.

## Proved and sorry left

Against the six-hole repository snapshot read in this second reading, four existing holes are
closed, by declaration name (all in `AlgebraicGeometry.Scheme.Modules`):
`scalarFunctor_preservesFiniteColimits`, `scalarCohomologyExtMap_add`,
`exists_scalarPullbackCoefficient`, and `exists_moduleExtEquiv`
(node `def-sc-field-linear-module-cohomology-operations`). The last closure is a decomposition:
its resolution-comparison glue is complete, while one strictly lower hole is added,
`moduleResolutionHomologyExtEquiv` (node `lem-sc-module-resolution-homology-ext`).
It compares one fixed sections complex with Ext; it does not assert the derived-functor
comparison or compatibility between different resolutions. Thus the textual net against this
snapshot is three fewer holes; final closure progress is measured by the maintainer's pinned
sorry ledger, including any overlapping delivery that lands first.

Two original holes remain in the assigned module:
`AlgebraicGeometry.Scheme.Modules.scalarCohomologyExtMap_smul` and
`AlgebraicGeometry.Scheme.Modules.scalarCohomologyExtMap_bijective`
(both node `def-sc-field-linear-module-cohomology-operations`). No hole inside a definition
is added. The earlier first-reader report used a three-hole baseline and credited three
closures to intervening D2 work; that accounting did not match the repository snapshot
available to the second reader and is corrected here.

## No longer needed

No import or old `proof_deps` node is removed against the repository snapshot: its
`proof_deps` is empty. No DAG node or project module is pruned. The previous claim that
`Mathlib.CategoryTheory.Sites.PreservesSheafification` was removed referred to an earlier
candidate, not the repository, and is withdrawn. The second reader removed the candidate's
redundant newly added proof-only `Mathlib.Algebra.Homology.ConcreteCategory` import; compilation
still passes. The unit `sk-prop-av-cube` and its `realized` fields remain unchanged.

## Where the brief, the DAG or earlier work was wrong

The node has no listed proof dependencies for its unresolved Ext comparison. The new node records
the needed fixed-resolution component. The source cites Stacks Tags 01DZ and 0B6A; the latter is
the global derived Hom statement, which supplies Ext as derived sections of Hom.

The original module repeatedly approached or exceeded the 60-second per-file compile limit.
Local reducibility controls and the additive-homomorphism proof avoid unnecessary unfolding;
they do not change exported reducibility, signatures, visibility, or data. Scalar-linearity was
proved in a diagnostic file via multiplication of cocycle representatives and Mathlib Ext laws,
but its expensive generated conversions push the full file over the time limit. That proof is
not part of this delivery; its original named obligation remains unchanged.

## New nodes

`lem-sc-module-resolution-homology-ext`, in
`lean/Sheaf/AlgebraicGeometry/ModuleResolutionHomologyExt.lean`, states the additive identification
between sections homology of one fixed injective resolution and Ext from the structure sheaf.
Evaluation at 1 identifies cycles; boundaries correspond to null-homotopic cocycles. This includes
degree zero, zero modules, and the empty scheme. The natural-language proof and three search kinds are
recorded in the node (leansearch is unavailable with Internal Server Error). The parent node records the actual resolution-comparison route.

Change record: `coord/changes/fieldLinearOperationsLocalTransparencyU3.md`.

## Second reading by U3

1. Interfaces: diffed both delivered modules against the repository (the fixed-resolution
module is new), and compared all existing declaration signatures with the project's
parser. Every existing signature is byte-identical, no declaration is removed, and no
public import changes. The only existing definition body edit is the additive-equivalence
constructor; an independent scratch equality against the old `AddEquiv.ofBijective`
expression compiles by `rfl`. Local irreducibility is scoped and does not alter the
exported global attributes. Verdict: no changed target meaning or arbitrary data witness.
The cocycle characterization uniquely determines moduleExtEquiv: homologyπ is surjective
and every section cycle is evaluation of its multiplication morphism from the unit.
The pullback coefficient is likewise determined by the adjunction and its sectionwise formula.

2. Proof and axioms: compiled the new module and the assigned module in import order,
with no warnings or errors (4.5 and 51.5 seconds after import pruning). Only the two
reported original named theorems and the one new named theorem contain `sorry`.
Explicit `#print axioms` on the four closed declarations, both retained holes, and the
new lemma shows only propext, Classical.choice, Quot.sound, and where expected sorryAx.
The finite-colimit and pullback-coefficient proofs have no sorryAx. The additive proof
and derived-functor comparison transitively use the fixed-resolution obligation.
No forbidden declaration mechanism or hollow definition occurs. Verdict: checked proof
terms with the reported residual dependency, not a fully closed module.

3. Split statement: read the new Lean statement, its node and its complete docstring
proof. Stacks [01DZ](https://stacks.math.columbia.edu/tag/01DZ), equation
cohomology-equation-cohomology-modules, and [0B6A](https://stacks.math.columbia.edu/tag/0B6A),
Global derived hom, support the comparison. At n=0 boundaries vanish and evaluation at 1
is the ordinary Hom/sections identification. In positive degrees boundaries are precisely
preceding-differential composites, hence zero Ext classes. For zero coefficients or the
empty scheme both cohomology groups vanish. No quasi-coherence, separation, finiteness,
or field hypothesis is needed or added. The new lemma omits the parent's comparison of
all resolutions, which is supplied by its 35-line actual comparison argument: a genuine
strict reduction. Repeated leanfinder, loogle and grep searches with different wording;
read the partial unitHomEquiv and Ext APIs and the existing abelian-sheaf resolution
comparisons named in the new node. None is the needed public module-sheaf statement with
its representative formula; the generic nonnegative Hom-complex comparison is private.
Closing the remaining quotient/sections identification is not a one-lemma repair.
Verdict: true, properly characterized, strictly smaller and not duplicated.

4. Route and pruning: followed the chosen-resolution proof through desc(identity),
cyclesMap_i, homologyπ_naturality, isoRightDerivedObj_inv_naturality, and extMk_comp_mk₀.
These compare the same classes with the same orientation. Read the finite-colimit
proof against [03DB](https://stacks.math.columbia.edu/tag/03DB): restriction/coextension
and sheafification make forgetting a left adjoint, and its conservative finite-colimit
reflection gives exact scalar restriction. Read the pullback proof against
[0096](https://stacks.math.columbia.edu/tag/0096): the unit is restricted to a k-linear
natural transformation using the equation a ≫ f = g, and inverse adjunction provides j.
The additive proof is the composite additive homomorphism map_add law. Removed only the
redundant new ConcreteCategory import after recompiling. The old proof_deps list is empty;
no old node becomes unused. Read sk-prop-av-cube's sole cube-theorem step and its realized
record; no chapter or unit route is bypassed. Verdict: route retained and pruning list corrected.

5. Nodes: compared the parent node with its repository version; only proof, proof_deps,
and proof_origin differ. proof_deps is exactly the new lemma used by the comparison.
Added the missing pullback-coefficient argument to the parent's last proof step. Checked
the new node's id, kind, source, statement dependencies, actual recorded searches, status,
created/blueprint/chapter/unit fields, and verbatim lean.statement against the module.
Its lean.module and file agree, and every remaining hole has its recorded node.
Verdict: node and Lean agree after repairs.

Second-reading changes: corrected hole accounting and the nonexistent old-import pruning
claim; added the omitted pullback-coefficient route to the parent node; removed the redundant
new ConcreteCategory import; added the new module's blueprint docstring tag; rendered the
new node's statement in TeX, marked the failed LeanSearch as unavailable, and recorded the
independent searches and this review. Existing statements and proofs were otherwise retained.
