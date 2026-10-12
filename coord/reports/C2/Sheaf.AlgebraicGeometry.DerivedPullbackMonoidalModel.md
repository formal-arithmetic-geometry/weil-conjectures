## What changed

Replaced the proof of `AlgebraicGeometry.exists_derivedPullbackMonoidalModel` by an
assembly from `AlgebraicGeometry.derivedPullback_tensorProduct` and two strictly smaller
coherence statements, in new modules `Sheaf.AlgebraicGeometry.ModulePullbackTensorCoherence`
and `Sheaf.AlgebraicGeometry.DerivedPullbackMonoidalDescent`. The coherence import is
proof-only. The descent module is publicly imported because
its named, fully defined instance wrappers now occur in the exposed predicate's body.
The predicate and theorem signatures, existing public imports and visibility are unchanged.
The predicate's local instance expressions have been replaced by definitionally equal
named wrappers; the mathematical predicate is unchanged.

The existing tensor-product theorem supplies the functor, its object and arrow formulas,
additivity, left-derived counit, total-complex comparisons, their naturality, and their
invertibility on K-flat pairs. The first new statement supplies only underived module
coherence. The second takes that coherent structure and the supplied counit and complex
comparisons as inputs and supplies only derived coherence. A proved private categorical associativity helper combines the pinning equation with
the existing summand formula to establish the exact
summand formula, then combines all witnesses into the original predicate. Local instance
registrations reuse the descent module's checked instance setup. Repair of return 8:
the predicate now uses the same named wrappers as the descent statement. This avoids
repeated large instance comparisons. The theorem-scoped transparency overrides have
been removed; the file retains its original transparency settings. No proof was split
for performance and no timeout limit was increased. The private helper
`reassoc_pinned` is fully proved and contains no hole.

Updated the original node's proof, proof_deps and proof_origin to this route. Each new
statement has a separate module and node, complete proof in words, source attribution,
and the three required kinds of search. No data is defined by choosing a new existential
witness; all existential elimination occurs inside theorem proofs.

## Proved and sorry left

This is a decomposition, not a completed proof without open dependencies.

Hole closed in the item's module:
`AlgebraicGeometry.exists_derivedPullbackMonoidalModel`
(node `def-pc-derived-pullback-monoidal-model`). Its combining proof has no `sorry`.

Holes added, each the entire proof of a named public theorem:

- `AlgebraicGeometry.modulePullback_tensor_coherent`
  (node `lem-pc-module-pullback-tensor-coherence`). It concerns module sheaves only;
  it neither constructs nor assumes any derived monoidal model.
- `AlgebraicGeometry.derivedPullback_monoidal_descent`
  (node `lem-pc-derived-pullback-monoidal-descent`). It starts with a coherent underived
  structure, a fixed derived counit and fixed natural total-complex comparisons, including
  their summand and invertibility properties. It constructs only their coherent descent.

No `sorry` remains in the item's module. The existing imported theorem
`AlgebraicGeometry.derivedPullback_tensorProduct` remains open and is not edited by this
delivery. Other existing dependency holes are unchanged. Net holes closed minus added
by this delivery: 1 - 2 = -1; no net-hole progress is claimed.

Edge cases checked mathematically: identity morphisms give the ordinary tensor/unit
comparisons after the functor identifications; the empty scheme gives the unique diagrams;
zero complexes make the tensor compatibility diagram an equality of zero maps; taking
one argument to be the unit reduces descent to the unit comparison. Neither lemma needs
flatness or exactness of a general scheme morphism. Arbitrary choices of the left-derived
counit are allowed because its universal property transports the comparison coherently.

## No longer needed

No original import, node, or module is pruned. Both original public imports are needed
by the model definition. K-flat resolution, preservation and tensor closure
remain part of the descent argument and the existing tensor-product theorem's route.
The unit record has no realized node that this route bypasses.

The new underived coherence module imports only ModulePullbackTensor and DerivedCategory
(the latter supplies the shared moduleRings carrier). It does not import the derived
tensor structure or DerivedPullbackTensorProduct. The new descent module imports
DerivedTensorStructure and DerivedPullback; it does not need to import the theorem
DerivedPullbackTensorProduct, whose data are supplied as hypotheses. These are omissions
of unnecessary candidate imports, not pruned existing dependencies.

## Where the brief, the DAG or earlier work was wrong

The original node had empty proof and proof_deps despite the module docstring's explicit
plan. The new node records make the underived coherence and derived descent steps explicit.
The earlier attempt merely restated the original existence theorem. This delivery instead
uses the existing tensor-product theorem and separates the underived coherence construction
from conditional derived descent; neither helper asserts IsDerivedPullbackMonoidalModel
or the full original existential package.

The upstream exact-functor tensor comparison requires PreservesFiniteLimits, which a
general module pullback does not satisfy. It is not used. LeanSearch was unavailable
(HTTP Internal Server Error); LeanFinder, Loogle and source searches found no exact
replacement. Blueprint searches found no matching coherence/descent node.

WANTED: literature/stacks-project/modules.tex, Tag 01CD, for
lem-pc-module-pullback-tensor-coherence; literature/stacks-project/cohomology.tex,
Tag 079U and Section 20.27, for lem-pc-derived-pullback-monoidal-descent. These source
files are absent here. The proofs in words are therefore explicitly recorded as
agent-written arguments following the original module's plan, not quotations of a
locally inspected source.

Return 8 was reproduced: the previous delivery's target timed out after 60 seconds.
The repaired full delivery compiled with `lcompile.py --all`: descent 33.0 seconds,
module coherence 4.9 seconds, and the target 35.8 seconds, with no warnings.
The independent second-reading section below records the earlier delivery and predates
this repair; its proof-only descent-import description is superseded by this repair.
Both direct importers compiled unchanged against the repaired target: 
`PerfectRHomTensorComparison` in 33.3 seconds and `PerfectTensorHomDuality` in 8.7 seconds.
The scratch importer sources are outside the delivered `lean/` tree; they add no files
to the delivery. The scratch module `scratchpad/equality/lean/Sheaf/AlgebraicGeometry/ModelEquality.lean`
compiled in 50.5 seconds. It elaborates the repository's original predicate with the
original instance expressions, then proves `OriginalModel g m =
IsDerivedPullbackMonoidalModel g m` by `rfl`. This verifies that the comparisons and
all instance-dependent parts of the predicate remain definitionally equal.
The delivery dry run performs the final compilation and axiom probes.

## New nodes

`lem-pc-module-pullback-tensor-coherence`:
`dag/nodes/sec-picard-framework/lem-pc-module-pullback-tensor-coherence.json`, realized by
`Sheaf.AlgebraicGeometry.ModulePullbackTensorCoherence`. The recorded module comparison
has a unit and satisfies associativity and unit coherence, proved in words using pure
tensors and the balanced tensor relations.

`lem-pc-derived-pullback-monoidal-descent`:
`dag/nodes/sec-picard-framework/lem-pc-derived-pullback-monoidal-descent.json`, realized by
`Sheaf.AlgebraicGeometry.DerivedPullbackMonoidalDescent`. The supplied coherent module
comparison, total-complex comparison, and counit descend through K-flat resolutions.
Its conclusion is only the derived structure and its prescribed compatibility equation.

Change record: `coord/changes/derived-pullback-monoidal-local-instances.md` documents
the local instance registrations, named wrappers in the predicate, and the imports. Existing signatures and
visibility are unchanged; the predicate's instance expressions now refer to named,
definitionally equal wrappers. No module is adapted.

## Earlier second reading (a previous round; superseded)

1. I compared the delivered module and node records with the repository versions. Existing declaration signatures and the predicate body are unchanged; the target proof only adds proof terms and the two separately recorded split lemmas. The two new theorem statements are distinct reductions rather than restatements of the target.

2. I compiled all three delivered modules with `lcompile.py`, and separately compiled the target module after changing the descent import to proof-only. No compiler errors remain. The only `sorry`s are the two named split-off theorem declarations, each with a corresponding node; no definition contains `sorry`, and no forbidden declarations occur. The target assembly uses only the permitted categorical reassociation helper.

3. I checked the split statements against their hypotheses and edge cases. The module lemma is the underived tensor coherence assertion and the descent lemma takes the complete underived, counit, and complex-comparison data as inputs; neither weakens the target. Their docstrings and DAG proof steps explain the constructions and cite their sources. No existing declaration in the local library duplicates either statement.

4. I checked the proof route from the target downward: it uses the existing tensor-product theorem, then the underived coherence reduction, then the conditional derived descent reduction. The original imports are still needed for the predicate and tensor theorem; the descent module is imported only for proof elaboration and is now plain `import`, so no proof-only dependency is exported. No old proof dependency is pruned.

5. I checked the node records and unit route. The target node's proof, dependencies, and origin follow the assembled proof, and each split node has its Lean record, source, proof steps, searches, and status. The unit's realized route is not bypassed by this below-unit decomposition.

I changed the descent import from `public import` to proof-only `import`, updated the change record and this report, and left all mathematical statements and proofs unchanged.


## Second reading by C2

1. **Existing interface and definition.** I diffed the delivered target against the
repository and compared both existing declaration signatures byte for byte: they match.
The only definition-body change is the recorded replacement of local instance expressions
by the descent module's named wrappers. I read each wrapper body and the complete change
record. I independently recompiled `scratchpad/equality/lean/Sheaf/AlgebraicGeometry/ModelEquality.lean`:
`OriginalModel g m = IsDerivedPullbackMonoidalModel g m` closes by `rfl` (43.7 s).
The scratch original uses precisely the original instance expressions and predicate body,
without the new local registrations. Thus the localization tensorators and the complete
predicate remain definitionally equal, with no new hypothesis or weakened conclusion.
The unchanged direct importers `PerfectRHomTensorComparison` and `PerfectTensorHomDuality`
compiled against the delivery in 31.3 s and 7.9 s. Verdict: the recorded implementation
change preserves the existing mathematical interface.

2. **Proof and axioms.** I read the entire three Lean modules, the reassociation helper,
and the declaration `derivedPullback_tensorProduct` used in the assembly. Its existential
package supplies exactly F, hF, hmap, additivity, epsilon, its universal property, phi,
the summand formula, naturality, and K-flat invertibility. `reassoc_pinned` rewrites the
pinning equation and uses only category associativity; it supplies the two occurrences
of the summand formula without changing any witness. The only delivered `sorry`s are
`modulePullback_tensor_coherent` and `derivedPullback_monoidal_descent`, both whole named
public theorem proofs, matching their nodes. The current target scratch copy with
`#print axioms` for the predicate, existence theorem and both split statements compiled
in 26.1 s: each prints only propext, Classical.choice, Quot.sound and sorryAx. No forbidden
declaration or definition containing sorry occurs. Existential elimination is solely
inside theorem proofs; the named wrappers reuse actual existing constructions and introduce
no arbitrary object chosen from a new unproved existence theorem. Verdict: valid assembly
with two explicitly open dependencies, a decomposition with net 1 - 2 = -1 holes.

3. **The split statements.** I matched each hypothesis and conclusion to its node.
Module coherence assumes the full object and arrow identifications and pins the inverse
tensorator to the recorded `module_pullback_tensor` comparison; it asserts neither a
derived model nor its counit. The section formula in the existing tensor theorem and
adjunction/sheafification generation make the pure-tensor coherence argument applicable.
Descent takes the fixed F, coherent mF, epsilon with its left-derived universal property,
and phi with its summand, naturality and invertibility hypotheses. It supplies only m
and the prescribed equation. Neither lemma restates the original existential package.
On a K-flat pair, A=L(mu_Q), B=epsilon_tensor;Q(phi), and
C=(epsilon_P tensor epsilon_N);mu_Q have the asserted sources and targets;
C;B^{-1};A^{-1} therefore has exactly the direction of the requested tensorator.
K-flat closure, pullback preservation, and resolutions supply the required invertibility
and descent, without requiring a flat scheme morphism or exact module pullback.
I checked empty schemes, zero complexes, a degree-zero unit argument, and identity
morphisms; arbitrary counit choices transport the monoidal structure, so identity morphisms
need not give literally identity comparison maps before that transport.
I also read [Stacks 01CD](https://stacks.math.columbia.edu/tag/01CD) and
[Stacks 079U](https://stacks.math.columbia.edu/tag/079U) online: the former states the
underived comparison with proof omitted; the latter explicitly uses K-flat tensor closure
and the degreewise underived comparisons. The additional coherence arguments remain
agent-written, as the nodes correctly say. Fresh LeanFinder searches for localization
of strong monoidal functors and inverse-image/extension-of-scalars coherence, a Loogle
search for `"CoreMonoidal"`, and grep searches of the library, Mathlib and DAG found no
exact replacement. I read `Localization.Monoidal.functorCoreMonoidalOfComp`: it assumes
a strong monoidal localization and a monoidal lifting, whereas Q is only lax on arbitrary
complexes. I read upstream `Scheme.Modules.pullbackMonoidal`: it concerns the other
pullback functor and gives no pinning equality for the tensor-formula functor. The upstream
left-derived tensor comparison also requires finite-limit preservation. These are useful
construction tools, not a few-minute proof of either split statement. Verdict: true,
strictly smaller reductions with sufficient hypotheses and complete proof plans.

4. **Route and pruning.** The shortest available target assembly uses the already stated
tensor-product theorem, then module coherence and conditional K-flat descent. The original
node has empty proof_deps, so there is no old dependency omitted from `No longer needed`.
Both original public imports occur in the predicate's types or body. Module coherence is
correctly a plain proof-only import. Descent is necessarily public here because its named
instance wrappers occur in the exposed predicate body. In the new coherence module,
DerivedCategory supplies moduleRings and ModulePullbackTensor supplies the pinned comparison;
in descent, DerivedPullback and DerivedTensorStructure supply the statement's structures.
I read `dag/units/sk-thm-picard-duality.json`: its realized statement and step arrays are
empty, so no realized unit step is bypassed. Verdict: no original import or module is pruned.

5. **Nodes and changes.** I checked all three JSON records and their Lean declarations.
The original node changes only proof, proof_deps and proof_origin. Its three steps match
the tensor-data extraction, pinned summand reassociation and descent/witness assembly.
Each proof_deps is exactly the union of its step uses. Both new nodes have source,
agent proof_origin, three search kinds, complete proof steps, split status, worker/item/
group/date creation, blueprint ancestry, matching chapter/unit, and a Lean record whose
normalized statement matches the actual theorem signature. Their hypotheses and comparison
orientations match the mathematical statements. The change record lists the implementation
change and downstream users. Verdict: records agree with the delivery.

Changes in this second reading: added the missing source and blueprint references to the
two new module docstrings and appended this current review. No proof, theorem statement,
predicate implementation, node, or import was changed. The earlier second reading remains
explicitly superseded. Final dry run and delivery compile and probe the complete set.
