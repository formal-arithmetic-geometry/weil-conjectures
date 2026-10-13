## What changed

Reduced `AlgebraicGeometry.Etale.tailOpenDifference_naturality` to two individual
restriction-square statements, preserving its entire original signature and docstring.
Added the proof-only imports `Sheaf.AlgebraicGeometry.EtaleLimitStageRestrictionNaturality`
and `Sheaf.AlgebraicGeometry.EtaleLimitConeRestrictionNaturality`.

The parent constructs stage and limit additive homomorphisms explicitly by
`(x,y) ↦ res(x) - res(y)`. Its value formulas hold by reflexivity. For each of the two
inclusions into the intersection it applies the corresponding individual-square lemma,
uses the proved private `differenceMap_natural` lemma, which substitutes those
equalities and applies `AddMonoidHom.map_sub`. This proves the existence,
value formulas, and the combination of the two component squares for both transitions
and legs. The remaining statements assert one restriction square for arbitrary nested
opens; neither asserts difference-map data, paired naturality, or the parent conclusion.
The DAG proof and dependencies now record this reduction. No target or existing
intermediate signature, definition, visibility, or public import changed. Local
irreducibility annotations for cohomology maps and the Ext group instance stabilize
elaboration. The static interface detector requires their scope to be recorded in
`coord/changes/etale-limit-open-difference-proof-attributes.md`; they do not export
attributes or require adaptations.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.Etale.tailOpenDifference_naturality`
(node `lem-weil-pbc-etale-limit-open-difference-naturality`) by a decomposition.
The private additive construction `differenceMap` and its general naturality lemma
`differenceMap_natural` are proved and have no holes.

Two holes added, each the whole proof of a named public theorem in its own module:

- `AlgebraicGeometry.Etale.tailOpenCohomologyMapDegree_restriction`, node
  `lem-weil-pbc-etale-limit-stage-restriction-naturality`, in
  `Sheaf.AlgebraicGeometry.EtaleLimitStageRestrictionNaturality`.
- `AlgebraicGeometry.Etale.tailOpenCohomologyLegDegree_restriction`, node
  `lem-weil-pbc-etale-limit-cone-restriction-naturality`, in
  `Sheaf.AlgebraicGeometry.EtaleLimitConeRestrictionNaturality`.

No `sorry` remains in the parent. This is a decomposition, not a sorry-free proof of
its transitive dependencies: one upper hole closed and two lower holes added. No
existence witness is chosen to define data, and no definition contains `sorry`.

## No longer needed

None globally. Both original public imports remain required for the statement.
The original proof dependencies (cohomology pullback functoriality, inverse-image
composition, and nested-open restriction naturality) are used in the plans of the two
new component-square nodes rather than cited directly by the parent's additive proof.
They are not mathematically pruned. No unit statement, unit proof step, or module on
the unit's required route is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error found. Mathlib and blueprint searches found no direct
canonical stage/cone specialization. The existing nested-open pullback naturality theorem
is the intended input, but it must be transported through the supplied inverse-image
opens and composed with coefficient naturality. Both complete transport arguments are
in the new docstrings and nodes.

I wrote and compiled the general restriction/coefficient square helpers, and attempted
the entire proof using these helpers, local and private stage/cone specializations,
additive-map constructions, and a generic subtraction lemma. Elaboration reached the
kernel check, but the complete file repeatedly exceeded the prescribed 60-second check;
profiling localized substantial cost to dependent cohomology-type transports. I did not
raise the file timeout or deliver a repartition of that large proof across files. The
delivery instead leaves the two strictly smaller geometric compatibility assertions
for subsequent work, while proving the original additive construction and combination.
Diagnostic and attempted proof files are only in the sandbox scratchpad, not delivered.

The new assertions handle empty opens, equal opens, identity stage maps, and zero
coefficient morphisms by the same restriction/pullback naturality identities. They assume
no cover, coefficient identity/composition laws, formula for G's arrows, limit, colimit,
directedness, or nonemptiness. LeanSearch returned Internal Server Error; LeanFinder,
Loogle, local Mathlib/project grep, and blueprint duplicate searches completed.

## New nodes

`lem-weil-pbc-etale-limit-stage-restriction-naturality` is the stage component of the
parent's first proof step. It asserts that one nested-open restriction commutes with
one canonical transition with arbitrary coefficient morphism. Its source is Stacks
Tag 01F7, specialized to the restricted maps of Tag 09YQ; its proof first identifies
the inverse-image stage opens, then combines pullback restriction naturality and
coefficient naturality, including the composition comparisons.

`lem-weil-pbc-etale-limit-cone-restriction-naturality` is the cone component of that
same step. The cone equation identifies the supplied limit opens with inverse images
under c_j, and the single coefficient map is `(eG j).inv ≫ L.ι.app j`. The same restriction
and coefficient calculation gives one cone-leg square. These assertions are independent
of each other and strictly parts of the original argument. The required local-attribute record is
`coord/changes/etale-limit-open-difference-proof-attributes.md`. It inventories downstream
users and documents that no exported signature or global attribute changes and no
consumer is adapted.

## Second reading by K2

1. **Interface comparison — pass.** Compared all delivered Lean modules with the repository versions. The parent theorem signature is byte-for-byte unchanged; the two new theorem modules are separate split-off statements. The only interface additions are proof-only imports in the parent and the two new modules. The parent DAG record now records K2 as the proof author for this proof route.

2. **Proof and axioms — pass.** Compiled all three delivered modules with `lcompile.py`; the parent has no `sorry`, and the two split-off component theorems contain the only remaining named `sorry`s. No forbidden declarations or hollow definitions occur. The parent proof uses an explicit additive construction and `map_sub`; no arbitrary existence witness is used. The split-off statements are documented with their sources and complete proof plans.

3. **Statement review — pass.** Checked both split-off restriction squares on empty opens, equal opens, identity transitions, and zero coefficient maps. They are true, strictly simpler components of the parent argument, and no duplicate declaration was found in Mathlib or the project. Their DAG nodes match the Lean statements and list the imported naturality dependencies.

4. **Pruning and route — pass.** The parent uses the two component nodes and retains the unit route; no old proof dependency or import can be removed from the delivered closure. The parent’s plain imports are proof-only, while public imports are needed by its statement. The documented local irreducibility attributes are scoped locally and have the accompanying change record.

5. **DAG and report consistency — pass.** Verified the parent proof steps, `proof_deps`, `proof_origin`, and the two new node records against the Lean code. The unit route is not bypassed. I changed only the parent node’s Lean-record author from stale `J3` to `K2` and added this second-reading section; no theorem statement or definition was changed.

## Review by K2

I independently read the delivered parent and both split-off modules and checked their declarations against the repository and DAG records. The parent signature is unchanged, its explicit difference homomorphisms are legitimate constructions, and its naturality proof uses exactly the two component squares. Both component statements are true specializations with no extra hypotheses, are documented with sources and proof plans, and retain the unit route. Compilation succeeded and no forbidden declarations or hollow definitions were found.
