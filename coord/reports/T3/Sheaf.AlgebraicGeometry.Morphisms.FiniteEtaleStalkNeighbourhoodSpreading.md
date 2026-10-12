## What changed

The original theorem `AlgebraicGeometry.Scheme.FiniteEtale.exists_neighbourhood_model_of_stalk`
now has a complete Lean proof with its signature unchanged. If s lies in U, it uses U and PA
and the identity comparison. Otherwise it descends Q, transports the supplied comparison
along the pullback of the descended-model isomorphism, descends that comparison on a
smaller neighbourhood, and returns the actual restriction of the model.

Two new proof-only imports state the separate object-descent and comparison-descent steps.
The existing node's proof and proof dependencies now follow this assembly.
All three modules compile cleanly with lcompile.py.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.FiniteEtale.exists_neighbourhood_model_of_stalk`
(node `lem-sbc-finite-etale-stalk-neighbourhood-spreading`).
There is no sorry in the original module.

Added two holes, each as the entire proof of a public named theorem in its own module:
- `AlgebraicGeometry.Scheme.FiniteEtale.exists_stalk_neighbourhood_model`
  (`lem-sbc-finite-etale-stalk-model-descent`). This descends an object and properties only;
  it has no U, PA, or overlap comparison.
- `AlgebraicGeometry.Scheme.FiniteEtale.exists_neighbourhood_comparison_of_stalk`
  (`lem-sbc-finite-etale-stalk-comparison-descent`). Both models already exist;
  it only shrinks W and compares their prescribed restrictions, constructing no model.

This is a decomposition, not a completed proof from sorry-free dependencies: one hole
closed and two added. The direct s-in-U branch is independently proved. No data definition
was added and no arbitrary existence witness was used to define an object.

## No longer needed

Removed from the item's direct imports:
- `Sheaf.AlgebraicGeometry.DescendFinite`, node `lem-weil-pbc-descend-finite`;
- `Sheaf.AlgebraicGeometry.EtaleInverseLimitDescent`, node `lem-weil-pbc-descend-etale`;
- `Sheaf.AlgebraicGeometry.SpecStalkLimitAffineNeighbourhoods`, node
  `lem-weil-pbc-local-ring-spec-limit-affine-neighbourhoods`.

These are no longer direct proof dependencies of the assembly. They remain in the
object-descent plan and are imported there; the stalk-limit module is also imported
by comparison descent. Thus none is claimed as pruned from the import closure.
The original public imports support the unchanged signatures. No unit step is bypassed.
No gluing over U union W is required or imported.

## Where the brief, the DAG or earlier work was wrong

The existing node's third step describes non-elementary comparison descent but has an empty
uses list. Its first two steps also omit the finite-presentation object-descent input.
The new nodes record object descent and comparison descent separately, including the
morphism and equality clauses of `thm-pd-spreading-out`. The first worker's starting copy omitted proof-dependency imports, but the current
repository version has all three original planned imports. The second reading relocated
these imports into the object-descent module, where their planned steps now live.

The stalk theorem and property-descent statements were read, as were the upstream
finite-presentation object, map, equality, and isomorphism descent APIs. None directly
states neighbourhood descent with the open-subscheme maps in this item. The assembly
now isolates that geometry instead of moving the original theorem under a new name.

Read the local Stacks limits.tex proofs of 0BQ5 and 0EY3. Their written gluing statement
assumes s outside U, but the inverse-limit object and comparison arguments used here do
not require that assumption. The original theorem handles s in U directly. Empty overlaps
are allowed; W empty is excluded by s in W; an empty C causes no obstruction to either
object descent or descent of the two inverse equations. The unit's route is preserved.
Mathlib searches were run through msearch.py: LeanSearch returned Internal Server Error;
LeanFinder returned etale-locus/stalk API results, Loogle returned fromSpecStalk APIs,
and grep found no matching neighbourhood finite-etale descent theorem.

## New nodes

`lem-sbc-finite-etale-stalk-model-descent` in
`lean/Sheaf/AlgebraicGeometry/Morphisms/FiniteEtaleStalkModelDescent.lean` isolates
object descent, eventual finiteness and etaleness, and the cartesian model comparison.
Its local map l is determined by its composite with the monomorphic open inclusion.

`lem-sbc-finite-etale-stalk-comparison-descent` in
`lean/Sheaf/AlgebraicGeometry/Morphisms/FiniteEtaleStalkComparisonDescent.lean` isolates
spreading an isomorphism between existing models. The returned model is explicitly the
pullback of the supplied R, so the statement cannot substitute an unrelated object.

No statement or definition changed; no change record or forced adaptation is needed.

## Second reading by T3

1. PASS. Diffed every delivered module against the read-only repository. The sole
   existing theorem signature is byte-for-byte unchanged, as is its docstring.
   The other two modules are new; no definition, existing declaration visibility,
   public import, or target statement changes. No change record is necessary.
2. PASS. Compiled all three modules in import order with lcompile.py. The assembly
   has no sorry; the only two sorries are the complete proofs of the two named
   public theorems reported above. No definition is added. Checked the declarations'
   axioms using scratch copies and the delivery probe; only standard axioms and
   sorryAx from the two open descent statements occur. No forbidden declaration
   or compiler trust bypass occurs.
3. PASS as decomposition. Read both new statements and docstring proofs against
   the local Stacks limits.tex proofs of 0BQ5 and 0EY3, and the existing finite-
   presentation object, morphism, and equality descent declarations. Object descent
   omits the prescribed-open comparison; comparison descent fixes the existing R
   and returns its actual restriction, without descending a new object. Each is
   strictly a part of the original argument. No arbitrary existence witness is
   used in a data definition. Tested the empty overlap, U empty, s in U, W=top,
   and empty C: the conclusions and inverse-limit arguments still apply. A point
   s rules out empty S, and hsW rules out empty W. Monicity of the open inclusion
   determines l, so the equation hl cannot permit an unrelated local map.
   Fresh LeanFinder, Loogle, grep, and searches of both Lean roots found no exact
   neighbourhood descent statement: the generic limit APIs still require the
   geometric diagram construction and pullback identifications. Neither new hole
   has a short direct proof from the existing APIs.
4. PASS after repair. The direct s-in-U branch is valid, and the remaining assembly
   transports e by the inverse of the pulled-back model isomorphism in the correct
   direction. New imports in the assembly are proof-only. Added proof-only imports
   to the two split modules for the dependencies of their recorded plans, preserving
   the original dependency closure rather than accidentally pruning it. Corrected
   No longer needed to list all three removed direct imports and their nodes, and
   to distinguish relocation from closure pruning. Read sk-prop-input-spreading's
   realized record and its maximal-open spreading step; no unit route is changed.
5. PASS. The original node's four steps exactly describe the compiled proof; its
   proof_deps are the two applied split statements. Each new node's proof_deps is
   the union of its steps' uses, with source, searches, status, creation, blueprint,
   chapter, unit, and verbatim Lean statement records. The old three dependencies
   remain below model descent. No non-owned node field needs changing.

Second reading changed only the two new modules' proof-plan imports and the report's
removed-import accounting and stale baseline claim. It left the working proof and
all signatures unchanged. One original hole closed, two added: decomposition,
net minus one hole, with no module pruned.
