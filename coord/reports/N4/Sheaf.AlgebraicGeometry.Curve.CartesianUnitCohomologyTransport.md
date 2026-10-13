## What changed

The original `exists_cartesian_unit_cohomology_transport` statement and docstring are unchanged.
Its proof now constructs a forward linear map from canonical base-change cohomology to displayed
unit cohomology using `h.isoPullback.hom`, the ordinary `pullbackObjUnitIso`, and the structural
unit map. `LinearEquiv.ofBijective` inverts this map; injectivity and the forward composition
identity prove the requested inverse-transport equality.

The new module `Sheaf.AlgebraicGeometry.Cohomology.UnitCohomologyPullbackLinear` gives the actual
Ext-based linear map, with a proved scalar-compatibility argument, and separates its bijectivity
for scheme isomorphisms. The new module
`Sheaf.AlgebraicGeometry.Cohomology.CartesianUnitCohomologyPullbackComposition` states the
composition identity for that specified forward map. Proof-only dependencies are plain imports.
No arbitrary equivalence is chosen from an existence theorem; all data is constructed.

## Proved and sorry left

Closed original hole: `AlgebraicGeometry.Scheme.Modules.exists_cartesian_unit_cohomology_transport`.
There is no direct `sorry` in the item's module. Its proof still depends on the lower holes below;
this is a decomposition, not a completed axiom-free proof of the target.

Added holes:
- `AlgebraicGeometry.Scheme.Modules.unitCohomologyPullbackLinear_bijective`, node
  `lem-pbc-unit-cohomology-pullback-linear-bijective`.
- `AlgebraicGeometry.Scheme.Modules.cartesian_unit_cohomology_pullback_comp`, node
  `lem-pbc-cartesian-unit-cohomology-pullback-comp`.

The real definition `AlgebraicGeometry.Scheme.Modules.unitCohomologyPullbackLinear` has no hole.
Against the repository baseline this closes one hole and adds two (net minus one), so no net
proof progress is claimed. Both lower statements are strictly parts of the argument: invertibility
of a specified map, and its composition identity. Neither restates existence of the target's
compatible linear equivalence.

The first worker's never-delivered `cartesian_unit_cohomology_equiv` and
`cartesian_unit_cohomology_equiv_compat` and their two new node files were removed. They do not
count as baseline holes closed.

## No longer needed

Removed direct imports from the item:
- `Sheaf.AlgebraicGeometry.TensorPullbackStructureSheaf`: its tensor-pullback construction is
  unnecessary; this argument uses Mathlib's ordinary pullback of the unit.
- `Sheaf.AlgebraicGeometry.Cohomology.InverseImageCoefficientComposition`: moved to the new
  composition lemma's proof dependency, so it remains a transitive import.

Every old direct `proof_deps` entry was checked:
`def-pc-flat-cohomology-comparison` is retained;
`lem-pc-coefficient-unit-composition` is now a dependency of the composition helper rather than
of the final inversion argument;
`lem-weil-pbc-module-pullback-structure-sheaf` is unnecessary as a proof dependency, because
Mathlib's already proved ordinary `pullbackObjUnitIso` and its adjunction identity suffice.
No unit-level realized node is bypassed. Global module pruning is left to the maintained import
closure and ledger; removing a direct import alone is not a global pruning count.

The previous draft's undelivered `UnitCohomologyPullbackComposition` and
`UnitCohomologyPullbackIsomorphism` modules are not part of this delivery.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the first worker's new `cartesian_unit_cohomology_equiv_compat` quantified over
an arbitrary linear equivalence, although its prose referred to a canonical comparison. Already
for identity base change on Spec Q in degree zero, the structural map is nonzero and negating
an equivalence destroys its compatibility. Existence of an equivalence with conclusion `True`
does not select the canonical one. This was a mathematical error, not a proof tactic issue.

The two first-worker nodes also depended on their own parent transport theorem, giving a circular
plan, and their natural-language statements were placeholders rather than self-contained claims.
The repaired nodes have explicit statements, acyclic dependencies, and complete proof descriptions.
Splitting files to evade a timeout is not an acceptable justification: the new separation follows
the generic isomorphism lemma and the distinct cartesian composition identity.

## New nodes

`def-pbc-unit-cohomology-pullback-linear` records the explicit Ext comparison and its proved
linearity, in `UnitCohomologyPullbackLinear.lean`.

`lem-pbc-unit-cohomology-pullback-linear-bijective` records invertibility of that map through a
scheme isomorphism and a specified coefficient isomorphism, in the same module.

`lem-pbc-cartesian-unit-cohomology-pullback-comp` records composition with the untensored
base-change map, in `CartesianUnitCohomologyPullbackComposition.lean`. Its conclusion contains
no existential comparison or invertibility claim. Searches by different terminology found only
the generic Ext and adjunction APIs; LeanSearch returned Internal Server Error and is recorded
as unavailable. No definition or existing statement changes; no change record is needed.

## Second reading by N4

1. Compared the original and delivered item with `diff` and checked the complete existing theorem
   signature byte for byte: identical. Its docstring is identical too. No existing definitions,
   visibility, or public imports were changed, and no other existing module is adapted. Verdict:
   preserved after repair.
2. All three delivered modules compile separately in import order through `lcompile.py`, without
   errors or warnings. The only direct holes are the two named lower theorems listed above, and
   there are no hollow definitions or forbidden commands. Axiom inspection is recorded below.
   Verdict: valid reduction, still conditional on the documented lower holes.
3. Rejected the false arbitrary-equivalence compatibility statement and replaced both helpers.
   The new bijectivity claim assumes a scheme isomorphism and an explicit coefficient isomorphism;
   the composition claim uses the constructed map and requires no bijectivity. Checked identity
   base change, degree zero, zero rings and empty schemes mathematically. Each lower theorem has
   a source, full proof docstring, self-contained node, and searches against Mathlib and lean/.
   Verdict: true, needed, and strictly smaller; neither is a target restatement.
4. Read the plan and `dag/units/sk-thm-p1.json` realized routes. The changes are below unit level;
   the Artin-Schreier/curve route is kept. Reused the existing linearity and coefficient APIs and
   Mathlib's ordinary unit pullback rather than tensor-pullback infrastructure. The report lists
   every old proof dependency's disposition. Verdict: route kept and imports pruned appropriately.
5. Opened the original node and every new node beside the Lean. Their signatures agree verbatim
   after whitespace normalization, proof dependencies are exactly the union of step uses, and
   there is no backward dependency on the parent. The original node's only edited fields are
   proof, proof_deps, and proof_origin. Verdict: DAG matches the actual reduction.

Changed in the second reading: removed the false and circular split, constructed and proved the
linear forward map, supplied two sound smaller obligations, rewrote the inversion proof, removed
the tensor-pullback proof import, and corrected the nodes and report. This reports decomposition
honestly instead of calling the conditional target a finished proof.

Axiom check: a scratch copy compiled with `#print axioms` for all four declarations.
`unitCohomologyPullbackLinear` uses only `propext`, `Classical.choice`, `Quot.sound`.
The two lower theorems and the final transport theorem additionally use `sorryAx`, exactly as
reported. No other axiom occurs. The scratch copy was removed before delivery. A short attempt
to close the generic bijectivity statement using an explicit pushforward equivalence reached
the 60-second compile limit; that unfinished experiment stays outside the delivered lean/ tree.
