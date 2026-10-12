## What changed

Proved `AlgebraicGeometry.Scheme.fromSpecStalk_limit_affine_neighbourhoods` completely,
with its original signature, all ten conjuncts, and no additional declarations.
The final universal property is a categorical construction, not a new holed lemma.

The affine neighbourhood subtype is cofiltered. Its inclusion into all neighbourhoods
is final after taking opposites, so whiskering the existing stalk colimit gives the
colimit of affine-neighbourhood sections. `Scheme.Spec` preserves the corresponding
opposite limit. Compose a compatible family with each affine open's `toSpecΓ`, use the
resulting limit lift, and cancel the affine `toSpecΓ` isomorphisms. `IsLimit.uniq`
proves uniqueness. The neighbourhood factorization and compatibility use Mathlib's
`fromSpecStalkOfMem_ι` and cancellation of open immersions.

This adapts the fully proved construction in
`WeilConjectures.AlgebraicGeometry.FunctionFieldLimit` to an arbitrary point, without
importing that integral-scheme specialization. The source route is still stalk
colimit followed by Spec and affine identification, as in
[Stacks 0GWT](https://stacks.math.columbia.edu/tag/0GWT) and
[Stacks 01YW](https://stacks.math.columbia.edu/tag/01YW). The item's node is not a
unit realization in `dag/units/sk-thm-p1.json`; no unit statement or step is bypassed.

Replaced the public `SpecLocalRingCanonicalMorphism` import with Mathlib's `Stalk`,
removed the module-stalk proof import, and added the proof-only
`Mathlib.CategoryTheory.Filtered.Final` import. The node's proof, proof_deps and
proof_origin now describe the categorical argument. The import/open-command change
record is `coord/changes/spec-stalk-limit-mathlib-imports.md`; its users table lists
all 157 downstream modules. `import_prune_check.py` returned exit code 0.

Local compilation is clean. The unused-variable linter is disabled only for the
existing theorem: its original forall binder `hxU` does not occur in that binder's
conclusion, and preserving the statement leaves this otherwise unavoidable warning.

Searches: LeanFinder for the spectrum-of-stalk limit found the canonical maps but no
limit theorem. Loogle searched `Scheme.Opens.fromSpecStalkOfMem`; grep searched
`isColimitAffineOpensRingCocone|fromSpecStalkOfMem_toSpecΓ`. Direct rg found the complete
function-field construction and checked the exact Mathlib signatures in Stalk,
AffineScheme and Restrict. No new statement was needed.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.fromSpecStalk_limit_affine_neighbourhoods`
(node `lem-weil-pbc-local-ring-spec-limit-affine-neighbourhoods`).

One of one holes proved; zero holes added or split off. No sorry remains in the
item's module or anywhere added by this delivery. All auxiliary constructions are
local to the proof. No axiom, definition, target statement or universe was added or changed.

## No longer needed

Removed imports:
- `Sheaf.AlgebraicGeometry.SpecLocalRingCanonicalMorphism` (replaced by Mathlib `Stalk`).
- `Sheaf.Topology.PresheafModuleStalkFunctor` (ring stalk colimits use Mathlib directly).

Removed proof dependencies:
- `lem-weil-pbc-spec-local-ring-canonical-morphism`: no unfinished affine-description,
  local-properties, module-stalk or quotient-factorization theorem is used.
- `def-weil-pbc-module-stalk`: no module-stalk functor is used; the ring stalk cocone
  is Mathlib's existing neighbourhood colimit.
- `lem-weil-pbc-stalk-germs-on-basis`: finality replaces the elementwise representative
  and equality argument.
- `lem-weil-pbc-affine-open-stalk-localization`: the existing projection-toSpecΓ
  formula identifies the projections directly, without a localization calculation.

The declaration still mentions the canonical map and stalk, so the corresponding
statement dependencies are unchanged. These nodes may be needed elsewhere; this
report removes them from this proof's route only. No import of the function-field
specialization was added.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error found. The earlier seven-step proof plan is valid,
but its elementwise stalk construction and localization comparison are unnecessary:
Mathlib's final-functor colimit transport and projection formula already supply them.
The source checkout's integral hypothesis belongs to its generic-point index type;
the cofinality argument generalizes to the neighbourhoods of any point.

The named local Stacks TeX file is absent on this machine, so the two cited tags were
read directly on the official Stacks website. No source file was written to the
read-only repository. The sandbox is the only manually written workspace.


## Second reading by R3

1. Compared the sole delivered Lean module with the repository using diff and an
   exact string comparison of the existing theorem signature. Verdict: all ten
   conjuncts, binders and universes are byte-for-byte unchanged. There are no new
   declarations or definitions. The public-import and open-command changes are
   declared in `coord/changes/spec-stalk-limit-mathlib-imports.md`.
2. Compiled the delivered file locally without errors or warnings. Compiled a
   scratch copy with `#print axioms` for
   `AlgebraicGeometry.Scheme.fromSpecStalk_limit_affine_neighbourhoods`: exactly
   `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`. Scanned the delivered
   Lean source for sorry, axioms, unsafe, opaque, extern, implemented_by and kernel
   checking bypasses: none. Verdict: a complete kernel-checked proof.
3. No statements were split off and no holes were added. Checked the local
   constructions: the index subtype is nonempty because x has an affine
   neighbourhood; intersections supply common smaller neighbourhoods, even when
   X is not integral or separated. An empty scheme has no x, so creates no extra
   case. Finality is correctly on the opposite inclusion. Cone naturality has
   the correct inclusion direction, and uniqueness uses the full limit property
   for arbitrary T. Verdict: no extra hypotheses or disguised restatement.
4. Read the existing FunctionFieldLimit construction and Mathlib Stalk projection
   formulas; searched the project for alternative stalk-limit constructions.
   The generic-point specialization cannot directly prove this arbitrary-point
   statement. The proof uses Mathlib finality, the stalk colimit and Spec's limit
   preservation, then cancels affine toSpecΓ isomorphisms. The two public imports
   supply signature notions; Filtered.Final is proof-only. Compared old and new
   proof_deps: the report lists all four removed dependencies. Inspected
   sk-thm-p1.realized: this node realizes neither its statement nor a step, and
   that unit route is unchanged. Verdict: valid shorter route and complete pruning.
5. Compared node records: only proof, proof_deps and proof_origin change. Read
   every retained dependency's Mathlib match and checked that the recorded steps
   describe the actual Lean argument, including the canonical projections and
   final cancellation. Verdict: DAG agrees with Lean, with no new nodes needed.

Second reading changed only this report, adding the independent checks above;
no proof repair was needed. The existing theorem docstring still describes the
older seven-step plan (including pruned lemmas); it remains unchanged as existing
API documentation. The updated node and this report describe the actual shorter
proof.
