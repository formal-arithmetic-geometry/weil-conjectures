## What changed

Filled `AlgebraicGeometry.etale_reduced_cartier_descent` without changing its statement,
universes, visibility, public imports, or existing docstring. The proof establishes the
kernel equality and isomorphism for an arbitrary etale pullback, uses flat ideal comap for
the forward implication, and applies the existing `fpqc_cartier_ideal_reflection` for the
reverse implication. Pullback symmetry aligns the two conventions for projections.

Added proof imports of `Mathlib.AlgebraicGeometry.PullbackCarrier` and
`Sheaf.AlgebraicGeometry.FpqcCartierIdealReflection`. Updated only the item's node's proof,
proof dependencies, proof origin, and obsolete tool approvals. No other existing module or
node is changed.

Read the dependency declarations before assembling the argument. Searches with the supplied
LeanFinder, Loogle, and grep services found no theorem solving the whole item; direct source
search found the shorter reduced-structure uniqueness argument. The sources checked were
Stacks Tags 083C, 034E, and 01J3 in the local literature. The unit route is preserved: this
still supplies the same descent statement used in the free-characteristic boundary step.

## Proved and sorry left

Closed the one existing hole: `AlgebraicGeometry.etale_reduced_cartier_descent`
(node `lem-trf-etale-reduced-cartier-descent`). There are zero holes left in the item and
zero holes added by this delivery. No new declarations or split statements are introduced.

The converse uses the already stated `AlgebraicGeometry.fpqc_cartier_ideal_reflection`
(node `lem-trf-fpqc-cartier-ideal-reflection`), whose existing proof remains `sorry` in its
own module. This delivery proves the item from that declared dependency; it does not claim
that the entire transitive dependency closure is axiom-free yet.

Validation: the completed item compiled cleanly through `lcompile.py` in 3.5 seconds,
with no warnings. The new proof import was checked for absence of an import cycle.

The argument retains arbitrary covering-index universes. Joint surjectivity is used
pointwise, without assuming a nonempty index type. Empty covers over the empty scheme,
empty divisors (unit ideals), and the closed subset equal to the whole scheme require no
extra hypothesis or separate branch.

## No longer needed

Removed these private proof imports from the item:

- `Sheaf.AlgebraicGeometry.FpqcFinerThanEtale`;
- `WeilConjectures.AlgebraicGeometry.Descent`;
- `WeilConjectures.AlgebraicGeometry.Modules.VeryAmple`;
- `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier`.

The planned dependency `lem-trf-reduced-flat-pullback-recognition` and its module
`Sheaf.AlgebraicGeometry.ReducedFlatPullbackRecognition` are unnecessary here: the item
needs only the kernel equality and isomorphism, already supplied by reduced-structure
uniqueness after the Mathlib range formula. It needs none of that lemma's tensor-module
injection or image-subobject assertions.

The planned dependency `lem-weil-pbc-fpqc-finer-than-etale` and the proof dependency
`def-weil-pbc-etale-site` are unnecessary here: the family is directly an fppf family of
scheme morphisms, and the existing Mathlib leaf `lem-trf-fppf-covering-is-fpqc` gives fpqc
membership. No small-site construction is used.

The Cartier-ideal definition remains a statement dependency. No separate use of it as a
proof lemma is needed, since `IsInvertible` is already the regular-generator condition.
Likewise no separate Cartier-centre/invertible-ideal equivalence is used. Removed obsolete
direct tool approvals for `lem-pc-fpqc-descent`,
`lem-weil-pbc-fpqc-finer-than-etale`, `lem-pc-closed-imm-base-change`,
`lemma-nagata-effective-cartier-is-invertible`, and
`lemma-nagata-invertible-ideal-is-effective-cartier`. Generic module descent and ideal
comparison remain internal responsibilities of the retained fpqc reflection dependency.

These are dependency removals for this item. No library module is withdrawn, and no claim
is made that these modules are unused by all other consumers.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement defect was found. The DAG's recognition step was stronger than
needed by this consumer, and its small-etale-to-fpqc packaging can be replaced by the
existing Mathlib fppf-to-fpqc inclusion. Both simplifications are below the unit route.

## Second reading by U3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
