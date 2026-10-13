## What changed

Proved `AlgebraicGeometry.Scheme.regular_dim_ge_two_outside_divisor_generic_neighbourhood`
in `Sheaf.AlgebraicGeometry.Morphisms.RegularIntegralDivisorBoundary`, preserving its
statement and both public imports. Added the proof-only import
`Mathlib.RingTheory.KrullDimension.Regular` for the nonzerodivisor quotient dimension formula.

The two proved private helpers implement the existing node's first step. `exists_stalk_equation`
chooses the affine equation supplied by the invertible kernel, localizes the surjective
section map, and uses `IsLocalization.ker_map` to identify the stalk kernel. Flatness preserves
the nonzerodivisor, and its zero image puts it in the ambient maximal ideal.
`lift_regular` reuses the generator-lifting argument already proved privately in
`Sheaf.RingTheory.RootAlgebraRegularAtRoot`: lift generators of the quotient maximal ideal,
adjoin the equation, and use the dimension formula to satisfy the regular-local-ring criterion.
This follows Stacks Tag [00NU](https://stacks.math.columbia.edu/tag/00NU).
The local Cartier presentation is Tag [01WS](https://stacks.math.columbia.edu/tag/01WS).

The main proof obtains a nongeneric preimage of a boundary point, proves its stalk dimension
is at least one using `ringKrullDim_stalk_eq_coheight` and `Order.coheight_add_one_le`,
identifies the divisor stalk with the ambient quotient by the first isomorphism theorem,
then combines regularity lifting and the quotient dimension formula. This is the existing
DAG route and keeps the trait/purity step of `sk-prop-input-spreading` intact.

Local compilation passes without warnings, in approximately four seconds.
A separate `#print axioms` check against the compiled sandbox theorem reports exactly
`propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` is reachable. The cases of an
empty boundary and of a zero-dimensional integral divisor are handled by the same proof:
any boundary preimage would be nongeneric and force positive divisor-stalk dimension.
No interface changes or adaptations were made.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.regular_dim_ge_two_outside_divisor_generic_neighbourhood`
(blueprint: `lem-sbc-regular-integral-divisor-boundary`).

There are no `sorry`s left in the item and no holes added elsewhere. Both private helpers
are fully proved. This is a proof, not a decomposition; one hole closed, zero added.

## No longer needed

No original imports, nodes, or planned modules were removed: pruning is none.
The attempted explicit imports `Mathlib.RingTheory.Localization.Algebra` and
`Mathlib.RingTheory.Flat.Localization` were removed after successful compilation because
the original public imports already expose the required localization results.
No new Sheaf proof-dependency module is needed. The generator-lifting argument uses no
root-algebra theorem and therefore does not import `Sheaf.RingTheory.RootAlgebraRegularAtRoot`.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The node's intended Cartier stalk argument and dimension
calculation can be completed using existing library and Mathlib declarations, without
splitting off any additional statement. The source-local private regularity-lifting proof
was useful reusable material; no change to its module was necessary.

## Second reading by F1

1. **Interface and accidental changes.** Compared the delivered module with the repository
version. The public theorem statement is byte-for-byte unchanged; only its proof and one
proof-only Mathlib import were added. No definitions, public declarations, or target
statements changed. Verdict: pass.

2. **Proof and axioms.** Compiled the module with `lcompile.py`; it succeeds without
warnings. The module contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or
`implemented_by`. A scratch `#print axioms` check reaches only `propext`,
`Classical.choice`, and `Quot.sound`. Verdict: pass.

3. **Statements and split work.** No statements were split off and no new nodes were
added. The two private helper theorems are internal proof steps, fully proved, and the
main theorem has exactly the existing target statement. The edge cases described in the
report are covered by the hypotheses and proof. Verdict: pass.

4. **Route and pruning.** The proof follows the node's Cartier stalk, regular quotient,
and dimension-increase route, preserving the unit `sk-prop-input-spreading`. The added
Krull-dimension import is used; the attempted localization imports were correctly
removed, and no existing proof dependency or module can be pruned. Verdict: pass.

5. **DAG agreement.** The node's declaration, statement, proof origin, and proof
dependencies agree with the delivered Lean module. The unit realization remains
unchanged. Verdict: pass.

I changed only this report by adding this second-reading record; no Lean or DAG repairs
were needed.
