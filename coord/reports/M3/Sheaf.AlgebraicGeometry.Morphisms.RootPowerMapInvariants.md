## What changed

Replaced the proof of `AlgebraicGeometry.Scheme.root_power_map_invariants` in
`Sheaf.AlgebraicGeometry.Morphisms.RootPowerMapInvariants` with a complete Lean proof.
Its signature, visibility, docstring and imports are unchanged.

Injectivity uses the two monic power bases, Lagrange's cardinality identity,
and linear independence of the target basis restricted to exponents `|K| * i`.
The fixed-element calculation expands in the monic basis, computes the diagonal
rotation action on coefficients, and uses a generator of K and the unit-separation
hypothesis to kill coefficients whose exponents are not divisible by |K|.
The preimage is the explicit finite sum of those coefficients times powers of the
source root. Conversely, each rotation composed with the power map equals the
power map by root extensionality and the subgroup cardinality power identity.
The zero ring is handled separately; the argument includes n=1, trivial and full
subgroups, and arbitrary h (including zero).

Mathlib and both project roots were searched for existing power-map invariant
results. LeanFinder returned monic-root coefficient and power-basis ingredients,
not an exact theorem. The proof uses the existing Mathlib ingredients directly.
No dependency modules or intermediate statements were added.

## Proved and sorry left

Closed the one original hole: `AlgebraicGeometry.Scheme.root_power_map_invariants`
(node `lem-sbc-root-power-map-invariants`). No sorry remains and no hole was added.
The final module compiles cleanly through lcompile.py.

## No longer needed

None. No imports were added or removed. The original DAG has no proof dependencies;
the proof follows its three monic-basis, coefficient-vanishing and explicit-image
steps using Mathlib. No project node or module is bypassed.

## Where the brief, the DAG or earlier work was wrong

None. The node's mathematical plan works over arbitrary commutative rings with
the given hypotheses. The unit route is preserved, and no interface changed.

## Second reading by M3

1. I diffed the delivered module against the repository version. The theorem
   signature, declaration visibility, docstring, and imports are unchanged; the
   only change is the proof body.
2. I compiled the module with `lcompile.py`, and compiled a scratch copy with
   `#print axioms`. It is error-free and uses only `propext`, `Classical.choice`,
   and `Quot.sound`; there are no `sorry`s, axioms, unsafe declarations, or
   hollow definitions.
3. The proof closes the original target directly. Its finite-basis argument and
   coefficient calculation cover the zero ring branch, positive n, trivial and
   full subgroups, and arbitrary h. No statement was split off, and searches
   found no pre-existing theorem with this statement.
4. The proof follows the node's three stated steps (monic bases and injectivity,
   coefficient vanishing under the cyclic action, and explicit image/range
   construction). It uses only the existing Mathlib imports, so no import or
   proof dependency can be pruned; the unit record remains unchanged.
5. The DAG node's declaration, proof route, proof dependencies, and origin agree
   with the Lean proof. The unit route is preserved and no interface changed.

I changed only this report by adding this second-reading record; no Lean source,
node, or import needed repair.
