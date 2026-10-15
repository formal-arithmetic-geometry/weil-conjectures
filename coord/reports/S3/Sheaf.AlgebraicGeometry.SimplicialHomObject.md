## What changed

In `Sheaf.AlgebraicGeometry.SimplicialHomObject`, proved
`AlgebraicGeometry.Scheme.SimplicialHomFamily.precomp_compatible` by introducing
`m n φ s`, rewriting by `Category.assoc`, and applying `f.property m n φ s`.
This is exactly the argument already in the declaration's docstring: precompose
the compatibility equation with `g`. No declaration signature or definition changed.

The whole module compiled cleanly through `lcompile.py`. Loogle confirms
`CategoryTheory.Category.assoc` in `Mathlib.CategoryTheory.Category.Basic`;
the local source search confirms it is the required associativity equation.
The proof uses no finiteness or nonemptiness assumptions, so also covers empty
simplicial degrees without any extra cases.

## Proved and sorry left

Closed the only hole:
`AlgebraicGeometry.Scheme.SimplicialHomFamily.precomp_compatible`
(node `def-weil-pbc-simplicial-hom-object`). Proved 1 of 1 sorries in the item;
0 split off, 0 added, and none left in the delivered module.
The imported existence theorem is unchanged and is not used to prove compatibility.

## No longer needed

None. No proof dependency imports were added or removed. The two existing public
imports supply the formal étale coproduct and simplicial-set interfaces, the
existence theorem cited in the definition's documentation, and `IsRepresentedBy`.
No node or module is made unnecessary by this elementary proof. The node already
has empty `proof_deps`, which agrees with a proof using only a defining equation
and the category associativity law.

## Where the brief, the DAG or earlier work was wrong

None. This item has one elementary compatibility obligation, rather than a
multi-page argument. Its existing docstring already gives the complete proof.
The unit record `sk-prop-h2` has no realized statement or step attached to this
node; the proof changes no unit route. No new nodes or interface changes.

## Second reading by S3

1. **Statements and accidental changes.** Compared the delivered module with the repository
   version. The declaration signatures and definitions are byte-for-byte unchanged; only the
   proof of `SimplicialHomFamily.precomp_compatible` changed.
2. **Proof and axioms.** Compiled the module with `lcompile.py`; it succeeds with no errors,
   and the delivered module contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or
   `implemented_by`. A scratch copy with `#print axioms` for all six declarations compiled:
   every declaration uses only `propext`, `Classical.choice`, and `Quot.sound`, with no
   `sorryAx`. In particular no data is chosen from the imported unproved existence theorem;
   `simplicialHomRestriction` inverts the bijection supplied by its `hu'` argument. Verdict: pass.
3. **Statements split off.** No statements were split off and no new nodes were added. The
   existing theorem is exactly the compatibility equation documented in the module and is
   true for all degrees, maps, and simplices, including empty degrees.
4. **Route and pruning.** The proof follows the declaration's direct elementary route and does
   not bypass a realized unit step. No imports or proof dependencies became unnecessary.
5. **DAG agreement.** The existing node `def-weil-pbc-simplicial-hom-object` remains the
   theorem's node; its statement and empty `proof_deps` agree with the proof. The unit
   `sk-prop-h2` has no realized statement or step for this item.

All five checks pass. Changed during second reading: appended this review and the independent
axiom-check results; no Lean code or DAG changes were needed.
