## What changed

Proved `AlgebraicGeometry.isAffine_of_finite_closed_cover`. The proof forms the finite
coproduct map `f := Limits.Sigma.desc i`, obtains its affine source and finite morphism
instances, proves surjectivity from `hcover` using
`Surjective.sigmaDesc_of_union_range_eq_univ`, and applies
`isAffine_of_surjective_of_universallyClosed`. Added the proof-only import
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Finite`, which provides finiteness
of a finite coproduct of finite morphisms.

## Proved and sorry left

The declaration `AlgebraicGeometry.isAffine_of_finite_closed_cover` is proved. No
`sorry` remains in the delivered module, and no new declarations with `sorry` were added.
Holes closed: `AlgebraicGeometry.isAffine_of_finite_closed_cover` (one). Holes added: none.
This closes the local hole using an existing open dependency; it is not an axiom-free
proof of the entire import closure: `#print axioms` reports `propext`, `Classical.choice`,
`Quot.sound`, and `sorryAx` from the existing affine-target theorem.

## No longer needed

No imports or DAG nodes from the module's stated plan were removed. The finite-coproduct
finiteness step is supplied directly by the existing source-library instance
`AlgebraicGeometry.IsFinite.sigmaDesc`.

## Where the brief, the DAG or earlier work was wrong

Nothing was wrong. The planned coproduct, finiteness, surjectivity, universal-closedness,
and affine-target steps all elaborate through existing instances and the stated affine
target theorem.


## Second reading by U1

1. Compared the sole delivered module with the repository using `diff -u`. The existing
   theorem signature is byte for byte unchanged, including universes, both indexed
   instances and `hcover`. Only its proof and one plain proof-only import changed.
   No definition, target, public import or other declaration changed. Verdict: pass.
2. Compiled the delivered module with `lcompile.py --all`: clean, exit 0. Compiled a
   scratch copy with `#print axioms` for the theorem and `IsFinite.sigmaDesc`.
   The theorem uses only the three permitted axioms and the existing `sorryAx` noted
   above; the coproduct instance uses only the three permitted axioms. There is no
   local `sorry`, forbidden declaration form, or chosen data from an unproved existence
   theorem. `f` is the actual categorical coproduct map. Verdict: pass.
3. No statements or holes were split off. Checked the empty family: `Fin 0` makes
   `hcover` force the target empty; the finite-coproduct affine and finite instances
   include the empty coproduct. The source instance explicitly handles its empty case.
   For one member the same argument is a finite surjective map from that affine member;
   no disjointness or reducedness is assumed. Verdict: pass.
4. Read Stacks 09NL at https://stacks.math.columbia.edu/tag/09NL and the imported
   affine-target statement. The proof is precisely its coproduct argument, using the
   stronger finite property. Searched `lean/Sheaf`, `lean/WeilConjectures` with closed,
   union, cover and finite-affineness terms, and read Mathlib's finite affine coproduct
   instance and the source `IsFinite.sigmaDesc` proof. No shorter closed-cover theorem
   was found. All three imports have a role: the public closed-immersion vocabulary,
   the final affine-target theorem, and the finite-coproduct instance. No old dependency
   is bypassed. Read `dag/units/sk-thm-curveestimate.json`: its realized statement is
   `thm-sc-proper-cohomology`; this auxiliary proof changes no unit realization or route.
   Verdict: pass; pruning list remains empty.
5. Read node `lem-sc-closed-affine-union-affine` and the records of its permanence,
   closed-immersion-finite, finite-coproduct, finite-closedness and affine-target
   dependencies. Its proof, proof-dependency list and documentary origin still describe
   this argument: the source instance implements the binary finite-coproduct induction,
   and typeclass inference supplies finite implies universally closed. The empty case
   is handled uniformly by those same instances rather than a separate tactic branch.
   No node or dependency change is required. Verdict: pass.

Changed during second reading: clarified the report's local-hole count and remaining
axiom dependency, and added this independent review. The Lean proof needed no repair.
