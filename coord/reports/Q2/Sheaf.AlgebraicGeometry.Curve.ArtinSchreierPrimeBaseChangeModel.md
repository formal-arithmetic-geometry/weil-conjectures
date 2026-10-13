## What changed

In `Sheaf.AlgebraicGeometry.Curve.ArtinSchreierPrimeBaseChangeModel`, replaced the sole
`sorry` in
`AlgebraicGeometry.IsCurve.exists_constantZMod_one_frobenius_baseChange_model`
with a complete proof from compatible Artin--Schreier exact rows and coherent models.
The original theorem signature and its docstring remain unchanged. Added only an ordinary
proof import of `Sheaf.AlgebraicGeometry.Curve.ArtinSchreierFrobeniusExactRows`.

The proved private helper `exists_fixedPoints_equiv_of_exact_row` works for any short
exact row of abelian etale sheaves and any additive Frobenius model of its middle term.
It proves the connecting map zero using degree-zero surjectivity, proves the first
cohomology map injective, and uses long-exact-sequence exactness to prove that its image
is precisely the Frobenius fixed subgroup. It builds the additive equivalence and keeps
its value formula. The final proof applies the helper to both rows, then combines the
sheaf-map square, functoriality and `Etale.cohomologyMap_map` to prove the target equality.
Neither fixed-point invariance nor the proper base-change theorem is used.

The new module `Sheaf.AlgebraicGeometry.Curve.ArtinSchreierFrobeniusExactRows` states the
remaining construction of the two coherent Frobenius models and compatible exact rows.
This is a part of the argument, not the target under a different name: it supplies no
kernel equivalences for prime-coefficient first cohomology. The target's injectivity,
surjectivity, equivalence construction and final kernel-level equality are proved here.
Updated the original node's proof route and added the new node with its source, proof
steps, searches, signature and inherited unit. No existing definition, statement,
visibility or public import changed; no forced adaptations or change records are needed.

Validation: both modules compile together through `lcompile.py --all`. The target
compiled on the first attempt, including the generic helper and final naturality proof.
The new statement was checked against the proofs in Stacks Tags 0A3P, 02KH and 0A3J
online; the Stacks tex files are not present in this machine's repository mirror.

## Proved and sorry left

Hole closed (1):
`AlgebraicGeometry.IsCurve.exists_constantZMod_one_frobenius_baseChange_model`, node
`lem-pbc-artin-schreier-prime-base-change-model`.

Hole added (1), exactly `:= by sorry`:
`AlgebraicGeometry.IsCurve.exists_artinSchreier_frobenius_exact_rows`, node
`lem-pbc-artin-schreier-frobenius-exact-rows`, in the new module
`Sheaf.AlgebraicGeometry.Curve.ArtinSchreierFrobeniusExactRows`.

No `sorry` remains in the item's module or its private helper. This delivery is a
**decomposition**, with one upper hole closed and one strictly earlier construction
hole added; it does not claim a net reduction of the number of holes or an unconditional
proof of the target. The remaining work constructs the actual lifted additive structure
sheaves, their constant inclusions and structure-ring pullback map, and the finite scalar
models together with canonical coherent base-change naturality.

Edge cases checked mathematically: dimension-zero connected smooth proper curves are
Spec of the algebraically closed field, so coherent H1 and both fixed groups vanish.
The statement includes this case, whereas the scalar-model dependency requires exact
dimension one. A zero-dimensional V and F=0 cause no exceptional case in the proved
helper: exactness gives the required unique equivalence. The identity field extension
uses the usual tensor-unit comparison. The prime hypothesis excludes characteristic
zero and p=0 or 1. An arbitrary displayed pullback square is handled by transport from
the canonical pullback; no particular model of C' is assumed. No data is defined by
choosing an arbitrary witness of an unproved existence theorem; there are no new data
definitions. The kernel equivalence constructed from a bijection is determined by its
proved underlying-value formula.

## No longer needed

No nodes or modules are pruned. The redundant added proof import
`WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic` was removed during
second reading: it is already publicly imported by `TopologicalInvariance`. No original
imports were removed. The original five planned proof dependencies are
retained in the proof plan of the new construction node, rather than claimed as pruned:
`lem-sc-additive-cohomology-finite-scalar-model`, `lem-sc-as-sequence`,
`lem-sc-flat-base-change-coherent`, `lem-weil-pbc-sheafH-ext-derived-comparison`, and
`lemma-weil-pbc-smooth-curve-artin-schreier-proper-degree-zero`.
The new node additionally records the quasi-coherent comparison and Cech-computation
ingredients needed to establish canonical Frobenius and pullback naturality.
The unit `sk-thm-p1` and all its realized steps stay intact.

## Where the brief, the DAG or earlier work was wrong

The planned declarations do not directly expose the joint coherent comparison diagram
with its base-change map, Frobenius compatibility and constant-inclusion square. In
particular `nonempty_H_pullback_linearEquiv` only states existence of a linear
equivalence, not its compatibility with the canonical cohomology pullback and Frobenius.
This missing interface is precisely the new construction statement. Existing scalar
models and proper degree-zero statements require `IsConnectedCurve` (dimension exactly
one); the item permits dimension zero as well. The new node explicitly records that
case instead of applying those declarations outside their hypotheses.

Naturality in O-linear module maps alone does not give compatibility with Frobenius,
which is semilinear. The new construction proof specifies common affine-cover Cech
comparisons; sectionwise powers commute with these comparisons and with structure-ring
pullback. LeanSearch returned Internal Server Error and LeanFinder was unavailable;
these failures are recorded honestly. Loogle and source searches found the algebraic
exactness machinery used in the completed proof, but no complete coherent diagram.
There is no disputed mathematical statement.

## New nodes

`lem-pbc-artin-schreier-frobenius-exact-rows`, in
`dag/nodes/sec-proper-base-change/lem-pbc-artin-schreier-frobenius-exact-rows.json`, states
compatible Artin--Schreier exact rows and coherent Frobenius models before computing
their degree-one kernels. Its module is
`lean/Sheaf/AlgebraicGeometry/Curve/ArtinSchreierFrobeniusExactRows.lean` and its sole
public theorem is
`AlgebraicGeometry.IsCurve.exists_artinSchreier_frobenius_exact_rows`.
It inherits `sec-proper-base-change` / `sk-thm-p1` and the item's blueprint ancestry.
The old node's only proof dependency is now this new node; its Lean proof separately
performs the generic long-exact-sequence argument and naturality calculation.
No change record is required.


## Second reading by Q2

1. **Interfaces: pass.** Compared the complete item against the repository with `diff -u`.
   The sole existing theorem signature and its docstring are byte-for-byte unchanged;
   all existing public imports remain. Only a private proved helper, a proof import,
   and the target proof were added. There are no definitions, interface changes,
   forced adaptations or change records.
2. **Proof and axioms: pass as a decomposition.** Compiled both delivered modules through
   `lcompile.py --all`, then compiled a scratch copy with `#print axioms` for the private
   helper, target and new construction theorem. The helper uses only `propext`,
   `Classical.choice`, `Quot.sound`; the other two additionally use `sorryAx` as expected.
   Exactly one named public theorem has `:= by sorry`, in the new module; there are no
   forbidden declarations or data definitions. Read the long-exact-sequence arguments
   and the final naturality rewrite against the upstream API. The target derives both
   equivalences with proved bijectivity, rather than choosing unconstrained data in a
   definition.
3. **Split statement: pass.** Independently read Stacks
   [0A3P](https://stacks.math.columbia.edu/tag/0A3P),
   [02KH](https://stacks.math.columbia.edu/tag/02KH) and
   [0A3J](https://stacks.math.columbia.edu/tag/0A3J), the scalar-model, exact-sequence,
   degree-zero and flat-base-change declarations. The remaining theorem concerns the
   compatible additive structure-sheaf/coherent diagram, before identifying kernels;
   it omits the target's kernel equivalences. Its proof docstring and node specify a
   real construction. Checked Spec k, V=0, F=0, identity extension, prime p=2 and arbitrary
   displayed pullback squares; none needs a new hypothesis. Connected smooth proper
   schemes here are geometrically connected, and dimension zero gives Spec k. The
   new statement is true and supplies exactly the diagram used by the proved reduction.
   Independent `msearch.py` Loogle search for `Function.Exact, Function.Surjective`
   finds generic algebraic exactness only. Source searches with `cohomology`,
   `Frobenius`, `artinSchreier` and exactness names found no existing compatible diagram;
   `ArtinSchreierCohomologyEpi` constructs a single Frobenius model but supplies no
   canonical base-change comparison. The independent LeanFinder result is recorded
   in the search log. Closing the remaining construction is substantial further work.
4. **Route and pruning: pass after repair.** The reduction directly uses upstream
   exactness and functoriality, followed by the new strictly earlier construction
   statement. The old five planned dependencies remain in that construction's proof
   plan; none is reported pruned. Read `dag/units/sk-thm-p1.json`: all realized steps
   remain untouched, and no unit-level argument is bypassed. Removed the redundant
   newly added Basic proof import, since TopologicalInvariance publicly exports it;
   recompilation without it succeeds. All retained public imports serve the signatures.
5. **DAG: pass.** Checked both nodes against the delivered Lean, including the new
   theorem's recorded signature, source, proof steps, dependency union, ancestry,
   chapter/unit, creation and search fields. The existing node changes only the
   permitted proof-route fields. Its exactness and naturality steps match the actual
   helper and final proof; the new node retains the construction ingredients.

Second reading changed only the redundant proof import and this report. One original
hole is closed and one construction hole is added: net zero, a decomposition rather
than an unconditional proof. No new mathematical or interface fault was found.
