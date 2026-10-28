## What changed

Replaced the proof hole in
`AlgebraicGeometry.Scheme.hasTorsionEtaleCohomologicalDimensionLE_one_of_finite_baseField`
without changing its statement, public imports, or any definition. The proof uses the
proved source equivalence between étale sheaves and discrete Galois modules, the
all-torsion degree-two criterion, and the Ext/derived-global-sections comparison.

For an open Galois subgroup, infinite Galois correspondence supplies a finite fixed
field. The proof handles its characteristic-prime constant coefficients by the
proved affine Artin–Schreier theorem. The other constant prime coefficients are the
one remaining obligation, in the new module
`Sheaf.RepresentationTheory.FiniteFieldPrimeCohomology`.

All added imports of the item are private proof imports. Existing source modules,
existing signatures, attributes, instances, and public imports are unchanged.

## Proved and sorry left

Original holes: 1. Item holes remaining: 0. Holes closed: 1. Holes added: 1.
This is a decomposition, with net zero holes removed, not a completed unconditional
proof of the finite-field cohomological-dimension theorem.

Closed the original hole in
`AlgebraicGeometry.Scheme.hasTorsionEtaleCohomologicalDimensionLE_one_of_finite_baseField`
(node `det-base-field-cd-finite-torsion-bound`). Its assembly proof is complete:
fixed fields, characteristic-prime vanishing, transport along the fixing-subgroup
isomorphism, arbitrary torsion devissage, all degrees greater than one, stalk
comparison, and the derived-category comparison are written in Lean.

The sole added sorry is
`DiscreteModule.subsingleton_H_two_trivialZMod_of_finiteField`
(node `lem-sfb-finite-field-prime-degree-two`). It concerns only degree two, trivial
coefficients Z/ell, and primes nonzero in the finite base field. It has no arbitrary
sheaf, arbitrary torsion module, open-subgroup hypothesis, or higher-degree conclusion.
It is strictly a part of the argument, rather than the original theorem renamed.
Its docstring and node retain the finite cyclic quotient/inflation proof.

The complete sandbox compiled with lcompile.py: new module 3.2 s and item 9.5 s,
with no warnings or errors. A final compile after removing two redundant imports
is recorded by the delivery checks.

## No longer needed

Removed the experimental private imports
`WeilConjectures.RepresentationTheory.DiscreteModule.Transport` and
`Mathlib.FieldTheory.Galois.Infinite`: the public import closure of the required
source GaloisModule comparison already supplies them. No original import was removed.

No existing module or node is withdrawn. In particular,
`det-base-field-cd-galois-group`, `det-base-field-cd-cochains`, and
`det-base-field-cd-inflation` remain dependencies of the new prime degree-two node;
the cyclic computation has not been pruned or bypassed. The full abelian-stalk and
section/invariant comparison interfaces are supplied directly by the proved source
GaloisModule API; their separate Sheaf interface modules need not be imported here.
No source declaration is removed or replaced by a sorry.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The already proved finite-field bound in
`Sheaf.AlgebraicGeometry.Sites.FiniteFieldTorsionCohomologicalDimension` cannot be
imported here: it depends on this item through BaseFieldCohomologicalDimension.

The original plan did not exploit the existing source theorem
`DiscreteModule.subsingleton_H_of_two_le_of_isTorsion`. That theorem implements the
finite-primary decomposition, finite-stable-submodule argument, and coinduced
cokernel dimension shifting needed for arbitrary torsion coefficients. It is used
as a generic devissage tool, as is the proved affine Artin–Schreier vanishing theorem.
Neither tool replaces the finite cyclic quotient/inflation core of the unit: that
core remains exactly the proof obligation of the new lemma.

The node copy now describes the actual assembly proof and names these tools and the
new residual lemma. Only its proof, proof_deps, and proof_origin were changed.
No unit record or target statement was changed.

## New nodes

`lem-sfb-finite-field-prime-degree-two`, in
`dag/nodes/sec-six-functors-basics/lem-sfb-finite-field-prime-degree-two.json`,
attaches the new theorem in
`lean/Sheaf/RepresentationTheory/FiniteFieldPrimeCohomology.lean`.
The source is the current blueprint finite-field proof, Finite modules and
Consequences. Its proof uses the existing absolute-Galois, continuous-cochain, and
cyclic-inflation nodes. LeanSearch, LeanFinder, and source grep found no existing
Mathlib theorem closing this precise case. The trivial finite quotient is included;
prime 0 or 1 is excluded by primality; the characteristic-prime case is handled in
the item by Artin–Schreier; no roots of unity hypothesis is imposed.

There are no definition or existing-statement changes, hence no change record or
forced consumer adaptations are required.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.AlgebraicGeometry.BaseFieldFiniteTorsionCohomologicalDimension": "972c791665504afacf8db36944337b43a1e32645", "Sheaf.RepresentationTheory.FiniteFieldPrimeCohomology": "abfe2b292cac33e460cb3c2ac231615a8a23d98c"}, "results": {}, "time": "2026-10-28T14:16:28+0800", "transitive": 0, "version": 1}
```

## Second reading by Q9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
