## What changed

Replaced the hole in
`AlgebraicGeometry.Scheme.adicResidue_koszul_tensor_cone_proZero` by a reduction
using the proved algebraic Noetherian Koszul augmentation theorem, exact-functor
transport of localized zero maps, the proved K-flat tensor transport, and an
isomorphism of the actual strict mapping-cone towers. The last isomorphism comes
from the existing transposition isomorphism and the identity on the target.
The original declaration's signature and public imports are unchanged.

Added `Sheaf.Paper.AdicResidueKoszulCoefficientConeComparison`. Its one remaining
obligation is a finite comparison: an exact realization functor and isomorphisms
between algebraic and actual coefficient augmentation cones, commuting with the
specified transitions. It asserts neither pro-zero vanishing nor tensor transport,
and contains no arbitrary complex P or derived inverse limit. The supplied algebraic
maps are normalized on every component; their derived pro-zero property is proved
by the existing algebraic theorem and is not assumed in this new comparison.

Proof imports use the existing algebraic theorem and the proved internal transport
lemmas in `Sheaf.CategoryTheory.FlatConstantTensorProZeroCones` (`import all`).
Local irreducibility keeps completed sheaves and internal Hom models folded during
elaboration; no shared definition or exported attribute changes. A proved private
generic comparison lemma factors out transport of localized zero maps, avoiding
repeated expansion of the concrete Koszul complexes.

Validation: the remote compiler accepts the item in 53.2 seconds and the new
finite-comparison module in about 23 seconds, below the 60-second limit. The
original statement was compared verbatim and is unchanged. All Lean lines have
at most 100 characters. There are no debugging options or proof placeholders
inside the item.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.adicResidue_koszul_tensor_cone_proZero`
(node `lem-sfb-adic-residue-koszul-tensor-cone-pro-zero`).

Added one hole, the entire proof of the public theorem
`AlgebraicGeometry.Scheme.adicResidue_koszul_coefficient_cone_comparison`
(node `lem-sfb-adic-residue-koszul-coefficient-cone-comparison`). Its source,
complete proof in words, normalized algebraic maps, and all transition equations
are in its docstring and node.

This is a decomposition: one upper hole closed, one strictly smaller finite
comparison added, net zero holes closed. The item module has zero holes; the
new module has one. No hole is inside a definition or a private theorem.

## No longer needed

No original import was removed and no module is claimed globally pruned.
The unit's route is preserved.

`lem-weil-pbc-ringed-negative-koszul-duality`,
`lem-cbc-signed-koszul-finite-coordinates`, and
`lem-weil-pbc-constant-completion-equivalence` are no longer direct proof
dependencies of the item: they belong to the finite coefficient comparison.
They remain dependencies of that new node and are not withdrawn.

The flat-term hypothesis on P is retained verbatim, although the proved tensor
transport uses K-flatness alone. No tensor product is interchanged with an
infinite product, and no derived-limit theorem is needed.

## Where the brief, the DAG or earlier work was wrong

The original one-step proof plan did not provide the finite comparison between
the ordinary exterior complexes of its algebraic dependency and the actual
completed coefficient complexes on the chosen slice. The library's existing
finite comparisons use a different scheme/site/coefficient presentation, with
coefficient universe `u + 1`, rather than this independent universe
`max v (u + 1)`. They do not directly instantiate to this statement.

The algebraic pro-zero theorem and generic exact/K-flat transport already have
complete proofs; they are used rather than split off again. Only the finite
realization comparison remains. No original statement is disputed or weakened.

## New nodes

`lem-sfb-adic-residue-koszul-coefficient-cone-comparison`, in
`dag/nodes/sec-six-functors-basics/`, records the finite exact-realization and
strict cone comparison before tensoring. It has no pro-zero conclusion and
requires no pro-zero hypothesis. Its module is
`Sheaf.Paper.AdicResidueKoszulCoefficientConeComparison`.
No change record is needed: no existing interface or other module is changed.

## Second reading by G2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
