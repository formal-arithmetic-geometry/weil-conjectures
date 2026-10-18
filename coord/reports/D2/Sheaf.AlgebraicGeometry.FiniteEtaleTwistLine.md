## What changed

Proved `AlgebraicGeometry.Scheme.finite_etale_torsion_twist_line` with its original signature,
universes, visibility, and public imports. Added three fully proved private helpers:
`zmodScalarExtensionIso`, `finiteEtaleLineAbIso`, and `exists_first_twist_cover`.
The first uses uniqueness of left adjoints to identify extension from ZMod N with extension
of the underlying abelian group. The second sheafifies this comparison. The third pulls back
the existing primitive-root cover of the global section ring and uses the existing cyclic
roots-of-unity trivialization, including the coefficient module action. Positive tensor powers
are trivialized by induction, and degree zero by the monoidal unit comparison.

Transport through the equivalence between the localized site and the cover scheme's small
etale site gives the exact isomorphisms required by the statement. These give local constancy.
The existing locally trivial tensor-inverse construction makes tensoring an equivalence,
which supplies preservation of both finite limits and finite colimits.

Added only proof imports `WeilConjectures.EtaleCohomology.TateTwist.Sheaf`,
`WeilConjectures.ConstructibleSheaf.Pullback`, and
`WeilConjectures.CategoryTheory.Abelian.Flat.Basic`. Updated the item's node proof,
proof dependencies, proof origin, and withdrew obsolete tool approvals. No definition,
statement, public import, or consumer was changed.

Validation: the complete proof compiled through lcompile.py; the reduced import set also
compiled (about 6.4 seconds). Edge cases: degree zero uses the unit isomorphism; N=1 permits
the zero coefficient ring; no Nontrivial instance on A or Gamma(T,O_T) is used, so the empty
scheme and zero ring are included. Finiteness of A is not needed by the argument but the
original binder remains.

## Proved and sorry left

Closed the sole hole: `AlgebraicGeometry.Scheme.finite_etale_torsion_twist_line`
(node `lem-asd-finite-etale-twist-line`). Proved 1 of 1 original sorries.
Holes added: zero. Split-offs: zero. No sorry remains in any delivered Lean declaration.
Existing imported obligations are not claimed proved by this delivery. A temporary
`#print axioms` probe reports `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`
from the existing dependency closure (including finiteEtaleMu_annihilated and the
module-enhancement laws in FiniteEtaleTateTwist). The delivered theorem body and all three
new private helpers have no sorry; this is a stage-3 proof from the stated library,
not a claim that the full transitive closure is finished.

## No longer needed

Removed the following original proof imports:

- `Sheaf.AlgebraicGeometry.EtaleStalkTensorScalar`
- `Sheaf.AlgebraicGeometry.Morphisms.RootSplitAwayCoverEtale`
- `WeilConjectures.Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed`
- `WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`
- `Mathlib.AlgebraicGeometry.Sites.EtalePoint`
- `Mathlib.AlgebraicGeometry.Sites.MorphismProperty`
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`
- `Mathlib.CategoryTheory.Sites.Point.Basic`
- `Mathlib.CategoryTheory.Sites.Point.Skyscraper`
- `Mathlib.Algebra.Homology.ShortComplex.ShortExact`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses`
- `Sheaf.CategoryTheory.RingedSiteModules`

The new proof does not use these old proof dependencies:

- `lem-sbc-root-split-away-cover-etale`: the existing, proved primitiveRootsCover API
  supplies the needed etaleness directly; no separate root-cover statement import.
- `lem-weil-pbc-open-immersion-etale` and `lem-weil-pbc-etale-covering-composition`:
  use one pullback of a surjective etale cover over the global section ring.
- `def-weil-pbc-geometric-stalks`, `prop-weil-pbc-geometric-stalks-exact`,
  `lemma-weil-pbc-geometric-stalk-conservative`, `lem-pod-etale-stalk-tensor-scalar`,
  `lem-weil-pbc-etale-cover-geometric-point-lift`, and
  `lem-weil-pbc-constant-sheaf-geometric-stalk`: the tensor-inverse argument replaces
  the full stalk proof of exactness.
- `def-weil-sheaf-of-modules-category` is not a proof dependency: the statement still
  retains it among its statement dependencies, and the implementation uses the published
  category of module-valued sheaves throughout.

Removed the old tool_uses approvals for the eight obsolete tools above, retaining
`lem-sc-primitive-root`, which is used by the source primitive-root covering argument.
Modules newly unreachable from all targets, if any, are for the maintainer's closure audit;
these are claims about this proof's dependencies, not a claim that every removed import is
absent transitively from the whole library.

## Where the brief, the DAG or earlier work was wrong

The planned geometric and interpolation constructions already exist as fully proved source
APIs in PrimitiveRootsCover and Sites.RootsOfUnityConstant. The old direct-proof import list
did not expose them. The finite twist uses extension from ZMod N, whereas the source API
extends the underlying abelian group; the private adjunction comparison supplies the missing
identification without changing either definition.

The stalk-based flatness argument is unnecessary: the existing etale-locally trivial tensor
inverse proves exactness formally. No mathematical statement was disputed or weakened.
The unit record sk-prop-sf-cbc has empty realized statement and steps; no fixed unit route
was bypassed. Sources read: Stacks etale-cohomology.tex section-kummer and
lemma-kummer-sequence (03PK/03PL), groupoids.tex example-roots-of-unity (040M), and
etale-cohomology.tex lemma-characterize-finite-locally-constant (03RV).

## Second reading by D2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
