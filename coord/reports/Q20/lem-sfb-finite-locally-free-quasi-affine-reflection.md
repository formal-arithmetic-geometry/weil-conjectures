## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteLocallyFreeQuasiAffineReflection` states
`AlgebraicGeometry.isQuasiAffineHom_of_finiteLocallyFree`. It uses `X Y : Over S`, so
`π : X ⟶ Y` is an arrow over `S` and carries the structure-map compatibility required
by “an S-morphism”. The class hypothesis
`[π.left.IsFiniteLocallyFreeOfDegree d]` renders finite, flat, locally finitely presented,
and constant fibre degree `d`; `(hd : 1 ≤ d)` renders `d ≥ 1`; and
`[IsQuasiAffineHom X.hom]` renders that `X → S` is quasi-affine. The conclusion
`IsQuasiAffineHom Y.hom` renders that `Y → S` is quasi-affine.

The declaration is a theorem with a `sorry` proof, as required at stage 2. Its docstring
records the four proof clauses from the node: restriction to affine opens of `S`, norm
surjectivity using the positive degree, ampleness of the source structure sheaf and
ampleness reflection, and the basic-open criterion for the target. No additional
Noetherianity, reducedness, separatedness, characteristic, or invertibility assumption
is present.

The statement dependencies and declarations used are:

* `def-pc-scheme`: `AlgebraicGeometry.Scheme` from `Mathlib.AlgebraicGeometry.Scheme`; `CategoryTheory.Over` bundles the
  structure maps (the `Over` structure maps are `X.hom` and
  `Y.hom`).
* `def-pc-finite-locally-free`:
  `AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFreeOfDegree`, from
  `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`.
* `def-nagata-quasi-affine-morphism`:
  `AlgebraicGeometry.IsQuasiAffineHom`, from
  `WeilConjectures.Mathlib.AlgebraicGeometry.QuasiAffine`.

The proof-dependency modules that already have Lean records are imported as plain
imports: `Sheaf.AlgebraicGeometry.FiniteLocallyFreeFunctionNorm`
(`AlgebraicGeometry.exists_finiteLocallyFree_functionNorm`),
`WeilConjectures.AlgebraicGeometry.Ample`
(`AlgebraicGeometry.Scheme.Modules.IsAmple`),
`WeilConjectures.AlgebraicGeometry.Modules.Invertible`
(`AlgebraicGeometry.Scheme.Modules.IsInvertible`), and
`Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`
(`AlgebraicGeometry.Scheme.Modules.tensorPullbackSectionAdjunction`). The two proof
leaves recorded as Mathlib matches are
`AlgebraicGeometry.Scheme.Hom.isClosedMap`/
`AlgebraicGeometry.Scheme.Hom.finite_preimage_singleton` for finite closed maps and
`AlgebraicGeometry.Scheme.IsQuasiAffine.of_forall_exists_mem_basicOpen` together with
`AlgebraicGeometry.Scheme.IsQuasiAffine.toCompactSpace` and
`AlgebraicGeometry.Scheme.IsQuasiAffine.isBasis_basicOpen` for the basic-open criterion.
The ampleness-reflection theorem is a later proof dependency and is not needed by the
stage-2 type checker.

Edge cases checked against the source statement are: `d = 1` is admitted; `d = 0` is
excluded by `hd`; `d` need not be invertible on `S`; empty schemes and an empty base are
allowed by the relative class formulation; no reducedness or Noetherianity is assumed;
and the finite locally free class is the constant-fibre-degree version rather than a
stronger global-basis assumption.

Searches for an existing declaration were made as follows:

* `msearch.py ... leanfinder "finite locally free morphism of positive constant degree
  reflects quasi-affineness over a base"`: hits were affine-morphism preservation,
  finite/locally-quasi-finite facts, and affine-property infrastructure; no target
  reflection statement.
* `msearch.py ... loogle 'IsQuasiAffineHom, IsFiniteLocallyFreeOfDegree'`: no hits
  (`IsQuasiAffineHom` is not recognized by the Loogle identifier parser).
* `msearch.py ... grep 'finiteLocallyFree.*quasiAffine|quasiAffine.*finiteLocallyFree'
  AlgebraicGeometry`: zero hits.
* `rg` over `lean/Sheaf` and `lean/WeilConjectures` for the theorem name and the node id,
  and `grep -rl` over `dag/nodes`, found no existing declaration of this statement.
  The only DAG matches are this node and its downstream use, plus the separately stated
  basic-open criterion node.

No statement correction, new node, dependency-module repair, or `STATEMENT-DISPUTED`
flag was needed.

Additional completed searches: `msearch.py ... leansearch "Quasi-affineness of the
target of a finite locally free morphism of positive degree"` gave eight hits on
affine-target infrastructure, affine preservation, and finite morphisms, with no
reflection statement. `msearch.py ... loogle '\"IsQuasiAffine\", \"IsFinite\"'` gave
zero hits. Searches of `dag/lean_names_upstream.json`, Mathlib, `lean/WeilConjectures`,
and `lean/Sheaf` found no clash with the chosen declaration name.

Read the actual local sources for Stacks Divisors `lemma-norm-quasi-affine` and
`lemma-finite-locally-free-has-norm` (Tags 0BD1 and 0BD2), which give exactly the
absolute reflection over each affine open of the base. The later docstring explicitly
names the dependency nodes at each of its four proof steps. Plain imports of
`Mathlib.AlgebraicGeometry.Morphisms.Proper` and
`Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite` expose the recorded finite-closed-map
proof leaf; the basic-open criterion comes from the quasi-affine statement import.

## Second reading by Q20

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
