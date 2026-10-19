## Worker report

The module `lean/Sheaf/AlgebraicGeometry/FlatPullbackAssociatedPoints.lean` states
`AlgebraicGeometry.Scheme.Modules.associatedPoints_tensorPullback_of_flat`. It uses the
existing scheme flatness class, locally Noetherian class, scheme fibre, tensor pullback,
associated-points definition, and structure-sheaf module. The proof is `sorry`, as required
for stage 2.

The Lean rendering of each hypothesis is:

- `Y` and `Z` are schemes in one explicit universe: `{Y Z : Scheme.{u}}`.
- `h : Y ⟶ Z` is the scheme morphism.
- `[Flat h]` is Mathlib's flat morphism class.
- `[IsLocallyNoetherian Z]` is Mathlib's locally Noetherian scheme class.
- `G : Z.Modules` is an arbitrary module on `Z`.
- `[SheafOfModules.IsQuasicoherent.{u} G]` supplies exactly quasi-coherence, with no finite-type or
  coherence assumption and no condition on `Y`.

The conclusion renders the two clauses as follows. The left side
`associatedPoints ((tensorPullback h).obj G)` is the associated-point set of the canonical
module pullback `h^* G`. The right side is
`⋃ z ∈ associatedPoints G, (h.fiberι z) '' associatedPoints
(SheafOfModules.unit (h.fiber z).ringCatSheaf)`: a union over associated points `z` of `G`,
of the image under the fibre projection of the associated points of the fibre's structure
sheaf. The equality is equality of subsets of `Y`.

Dependency declarations used:

- `AlgebraicGeometry.Flat` from `Mathlib.AlgebraicGeometry.Morphisms.Flat`.
- `AlgebraicGeometry.IsLocallyNoetherian` from `Mathlib.AlgebraicGeometry.Noetherian`.
- `AlgebraicGeometry.Scheme.Modules.tensorPullback` and its interface from
  `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction` (the recorded pullback node).
- `AlgebraicGeometry.Scheme.Modules.associatedPoints` from
  `Sheaf.AlgebraicGeometry.RelativeAssassin`.
- `AlgebraicGeometry.Scheme.Hom.fiber` and `fiberι` from `Mathlib.AlgebraicGeometry.Fiber`.
- `SheafOfModules.IsQuasicoherent` and `SheafOfModules.unit` from Mathlib's module-sheaf
  definitions.

The proof docstring records the source proof's stalkwise reduction: flat stalks and
Noetherian base stalks, the pullback-stalk tensor identification, the fibre local-ring
quotient, the arbitrary-module flat-base-change associated-prime equality, the local
annihilator argument forcing the auxiliary prime to be the base maximal ideal, and the
annihilator correspondence under the quotient. It explicitly preserves the absence of
finite-type and source Noetherianity hypotheses.

Edge cases checked against the statement: `G = 0` (both associated-point sets are empty),
`h = 𝟙 Z` (the fibre is the residue-field point and the formula reduces to the identity
case), an empty scheme `Y`, a non-Noetherian source `Y`, and `Z = Spec k`. The union binder
allows an empty associated-point set. No finite type was introduced.

Searches for an existing declaration: `msearch.py` LeanFinder query “Associated points of
the pullback of an arbitrary quasi coherent module by a flat scheme morphism over a locally
Noetherian base are the union of the associated points of fibres over associated points”
returned only flatness, stalk-map, and fibre declarations; no formula. The LeanSearch query
“Associated points of a flat pullback of a quasi coherent sheaf over a locally Noetherian
scheme are the union of images of associated points of fibres” likewise returned only
flatness, fibre, and pullback infrastructure. The Loogle query `associatedPoints,
tensorPullback` returned zero hits. Grep for `associatedPoints|assassin` in Mathlib's
AlgebraicGeometry directory returned no matching theorem, and grep of the source
`WeilConjectures` and project `lean/Sheaf` found no same statement. The DAG's existing
`relativeAssassin` and `associatedPoints` definitions were reused; no new definition node
was needed. `STATEMENT-DISPUTED:` none.

## Second reading by Q24

I reread the node and module side by side. `Flat h`, `IsLocallyNoetherian Z`, arbitrary
`G : Z.Modules`, and quasi-coherence are all present. The conclusion uses the canonical
`tensorPullback`, the existing `associatedPoints` notion on both schemes, the canonical
scheme-theoretic fibre `h.fiber z`, its projection `h.fiberι z`, and the fibre structure
module `SheafOfModules.unit (h.fiber z).ringCatSheaf`. The two inclusions are represented by
set equality exactly as the node's union formula. No finite-type condition on `G` and no
Noetherian condition on `Y` was added. The file compiles cleanly with `scompile.py`; no
mismatch was found and no change was needed in this second reading.
