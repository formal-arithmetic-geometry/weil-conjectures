## Worker report

This item is covered by existing, sorry-free declarations in
`WeilConjectures.SixFunctors.BaseChange.Square`; no new Lean module is written.
The declarations are `AlgebraicGeometry.Etale.isIso_baseChangeMap_of_isUniversalHomeomorphism`
and `AlgebraicGeometry.Etale.unit_map_baseChangeMap_app`.

The node's diagram hypothesis is a chosen cartesian square.  The existing theorem is
stated for its underlying `CommSq`; for a `ChosenCartesianSquare` this is
`sq.toCommSq`, while the chosen pullback identification is exactly the extra data in
`ChosenCartesianSquare` and does not alter the underlying square maps.  The two
horizontal hypotheses are rendered by the typeclass assumptions
`[IsUniversalHomeomorphism g]` and `[IsUniversalHomeomorphism g']`.  The coefficient
category is specialized to `AddCommGrpCat`, so `F` is an abelian-group-valued sheaf on
`X.smallEtaleTopology`, i.e. an abelian étale sheaf.

The conclusion that the canonical underived exchange is an isomorphism is rendered by
`IsIso (Etale.baseChangeMap A sq)` in
`isIso_baseChangeMap_of_isUniversalHomeomorphism`; `Etale.baseChangeMap` is the
mate-defined canonical map recorded by `def-weil-pbc-underived-exchange`.  The
source's `unit_map_baseChangeMap_app` renders the displayed unit equation:
its left side is the direct-image unit followed by `g_*` applied to the exchange, and
its right side is `f_*` applied to the `g'` unit followed by
`Etale.squareLowerStarIso`.  That square isomorphism is defined in the same source file
from `lowerStarComp`; its components are the canonical direct-image composition maps
`d_{f,g'} \circ d_{g,f'}^{-1}` required by the node.  Thus the implicit composition
identification in the node is present in the existing declaration.

The statement field records the exact signature of the primary existing instance;
the second declaration supplies the equation clause.  Both declarations are in the
recorded module and are on the `slopmaster2` branch.

Dependencies used (recorded declarations):

- `def-weil-pbc-cartesian-square`: `AlgebraicGeometry.ChosenCartesianSquare` in
  `Sheaf.AlgebraicGeometry.ChosenCartesianSquare` (its `toCommSq` is used).
- `def-weil-universal-homeomorphism`: the project class
  `AlgebraicGeometry.IsUniversalHomeomorphism`, used as the two typeclass hypotheses.
- `def-weil-pbc-underived-exchange`: `AlgebraicGeometry.Etale.baseChangeMap` in
  `WeilConjectures.SixFunctors.BaseChange.Square`.
- `def-weil-pbc-direct-image`: `AlgebraicGeometry.Etale.lowerStar` in
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`.
- `def-weil-pbc-inverse-image`: `AlgebraicGeometry.Etale.upperStar` and
  `AlgebraicGeometry.Etale.upperStarLowerStarAdjunction` in the same module.
- `lem-weil-pbc-inverse-image-composition`: its canonical direct-image composition
  interface; the source implementation is `lowerStarComp` and the resulting
  `squareLowerStarIso`.

Edge cases checked against the source signatures and definitions: the identity square
(with both horizontal maps identities), a nilpotent thickening (a standard universal
homeomorphism), `f = id`, the zero sheaf, and an arbitrary commutative square whose
chosen pullback identification is ignored after `toCommSq`.  The source theorem has no
extra quasi-compactness, separatedness, torsion, coefficient-ring, or nonempty-object
hypothesis.

Searches made:

- `msearch.py ... leanfinder "underived étale exchange map is an isomorphism for a cartesian square whose horizontal maps are universal homeomorphisms"`: only generic étale and base-change hits; no matching theorem.
- `msearch.py ... loogle "isIso_baseChangeMap_of_isUniversalHomeomorphism, unit_map_baseChangeMap_app"`: no Loogle hit (the names are project declarations rather than Mathlib identifiers).
- `msearch.py ... grep "isIso_baseChangeMap_of_isUniversalHomeomorphism|unit_map_baseChangeMap_app" WeilConjectures/SixFunctors`: no msearch grep result; direct `rg` found both declarations in `WeilConjectures/SixFunctors/BaseChange/Square.lean:169,213`.
- `rg` over the source repository for the two declaration names: found the exact declarations and their docstrings in `BaseChange/Square.lean`.
- `rg` over `lean/Sheaf` for exchange/universal-homeomorphism terms: found no duplicate declaration of this complete item; only dependent explanatory modules.
- Exact item-id grep over the source repository: no source declaration tagged with this item id.

No statement correction, new node, dependency module, or `STATEMENT-DISPUTED` marker is needed.

## Second reading by Q22

I independently opened the item node, every statement dependency, and the two source
signatures.  The cartesian-square data is represented by `ChosenCartesianSquare` and
its inherited `CommSq`; the source theorem takes precisely that inherited square.  The
universal-homeomorphism assumptions occur on both horizontal arrows.  The existing
`IsIso` instance supplies the first conclusion clause, and `unit_map_baseChangeMap_app`
supplies the unit equation.  Reading the definition of `squareLowerStarIso` confirms
that it is the canonical `lowerStarComp` comparison, hence the node's
`d_{f,g'} \circ d_{g,f'}^{-1}` factor.  No hypothesis or conclusion is added, removed,
or weakened by the specialization to `AddCommGrpCat`; the chosen pullback witness only
packages the cartesian-square notion and is not silently replaced by an arbitrary map.
The node therefore uses the existing declarations exactly, and no file-level Lean
compile is needed for an existing attachment.
