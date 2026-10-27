## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteTypeGroupIdentitySubgroup` states
`AlgebraicGeometry.GrpObj.finiteType_identityComponent_closedSubgroup` with one
`sorry`, and introduces no definitions. The natural-language node is unchanged.
The theorem combines the already implemented arbitrary-field open identity subgroup
with the closed-subgroup conclusion. No single existing declaration found in
Mathlib, WeilConjectures or Sheaf states this complete arbitrary-field result.

Hypotheses and conclusions, clause by clause:

- A field k: `(k : Type u) [Field k]`, with explicitly declared universe `u`.
- A group scheme G over k: `(G : Over (Spec (.of k))) [GrpObj G]`.
  `GrpObj` is exactly the recorded definition in `def-sc-group-scheme`, specialized
  to schemes over Spec k. It includes multiplication, unit, inverse and their diagrams.
- Finite type: `[LocallyOfFiniteType G.hom] [QuasiCompact G.hom]`, the two
  conjuncts specified by `def-weil-finite-type-morphism`.
- The identity point e: `GrpObj.onePoint G`. Its existing definition applies the
  identity section to the unique point of Spec k, represented by its zero prime.
- The maximal connected subset containing e: `connectedComponent (GrpObj.onePoint G)`.
- Openness and closedness: `IsClopen (connectedComponent (GrpObj.onePoint G))`.
- Its open-subscheme structure: the existing `GrpObj.identityComponent G` is
  `Over.mk ((GrpObj.identityComponentOpens G).ι ≫ G.hom)`, and
  `GrpObj.identityComponentOpens G` is exactly that connected component with its
  openness proof. Thus this retains the restriction of the full structure sheaf,
  including nilpotents, and does not use the reduced induced subscheme.
- Its connectedness: `ConnectedSpace (GrpObj.identityComponent G).left`.
  This definition includes nonemptiness.
- Its group scheme structure: the existing public `GrpObj (GrpObj.identityComponent G)`
  instance in `WeilConjectures.AlgebraicGeometry.GroupScheme.Basic` supplies the
  canonical restricted unit, multiplication and inverse. It is part of the fixed
  object used in the statement, rather than an extra assumption or a new choice.
- Its inclusion j: the existing `GrpObj.identityComponentι G`, defined using the
  canonical open immersion. Its image is the specified connected component by
  `GrpObj.range_identityComponentι` in the same module.
- The homomorphism, closed immersion and closed subgroup conclusions are precisely
  `IsClosedSubgroupScheme (GrpObj.identityComponentι G)`. The recorded class from
  `def-sc-group-scheme-subgroup` extends `IsSubgroupScheme`, which extends
  `IsMonHom` and requires injectivity on every k-algebra's points. Its additional
  field is `IsClosedImmersion` of the underlying scheme map. Hence none of these
  clauses is dropped or replaced by a statement merely about rational points.
- No perfectness, algebraic closedness, reducedness, smoothness or commutativity
  hypothesis appears. All characteristic and imperfect-field cases are retained.

Dependency declarations read and used:

- `def-weil-field`: `Field`, `Mathlib.Algebra.Field.Defs`.
- `def-sc-group-scheme`: `CategoryTheory.GrpObj`,
  `Mathlib.CategoryTheory.Monoidal.Grp`; homomorphisms are
  `CategoryTheory.IsMonHom`, `Mathlib.CategoryTheory.Monoidal.Mon`.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType`,
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, and
  `AlgebraicGeometry.QuasiCompact`, `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.
- `def-weil-connected-scheme`: `ConnectedSpace`, `Mathlib.Topology.Connected.Basic`.
- `def-weil-open-immersion`: `AlgebraicGeometry.IsOpenImmersion`,
  `Mathlib.AlgebraicGeometry.OpenImmersion`.
- `def-weil-closed-immersion`: `AlgebraicGeometry.IsClosedImmersion`,
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`.
- `def-sc-group-scheme-subgroup`: `AlgebraicGeometry.IsSubgroupScheme` and
  `AlgebraicGeometry.IsClosedSubgroupScheme`,
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`. This is a usable record;
  it needs no repair.
- Canonical identity component, point, open subset, group structure, inclusion and
  inclusion homomorphism: `WeilConjectures.AlgebraicGeometry.GroupScheme.Basic`.
  Read both the local module and the current server module through `scompile.py --source`.
  These public imports also expose all Mathlib statement-dependency definitions.

Proof-dependency imports and sources:

- `lem-trf-geometrically-connected-image-criterion` is imported privately via
  `Sheaf.AlgebraicGeometry.GeometricallyConnectedImageCriterion`, declaration
  `AlgebraicGeometry.GeometricallyConnected.of_connectedSpace_of_geometricallyConnected`.
- `lem-weil-pbc-morphism-factors-through-open-subscheme` uses the recorded
  `IsOpenImmersion.lift`, `lift_fac`, `lift_uniq` in Mathlib's OpenImmersion module.
- `lem-weil-pbc-geometrically-connected-product-components` uses the recorded
  `Scheme.Hom.connectedComponentsHomeomorph` from
  `Mathlib.AlgebraicGeometry.Geometrically.Connected`.
- `lem-weil-pbc-immersion-closed-image-closed-immersion` uses
  `IsClosedImmersion.iff_isPreimmersion` and `of_isPreimmersion` from Mathlib's
  ClosedImmersion module. These Mathlib modules are exposed through Basic.
- `lem-trf-finite-type-component-open-qc` has no Lean record or mathlib_match
  in the read DAG, so no unstated module is imported. It is a proof prerequisite,
  not a missing notion required to type this statement. Its role and all seven
  proof steps are retained in the theorem docstring. No proof was supplied here.

Source and edge-case checks:

Read Stacks `groupoids.tex`, Proposition Tag 0B7R including its proof, and the
current blueprint's `sk-thm-sf-ctf-stability-direct-images.proof.md`, part (3).
The node's finite-type specialization uses an open component; the Stacks argument
restricts the identity, multiplication and inverse and proves the canonical
closed-subgroup assertion. The Lean states the node's requested clauses only;
it adds no flatness, geometric irreducibility or quasi-compactness conclusion.

Checked conceptually: the trivial group has the entire one-point scheme as its
component; a disconnected finite etale group retains only the neutral component;
alpha_p and mu_p in characteristic p retain their nonreduced structure; G_m has
its whole scheme as the neutral component; a disconnected positive-dimensional
group is allowed. The empty scheme cannot be a group object over Spec k because
it would have to receive a unit section, so no missing nonempty hypothesis is
needed. No requirement for nonidentity rational points or rational points on
other components is introduced. A shared universe for k and the ambient scheme
matches the existing canonical construction and admits any size after lifting
into a common universe; there is no separate small universe of test algebras
that could make injectivity vacuous.

Searches (all through `msearch.py Q132 lem-sfb-finite-type-group-identity-subgroup`):

- LeanFinder: “The identity component of a finite type group scheme over an
  arbitrary field is an open and closed subgroup scheme”. Eight hits, including
  `Subgroup.connectedComponentOfOne` and finite-morphism / Galois-topology facts;
  none is a scheme-theoretic arbitrary-field closed-subgroup result.
- Loogle: `IsClosedSubgroupScheme, identityComponentι`. No hits; the service
  reports unknown identifier `IsClosedSubgroupScheme` (a project declaration).
- Grep: `identityComponent|connectedComponent.*[Gg]roup|[Gg]roup.*connectedComponent`
  in Mathlib/AlgebraicGeometry: zero hits.
- LeanSearch: “connected identity component finite type group scheme closed
  immersion”. Eight hits, including `IsClosedImmersion.of_isPreimmersion` and
  `IsClosedImmersion.iff_isPreimmersion`, but no combined group-scheme theorem.
- `rg` in WeilConjectures and Sheaf for `identityComponentι`,
  `isClosedSubgroupScheme`, and connected-component variants located the canonical
  construction in GroupScheme/Basic and definitions in GroupScheme/Defs.
  `GroupNeutralComponentTranslates` includes the closed-subgroup clause but assumes
  an algebraically closed field and states further translate assertions, so it
  cannot serve as the exact arbitrary-field statement. The general-linear closed
  subgroup modules concern particular matrix groups and do not give this theorem.
- The exact node-id search in WeilConjectures has no hits. The proposed full
  declaration name has no hits in Mathlib, WeilConjectures, Sheaf or
  `dag/lean_names_upstream.json`.

Validation: `scompile.py` compiled the delivered module in both sandbox and
library module modes on the server, with no errors or warnings (5.4 s and 4.6 s).
Every variable and universe is explicitly bound and `autoImplicit` is false.
No statement correction, dependency repair, new definition node or dispute is needed.

## Second reading by Q132

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
