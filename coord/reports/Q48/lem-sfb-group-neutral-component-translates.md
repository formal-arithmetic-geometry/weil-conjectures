## Worker report

The module `Sheaf.AlgebraicGeometry.GroupNeutralComponentTranslates` states
`AlgebraicGeometry.GrpObj.finiteTypeGroup_neutralComponent_translates`.
Its only theorem has proof `sorry`; its docstring carries the four proof steps
from the node, with their named dependencies. There are no new definitions,
new nodes, dependency repairs or changes to the natural-language statement.
The node copy changes only `lean`.

Hypotheses and clauses, individually:

- The base field is `(k : Type u) [Field k]`; algebraic closedness is
  `[IsAlgClosed k]`. The universe `u` is explicitly bound.
- The group scheme over k is `(G : Over (Spec (.of k))) [GrpObj G]`.
  This is the recorded group-object encoding, without commutativity.
- Finite type is exactly `[LocallyOfFiniteType G.hom] [QuasiCompact G.hom]`,
  the two predicates in the recorded finite-type node.
- The component containing the identity is
  `connectedComponent (GrpObj.onePoint G)`. Mathlib defines connectedComponent
  as the maximal connected subset containing the given point; it contains
  that point, so it is nonempty, as required by the connected-scheme node.
- The first conclusion `IsClopen (connectedComponent (GrpObj.onePoint G))`
  gives both openness and closedness of that subset.
- Its scheme structure is the existing `GrpObj.identityComponent G`:
  by its defining abbreviation this is
  `Over.mk ((GrpObj.identityComponentOpens G).ι ≫ G.hom)`, the open subscheme
  of exactly that subset. Its inclusion is `GrpObj.identityComponentι G`.
  `IsClosedSubgroupScheme (GrpObj.identityComponentι G)` asserts the stated
  closed subgroup property with the canonical restricted group structure.
  In particular it includes the homomorphism, injectivity on algebra-valued
  points and closed immersion conditions of the subgroup dependency.
- `Finite (ConnectedComponents G.left)` says there are finitely many
  connected components, counting topological components rather than points.
- Every component is `connectedComponent x` for some `x : G.left`; the final
  universal quantifier therefore covers exactly all connected components.
  It supplies `D : G.left.Opens` and the equality
  `(D : Set G.left) = connectedComponent x`, equipping D with its open
  subscheme structure, without a reduced induced structure.
- The witness `g : 𝟙_ (Over (Spec (.of k))) ⟶ G` is a k-rational point.
  The witness `e : GrpObj.identityComponent G ≅ Over.mk (D.ι ≫ G.hom)` is an
  isomorphism in the category of k-schemes, not just of underlying spaces.
  Its equation
  `e.hom.left ≫ D.ι = (GrpObj.identityComponentι G).left ≫ (GrpObj.mulLeft G g).left`
  identifies its forward map with the restriction of the specified left
  translation. Evaluating at the identity also implies that g lies in D.
- There is no reducedness, smoothness, affine, proper, separated,
  characteristic-zero or connectedness assumption on G.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field` (def-weil-field).
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`, the algebraically
  closed field predicate explicitly identified in def-weil-algebraic-closure's
  mathlib_match. No algebraic-closure construction is needed in this statement.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`, specialized
  to `Over (Spec (.of k))` as required by def-sc-group-scheme.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Mathlib.Topology.Connected.Basic`: `connectedComponent`, `ConnectedSpace`;
  the maximality and nonemptiness properties give precisely the components
  meant in the node. `ConnectedComponents` is the usual component quotient.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`; the existing
  `Scheme.Opens` scheme and inclusion give the open subscheme structure.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`:
  `IsSubgroupScheme`, `IsClosedSubgroupScheme`, the recorded subgroup notions.
  This is a direct public import; Basic alone does not expose these predicates
  on the current server, as the first compile showed.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Basic`:
  `GrpObj.onePoint`, `GrpObj.identityComponentOpens`, `GrpObj.identityComponent`,
  `GrpObj.identityComponentι`, and its canonical group and homomorphism
  instances; `GrpObj.mulLeft`, `GrpObj.mulLeftIso`, and the translation
  inverse formulas from the recorded translation nodes. The existing
  identity component is used directly; it is not redefined.
- `Sheaf.AlgebraicGeometry.LocallyAlgebraicGroupIdentityComponent`:
  `locallyAlgebraicGroup_identityComponent`, imported privately for proof step 1.
- The remaining proof dependencies are exposed by the public Basic import:
  `IsClosedImmersion` in `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `LocallyOfFiniteType.jacobsonSpace` in Mathlib's FiniteType module, and
  `residueFieldIsoBase` / `SpecMap_residueFieldIsoBase_inv` in
  `Mathlib.AlgebraicGeometry.AlgClosed.Basic`. Their signatures and docstrings
  were read, including the algebraically closed and locally finite type
  hypotheses of the residue-field result.

Edge cases checked before writing:

- The trivial group has one component; the statement allows D = G and the
  identity rational translation.
- A connected finite type group has one component and C = G, with its full
  scheme structure. A nonreduced connected group, such as alpha_p over an
  algebraically closed field of characteristic p, remains in scope: neither
  C nor D is replaced by its reduction.
- A disconnected finite constant group has finitely many singleton components;
  rational left translations identify those components as asserted.
- The empty scheme cannot carry this group-object structure over a field,
  because the unit section would map the nonempty Spec k to the empty scheme.
  No extra nonemptiness assumption is introduced.
- Positive characteristic, noncommutative groups, nonaffine groups and
  positive-dimensional components are all allowed by the binders. A point x
  indexing a component may be nonclosed; the proof chooses a possibly different
  closed point of that component to obtain the rational translation.
- The isomorphism equation is equality of scheme morphisms, so it preserves
  nilpotents and rules out an arbitrary unrelated component isomorphism.

Searches for an existing full statement (all through msearch.py Q48 and this item):

- LeanFinder: "A finite type group scheme over an algebraically closed field
  has finitely many connected components and every component is a rational
  translate of the open and closed identity subgroup". Eight hits, principally
  Galois-category decompositions and ordinary open-subgroup quotient finiteness;
  none states this group-scheme conjunction.
- Loogle: `"connectedComponent", "IsClosedSubgroupScheme"`: zero hits.
- Mathlib grep: `identityComponent|image_mulLeft_connectedComponent|GrpObj.*connectedComponent`
  in AlgebraicGeometry: zero hits.
- LeanSearch: "A finite type group scheme over an algebraically closed field
  is a finite union of translates of its clopen identity subgroup scheme".
  Eight hits about compact open subsets, open subgroups and finite schemes;
  none gives the complete statement.
- Project ripgrep for the same identity-component and translation patterns in
  WeilConjectures and Sheaf found GroupScheme/Basic.lean and AmpleFamily.lean.
  Basic supplies openness, finiteness and the image formula separately.
  AmpleFamily supplies `GrpObj.range_identityComponentTranslate` and
  `GrpObj.sigmaIdentityComponentIso`, but neither declaration states the full
  conjunction, including the closed subgroup predicate and the isomorphism
  of k-schemes onto each component with the restriction equation.
- Ripgrep for this item's blueprint id in WeilConjectures found no match;
  in Sheaf it found a proof-docstring citation in SimplyConnectedMultiplicativeLifting,
  not a declaration of this node. Searches of Mathlib, WeilConjectures, Sheaf
  and dag/lean_names_upstream.json found no declaration with the new full name.

Sources checked: groupoids.tex, proposition-connected-component (Stacks 0B7R),
and the actual Milne PDF, printed pp.16-18, especially Proposition 1.34,
Corollary 1.35, and the following homogeneity discussion. These agree with
using the full open subscheme structures. No statement fault or dispute found.

Validation: scompile.py compiled this module in both sandbox and final library
module modes with no errors or warnings (39.7 s and 10.5 s respectively, each
within the 60 s per-file limit). The only earlier failure was the missing direct
public import of GroupScheme.Defs, repaired before this successful compile.

## Second reading by Q48

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
