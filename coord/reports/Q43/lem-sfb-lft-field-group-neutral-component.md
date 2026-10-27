## Worker report

The module `Sheaf.AlgebraicGeometry.LftFieldGroupNeutralComponent` states
`AlgebraicGeometry.lftFieldGroup_neutralComponent`. Its only theorem has proof `sorry`.
There are no new definitions, dependency repairs, statement corrections or disputed clauses.
The existing node is changed only in `lean`.

Hypotheses and conclusions, in full:

- Any field k: `(k : Type u) [Field k]`.
- A group scheme over k: `(G : Over (Spec (.of k))) [GrpObj G]`.
- Locally of finite type: `[LocallyOfFiniteType G.hom]`.
- The identity point e: the existing `GrpObj.onePoint G`, which is the image of the
  unique point of `Spec k` under the unit section, including its original scheme structure.
- The maximal connected subset C containing e: the existing
  `connectedComponent (GrpObj.onePoint G)`. The existential `U : G.left.Opens` and
  `(U : Set G.left) = connectedComponent (GrpObj.onePoint G)` give precisely that subset
  its open-subscheme structure, with no choices of an unrelated scheme or thickening.
- C is open and closed: openness is part of `U : G.left.Opens`, and closedness is
  `IsClosed (U : Set G.left)`.
- The open subscheme is of finite type: `LocallyOfFiniteType (U.ι ≫ G.hom)` and
  `QuasiCompact (U.ι ≫ G.hom)`, the recorded conjunction for finite type.
- It is geometrically irreducible: `GeometricallyIrreducible (U.ι ≫ G.hom)`.
  Mathlib's `IrreducibleSpace` includes nonemptiness, so this asserts nonempty
  irreducibility after every extension, as requested; it does not merely assert
  preirreducibility or geometric reducedness.
- It is a subgroup with the open structure: the existential
  `gC : GrpObj (Over.mk (U.ι ≫ G.hom))` equips exactly that open subscheme with its
  group operations. `@IsMonHom ... gC.toMonObj ... (Over.homMk (V := G) U.ι)` says
  its inclusion preserves multiplication and unit. Group homomorphisms preserve inverse;
  the inclusion is an open immersion, hence a monomorphism, so this is a subgroup scheme.
  The group structure is quantified together with its compatibility, never assumed.
- For every extension K/k: `(∀ (K : Type u) [Field K] [Algebra k K], ...)`.
  The inverse image of U under `pullback.fst G.hom (Spec.map ... (algebraMap k K))`
  equals the connected component of `GrpObj.onePoint` in
  `((Over.pullback (Spec.map ... (algebraMap k K))).obj G)`.
  `Over.pullback` carries the actual base-changed group, with the canonical structure
  supplied by Mathlib's scoped `CategoryTheory.Functor.grpObjObj`. Its identity is
  therefore the base-changed identity, not an arbitrary point. The inverse image is
  exactly the open subset representing the base change of U. Equality of these subsets
  is equality as open subschemes: both have the restriction of the ambient structure
  sheaf to that same open subset. It is stronger than an unspecified isomorphism.
  This is the usual scheme-universe convention: schemes, rings and extension fields
  live in u, with u arbitrary. No independent smaller test universe is introduced.
- No extra assumptions: in particular no `QuasiCompact G.hom`, `IsAlgClosed k`,
  perfectness, smoothness, reducedness or commutativity occurs.

Dependency declarations read and used:

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs (commutative ring with
  nonzero inverses and nontriviality).
- `def-sc-group-scheme`: `CategoryTheory.GrpObj`, Mathlib.CategoryTheory.Monoidal.Grp,
  and `CategoryTheory.IsMonHom`. The specialization to `Over (Spec k)` is documented
  in WeilConjectures.AlgebraicGeometry.GroupScheme.Defs. The identity point comes from
  `AlgebraicGeometry.GrpObj.onePoint` in
  WeilConjectures.AlgebraicGeometry.GroupScheme.Basic, which is publicly imported.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType` in
  Mathlib.AlgebraicGeometry.Morphisms.FiniteType and `AlgebraicGeometry.QuasiCompact`
  in Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact, exposed by GroupScheme.Basic.
- `def-weil-connected-scheme`: `ConnectedSpace` and `connectedComponent`,
  Mathlib.Topology.Connected.Basic. The latter is the maximal connected set containing
  the point, not the component of the reduction.
- `def-weil-open-immersion`: `AlgebraicGeometry.IsOpenImmersion`,
  Mathlib.AlgebraicGeometry.OpenImmersion; `U.ι` is the canonical open immersion of
  the existing `Scheme.Opens.toScheme`. These are exposed through GroupScheme.Basic.
- `def-pc-geometrically-irreducible`: `AlgebraicGeometry.GeometricallyIrreducible`,
  Mathlib.AlgebraicGeometry.Geometrically.Irreducible, publicly exposed by the recorded
  Mathlib.AlgebraicGeometry.Geometrically.Integral. Its `geometrically` definition and
  `geometrically_iff_of_commRing` express the field-extension definition exactly.
- `def-pc-base-change`: the recorded
  WeilConjectures.AlgebraicGeometry.BaseChangeConventions is publicly imported.
  As its module docstring specifies, scheme base change is `Over.pullback`, with
  underlying scheme `Limits.pullback`, projection `pullback.fst`, structure map
  `pullback.snd`, and morphism base change the functor's map. The module's
  `Scheme.Modules.moduleBaseChange` is for modules and is not substituted for scheme
  base change. The full source and the section-characterization signature were read.

All available proof-dependency modules are imported, with private imports when used
only for the later proof: localization, prime-spectrum topology, locally Noetherian
component finiteness, reduction, and geometrically irreducible products. The two
proof prerequisites `lem-sfb-group-local-minimal-prime` and
`lem-sfb-irreducible-group-quasi-compact` currently have no recorded Lean or Mathlib
match, so have no import to add. They are not needed to type the statement and are
explicitly named in the theorem's complete six-step natural-language proof.

Sources read: Stacks groupoids.tex, proposition-connected-component (Tag 0B7R),
including its proof; the node's six proof steps; and the current latest blueprint's
`sk-thm-sf-ctf-stability-direct-images.proof.md`, part (3), the inherited route.
The source retains the nilpotents on the component. No claim about the reduction is
added to the Lean conclusion.

Edge cases checked mathematically:

- The trivial group `Spec k` has U equal to the whole scheme and survives K=k.
- A constant infinite discrete group has neutral component one copy of `Spec k`;
  this checks that the ambient group need not be quasi-compact or finite type.
- `G_a` is connected and U is the whole scheme; disconnected groups give a proper U.
- `alpha_p` and `mu_p` in characteristic p retain their nonreduced structure;
  geometric irreducibility does not impose reducedness or smoothness.
- `mu_3` over the rational field tests the non-algebraically-closed base.
- Purely inseparable extensions are allowed by `[Algebra k K]`, with no separability
  or perfectness binder. Noncommutative groups are also allowed.
- An empty group scheme over a field cannot admit its unit section, so no omitted
  nonemptiness hypothesis is necessary.

Searches for an existing statement (2026-10-24):

- msearch leanfinder: “The identity component of a locally finite type group scheme
  over a field is open closed finite type geometrically irreducible and commutes
  with field extension”: eight unrelated finite-morphism or spectrum hits, no match.
- msearch loogle: `"GrpObj", "connectedComponent"`: zero hits.
- msearch grep: `identityComponent|connectedComponent.*GrpObj|GrpObj.*connectedComponent`
  in Mathlib/AlgebraicGeometry: zero hits.
- msearch leansearch: “The neutral component of a group scheme locally of finite type
  over any field is an open closed finite type geometrically irreducible subgroup”:
  ordinary topological-group components and Noetherian component facts, no match.
- rg over WeilConjectures and Sheaf for identityComponent, neutralComponent and
  connectedComponent, plus grep for the node id: no theorem with the full statement.
  GroupScheme.Basic's existing identity-component construction requires the whole
  group to be quasi-compact (and its group structure is in the algebraically closed
  section). It cannot be used for the node's general G.
- Sheaf.AlgebraicGeometry.LocallyAlgebraicGroupIdentityComponent's
  `locallyAlgebraicGroup_identityComponent` assumes `[IsAlgClosed k]` and includes
  extra reduction conclusions. It does not state the arbitrary-field result here.
- rg for `lftFieldGroup_neutralComponent` in both project roots, Mathlib and the
  upstream-name index found no declaration-name collision.

Validation uses only scompile.py and deliver2.py. An initial compile diagnosed the
missing scoped functor group-object instance for the base change; enabling the
existing `CategoryTheory.Obj` scope repairs it without adding a definition or hypothesis.
The final per-file compile and the delivery preflight results are recorded below.

Final validation: scompile.py compiled the sandbox probe in 14.0 s and the named
library module in 2.1 s, with no errors or warnings. deliver2.py --no-push printed
`OK (dry run): commit 53c7d129399 passes the preflight and compiles; nothing pushed`.

## Second reading by Q43

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
