## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteLocallyFreeOpenAffineCover` states
`AlgebraicGeometry.AlgebraicSpace.exists_scheme_of_finiteLocallyFree_openAffineCover`.
Its only theorem proof is `sorry`; it introduces no definitions or auxiliary theorems.
The module and declaration docstrings cite Stacks Tag 07S6 and give all seven
steps of the accepted node proof, including the direct prime-avoidance argument.

Clause-by-clause correspondence:

- The arbitrary base scheme is `{S : Scheme.{u}}`.
- The algebraic space over S is `(X : AlgebraicSpace S)`. This is the existing
  full subcategory of fppf sheaves with representable diagonal and an etale atlas.
- The source scheme and its S-structure are `(U : Over S)`; its underlying scheme
  is `U.left`. The map from that scheme to X is
  `(p : yoneda.obj U ⟶ X.obj.obj)`, a natural transformation on schemes over S.
- Representability and finite local freeness of every scheme pullback are combined
  in `hp : IsRepresentableWith (fun _ _ q ↦ q.left.IsFiniteLocallyFree) p`.
  The recorded definition quantifies over every `T : Over S` and every
  `yoneda.obj T ⟶ X.obj.obj`, and supplies a represented pullback square whose
  projection has exactly this scheme-morphism property. Consequently a separate
  representability hypothesis would be redundant. No new map-property notion is defined.
- Surjectivity on field-valued point classes is `hsurj : pointImage p = Set.univ`.
  This uses the dependency's image defined by applying p to field-valued
  representatives and taking their existing quotient classes. It does not require
  surjectivity on sections over an arbitrary field before extending that field.
- The commutative ring is bundled as `(A : CommRingCat.{u})`.
- The condition that U be isomorphic to an open of `Spec A` is encoded by
  `(j : U.left ⟶ Spec A) [IsOpenImmersion j]`. An open immersion identifies its
  source with its open image, precisely the equivalence in def-weil-open-immersion.
  No S-structure or compatibility with S is required of the ambient affine scheme.
- Representation by an S-scheme is
  `∃ V : Over S, Nonempty (yoneda.obj V ≅ X.obj.obj)`. An isomorphism here is a
  natural isomorphism on `Over S`, so the conclusion includes the S-structure.
- The final sentence of the node excludes extra hypotheses: the Lean signature has
  no quasi-compactness, Noetherian, finite-type, separatedness, or nonemptiness binder.

Statement dependency declarations, read with full signatures and docstrings:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, its morphisms,
  and `AlgebraicGeometry.Spec` (the spectrum of a bundled commutative ring).
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicGeometry.AlgebraicSpace.IsRepresentableWith` and the underlying sheaf
  and presheaf fields. `IsRepresentableWith` uses an actual `IsPullback` square.
- `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`:
  `AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFree`, which extends `IsFinite`,
  `Flat`, and `LocallyOfFinitePresentation`, exactly the dependency's definition.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`:
  `AlgebraicGeometry.AlgebraicSpace.pointImage`, using `PointRepresentative.map`
  and `Point` from the imported point-classes module.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.

All available recorded proof-dependency modules are imported without `public`,
including the groupoid, fppf-covering calculus, sheafification, principal-open,
prime-avoidance, ideal-sheaf, finite-morphism, affine-quotient, etale,
finding-opens and schemes-representability modules. The proof dependency
`lem-sfb-locally-free-groupoid-invariant-affine` has neither a Lean record nor a
Mathlib match in the read repository, so there is no module to import for it.
It is not needed to type the statement and remains named in the proof docstring.

Edge cases checked before writing:

- Empty U: the point-image hypothesis forces X to have no point classes. The
  argument gives the empty S-scheme; the signature allows both empty source and
  empty representing scheme. No positive degree or nonempty atlas is imposed.
- Zero ring A: `Spec A` is empty, so an open immersion forces U empty; this reduces
  to the preceding case. `CommRingCat` imposes no nontriviality assumption.
- Arbitrary non-quasi-compact open U: the open immersion has no quasi-compactness
  constraint. The proof constructs principal affine neighbourhoods of individual
  finite orbits, rather than assuming a finite affine cover of U.
- Nonreduced rings and schemes: no reducedness, characteristic, or finite-type
  assumption is used. Orbits are finite because the kernel-pair projections are
  finite, with no constant-degree requirement.
- All scheme objects and the ring use the same explicit universe u as the
  recorded algebraic-space site. This includes every object allowed by that
  dependency; no independent smaller test universe is introduced.

Sources read: `literature/stacks-project/spaces-properties.tex`,
`proposition-finite-flat-equivalence-global` (Tag 07S6), its proof and the paragraph
immediately following it. Its locally-closed-in-affine sufficient condition
includes an arbitrary open of an affine, without quasi-compactness. The current
blueprint unit's direct-image stability route is the inherited ancestor context;
this node is a supporting Stacks lemma, not the unit's statement.

Searches performed with the prescribed `msearch.py` wrapper:

- LeanFinder: “An algebraic space admitting a finite locally free surjection from
  an open subscheme of an affine scheme is represented by a scheme.” Eight hits
  concern affine schemes, quasi-affine schemes, finite scheme morphisms, and the
  local-ringed-space open-immersion construction. None states this result.
- LeanSearch: “An algebraic space with a finite locally free surjection from an
  open subscheme of an affine scheme is representable by a scheme.” Eight hits
  include `Scheme.LocalRepresentability.isRepresentable`, scheme constructors,
  `IsFinite`, and locally finite presentation. None matches this statement.
- Loogle: `"IsFiniteLocallyFree"`: zero hits.
- Mathlib grep: `AlgebraicSpace|finite.*locally.*free.*quotient`, restricted to
  AlgebraicGeometry: zero hits. Direct rg for `IsFiniteLocallyFree|finiteLocallyFree`
  under Mathlib/AlgebraicGeometry also returned no match.
- Project/source rg: `finiteLocallyFree|finite_locally_free|IsRepresentableWith|
  IsRepresentable|pointImage|schemeSpace` in the algebraic-space modules located
  the dependency interfaces above; no schematicity theorem of this form.
- Project/source rg: `lem-sfb-finite-locally-free-open-affine-cover|
  finite.*locally.*free.*[Oo]pen|schematic.*finite` under `lean/WeilConjectures`
  and `lean/Sheaf` found finite locally free module results and the consumer
  `AlgebraicSpaceDenseSchemeOpen.lean`, whose docstring names this missing input.
  There was no implementation of the item. An exact-name search of these trees
  and `dag/lean_names_upstream.json` found no declaration-name collision.

No statement correction, new notion, dependency interface repair, or disputed
statement was needed. Only the item's `lean` field changes.

Validation: `scompile.py Q160 lem-sfb-finite-locally-free-open-affine-cover` compiled
the delivered file in sandbox mode (7.9 s) and at its library module path (9.8 s),
with no errors or unexpected warnings. All variables are explicitly bound and
`autoImplicit` is disabled. Every Lean line is at most 100 characters.

## Second reading by Q160

I reread the node and final signature after the first compile. This is a worker
self-review: the dispatcher explicitly prohibits starting other agents, and the
maintainer supplies the independent delivery review.

The base S, space X, scheme U over S, scheme-source natural transformation p,
scheme-test finite locally free property, and field-point surjectivity each have
the binders listed above. The open-immersion binder encodes exactly an isomorphism
with an open of an affine scheme and adds no structure on that affine over S.
The natural isomorphism in the conclusion is in presheaves on `Over S`, so it
represents X as an S-scheme. Combining representability with the pullback property
in `hp` loses no hypothesis. Bundling A as a commutative ring excludes neither the
zero ring nor arbitrary characteristic. Empty U and non-quasi-compact U are both
included. The seven-step proof docstring was checked against every proof step of
the node; the unstated invariant-affine input is retained there, and all other
available proof interfaces are imported. No mismatch or further change was found.
