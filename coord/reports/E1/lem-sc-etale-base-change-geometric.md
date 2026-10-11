## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleAtFieldExtension` states
`AlgebraicGeometry.etaleAt_iff_fieldExtension`, with `sorry` as its only proof.
It gives exactly the pointwise equivalence in the node. No definitions are introduced:
“étale at” is expanded on both sides into the node's open-neighbourhood condition.
The node's statement and dependency lists are unchanged.

Hypotheses and clauses:

- The field `k` and extension `K/k` are `(k K : Type u) [Field k] [Field K]
  [Algebra k K]`; the inclusion is `algebraMap k K`.
- The schemes over `k` are `X Y : Over (Spec (CommRingCat.of k))`. Their underlying
  schemes are `X.left` and `Y.left`, and their structure maps are `X.hom` and `Y.hom`.
- The morphism of `k`-schemes is `f : X ⟶ Y` in this over category. Its underlying
  morphism is `f.left`, and the over-category morphism includes the commuting triangle.
- `Spec.map (CommRingCat.ofHom (algebraMap k K))` is exactly `Spec K → Spec k`.
- `X_K` is `pullback X.hom` along that map. `Y_K` is the corresponding pullback of
  `Y.hom`, as the codomain of `fK`.
- The base-changed morphism is the underlying map of `(Over.pullback ...).map f`,
  named locally by `let fK`. Its two projections are those of the recorded base-change
  convention; no arbitrary isomorphic model or unspecified morphism is substituted.
- Every point of `X` is covered by `(x : X.left)`; every point of `X_K` by `xK`.
  The binder's explicit `: Scheme` annotation prevents Lean from choosing the category
  of types for the pullback; it does not restrict the points.
- “Above x” is `hx : (pullback.fst X.hom ...) xK = x`.
- “f is étale at x” is `∃ U : X.left.Opens, x ∈ U ∧ Etale (U.ι ≫ f.left)`.
  `U.ι` includes the open subscheme, so the composite is the restriction to `U`.
- The right side is the identical open-neighbourhood condition for `xK` and `fK`.
  `↔` asserts both preservation and reflection, for the particular arbitrary point above x.

Dependency declarations read and used:

- `def-pc-field-extension`: `Algebra`, Mathlib.Algebra.Algebra.Defs; also the existing
  `algebraMap`, `Spec`, and `Spec.map` from Mathlib.AlgebraicGeometry.Scheme.
- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  Mathlib.AlgebraicGeometry.Scheme. `Scheme.Opens.ι` is the open-subscheme inclusion
  in Mathlib.AlgebraicGeometry.Restrict.
- `def-pc-morphism-conventions` is a convention-only node with no declaration.
  Its named étale notion is used from `def-weil-etale-morphism` below.
- `def-pc-base-change`: imported Sheaf.AlgebraicGeometry.BaseChangeConventions,
  whose docstring and `baseChange_morphism_projections` specify `Limits.pullback`
  and `Over.pullback`. Its record expressly directs scheme-base-change citers to
  these existing declarations rather than `Scheme.Modules.moduleBaseChange`.
  Read `Over.pullback` in Mathlib.CategoryTheory.Comma.Over.Pullback as well.
- `def-weil-etale-morphism`: `AlgebraicGeometry.Etale`,
  Mathlib.AlgebraicGeometry.Morphisms.Etale; its `iff_flat_and_formallyUnramified`
  supplies exactly the three defining clauses of the node.

Edge cases checked: empty schemes yield no point binders, so no spurious existence
claim is made; empty neighbourhoods cannot witness the condition for a supplied point.
The identity extension gives the usual pullback of the original morphism. Arbitrary
characteristic, transcendental extensions, and non-finite-type schemes are allowed:
no separability, finiteness, Noetherian, or presentation hypothesis has been added.
Neither x nor xK is required to be closed or geometric. The universe `u` is explicit
and arbitrary; all fields and schemes can be placed in a common ambient universe,
with no fixed size bound.

Searches (all 2026-10-11):

- msearch leansearch, “etale scheme morphism at a point base change field extension”:
  service unavailable, Internal Server Error; no verdict inferred.
- msearch leanfinder, “A morphism of schemes is etale at a point if and only if its
  base change to a field extension is etale at a point above it”: eight hits, including
  global base-change stability and `Algebra.IsEtaleAt.comp`; no scheme pointwise iff.
- msearch loogle, `AlgebraicGeometry.Etale, pullback.map`: zero hits; the service
  reported unknown identifier `pullback.map`.
- msearch grep, `EtaleAt|etaleAt|etale.*baseChange|Etale.*pullback`, AlgebraicGeometry:
  nine hits, all global étale or weakly étale stability; none states this equivalence.
- rg of `IsEtaleAt|etaleAt|EtaleAt|etale.*point|etale.*neighbour` in the project and
  WeilConjectures: the project has ring-level `IsEtaleAt.of_fieldExtension`, not this
  scheme statement. The source has no equivalent scheme pointwise field-extension iff.
- rg for the item id in WeilConjectures and dag/lean_names_upstream.json: no match.
- rg for `etaleAt_iff_fieldExtension` in Mathlib, WeilConjectures, project Lean and
  dag/lean_names_upstream.json: no collision.

Source verification: the local Stacks source is absent on this machine, so read
https://stacks.math.columbia.edu/tag/0C4Y and
https://stacks.math.columbia.edu/tag/02VN directly. The former supplies faithful
flatness at each point above x; the latter is global fpqc descent, not itself the
pointwise assertion. The docstring follows both proof steps of the node and names
its separate pointwise-descent proof dependency, rather than claiming 02VN proves it.
No statement fault or disputed clause was found.

Validation: server single-file compilation succeeded cleanly (1.9 s) after adding
an explicit Scheme type annotation for the fibre-product point. All variables and
the universe are explicitly bound. The worker runs the delivery dry run only;
independent second reading and delivery are left to the second reader.

## Second reading by E1

The node introduces a field `k`, a field extension `K/k`, schemes `X` and `Y`
over `Spec k`, a morphism `f : X ⟶ Y`, its base change along
`Spec K → Spec k`, and points `x : X` and `xK : X_K` with `xK` above `x`.
The Lean binders `(k K : Type u) [Field k] [Field K] [Algebra k K]`,
`{X Y : Over (Spec (CommRingCat.of k))}`, `f`, `x`, `xK`, and `hx` render
these objects exactly. The base-change map is the recorded `Over.pullback`
construction, with the explicit `Scheme` annotation on `xK` fixing its type.

The conclusion has both clauses in the node's order. Its left side is
`∃ U : X.left.Opens, x ∈ U ∧ Etale (U.ι ≫ f.left)`, expressing étaleness on
an open neighbourhood of `x`; its right side is the identical condition for
`xK` and the induced `fK`, under the local `let fK := ...`. The equivalence
therefore preserves and reflects pointwise étaleness for every point above
`x`, with no additional finiteness, Noetherian, separability, or characteristic
hypothesis. Empty schemes have no point obligations, and the statement also
covers the identity extension, arbitrary characteristic, and arbitrary
transcendental extensions. No mismatch was found and no source or node
correction was needed.

Searches were repeated independently: grep of Mathlib, WeilConjectures, and
the project found no declaration named `etaleAt_iff_fieldExtension`; LeanFinder
returned only ring-level étale-locus and global morphism facts, and Loogle had
no matching pointwise theorem. Thus the module is new and uses the unique
`AlgebraicGeometry.etaleAt_iff_fieldExtension` declaration shown above.
