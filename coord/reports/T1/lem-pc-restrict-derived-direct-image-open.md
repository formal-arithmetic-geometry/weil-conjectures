## Worker report

The module states the scheme specialization of Stacks Lemma 20.32.4 (Tag 08FE):
restriction of the derived direct image along an open `V` is naturally isomorphic to
first restricting along `f ⁻¹ᵁ V` and then applying the derived direct image of
`f ∣_ V`. The theorem is intentionally a statement with `sorry`; no mathematical
claim is proved here.

The binders render the node as follows. `X Y : Scheme.{u}` and `f : X ⟶ Y` are the
scheme and its morphism. `V : Y.Opens` is the target open, `f ⁻¹ᵁ V` is its inverse
image, and Mathlib's `f ∣_ V` is the induced morphism of restricted schemes. The four
`HasDerivedCategory` binders provide the derived categories on `X`, `Y`, `f ⁻¹ᵁ V`,
and `V`. The left functor is `schemeDerivedDirectImage f` followed by the derived
open restriction composite (`overFunctor`, `Scheme.Modules.overEquiv`, and
`Functor.mapDerivedCategory`). The right functor is the corresponding derived open
restriction on `X` followed by `schemeDerivedDirectImage (f ∣_ V)`. `Nonempty` of the
functor isomorphism expresses the canonical natural isomorphism, hence all objects
`E` and naturality in `E`.

The explicit arguments to `Functor.mapDerivedCategory` are the additivity and finite
limit/colimit preservation witnesses. The local typeclass-search option is scoped to
the theorem declaration because synthesis of these composites exceeds the default
heartbeat limit.

Dependencies used: `AlgebraicGeometry.Scheme` and `Scheme.Hom` from
`Mathlib.AlgebraicGeometry.Scheme`; `AlgebraicGeometry.schemeDerivedCategory` from
`Sheaf.AlgebraicGeometry.DerivedCategory`; `AlgebraicGeometry.schemeDerivedDirectImage`
from `Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage`; the shared open-restriction
exactness instances imported transitively from `Sheaf.Paper.DerivedHomMayerVietoris`;
`Scheme.Modules.overEquiv` from `Mathlib.AlgebraicGeometry.Modules.Sheaf`; and
`AlgebraicGeometry.morphismRestrict` from `Mathlib.AlgebraicGeometry.Restrict`.

Edge cases checked: `V = ⊥` and `V = ⊤`, empty source or target, identity morphisms,
zero derived objects, and unbounded derived objects. No finiteness, separation,
quasi-compactness, or nonemptiness assumption is introduced.

Searches made: `msearch.py` LeanFinder query “derived direct image commutes with
restriction to an open subset naturally in the complex” returned only underived
restriction and morphism-restriction declarations; the Loogle query
“CategoryTheory.Functor.mapDerivedCategory, AlgebraicGeometry.Scheme.Modules.overEquiv”
returned zero hits; grep for `restrict.*direct.*image|derived.*restriction` in
Mathlib AlgebraicGeometry returned zero hits. `rg` over `WeilConjectures/`, `lean/Sheaf/`,
and `dag/lean_names_upstream.json` found no existing declaration of this statement.
The source was read at Stacks Tag 08FE and its K-injective proof (Tag 08BS).

## Earlier second reading (a previous round; superseded)

I reread the item node, all recorded statement dependencies, and the module. The
scheme and morphism binders, target open, inverse-image open, induced restricted
morphism, four derived-category instances, and both derived direct-image/restriction
functors match the node clause by clause. The `Nonempty` functor isomorphism records
naturality in every `E`. The source also phrases the result for general ringed spaces;
the node explicitly permits the scheme formulation, which is the formulation encoded
by this project's scheme derived-category and derived-direct-image declarations. No
hypothesis is added and no scheme edge case is excluded. The only repair from the
prior draft was to use explicit `mapDerivedCategory` witnesses and to scope the
synthesis option; the dependency object-file failure is resolved on the server.

## Second reading by T1

Independent reading against the item JSON, its three statement-dependency nodes,
their recorded declarations, and the Stacks TeX at
`cohomology.tex`, lines 7809–7916, especially
`lemma-restrict-direct-image-open` (08FE) and
`lemma-restrict-K-injective-to-open` (08BS). The introductory convention identifies
restriction with the exact functor on complexes; the source assumes only a morphism
of ringed spaces and an open of its target. The node asks first for schemes and
mentions the ringed-space generalization parenthetically. The delivery states that
scheme formulation, using the recorded scheme dependencies.

Object, hypothesis, and conclusion checklist:

- Schemes X and Y: `{X Y : Scheme.{u}}`, using
  `Mathlib.AlgebraicGeometry.Scheme`, the recorded `def-pc-scheme` declaration.
  Verdict: the same schemes, with no affine, Noetherian, or field hypothesis.
- Morphism f: `(f : X ⟶ Y)`, hence the recorded `Scheme.Hom` notion.
  Verdict: arbitrary scheme morphism, without quasi-compactness or separation.
- Target open V: `(V : Y.Opens)`. Verdict: arbitrary open, not required nonempty.
- U = inverse image of V: `f ⁻¹ᵁ V`, Mathlib's opens-map inverse image.
  Verdict: the specified U, not an independent open with an extra assumption.
- Induced g: `f ∣_ V`. I opened `morphismRestrict` in
  `Mathlib.AlgebraicGeometry.Restrict`: its signature is
  `(f ⁻¹ᵁ V).toScheme ⟶ V`, and its definition uses the canonical pullback
  restriction isomorphism and the second projection. Verdict: precisely g.
- E in D(O_X): the source of both functors is `schemeDerivedCategory X`.
  A functor isomorphism supplies a component at every E; its naturality quantifies
  over every morphism between E's. Verdict: all E, including unbounded objects,
  with f and V fixed before quantifying over E.
- Derived categories: the four `HasDerivedCategory` instances concern the shared
  `SheafOfModules.{u} (moduleRings ...)` carriers on X, Y, U, V. I opened
  `schemeDerivedCategory` in `Sheaf.AlgebraicGeometry.DerivedCategory`; it is the
  unbounded Mathlib localization of this exact carrier, not D_QCoh or D-plus.
  Verdict: the instances select localization realizations and morphism universes;
  they do not impose geometric hypotheses or different module categories.
- Rf_* and Rg_*: `schemeDerivedDirectImage f` and
  `schemeDerivedDirectImage (f ∣_ V)`. I opened the recorded declaration in
  `Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage` and its underlying
  `RingedSpace.derivedModuleDirectImage`: these are the right derived functors of
  module direct image, computed by K-injective resolutions. Verdict: the node's
  functors, not higher direct images of individual modules.
- Restriction to V and U: each `SheafOfModules.overFunctor` is followed by
  `Equivalence.functor (Scheme.Modules.overEquiv ...)`, then
  `Functor.mapDerivedCategory`. I opened all three declarations: restriction to
  the localized site, equivalence to modules on the open scheme, and the functor
  induced by an exact functor on cochain complexes, respectively. Their target
  categories are the same shared carriers used in `schemeDerivedCategory`.
  Verdict: the node's derived open restrictions. The explicit additivity and
  preservation witnesses are supplied terms, not extra theorem hypotheses;
  the shared `moduleOverFunctor_*` instances are reused, not restated.
- Left conclusion `(Rf_*E)|_V`: `schemeDerivedDirectImage f ⋙` the target
  restriction functor. Verdict: direct image first, restriction second.
- Right conclusion `Rg_*(E|_U)`: the source restriction functor `⋙
  schemeDerivedDirectImage (f ∣_ V)`. Verdict: restriction first, direct image
  second, with target D(O_V).
- Isomorphism and naturality: `Nonempty (leftFunctor ≅ rightFunctor)` is existence
  of one natural isomorphism, giving compatible isomorphisms at all E. Verdict:
  the natural comparison assertion. As for the source's equality, no additional
  normalization equation or specified comparison map occurs in the node; the
  docstring specifies its construction from the canonical sectionwise equality.

Edge cases: V = bottom and V = top remain in `Y.Opens`; U is their actual inverse
image. Empty schemes and identity morphisms are not excluded. Zero complexes and
zero derived objects are included since there is no condition on E. There is no
index family, positive degree, n, or characteristic restriction. Degree zero and
all negative degrees are included by the unbounded derived category. The scheme
universe u is arbitrary, and the four localization morphism universes are
independent, matching the dependencies. No variable or universe is unbound.

Independent searches used different wording from the worker's searches:

- LeanFinder: “unbounded pushforward of sheaves of modules is local on the target
  scheme”: eight hits, all underived pushforward/sections/adjunction declarations;
  none states the unbounded derived restriction assertion.
- Loogle: `Functor, NatIso, AlgebraicGeometry.morphismRestrict` was rejected for
  unknown identifier NatIso; the follow-up `AlgebraicGeometry.morphismRestrict`
  returned twelve restriction/pullback declarations, none the derived theorem.
- LeanSearch: “The derived pushforward of an O_X module complex restricts to the
  derived pushforward on the inverse image open subset”: unavailable (Internal
  Server Error), recorded as unavailable rather than a negative result.
- `rg` of Mathlib AlgebraicGeometry, the source project's `WeilConjectures`, and
  this project's `lean/Sheaf` for direct-image/pushforward with open/restrict
  in either order found the upstream
  `AlgebraicGeometry.nonempty_higherDirectImage_iso_restrict` in
  `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections`. I opened
  its signature and surrounding binders: it concerns a single module, q : Nat,
  injective resolutions of X.Modules, and an objectwise higher-direct-image
  comparison. It is not this natural isomorphism on unbounded D(O_X).
  Other hits concern etale/pro-etale sheaves or use this node in proof docstrings;
  they do not supply an existing declaration of this statement.

No new nodes, dependency modules, or statement correction are present. No H3/H4
mismatch was found. The module and node signature are preserved; the signature
was checked verbatim against `lean.statement`, and every line is at most 100
characters. The sole theorem remains `by sorry`; there is no new definition,
hollow data, private notation, local instance, or proved claim. Its docstring
contains both proof steps and their exact DAG references: restrict a K-injective
resolution using 08BS, then identify both direct-image complexes sectionwise
using `def-pc-ringed-spaces-derived-direct-image`, respecting differentials and
naturality. This reading changes only the report by adding the explicit checklist,
source/dependency verification, edge-case analysis, and independent searches.
