## Worker report

The module `Sheaf.AlgebraicGeometry.SepClosedFieldComponentsBijection` states
`AlgebraicGeometry.bijective_connectedComponentsMap_pullback_fst_of_isSepClosed`.
Its sole proof is `sorry`; no definitions, extra assumptions, or auxiliary theorems were added.
The statement agrees with Stacks Project, varieties.tex, label
`lemma-separably-closed-field-connected-components` (Tag 0363), first assertion.
I read that lemma and its proof and the product lemma Tag 0385 immediately preceding it.

Hypothesis and clause correspondence:

- The base field is `(k : Type u) [Field k]`; separable closedness is `[IsSepClosed k]`.
- The arbitrary field extension is `(L : Type u) [Field L] [Algebra k L]`;
  `algebraMap k L` is the prescribed extension homomorphism. Neither finite nor algebraic
  extension is assumed.
- The arbitrary scheme is `(Z : Scheme.{u}) [Z.Over (Spec (CommRingCat.of k))]`, with
  structure morphism `Z ↘ Spec (CommRingCat.of k)`.
- The extension morphism is `Spec.map (CommRingCat.ofHom (algebraMap k L))`.
- The scheme `Z_L` is Mathlib's chosen `pullback` of those two morphisms, and `p` is
  `pullback.fst` of the same two arguments. Thus the projection has exactly the requested
  orientation, from `Z ×_k Spec L` to `Z`.
- Components are Mathlib's `ConnectedComponents`: points are quotiented by equality of
  `connectedComponent`, the maximal connected subset containing the point. Such components
  are nonempty. This gives the same set as maximal nonempty connected subsets, including
  for spaces with components which are not open.
- The specified map is `p.continuous.connectedComponentsMap`, not a chosen bijection.
  `Continuous.connectedComponentsMap_mk` says it takes `[x]` to `[p x]`, hence sends each
  component to the unique component containing its image. The conclusion
  `Function.Bijective` asserts both injectivity and surjectivity of precisely this map.
- No finiteness, separatedness, quasi-compactness, or nonemptiness hypothesis occurs.
  The universe `u` is explicit and arbitrary, and all objects can be viewed in a common
  universe; there is no quantification over a too-small universe of test extensions.

Dependency declarations read and used:

- `Mathlib.FieldTheory.IsSepClosed`: `IsSepClosed` (def-pc-separably-closed).
- `Mathlib.Algebra.Algebra.Defs`: `Algebra`, `algebraMap` (def-pc-field-extension).
- `Mathlib.AlgebraicGeometry.Over`: `AlgebraicGeometry.Scheme.Over`
  (def-weil-scheme-over-base).
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd` (def-pc-fibre-product).
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`, `connectedComponent`
  (def-weil-connected-scheme). The component quotient and its map use the existing
  `Mathlib.Topology.Connected.Clopen.ConnectedComponents` declaration (namespace at root),
  and `Continuous.connectedComponentsMap` in `Mathlib.Topology.Connected.TotallyDisconnected`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Spec.map`
  (def-weil-affine-spectrum).
- Proof-only import `WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected`:
  `AlgebraicGeometry.GeometricallyConnected.of_connectedSpace_of_isSepClosed`
  (lem-weil-separably-closed-geometrically-connected). Its full signature and docstring were
  read; this theorem is the forward implication needed in the proof, so its recorded
  interface needs no repair here.
- `Mathlib.AlgebraicGeometry.Geometrically.Connected`:
  `AlgebraicGeometry.Scheme.Hom.connectedComponentsHomeomorph`
  (lem-weil-pbc-geometrically-connected-product-components). Its full signature takes a
  geometrically connected morphism and an open underlying map. Its specialization is the
  product-component result: geometric connectedness is stable under pullback and schemes
  over a field are universally open, as described by the dependency's mathlib_match.

The public imports expose all definitions in the signature; the geometric-connectedness
Mathlib import also carries the stated product proof dependency. No unstated proof dependency
module is missing and no proof import creates a cycle.

Edge cases checked against the definitions and source: the empty scheme has an empty
pullback and empty component quotient, so the canonical map is bijective between empty
sets; the identity extension gives the usual pullback projection isomorphism; transcendental
and infinitely generated extensions satisfy the same binders; disconnected schemes with
infinitely many components are allowed; non-locally-connected schemes are allowed because
components are not assumed clopen; separably closed imperfect fields in positive
characteristic are covered by IsSepClosed rather than IsAlgClosed. No statement fault or
STATEMENT-DISPUTED issue was found.

Existing-declaration searches (2026-10-15):

- `msearch.py leansearch`: “Connected components of a scheme over a separably closed field
  are invariant under arbitrary field extension” → UNAVAILABLE, service Internal Server
  Error. This is a recorded search limitation, not a mathematical verdict.
- `msearch.py leanfinder`: “Base change of any scheme over a separably closed field by an
  arbitrary field extension induces a bijection on connected components” → 8 hits:
  isField_of_universallyClosed, IsSeparated.isStableUnderBaseChange,
  PrimeSpectrum.isHomeomorph_comap_of_isPurelyInseparable, IsSeparated.instMap,
  PrimeSpectrum.isHomeomorph_comap_tensorProductMap_of_isPurelyInseparable,
  ext_of_isDominant_of_isSeparated, ext_of_isDominant_of_isSeparated', Scheme.isSeparated_iff.
  None states the component bijection for arbitrary extensions over a separably closed base.
- `msearch.py loogle`: `"ConnectedComponents.map", "IsSepClosed"` → OK, zero hits.
- `msearch.py grep`, Mathlib/AlgebraicGeometry:
  `connectedComponentsHomeomorph|of_isSepClosed|ConnectedComponents.map` → 5 hits:
  the two connectedComponentsHomeomorph lines in Geometrically/Connected and three étale
  lifting references in Sites/EtalePoint. The homeomorphism needs geometric connectedness
  and openness of the given map, so it is a proof input, not the same statement.
- `rg -n 'connectedComponents|of_connectedSpace_of_isSepClosed|lem-weil-pbc-sepclosed-field-components-bijection'`
  in WeilConjectures and lean/Sheaf found component topology infrastructure and the existing
  geometric-connectedness input, but no exact statement. In particular the upstream
  Geometrically/Connected module was opened and read: it has geometric connectedness of
  Spec of the extension and of connected schemes, not this component-map bijection.
- `rg` for `sepclosed_field_components|bijective.*connectedComponents|connectedComponents.*bijective`
  in lean/Sheaf, dag/lean_names_upstream.json and upstream Mathlib/AlgebraicGeometry found
  no duplicate of the proposed declaration. Direct source reads verified the component
  quotient, canonical map, pullback projections, fields, spectrum, and over-scheme APIs.

No new nodes, dependency modules, or node corrections are required. The node copy changes
only `lean`. Every binder and universe is explicit, and the file has no local notation,
private definitions, instances, or `#check` commands.

## Second reading by NW

I independently read the sandbox node and Lean module, Stacks varieties.tex
`lemma-separably-closed-field-connected-components` (0363), its proof, and the
preceding `lemma-bijection-connected-components` (0385), including the section's
convention that connected spaces are nonempty. Tag 0363 assumes only an extension
of fields, a scheme over the base, and separable closedness of the base. There is
no ambient finite-type hypothesis here.

My object/hypothesis/conclusion checklist, with the file open:

1. A separably closed field k: `(k : Type u) [Field k] [IsSepClosed k]`.
   Pass. The dependency's `IsSepClosed` is the separable-polynomial splitting
   condition, equivalent to the node's root condition; it is not algebraic closedness.
2. Any extension L/k: `(L : Type u) [Field L] [Algebra k L]`.
   Pass. `Algebra.algebraMap` supplies the specified unital field homomorphism.
   No separability, algebraicity, finite degree or finite generation is required.
3. Any k-scheme Z: `(Z : Scheme.{u}) [Z.Over (Spec (CommRingCat.of k))]`.
   Pass. I read `Scheme.Over`, which abbreviates the structure-morphism data
   `OverClass`, and its arrow notation. No connectedness of Z is assumed.
4. The base change Z_L: the domain of `pullback.fst` is the actual chosen scheme
   pullback of `Z ↘ Spec (CommRingCat.of k)` and
   `Spec.map (CommRingCat.ofHom (algebraMap k L))`. Pass. I read `Spec`,
   `Spec.map`, `pullback` and `pullback.fst`: the spectrum map is contravariant,
   and the first projection has target Z, exactly as the node requires.
5. Components are maximal nonempty connected subsets: the map's inferred domain
   and codomain are `ConnectedComponents` of the pullback and Z. Pass. I read
   `connectedComponentSetoid`, `ConnectedComponents`, and
   `isConnected_connectedComponent` together with the maximality API in Basic.
   Quotienting points by equality of their components gives precisely these
   subsets, with no empty component and no local-connectedness assumption.
6. The specified induced map: `.continuous.connectedComponentsMap` on that
   first projection. Pass. I read its definition and
   `Continuous.connectedComponentsMap_mk`: it sends `[x]` to `[p x]`, hence to
   the unique component containing the image of the source component. This is
   not a freely chosen bijection or a bijection in the opposite direction.
7. Both injectivity and surjectivity: `Function.Bijective` of that very map.
   Pass. All objects precede this conclusion, with no extra instance assumptions.
8. No finiteness hypothesis: none appears in the signature. Pass.

I opened each statement dependency node and its recorded declaration or Mathlib
match, rather than inferring its meaning from its name. I also opened both proof
dependencies. The upstream
`GeometricallyConnected.of_connectedSpace_of_isSepClosed` takes an arbitrary
connected scheme over a separably closed field, exactly the needed input for
Spec L. The Mathlib `Scheme.Hom.connectedComponentsHomeomorph` takes geometric
connectedness and an open map; its base-change instances and the universally-open
instance for a morphism to an integral subsingleton scheme give the recorded
product specialization. The ordinary proof-only import and the public Mathlib
imports cover these dependencies. No dependency repair or new notion is needed.

Edge cases: empty Z yields empty component quotients on both sides; identity and
transcendental/infinite extensions are included; infinitely many nonopen components
are included; imperfect separably closed fields in positive characteristic are
included. The zero ring is not a field, consistently with the node. No index set
or integer n is present. The explicit arbitrary common universe u is the usual
Scheme universe: the binders have no test-object quantification in a smaller
universe and impose no extra universe equality on a mixed-universe site.

Independent duplicate searches (2026-10-15), using different queries:

- LeanFinder through msearch: “The map on pi zero induced by extension of scalars
  of a scheme over a separably closed field is bijective”: eight results, including
  `Algebra.FormallyUnramified.bijective_of_isAlgClosed_of_isLocalRing`,
  `isIso_SpecMap_iff`, `Scheme.SpecToEquivOfField`, and purely inseparable
  algebra-map results. Their signatures concern rings or points, not this theorem.
- Loogle through msearch: `"IsSepClosed", "Bijective"`: one result,
  `IsSepClosed.algebraMap_bijective`, which assumes a separable extension and
  concerns the field map itself. It is not the component statement.
- LeanSearch through msearch: “Extension of scalars preserves pi zero of any scheme
  over a separably closed field”: service unavailable (Internal Server Error).
- Direct rg over upstream WeilConjectures, Mathlib/AlgebraicGeometry, and the
  project's lean/Sheaf for the declaration name, SepClosed/component combinations,
  and components/field-extension wording found no exact statement. The only
  unrelated prose hit was ReducedConstantLowerShriekReduction.lean. I also read
  the upstream geometric-connectedness module in full and the canonical component
  homeomorphism in Mathlib; neither duplicates the item's assertion.

No mathematical mismatch was found; the Lean module and its verbatim node
signature are unchanged. There are no new nodes, dependency modules, statement
corrections, hollow definitions, local notations, private declarations, or proved
auxiliary claims. The sole theorem has a whole-proof sorry. Its source/blueprint
docstring carries all three node proof steps, including the factor swap and its
compatibility with the projection. Every variable and universe is explicitly bound.
