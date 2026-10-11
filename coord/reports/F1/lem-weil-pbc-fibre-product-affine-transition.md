## Worker report

The module `Sheaf.AlgebraicGeometry.AffineFibreProductTransition` states
`AlgebraicGeometry.isAffineHom_pullback_map`, with its sole proof `sorry`.
No definitions, extra nodes, dependency modules, or statement corrections are needed.

Hypothesis and conclusion correspondence:

- The two diagrams consist of six schemes, rendered by
  `{X' S' T' X S T : Scheme.{u}}`, and their four structure maps
  `(f' : X' ⟶ S') (g' : T' ⟶ S') (f : X ⟶ S) (g : T ⟶ S)`.
- The three comparison morphisms are `(a : X' ⟶ X) (h : S' ⟶ S) (c : T' ⟶ T)`.
- Compatibility with the first structure map is `ha : f' ≫ h = a ≫ f`;
  compatibility with the second is `hc : g' ≫ h = c ≫ g`. These reverse
  the written equality in the node, without changing it mathematically.
- All three comparison morphisms are affine, exactly
  `[IsAffineHom a] [IsAffineHom h] [IsAffineHom c]`.
- The induced morphism is Mathlib's `pullback.map f' g' f g a c h ha hc`,
  from `pullback f' g'` to `pullback f g`. Its definition is the universal
  lift with components `pullback.fst f' g' ≫ a` and `pullback.snd f' g' ≫ c`.
  The conclusion is precisely `IsAffineHom` of this morphism.

Dependency declarations read and used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`, in
  `Mathlib.AlgebraicGeometry.Scheme`; locally affine locally ringed spaces
  and their morphisms.
- `pqf-def-affine-morphism`: `AlgebraicGeometry.IsAffineHom`, in
  `Mathlib.AlgebraicGeometry.Morphisms.Affine`; preimages of affine opens are affine.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback`, its projections,
  lift and `pullback.map`, in `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`;
  existence for schemes is the `HasPullbacks Scheme` instance in
  `Mathlib.AlgebraicGeometry.Pullbacks`. All are available through the single
  affine-morphisms import; no private notion is introduced.

Edge cases checked before writing: all six schemes are arbitrary in an explicitly
bound universe; there are no nonemptiness, finite-type, affine-object, or base-field
restrictions. Empty factors give an empty source fibre product and remain covered.
Identity comparison maps give the identity map between the fibre products.
The structure maps need not be affine. In particular, `IsAffineHom h` is retained
although the proof needs only separatedness of `h`; weakening this hypothesis would
change the node. The changing-base map is indispensable when `S'` differs from `S`.

Searches made:

- `msearch.py leanfinder`, query “Compatible diagrams of schemes with affine comparison
  morphisms induce an affine morphism between fibre products”: eight hits about
  affine pullback objects and affine inverse systems, no compatible triple-map statement.
- `msearch.py loogle`, query `IsAffineHom, pullback.map`: zero hits, unknown
  identifier `IsAffineHom` in that service; the qualified declaration was read locally.
- `msearch.py leansearch`, query “An induced map of fibre products of schemes is affine
  if the maps on both factors and bases are affine”: service unavailable, Internal
  Server Error; no verdict inferred from its unavailability.
- `msearch.py grep`, query `IsAffineHom.*map|affine.*pullback.map|pullbackMap`,
  in `AlgebraicGeometry`: thirteen hits, none the statement of this node.
- Local `rg` searches in source `WeilConjectures`, project `lean/Sheaf`, Mathlib,
  and `dag/lean_names_upstream.json`: the node id and proposed declaration name have
  no existing declaration; fibre-product map occurrences do not state this theorem.

Source checks: local Stacks TeX is absent on this machine, so the official pages
https://stacks.math.columbia.edu/tag/01SD (affine base change),
https://stacks.math.columbia.edu/tag/01SC (affine composition), and
https://stacks.math.columbia.edu/tag/01KR (changing-base map as a base change of the
base diagonal, closed immersion for a separated base map) were opened and read.
The docstring carries all four steps of the node's natural-language proof and its
named dependencies. No node fault or disputed statement was found.

Validation: server single-file compilation requested with `scompile.py`; the final
compile and mechanical preflight results are recorded by the delivery dry run.
The independent second reading is reserved for the next worker.

## Second reading by F1

I independently opened the delivered node and Lean module, all three statement-dependency
nodes, and the Mathlib declarations they record. No semantic mismatch was found; the
module and node signature are retained verbatim. No new definition node, dependency module,
or statement correction is present or needed.

Object/hypothesis/conclusion inventory and correspondence (H3):

1. Six arbitrary schemes, two cospans: `{X' S' T' X S T : Scheme.{u}}`,
   `(f' : X' ⟶ S') (g' : T' ⟶ S') (f : X ⟶ S) (g : T ⟶ S)`.
   Verdict: exact. `Scheme` extends `LocallyRingedSpace` with local affine charts
   (Scheme.lean:42); `Scheme.Hom` is the underlying locally ringed-space morphism
   (line 74), exactly the declarations of `def-pc-scheme`.
2. Comparisons in the stated direction: `(a : X' ⟶ X) (h : S' ⟶ S)
   (c : T' ⟶ T)`. Verdict: exact; no comparison is identified with an identity.
3. First compatibility: `ha : f' ≫ h = a ≫ f`. Since `≫` composes left to right,
   this is h after f' equals f after a. Verdict: exactly the node's equality,
   with sides exchanged.
4. Second compatibility: `hc : g' ≫ h = c ≫ g`. Verdict: exactly the second
   commuting square, with sides exchanged.
5. Affineness of each comparison, separately: `[IsAffineHom a]`, `[IsAffineHom h]`,
   `[IsAffineHom c]`. Verdict: all three hypotheses present, none added. Read
   Affine.lean:47-48: the class requires affine preimages of every affine open,
   exactly `pqf-def-affine-morphism`. In particular neither structure morphism
   nor any scheme is assumed affine; the affine-base comparison hypothesis is
   not weakened to separatedness even though the proof only needs that consequence.
6. Source and target fibre products: `pullback f' g'` and `pullback f g` inside
   `pullback.map f' g' f g a c h ha hc`. Verdict: exactly `def-pc-fibre-product`.
   Read HasPullback.lean:95,111,115,128,270 and Pullbacks.lean:481-486: schemes
   have all pullbacks, so no extra existence hypothesis is hidden in the theorem.
7. Induced morphism: HasPullback.lean:270-276 defines this map as the universal
   lift of `pullback.fst f' g' ≫ a` and `pullback.snd f' g' ≫ c`.
   Verdict: exactly the uniquely specified comparison, with `h`, `ha`, `hc`
   supplying compatibility. Argument order `a c h` is correct.
8. Sole conclusion: `IsAffineHom (pullback.map f' g' f g a c h ha hc)`.
   Verdict: exact affineness of the induced morphism, without extra conclusions.
   Quantification is universal over the schemes, maps, compatibility proofs, and
   three affine hypotheses; instances are Prop-valued hypotheses.

Source reading: local literature contains no Stacks TeX, so I fetched the official
Stacks source into this item's scratchpad and read morphisms.tex:1710-1742,
1967-2053 and schemes.tex:4236-4261. Also checked the official tag pages
[01SD](https://stacks.math.columbia.edu/tag/01SD),
[01SC](https://stacks.math.columbia.edu/tag/01SC),
[01SG](https://stacks.math.columbia.edu/tag/01SG), and
[01KR](https://stacks.math.columbia.edu/tag/01KR).
The affine section has no standing field, Noetherian, finite-type, or nonemptiness
assumption. Base change is along an arbitrary scheme morphism; composition is
unrestricted. The changing-base map is the base change of the base diagonal;
separatedness makes it a closed immersion. Tag 01S7 gives separatedness for an
arbitrary affine morphism and Tag 01SE gives affineness of a closed immersion.
Thus the node's four-step assembly and the Lean docstring match these sources.
Tag 01SG is an additional permanence lemma, not a missing hypothesis of this item.

Edge cases: empty schemes/fibre products are allowed, since no nonemptiness binder
appears. The empty affine scheme (Spec of the zero ring) is not excluded. Identity
comparisons are covered; a different base remains covered, not specialized away.
There is no index set or numerical n in this statement. No characteristic or field
is specified, so schemes over all rings and characteristics are allowed. The explicit
`universe u` is unrestricted; all six objects belong to the same category
`Scheme.{u}`, as needed to form its categorical pullbacks. Arbitrarily large schemes
are covered by choosing u large enough. Every variable and universe is explicitly bound.

Independent searches (H4), with wording different from the worker's:

- `msearch.py leanfinder`: "Affineness of the morphism on pullbacks associated to a
  natural transformation of cospans with affine components". Eight hits, concerning
  affine pullback objects, affine-space squares and local/base-change facts; none
  states affineness of the general changing-base comparison.
- `msearch.py leansearch`: "For a commutative morphism of cospans in schemes, affine
  maps on all three objects give an affine map on limits". Service unavailable
  (Internal Server Error); recorded as unavailable, without a mathematical verdict.
- `msearch.py grep`: `IsAffineHom.*(pullback|map)|pullback.*IsAffineHom`.
  Twelve hits: affine transition limits, affine pullback objects, and base-change
  instances; no exact statement. Direct `rg` on Mathlib/AlgebraicGeometry,
  source WeilConjectures, project lean/Sheaf and dag/lean_names_upstream.json also
  found no declaration of this item or name collision. Inspected the related
  `CategoryTheory.MorphismProperty.pullbackMap` (Limits.lean:254-260): its base
  comparison is literally `𝟙 S`; it is only the same-base factor of this item.
  Inspected `IsSeparated`'s closed-immersion instance for `pullback.mapDesc`
  (Separated.lean:130-132): it is only the changing-base factor, not the whole
  three-comparison theorem. Neither replaces this statement under H4.

H5/H6/H8/H9: no definitions or hollow data; one named theorem with only `sorry`
as its proof. The module and declaration docstrings name sources and the blueprint
id, and the theorem docstring carries all four proof steps with their dependency ids.
The sole import supplies the actual predicates, schemes and pullbacks used. Namespace,
file topic, explicit universe and line lengths conform. The node's `lean.statement`
is verbatim the theorem signature before `:=`.

Changes: appended this independent review only; no Lean, signature, dependency or
node-statement repair was necessary. Validation: `scompile.py F1
lem-weil-pbc-fibre-product-affine-transition
lean/Sheaf/AlgebraicGeometry/AffineFibreProductTransition.lean` compiled on the server
in 1.6 seconds, exit 0, without warnings. Delivery preflight follows below.
