## Worker report

The module `Sheaf.AlgebraicGeometry.QuasiAffineTargetLocality` states
`AlgebraicGeometry.isQuasiAffineHom_iff_of_affine_open_cover`. Its sole proof is `sorry`.
No definition, helper, new node, dependency repair, or statement correction was needed.
The original node is changed only in `lean`.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- “Let h : Z → S be a morphism of schemes”: `{Z S : Scheme.{u}} (h : Z ⟶ S)`.
  The scheme universe `u` is explicitly bound and arbitrary.
- “S = ⋃ a ∈ A, S_a be an affine open cover”: `{A : Type v} (U : A → S.Opens)`,
  `(hU : ∀ a : A, IsAffineOpen (U a))`, and `(hcover : iSup U = ⊤)`.
  `v` is explicitly bound and independent of `u`; this is an ordinary open cover,
  with no size, finiteness, or nonemptiness restriction on its index set.
  In the complete lattice of opens, `iSup U` is the union of this family.
- “A quasi-affine scheme means a scheme isomorphic to a quasi-compact open subscheme
  of an affine scheme”: the standard `Scheme.IsQuasiAffine` is used. Its definition
  extends `CompactSpace X` and `IsImmersion X.toSpecΓ`; Mathlib proves that this canonical
  map is an open immersion. Conversely, a quasi-compact open subscheme of an affine scheme
  is quasi-affine by `Scheme.IsQuasiAffine.of_isImmersion`. Thus these are exactly the
  node's objects, including its finite-subcover meaning of quasi-compactness.
- “h is quasi-affine”: `IsQuasiAffineHom h`, the exact recorded dependency class.
- “if and only if”: the proposition is an `↔`, with both directions and no additional clause.
- “h⁻¹(S_a) is a quasi-affine scheme for every a”: `∀ a : A,
  (h ⁻¹ᵁ U a).toScheme.IsQuasiAffine`. This uses the actual open inverse image and its
  induced open subscheme, rather than an arbitrary isomorphic substitute.
- “No quasi-compactness or separation hypothesis on S and no finite-type hypothesis on h”:
  the signature contains just the morphism and the affine-cover data listed above.
  It contains no such typeclass arguments, no quasi-compactness assumption on h,
  and no hypothesis asserting the sought locality principle.

Statement dependency declarations read in full, including docstrings:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`.
- `def-nagata-quasi-affine-morphism`:
  `WeilConjectures.Mathlib.AlgebraicGeometry.QuasiAffine`, declaration
  `AlgebraicGeometry.IsQuasiAffineHom`. Its sole field is
  `isQuasiAffine_preimage (U : Y.Opens) (hU : IsAffineOpen U) :
  (f ⁻¹ᵁ U).toScheme.IsQuasiAffine`, exactly the node's definition.
- Absolute quasi-affineness is Mathlib's
  `AlgebraicGeometry.Scheme.IsQuasiAffine` in `Mathlib.AlgebraicGeometry.QuasiAffine`;
  its compactness, open-immersion consequence, and `of_isImmersion` were inspected.

The two statement-dependency modules are public imports. The recorded modules of all stated
proof dependencies are ordinary imports: fibre products (`Pullback.HasPullback`), finite type
(`Morphisms.FiniteType`), open immersions (`OpenImmersion`, `Morphisms.OpenImmersion`),
quasi-separatedness (`Morphisms.QuasiSeparated`), quasi-compact target locality
(`Morphisms.Basic`), absolute quasi-affine canonical embeddings (`QuasiAffine`), affine qcqs
(`AffineScheme`, `Morphisms.QuasiSeparated`), maps to affines (`GammaSpecAdjunction`), gluing
(`Gluing`), `WeilConjectures.AlgebraicGeometry.AffineAlgebraLocalMaps`,
`WeilConjectures.AlgebraicGeometry.AffineMorphismRelativeSpec`,
`WeilConjectures.AlgebraicGeometry.QuasicoherentPushforwardQcqs`, and
`Sheaf.AlgebraicGeometry.CoherentFiniteType`. The module docstring and theorem docstring
cite Tag 01SM; the latter carries all six proof steps and their dependency node names.

Source and edge cases checked before writing:

- Read `literature/stacks-project/morphisms.tex`, `lemma-characterize-quasi-affine`,
  statement and full proof (lines 2224–2278). Its (2) ⇒ (4) ⇒ (3) ⇒ (1) proves the
  converse for any supplied affine cover, and its definition proves the forward direction.
  It imposes none of the excluded target or finite-type conditions.
- Empty index type: `iSup U = ⊤` forces S empty. A morphism to S then forces Z empty;
  the right side is vacuous and the left holds by its all-affine-opens definition.
- Empty source, including empty inverse images: empty schemes are affine and hence
  quasi-affine, so this case is included. The zero-ring affine scheme is included.
- Infinite, repeated, or empty cover members are allowed, and no finite subcover of S
  is assumed. An empty member contributes only an empty quasi-affine inverse image.
- A singleton affine cover is the usual equivalence over an affine base.
- Non-quasi-compact and nonseparated targets are permitted; only their specified opens
  must be affine. The identity on an arbitrary scheme has affine inverse images on an
  affine cover and is indeed quasi-affine, so no global quasi-affineness of S is implied.
- No limit-index or test-object universe condition is involved: A merely indexes actual
  opens of S. Both universes are explicitly bound, and `autoImplicit` is disabled.

Searches for an existing statement:

- `msearch.py ... leanfinder "A morphism of schemes is quasi affine if and only if inverse
  images of an affine open cover are quasi affine"`: eight hits, including
  `HasAffineProperty.iff_of_iSup_eq_top`, `of_iSup_eq_top`, `iff_of_openCover`, and
  `Scheme.IsQuasiAffine.of_isAffineHom`. The generic locality APIs require a
  `HasAffineProperty` instance for the property; the source supplies no such instance for
  `IsQuasiAffineHom`. The absolute lemma assumes the morphism affine and is not this node.
- `msearch.py ... loogle '"IsQuasiAffineHom"'`: no hits.
- `msearch.py ... leansearch "quasi affine morphism locality affine open cover target"`:
  eight hits on the same generic APIs, affine covers, and absolute quasi-affineness;
  none establishes locality for this relative class.
- `msearch.py ... grep 'IsQuasiAffineHom|quasi.affine.*local|local.*quasi.affine'
  AlgebraicGeometry`: two hits in Mathlib's absolute `QuasiAffine.lean`, not the statement.
- The same regular expression with `rg` in upstream `WeilConjectures` and side `lean/Sheaf`:
  upstream defines the relative class, its open restrictions, and base-change/Zariski-main
  consequences; the side library has base change, relative-spectrum embeddings, and descent.
  No module states the requested affine-cover equivalence.
- `rg` for the item id in upstream `WeilConjectures`: no matches.
- `rg` for the proposed declaration name in `dag/lean_names_upstream.json`, upstream,
  Mathlib, and side `lean/Sheaf`: no matches.

No mathematical fault or STATEMENT-DISPUTED issue was found. No source, target, or dependency
statement is changed. Validation uses only the prescribed `scompile.py`/`deliver2.py` wrappers.

## Second reading by Q29

The dispatcher brief forbids starting another agent and assigns independent review to the
maintainer. This section records the worker's own final rereading, not an independent review.
With the node and module open, I checked the morphism, arbitrary index universe, openness,
affineness, covering equation, relative quasi-affineness, both directions, and every inverse
image against the signature above. All match. The absolute quasi-affine predicate retains
quasi-compactness. The proof docstring follows the six node steps, including the common-chart
injectivity argument and diagonal locality. No hypothesis was added or omitted. The only
wording adjustment during rereading clarified that the maps Z_a → U a, rather than their
diagonals, are the morphisms whose quasi-separatedness is supplied by qcqs permanence.
