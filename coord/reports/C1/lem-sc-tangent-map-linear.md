## Worker report

The module `Sheaf.AlgebraicGeometry.TangentMapLinear` states
`AlgebraicGeometry.exists_tangentMap_linear`, with `sorry` as its only proof.
No definitions or extra nodes are needed, and no statement correction is made.

Hypothesis and clause correspondence:

- The field is `(k : Type u) [Field k]`. The schemes are `(X Y : Scheme.{u})`,
  with structure morphisms `pX` and `pY` to `Spec (.of k)`.
- The morphism of k-schemes is `(f : X ⟶ Y)` with `hf : f ≫ pY = pX`.
  This equality expresses precisely that the morphism is over k; it is not
  an additional geometric hypothesis.
- The point is `(x : X)` and the target point is everywhere `f x`.
- `KX := X.residueField x` and `KY := Y.residueField (f x)` are the residue fields.
  `he : Function.Bijective (f.residueFieldMap x).hom` is the stipulated
  residue-field isomorphism, packaged as `e : KY ≃+* KX` by
  `RingEquiv.ofBijective`. Thus no separate, unrelated field identification is used.
- `DX` and `DY` are the spectra of `DualNumber KX` and `DualNumber KY`.
  `cX`, `cY` are Spec of reduction modulo epsilon; `qX`, `qY` are Spec of
  the coefficient inclusions; `bX`, `bY` are the canonical point morphisms.
- `TX` is exactly the subtype from the vector-space dependency:
  `cX ≫ θ = bX` says the vector is at x, and
  `θ ≫ pX = qX ≫ bX ≫ pX` says the map is over k.
  `TY` is the same subtype at `f x` in Y.
  These local abbreviations expose the dependency's types, rather than
  introducing competing tangent-space definitions.
- The additive groups and native residue-field module structures on both
  subtypes are selected with `Classical.choose` from the last conjunct of
  `exists_tangentVectors_vectorSpace` and its witness specifications.
  Thus these are specifically the operations defined by the pushout and
  scalar-precomposition formulas, not arbitrary vector-space structures.
- The target becomes a KX-vector space using `Module.compHom TY e.symm.toRingHom`.
  Its action is `λ • θ = e.symm λ • θ` in the native KY-module. This is exactly
  the node's instruction to identify the target residue field through e.
- `d : DY ⟶ DX` is Spec of `DualNumber.mapRingHom e.symm.toRingHom`.
  The ring map sends both coefficients through the inverse residue-field
  isomorphism and preserves epsilon. This is the source-spectrum identification.
- The conclusion `∃ L : TX →ₗ[KX] TY, ∀ θ : TX,
  (L θ).val = d ≫ θ.val ≫ f` states both clauses: the identified composite
  belongs to TY (since `L θ : TY`) and the resulting function is KX-linear.
  After the displayed identification by d its underlying morphism is exactly
  `f ∘ θ`. No assertion of injectivity, surjectivity, finite dimension, or
  tangent/cotangent duality has been added.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.TangentVectorsVectorSpace`,
  `AlgebraicGeometry.exists_tangentVectors_vectorSpace`: full signature and
  construction docstring read; its final existential provides both structures.
- `Mathlib.AlgebraicGeometry.ResidueField`,
  `AlgebraicGeometry.Scheme.residueField`, `Scheme.Hom.residueFieldMap`, and
  `Scheme.fromSpecResidueField` (available through the tangent-space import).
- `Mathlib.Algebra.DualNumber`, `DualNumber`, an abbreviation for
  `TrivSqZeroExt R R`, and its reduction and inclusion maps.
- `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Spec` and `Spec.map`
  (available through the tangent-space import).
- `def-weil-pbc-scheme-conventions` introduces no independent declaration.
  Its scheme conventions are rendered by Mathlib's schemes and morphisms.
- Additional existing utility: `WeilConjectures.AlgebraicGeometry.DualNumbers`,
  `DualNumber.mapRingHom`, whose full definition was read. It maps coefficients
  by its argument homomorphism and supplies the dual-number identification.
  `Module.compHom` is Mathlib's existing restriction of scalars.

Source check: read `/home/ubuntu/c1-stacks-review/varieties.tex`,
`lemma-map-tangent-spaces` (Tag 0B2F). It states the natural linear map for a
morphism over a base with equal residue fields; the item is its S = Spec k
specialization without the separate cotangent-duality assertion. The module's
proof docstring records all three DAG proof steps, including residue-field
point naturality, scalar precomposition, and pushout uniqueness for addition.

Edge cases checked before writing: no finite-type, rational-point, smoothness,
or separability assumptions are imposed. General non-rational points and
nontrivial residue-field identifications are included. All field characteristics
are allowed. At Spec k the tangent space is zero. The identity gives the identity
map; on the affine line at zero, t ↦ t² gives the zero differential, including
characteristic two, and t ↦ a t gives scalar multiplication, including a = 0.
An empty source has no point x, as in the node, so the theorem is vacuous there.
The arbitrary universe u does not bound residue extensions or tangent dimension.

Searches for an existing statement:

- `msearch.py ... leanfinder "composition with a scheme morphism is linear on
  dual number tangent vectors"`: eight hits about cotangent maps and Kähler
  differentials; none states the dual-number scheme-tangent result.
- `msearch.py ... loogle "AlgebraicGeometry.Scheme, DualNumber, LinearMap"`:
  zero hits.
- `msearch.py ... grep "tangent|Tangent" AlgebraicGeometry`: nine hits, all
  elliptic-curve geometry, cotangent imports, or formal-unramified facts.
- `rg` on the source project's AlgebraicGeometry directory and this project's
  `lean/Sheaf/AlgebraicGeometry`: found general dual-number constructions and
  group-scheme Lie theory in the source; found the vector-space dependency
  here, but no scheme tangent-map linearity statement.
- `grep -rn "lem-sc-tangent-map-linear"` on the whole source `WeilConjectures`:
  no hit. Searches for `exists_tangentMap_linear` in Mathlib, the whole source,
  `lean/Sheaf`, and `dag/lean_names_upstream.json` found no declaration collision.

Server compile: `scompile.py C1 lem-sc-tangent-map-linear` on the module passed
in 2.9 seconds, exit code zero, with no errors or warnings.
- `msearch.py ... leansearch "a morphism of schemes induces a linear map on
  dual number tangent vectors"`: unavailable (Internal Server Error); the
  other searches above completed.

## Second reading by C1

Independent second reading of the sandbox node and TangentMapLinear.lean against
Stacks varieties.tex, section Tangent spaces, lemma-map-tangent-spaces (0B2F),
and the preceding diagram and lemma-tangent-space (0B2B). The section assumes
arbitrary schemes over a base, not varieties, finite-type schemes, or smooth
schemes. This node deliberately takes S = Spec k and only the natural linear
map clause of 0B2F; the cotangent-duality clause is not part of this node.

Object, hypothesis, and conclusion checklist (all verdicts: exact):

- A field k: `(k : Type u) [Field k]`; no characteristic restriction.
- Schemes X and Y over k: `(X Y : Scheme.{u})`, `pX` and `pY` with codomain
  `Spec (.of k)`. Explicit structure maps are appropriate here because both
  schemes and their morphism are involved, and the dependency takes one.
- A morphism of k-schemes f: `(f : X ⟶ Y)` and `hf : f ≫ pY = pX`.
  This is the over-base commutative triangle, not an extra hypothesis.
- A point x and its image y: `(x : X)` and `f x` throughout the target data.
  There is no extra independent y or equality hypothesis.
- The induced residue-field isomorphism: `he : Function.Bijective
  (f.residueFieldMap x).hom`; `e : KY ≃+* KX` is made from that very map,
  rather than an arbitrary field equivalence. Bijectivity is exactly the
  isomorphism condition for this ring homomorphism between fields.
- Residue fields and dual numbers: `KX := X.residueField x`,
  `KY := Y.residueField (f x)`, `DX` and `DY` are their dual-number spectra.
  Read Mathlib Scheme.residueField (the stalk modulo its maximal ideal),
  Hom.residueFieldMap (induced by the stalk map), DualNumber (TrivSqZeroExt
  R R), Spec, Spec.map, and fromSpecResidueField. They render the dependency
  nodes def-weil-residue-field, def-sc-dual-numbers, and
  def-weil-affine-spectrum exactly. The scheme-conventions dependency fixes
  no separate notion and imposes no geometric hypothesis here.
- Tangent vectors at x and y: `TX` and `TY` are the exact subtypes appearing
  in exists_tangentVectors_vectorSpace. `cX ≫ θ = bX` and its Y counterpart
  require the canonical residue-field point, not merely the same topological
  point. `θ ≫ pX = qX ≫ bX ≫ pX` and its Y counterpart require being over k
  with the canonical structure on the dual-number spectrum. Augmentation
  gives c from Spec K to Spec K[epsilon]; constants give q in the reverse
  direction. Both directions agree with the Stacks diagram.
- The vector-space structures given by lem-sc-tangent-space-vector-space:
  `hX` and `hY` select its final conjunct, then Classical.choose selects the
  additive group and module witnesses. I opened the dependency's whole
  signature and proof docstring: its choose specifications fix zero as the
  constant map, addition by pushout gluing followed by the sum map, and
  scalar multiplication by the epsilon-scaling map. Thus these structures
  are the specified canonical operations, not arbitrary structures on Hom.
  The local lets only expose definitionally identical dependency types.
- Identify the target scalars through the induced map KY -> KX:
  `Module.compHom TY e.symm.toRingHom` gives the KX-action lambda acting
  natively as e.symm(lambda). This is the required scalar transport.
- Identify the source spectra: `d : DY ⟶ DX` is Spec of
  `DualNumber.mapRingHom e.symm.toRingHom`. I read its upstream definition:
  both coefficients are mapped through e.symm and epsilon is preserved.
  Contravariance makes DY -> DX the correct direction. The underlying
  composite is therefore exactly f after theta under the field identification.
- Every image is a tangent vector at y: `L θ : TY` supplies both defining
  conditions, and `(L θ).val = d ≫ θ.val ≫ f` identifies that element with
  the required composite for every θ, in the same quantifier order.
- The composite function is KX-linear: `∃ L : TX →ₗ[KX] TY` together with
  that pointwise equality gives precisely linearity of this function.
  It adds no injectivity, surjectivity, or dimension assertion.

Edge cases: empty X admits no x and hence gives a vacuous statement; empty Y
likewise supplies no f from a pointed X. Zero tangent spaces, including Spec k
at its point, are included. No index set, n, or finite-dimensionality parameter
is introduced. Zero scalar, characteristic two and positive characteristic are
included by Module over an arbitrary field. Non-rational points and arbitrary
residue-field isomorphisms are covered; no separability is assumed. One arbitrary
universe u is shared with the dependency and Mathlib's scheme category; it can
be chosen large enough for all the schemes and the base field, without a
finiteness or cardinality restriction. Every variable and universe is bound.

Independent searches using different phrasing from the first worker:

- LeanFinder: "differential of a map of schemes preserves addition and scalar
  multiplication of infinitesimal points": eight hits, concerning presheaf
  derivations, Kähler-differential maps, and formally unramified morphisms;
  none is this scheme dual-number tangent-vector statement.
- Loogle: "DualNumber, AlgebraicGeometry.Scheme.Hom": zero hits.
- LeanSearch: "the differential of a scheme morphism is a linear function on
  infinitesimal points": unavailable, Internal Server Error; no match verdict
  is inferred from the service failure.
- rg for tangentMap, tangent_map, differential, and infinitesimal in Mathlib
  AlgebraicGeometry, upstream AlgebraicGeometry, and lean/Sheaf, plus the
  declaration name in the whole upstream project and lean_names_upstream.json.
  Opened upstream TangentSpace.lean: its declarations concern tangent sheaves
  and tangent sheaves along sections, not this pointwise tangent map. Opened
  GroupScheme/Lie.lean infPointsMap and differential: they require GrpObj and
  IsMonHom and concern the identity section, so are genuine special cases
  and cannot serve this general morphism at an arbitrary point. The project's
  TangentVectorsVectorSpace is the dependency used here; no existing general
  tangent-map linearity declaration or name collision was found.

No new nodes, dependency modules, or statement_change record are present or
needed. The imports are used, the sole theorem proof is sorry, there are no
hollow definitions, and the module and declaration docstrings cite 0B2F and
this blueprint node. The proof docstring carries all three node steps:
residue-field point naturality and the over-k triangle, scalar-precomposition
compatibility, and pushout uniqueness for addition. No mathematical mismatch
was found, and no Lean or node text was changed. Added this second-reading
record only, preserving the Worker report.

Validation: scompile.py C1 lem-sc-tangent-map-linear on
lean/Sheaf/AlgebraicGeometry/TangentMapLinear.lean completed in 2.8 seconds,
exit code 0, without errors or warnings. Checked lean.statement against the
file signature verbatim, and checked line lengths and explicit binders.
