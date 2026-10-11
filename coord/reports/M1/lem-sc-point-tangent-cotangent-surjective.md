## Worker report

The module `Sheaf.AlgebraicGeometry.CotangentSurjectiveOfTangentInjective` states
`AlgebraicGeometry.cotangent_surjective_of_tangent_injective`, with only a `sorry` proof.
No definitions, auxiliary axioms, new nodes, dependency replacements, or statement
corrections are introduced.

Hypothesis and clause correspondence:

- The field is `(k : Type u) [Field k]`; the two schemes are `(X Y : Scheme.{u})`.
- Schemes over k are given by `pX : X ⟶ Spec (.of k)` and `pY : Y ⟶ Spec (.of k)`.
  Explicit maps are needed by the recorded tangent-space API. The morphism is `f : X ⟶ Y`,
  and `hf : f ≫ pY = pX` says it is over k.
- Locally of finite type is `[LocallyOfFiniteType f]`. No finite-type assumption on either
  structure morphism is added.
- The source point is `(x : X)`; the target point y is written `f x` throughout.
- Closedness is `hx : IsClosed ({x} : Set X)` and `hy : IsClosed ({f x} : Set Y)`.
- Residue fields equal to k means their canonical maps from k are isomorphisms, not merely
  abstract field isomorphisms. This is `hκx : Function.Bijective (pX.residueFieldMap x).hom`
  and `hκy : Function.Bijective (pY.residueFieldMap (f x)).hom`: the residue field of the
  unique point of Spec k is canonically k. These bijections are precisely rationality.
- Differential injectivity is `hdf : ∃ he : Function.Bijective (f.residueFieldMap x).hom,
  Function.Injective (schemeTangentMap k X Y pX pY f hf x he)`.
  The existential packages the proof argument required by the dependency's API; it adds
  no restriction. Indeed the composite of the base residue map at y and the residue map
  of f is the base residue map at x (up to the equality induced by hf). Both base maps
  are bijective, so the map of f is bijective. Proof irrelevance makes the differential
  independent of which proof he is supplied.
- Cotangent surjectivity is stated via representatives:
  `∀ a : IsLocalRing.maximalIdeal (X.presheaf.stalk x),
  ∃ b : IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x)),
  (f.stalkMap x).hom b - (a : X.presheaf.stalk x) ∈
  (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) ^ 2`.
  The stalk map is a local ring homomorphism, hence sends m_y into m_x and m_y² into m_x².
  Consequently it induces the quotient map in the node. Every class in m_x/m_x² has a
  representative a, and a class from m_y/m_y² maps to it exactly when the displayed
  difference lies in m_x². This is exactly surjectivity of the induced map, with no
  strengthening to surjectivity of the stalk map or of the maximal-ideal map. It uses
  the existing Mathlib ideals, ring powers, and membership rather than introducing a
  duplicate cotangent-map definition. Scalar linearity is automatic for this induced
  map at the rational points; no extra linear map is supplied as input.

Dependencies read and used:

- `def-sc-scheme-tangent-space`: module `Sheaf.AlgebraicGeometry.SchemeTangentSpace`,
  `AlgebraicGeometry.schemeTangentSpace` and the canonical instances
  `schemeTangentSpaceAddCommGroup`, `schemeTangentSpaceModule`, and `schemeTangentMap`.
  The complete signatures and docstrings were read. In particular the differential is
  the chosen linear map with the postcomposition formula, not an arbitrary function.
- `def-weil-pbc-scheme-conventions` has a convention record, deliberately with no
  declaration or module; it collects the standard Mathlib meanings. We use
  `AlgebraicGeometry.Scheme`, `Scheme.Hom.stalkMap`, `Scheme.Hom.residueFieldMap`, and
  `AlgebraicGeometry.LocallyOfFiniteType` (module
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`). The full locally-finite-type
  definition and the residue/stalk map signatures were read in Mathlib.

The statement docstring carries both DAG proof steps: the functorial rational-point
identification from `lem-sc-rational-tangent-cotangent-duality`, followed by the dual
linear-map implication `lem-sc-dual-map-injective-iff-surjective`. The final representative
form follows from the definition of a quotient. Both proof dependencies are future proof
inputs, not new hypotheses or duplicated definitions.

Sources: the local Stacks checkout is absent on this machine. Read the primary source
online at https://stacks.math.columbia.edu/tag/0B2E and
https://stacks.math.columbia.edu/tag/0B2F. Tag 0B2E gives the rational-point cotangent dual;
Tag 0B2F identifies the differential with the dual induced map. No source discrepancy was
found. Closedness and locally finite type are retained even though the duality implication
does not need them.

Edge cases checked before writing: the empty scheme has no x and produces no instance;
Spec k at its unique point has zero maximal ideal and zero tangent space, so the conclusion
holds with b=0; identity maps give the identity on both spaces; t ↦ t² at zero on A¹ has
zero differential and zero cotangent map, so its injectivity hypothesis fails in every
characteristic. Singular rational points are admitted. There is no smoothness, Noetherian,
finite-dimensional, characteristic, or algebraic-closure assumption. Universe u is explicit
and arbitrary; the same arbitrary universe as the dependency covers the schemes and base
field without a cardinality bound. Every variable is bound explicitly.

Searches for an existing statement:

- `msearch.py leanfinder`, query "injective tangent map of schemes at rational points
  implies surjective map on cotangent spaces": eight hits, on formally smooth algebra,
  algebra-extension cotangent maps and formally unramified schemes; none is this statement.
- `msearch.py loogle`, query "Ideal.Cotangent, IsLocalRing": four cotangent span/range and
  quotient-map identities; none is the injective-differential implication.
- `msearch.py leansearch`, query "injective differential tangent spaces schemes rational
  point cotangent surjective": HTTP Internal Server Error; unavailable, no absence claim.
- `msearch.py grep`, query "tangent.*inject|cotangent.*surject|schemeTangentMap", directory
  AlgebraicGeometry: one hit using Ideal.toCotangent_surjective in FormallyUnramified,
  not the desired theorem.
- Direct rg of cotangent/tangent/injectivity in Mathlib, WeilConjectures, and lean/Sheaf:
  Mathlib gives Ideal.Cotangent, IsLocalRing.CotangentSpace and quotient identities;
  WeilConjectures gives dual-number/cotangent correspondences and an unrelated Lie-algebra
  injectivity theorem; lean/Sheaf gives the recorded tangent API and the distinct finite
  local-ring lemma SurjectiveOfFiniteOfCotangent. None duplicates this implication.
- Direct rg for the item id in WeilConjectures: no hits. Direct rg for
  cotangent_surjective_of_tangent_injective in Mathlib/source/project name records: no
  existing declaration. No statement faults or STATEMENT-DISPUTED issues were found.

Validation: server single-file compilation succeeded in 1.7 seconds with exit code 0 and
no warnings. Delivery dry run is the final mechanical check; the independent second reader
will add their own reading and deliver.

## Second reading by M1

Independently read the item node and delivered file, both statement dependencies and
`SchemeTangentSpace.lean`, and the underlying `exists_tangentMap_linear` signature and
postcomposition specification. No mismatch was found; the Lean and node are unchanged.
The only addition is this independent review.

Object/hypothesis/conclusion checklist (each verdict: exact):

- Ground field k: `(k : Type u) [Field k]`; schemes X,Y: `(X Y : Scheme.{u})`.
- Schemes over k: `pX : X ⟶ Spec (.of k)` and `pY : Y ⟶ Spec (.of k)`.
  The explicit maps are the parameters of the recorded tangent-space dependency.
- Morphism f over k: `(f : X ⟶ Y)` and `hf : f ≫ pY = pX`.
- Locally finite type f: `[LocallyOfFiniteType f]`. Its Mathlib definition at
  Morphisms/FiniteType.lean:43 is affine-local finite generation, not global finite type.
  No condition is imposed on the structure maps beyond the node's being over k.
- Point x and y=f(x): `(x : X)` and `f x` in every target stalk, residue field and tangent
  space. Eliminating y using its defining equality changes no quantifier.
- Closedness of both points: `hx : IsClosed ({x} : Set X)` and
  `hy : IsClosed ({f x} : Set Y)`.
- Residue fields equal to k: `hκx` and `hκy` assert bijectivity of the canonical base
  residue maps. This means equality as extensions of k, as in the source, rather than
  merely an abstract isomorphism of fields. The residue field at any point of Spec k
  is canonically k.
- Injective induced differential: `hdf` asserts injectivity of the recorded
  `schemeTangentMap k X Y pX pY f hf x he`. Its dependency constructs the linear map
  with value `d ≫ θ.val ≫ f`, where d transports dual numbers by the inverse residue
  isomorphism. It is not a freely supplied linear map. The existential he is redundant:
  `Scheme.Hom.residueFieldMap_comp`, `hf`, and the residue-field congruence identify
  the composite of the bijective base residue map at y and f's residue map with the
  bijective base residue map at x. Thus f's residue map is bijective; proof irrelevance
  makes its choice of he immaterial. No extra mathematical hypothesis is present.
- Surjectivity of the induced m_y/m_y² to m_x/m_x² map: the conclusion is
  `∀ a : maximalIdeal (X.presheaf.stalk x), ∃ b : maximalIdeal
  (Y.presheaf.stalk (f x)), (f.stalkMap x).hom b - ↑a ∈ maximalIdeal (...) ^ 2`.
  The stalk map is local and sends m_y into m_x, hence also squares into squares.
  `Ideal.toCotangent_surjective` and `Ideal.toCotangent_eq` (Cotangent.lean:65,72)
  show that representatives give exactly the quotient surjectivity condition. There
  is no assertion that the stalk map, or its restriction to maximal ideals, is surjective.
  The order is arbitrary target representative a, then source representative b.

Source reading: the local Stacks .tex is absent. Read the primary varieties.tex at
https://raw.githubusercontent.com/stacks/stacks-project/master/varieties.tex,
section-tangent-spaces, lemma-tangent-space-rational-point and lemma-map-tangent-spaces,
with the chapter notation (k is the ground field); also checked
https://stacks.math.columbia.edu/tag/0B2E and https://stacks.math.columbia.edu/tag/0B2F.
The rational-point identification specializes to m/m² over Spec k; the differential
is the dual induced map. These lemmas impose no ambient Noetherian, separated,
smoothness or finite-dimensional hypothesis. The node's closedness and locally-finite-type
hypotheses are retained exactly, even though the implication works without them.
The convention dependency fixes no additional object or declaration; its named Mathlib
scheme notions and the stalk/residue signatures were opened and checked.

Edge cases: empty X admits no x, so is vacuous. For X=Spec k, the target cotangent
space is zero and b=0 supplies the conclusion. The identity gives the identity maps.
For t ↦ t² at the origin of A¹, df is zero on a nonzero space in every characteristic,
so the injectivity hypothesis fails as expected. Singular points and non-Noetherian
schemes remain allowed. No index set or natural-number parameter occurs (including no
n>0 restriction). u is explicitly bound and arbitrary, with the same universe convention
as the recorded Scheme/tangent API; objects in different size universes can be placed
in a common larger universe. There are no implicit free variables or hidden finiteness
instances.

Independent searches, using different phrasing from the worker:

- msearch leanfinder: "Zariski tangent differential injectivity cotangent quotient maximal
  ideal surjection": eight results about algebra extension cotangents and formally smooth
  presentations, none the scheme differential implication.
- msearch loogle: "LinearMap.dualMap, Function.Injective": six hits including
  `LinearMap.dualMap_injective_iff`. This is the node's existing linear-algebra proof
  dependency, not the present theorem about schemes.
- msearch leansearch: "Zariski tangent space injective differential induces surjective
  maximal ideal quotient map": service returned Internal Server Error; no absence verdict.
- Direct rg for tangent/cotangent and injectivity/surjectivity in Mathlib AlgebraicGeometry,
  the full WeilConjectures tree and lean/Sheaf: no duplicate theorem. Opened upstream
  `tangentSpaceAt` (Picard/Jacobian.lean:701), which uses a chosen rational morphism;
  its available vector-space structure is for a group-scheme unit, not this differential.
  Opened `RingHom.surjective_of_finite_of_cotangent` in the project: it takes cotangent
  surjectivity as a hypothesis and concludes ring surjectivity, so does not serve this item.
  Mathlib's `Ideal.Cotangent`, `IsLocalRing.CotangentSpace`, and `Ideal.mapCotangent`
  already provide the quotient notions. The delivery creates none of these again.
- rg of the full declaration name and item id in upstream names and WeilConjectures:
  no existing declaration. The recorded tangent-space dependency is used directly.

No new definition node, dependency replacement, or statement correction is present.
The single theorem has only `sorry`; there are no definitions to be hollow and nothing
is proved. Header, namespace, imports, line lengths, source/blueprint docstrings and
both DAG proof steps meet H5-H9. The node's lean.statement is verbatim the signature.

## Reviewer fix (R-ptc0929, stage 2)

The delivered conclusion (every `a` in m_x differs from some `f.stalkMap x b`, `b` in m_y, by an
element of m_x²) was exact, but named no cotangent space. Per the cotangent-space convention
(Mathlib `IsLocalRing.CotangentSpace` on the stalk), the conclusion is restated as
`Function.Surjective` of Mathlib's `Ideal.mapCotangent` from `IsLocalRing.CotangentSpace` of the
stalk at `f x` to that of the stalk at `x`, along `(f.stalkMap x).hom.toIntAlgHom`, with the
inclusion m_y ⊆ comap m_x from `IsLocalRing.map_maximalIdeal_le`. The two forms were checked
equivalent in Lean (both directions proved by `Ideal.toCotangent_surjective`,
`Ideal.mapCotangent_toCotangent`, `Ideal.toCotangent_eq`) before the fix. Import
`Mathlib.RingTheory.Ideal.Cotangent` added. Hypotheses unchanged.
