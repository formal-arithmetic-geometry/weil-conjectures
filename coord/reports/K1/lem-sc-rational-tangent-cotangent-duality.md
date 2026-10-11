## Worker report

The module `Sheaf.AlgebraicGeometry.RationalTangentCotangentDuality` states
`AlgebraicGeometry.rational_tangent_cotangent_duality`. Its only theorem has proof `sorry`;
there are no new definitions, dependency modules, or statement corrections.

Sources read: Stacks Tags 0B2E and 0B2F at https://stacks.math.columbia.edu/tag/0B2E
and https://stacks.math.columbia.edu/tag/0B2F. The local literature/stacks-project/varieties.tex
is absent on this machine, so the official Stacks pages supplied the source statements.
Tag 0B2E specializes to the asserted maximal-ideal quotient because the base is Spec k
and its maximal ideal is zero. Tag 0B2F supplies functoriality; the node's explicit
proof computes this using the dual-number definition of Tag 0B2C.

Hypothesis and clause correspondence:

- The field is `(k : Type u) [Field k]`; `X Y : Scheme.{u}` are arbitrary schemes.
  Their maps `pX pY` to `Spec (.of k)` give their k-scheme structures.
  The named morphism `f : X ⟶ Y` and `hf : f ≫ pY = pX` say precisely that f is over k.
  No separatedness, finite type, Noetherian, smoothness, or dimension assumption is imposed.
- The point is `x : X` and y is written `f x`, so there is no independent point with
  an omitted equality. `RX`, `RY` are the two stalks, and `mX`, `mY` their maximal ideals.
- Rationality κ(x)=κ(y)=k is written as ring equivalences `eX : k ≃+* X.residueField x`
  and `eY : k ≃+* Y.residueField (f x)` respecting the base structure. `hX` and `hY`
  say that the k-valued point obtained by the inverse equivalence composes with the
  base map to the identity of Spec k. This encodes identification by the structure
  embedding, rather than abstract isomorphism of fields. The identifications exist
  exactly for rational points; they add no restriction beyond the node's rationality.
- `TX` and `TY` are the recorded `schemeTangentSpace` at those points. Their canonical
  residue-field module structures are restricted to k by `Module.compHom` along `eX`,
  `eY`. The same restriction on `IsLocalRing.CotangentSpace` supplies k-vector spaces
  for the maximal ideals modulo squares. The explicit `show` annotations expose the
  definitional equality between scheme residue fields and local-ring residue fields;
  they do not introduce a new scalar structure.
- `EX : TX ≃ₗ[k] Module.Dual k ...` and `EY : TY ≃ₗ[k] Module.Dual k ...` are the two
  k-linear isomorphisms. They are specified canonically, not arbitrary existential
  isomorphisms: for every vector θ there is a local-ring map φ representing it via
  `θ.val = Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk x` (and likewise Y).
  Its first coefficient is the residue of each a. Its epsilon coefficient on each
  maximal-ideal element a equals `EX θ (mX.toCotangent a)` after `eX.symm` (likewise EY).
  Thus the formula is precisely θ ↦ ℓθ, ℓθ(a mod m²)=Dθ(a). These representatives
  determine the linear forms, since `Ideal.toCotangent_surjective` is surjective.
  The factorization determines φ: `fromSpecStalk` is a preimmersion and hence mono,
  and the affine spectrum functor is faithful. The closed-point condition on θ forces
  φ to be local. No unanchored choice of canonical isomorphisms is being asserted.
- `U : CotangentSpace RY →ₗ[k] CotangentSpace RX` is the stalk-induced cotangent map,
  characterized by the formula on each b in mY. The existential `hb` says its image
  under `(f.stalkMap x).hom` belongs to mX, and the formula sends the quotient class
  of b to the quotient class of that image. It specifies exactly the induced map,
  without adding a new definition of cotangent spaces or maps.
- The conclusion first supplies `he : Function.Bijective (f.residueFieldMap x).hom`.
  This is a consequence of the two rational-point identifications, not an additional
  hypothesis. It is the certificate required by the recorded `schemeTangentMap`.
  The final formula, for every θ, is
  `EY (schemeTangentMap k X Y pX pY f hf x he θ) = (EX θ).comp U`.
  Precomposition with U is its dual map, so this is exactly the final naturality clause.

Dependency declarations read and used:

- `def-weil-pbc-scheme-conventions` is explicitly a convention-only record with no
  declaration or module. It collects Mathlib's `AlgebraicGeometry.Scheme` and morphism
  notions. This item uses schemes and their maps, not any extra scheme property.
- `def-sc-scheme-tangent-space`: `Sheaf.AlgebraicGeometry.SchemeTangentSpace`, full
  signatures and docstrings of `AlgebraicGeometry.schemeTangentSpace`,
  `schemeTangentSpaceAddCommGroup`, `schemeTangentSpaceModule`, `schemeTangentMap` read.
  The map's source `Sheaf.AlgebraicGeometry.TangentMapLinear` was also read to check
  its postcomposition formula and transported target residue-field scalar action.
- Mathlib.RingTheory.Ideal.Cotangent: `Ideal.Cotangent`, `Ideal.toCotangent`,
  `IsLocalRing.CotangentSpace` and its residue-field module instance. The canonical
  quotient is used directly. `Ideal.mapCotangent` was inspected, but needs algebra
  structures on the stalks; the conclusion specifies the same map on representatives
  and therefore does not construct or duplicate it.
- Mathlib.LinearAlgebra.Dual.Defs: `Module.Dual`.
- Mathlib.AlgebraicGeometry.ResidueField and Stalk (transitive imports): `Scheme.residueField`,
  `Scheme.Hom.residueFieldMap`, `Scheme.fromSpecResidueField`, `Scheme.fromSpecStalk`,
  `Scheme.Hom.stalkMap`. These give the actual scheme-local-ring and residue-field objects.

Edge cases checked before drafting: Spec k has zero tangent/cotangent spaces, so both
linear equivalences and the naturality formula are the unique zero-space ones. On A¹
at zero, t ↦ c epsilon corresponds to the functional [t] ↦ c. For t ↦ t² at zero,
the stalk-induced cotangent map and tangent differential are zero, including characteristic
2; there is no restriction on characteristic. An empty scheme has no point x and imposes
no case to prove. No Noetherian or finite-dimensional hypothesis is needed, since the
full algebraic dual is used. A common arbitrary universe u accommodates the field and
both schemes after universe enlargement, rather than imposing countability or dimension.

Searches actually run:

- msearch.py leansearch, query `tangent space scheme rational point dual cotangent maximal ideal naturality`:
  unavailable (Internal Server Error); no absence conclusion drawn.
- msearch.py leanfinder, same query: eight hits on algebra-extension cotangent maps and
  localization; none identifies dual-number scheme tangent spaces or states this naturality.
- msearch.py loogle, query `IsLocalRing.CotangentSpace`: twelve hits, including the
  quotient and its module structure, none states the scheme-level duality.
- msearch.py grep, query `tangentSpace|TangentSpace|CotangentSpace`, subdirectory
  `AlgebraicGeometry`: zero hits.
- Direct rg of the project's lean/Sheaf and source WeilConjectures for rational tangents,
  tangent/cotangent and schemeTangent: only the landed tangent-space definitions,
  source tangent sheaves, and separate cotangent algebra APIs. Source
  WeilConjectures/AlgebraicGeometry/TangentSpace.lean inspected: its blueprint discussion
  mentions the tangent space, but no matching pointwise dual-number declaration exists.
- Direct grep of the item id in source WeilConjectures: no hits.
- `python3 tools/lean_names_upstream.py show lem-sc-rational-tangent-cotangent-duality`:
  no declaration for this item (only index summary).
- Direct rg of candidate declaration name `rational_tangent_cotangent_duality` in source,
  project Lean and dag/lean_names_upstream.json: no match before drafting.

The module docstring includes the source and node id; the theorem docstring carries
all proof steps and their cited nodes. All binders and universe u are explicit.
Server compile succeeded without warnings (2.2 seconds). The statement of the DAG
node is unchanged; no STATEMENT-DISPUTED or node fault was found.

## Second reading by K1

Independent reading of the sandbox node and module, the two statement dependencies,
`SchemeTangentSpace.lean`, `TangentMapLinear.lean`, and Mathlib's stalk, residue-field,
and ideal-cotangent declarations. Verdict: the Lean states exactly the node, including
canonicality and naturality. No mathematical or signature repair was needed.

Source checked independently: downloaded the official Stacks `varieties.tex` to the
sandbox as `varieties-source.tex` and read Section `section-tangent-spaces`, the diagram
`equation-tangent-space`, `definition-tangent-space` (0B2C),
`lemma-tangent-space-rational-point` (0B2E), and `lemma-map-tangent-spaces` (0B2F).
Also read the official tag pages:
https://stacks.math.columbia.edu/tag/0B2C,
https://stacks.math.columbia.edu/tag/0B2E,
https://stacks.math.columbia.edu/tag/0B2F.
The section assumes only a scheme morphism and a point; there is no standing finite-type,
Noetherian, smoothness, or separatedness condition. At base `Spec k`, the base maximal
ideal is zero, so 0B2E gives exactly m/m². The additional separable algebraic generality
in 0B2E is not part of this node. 0B2F gives naturality with the differential cotangent
space; the explicit dual-number computation identifies this with the m/m² map here.

Object/hypothesis/conclusion checklist (node first, Lean second):

1. A field k: `(k : Type u) [Field k]`. Exact; no algebraic-closure or characteristic
   instance is assumed.
2. Schemes X,Y over k: `(X Y : Scheme.{u})`, `(pX : X ⟶ Spec (.of k))`,
   `(pY : Y ⟶ Spec (.of k))`. Exact. Explicit structure maps are appropriate because
   the recorded tangent declaration takes these maps. The convention-only dependency
   `def-weil-pbc-scheme-conventions` adds no separate notion; its referenced scheme and
   morphism notions are Mathlib's.
3. A morphism of k-schemes: `(f : X ⟶ Y) (hf : f ≫ pY = pX)`. Exact commutative
   triangle; no extra property of f.
4. A point x and y=f(x): `(x : X)` and `f x` throughout. Exact; y is determined,
   not independently quantified.
5. Rationality of both points: `eX : k ≃+* X.residueField x`, and likewise `eY`, with
   `hX`, `hY` the identity triangles for the corresponding k-valued points. Exact.
   These equations force the identifications to invert the structure embeddings;
   an arbitrary abstract field isomorphism would not suffice. Conversely, rationality
   supplies these equivalences and triangles. They express the node's hypotheses,
   rather than adding a restriction. Naturality forces
   `(f.residueFieldMap x).hom (eY a) = eX a`.
6. The respective local rings and maximal ideals: `RX`, `RY` are presheaf stalks at
   x and f x, and `mX`, `mY` are `IsLocalRing.maximalIdeal`. Exact, using the actual
   local rings of the schemes.
7. Tangent spaces and differential as in the dependency: `TX`, `TY` abbreviate the
   recorded `schemeTangentSpace`; `schemeTangentMap k X Y pX pY f hf x he` is the
   recorded differential. Exact. Reading its body and `exists_tangentMap_linear`
   confirms postcomposition, with dual-number spectra transported along the inverse
   residue-field equivalence. The existential `he` is a consequence of rationality,
   not an extra assumption on f. The final application uses its underlying function;
   the transported target residue scalar instance does not alter the underlying TY.
8. Cotangent spaces m/m²: `IsLocalRing.CotangentSpace` unfolds to the maximal ideal's
   `Ideal.Cotangent`, the quotient by `m • ⊤`. Mathlib's
   `Ideal.map_toCotangent_ker` identifies the corresponding ideal with m². Exact.
   The `Module.compHom` instances restrict the canonical residue-field actions along
   eX,eY and impose no finiteness or algebra-structure hypothesis on the stalks.
9. Canonical k-linear isomorphisms: `EX`, `EY` are `≃ₗ[k] Module.Dual k ...`.
   Both clauses `∀ θ, ∃ φ, ...` identify the representing local ring homomorphism
   through `θ.val = Spec.map ... ≫ fromSpecStalk`, fix its first coefficient as residue,
   and identify the value on `[a]` with `e.symm (φ a).snd`. Exact canonical formula.
   This is stronger than uncharacterized isomorphism existence only in the sense
   required by the word canonical: `fromSpecStalk` is a preimmersion (hence mono),
   Spec is faithful, and `Ideal.toCotangent_surjective` fixes every functional by
   its values on representatives. The representatives are local automatically:
   their first-coefficient condition detects precisely the maximal ideal. No private
   tangent or cotangent definition has been introduced.
10. The induced k-linear cotangent map: existential `U` with
    `∀ b : mY, ∃ hb, U (mY.toCotangent b) = mX.toCotangent ⟨..., hb⟩`.
    Exact: `(f.stalkMap x).hom` has the required direction RY→RX and locality gives
    `hb`. Surjectivity of `toCotangent` uniquely specifies U. This characterizes the
    existing notion on representatives; it does not add a competing definition.
11. Differential is the dual of that map under those very isomorphisms:
    `∀ θ : TX, EY (schemeTangentMap ... θ) = (EX θ).comp U`. Exact, with the same
    EX,EY,U fixed before θ is quantified. Composition is precomposition of the
    functional with U, the full algebraic dual, without finite-dimensionality.

Edge cases: an empty X has no x, and a morphism from inhabited X to empty Y cannot
supply this data. At Spec k the maximal ideal and both vector spaces are zero and
all characterization clauses give the unique zero maps. Affine-line origin gives
[t]↦c for t↦c epsilon; t↦t² gives zero cotangent map and differential at zero in every
characteristic, including 2. No dimension parameter or index set occurs, so n=0 and
empty-index exclusions do not arise. Arbitrary universe u is explicitly bound, and
k,X,Y can be placed in a common universe; the signature matches the universe of the
recorded general tangent definition. Infinite-dimensional cotangent spaces use their
full linear dual. Checked by eye: every variable and universe in the signature is bound.

Independent searches, using different words from the worker:

- msearch leansearch: `scheme infinitesimal vectors identified with linear forms on
  local maximal ideal square quotient`. Service returned HTTP 500; recorded as
  unavailable, with no absence inference.
- msearch leanfinder: `dual number valued points linear dual local ring maximal ideal
  quotient differential`. Eight hits: `IsLocalRing.CotangentSpace`, algebra extensions,
  and square-zero derivation lifting; none states this general scheme duality/naturality.
- msearch loogle: `"Cotangent", "Dual"`. Zero hits.
- Direct rg: `cotangent.*[Dd]ual|[Dd]ual.*cotangent|tangent.*[Dd]eriv|[Dd]eriv.*tangent`
  over project `lean/Sheaf`, source `WeilConjectures`, and Mathlib's AlgebraicGeometry
  and RingTheory. Inspected the useful additional hit
  `WeilConjectures/Mathlib/RingTheory/Ideal/Cotangent.lean` in full through its inverse
  formulas: `AlgHom.cotangentForm` and `AlgHom.toDualNumber` concern a k-algebra
  augmentation's kernel. They are useful stage-3 tools but do not state the scheme
  theorem, its stalk cotangent modules, its canonical linear equivalences, or naturality
  for an arbitrary scheme morphism. Source tangent sheaves and group-specific Lie
  declarations also do not match. No duplicate declaration was found.

H5/H6/H8/H9: there are no new definitions, new nodes, dependency modules, or statement
corrections to audit. Only one theorem, with `sorry` proof. Module and theorem docstrings
name the source and blueprint id; the theorem docstring includes both node proof steps,
including the representing derivation and stalk-composition computation. Imports serve
respectively the tangent dependency, the ideal quotient, and its linear dual. Header,
namespace and line lengths satisfy the conventions. The recorded `lean.statement` was
checked verbatim against the signature. Second reading changed only this report: no
mismatch found, and correct Lean was left intact.

Independent server compilation via scompile.py completed cleanly. Delivery dry run and
preflight are required before pushing this independently reviewed statement.

## Reviewer fix (R-rtc0938)

The delivered statement encoded rationality by abstract ring equivalences `eX`, `eY`
with Spec-level identity triangles `hX`, `hY`, and characterized the equivalences by a
`fromSpecStalk` factorization. Mathematically equivalent, but a second form of notions
already fixed by the landed lem-sc-rational-point-tangent-derivation-identification
(H1, ac1abbc78, `exists_rationalPoint_tangent_cotangent_linearEquiv`), whose clause (c)
is the per-point half of this node (H4/H12: one form per notion). The fix restates in
H1's exact forms: `rX`, `rY` = `toStalk k (p _) ≫ p.stalkMap _ ≫ residue _`, rationality
`Function.Bijective rX → Function.Bijective rY`, k-structures by `Module.compHom` along
`rX`, `rY`, duals as `CotangentSpace →ₗ[k] k`, and `EX`, `EY` characterized verbatim as
H1's `e` (closed-point equation, `stalkClosedPointTo` sharp map, unique `D`), so they are
H1's equivalences at `x` and at `f x`. The cotangent map `U` clause and the naturality
clause `EY (schemeTangentMap ... he θ) = (EX θ).comp U` are unchanged. This node is not
literally H1's clause (c) (it adds naturality), so it stays a new statement.
