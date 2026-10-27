## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicSpaceIntegralFiniteEtaleLocality`
states two equivalences, with `sorry` proofs only:
`AlgebraicGeometry.AlgebraicSpace.isRepresentableWith_integral_iff_etaleAtlas`
and `AlgebraicGeometry.AlgebraicSpace.isRepresentableWith_finite_iff_etaleAtlas`.
No definitions, new nodes, dependency repairs, or statement corrections are needed.
The item node changes only in `lean`.

Source read: `literature/stacks-project/spaces-morphisms.tex`,
`lemma-integral-local` (Tag 03ZQ), lines 9150–9205, including the proof and the
preceding definition. This is equivalence (1) and (3), for a prescribed atlas;
the proof works for every such atlas, rather than merely some atlas.

Hypotheses and clauses, for EACH of the two declarations:

- “S a scheme” is `{S : Scheme.{u}}`; `universe u` is explicit and all test
  schemes and rings use the universe of the recorded algebraic-space framework.
- “Y and X algebraic spaces over S; f:Y→X” is
  `(Y X : AlgebraicSpace S) (f : Y ⟶ X)`. These are the recorded full
  subcategory of fppf sheaves and its natural-transformation morphisms.
- The choice P=integral is `IsIntegralHom`; the choice P=finite is `IsFinite`.
  They are separate theorems, so no new property or auxiliary type is introduced.
- “Representable with P on every scheme T→X” is
  `IsRepresentableWith (fun _ _ r ↦ IsIntegralHom r.left) f.hom.hom`,
  respectively the same expression with `IsFinite`. I read its full definition:
  it quantifies over every `T : Over S` and every `yoneda.obj T ⟶ X.obj.obj`,
  and gives a scheme representing the fibre product with a projection having P.
- “Every representable surjective étale map p:U→X from a scheme U” is
  `(U : Over S) (p : yoneda.obj U ⟶ X.obj.obj)` with `(he : IsEtale p)`
  and `(hs : IsSurjective p)`. Both recorded predicates include scheme-test
  representability, so a separate representability assumption is unnecessary.
- “If and only if” is `↔`. Its right side is
  `∃ (W : Over S) (r : W ⟶ U) (q : yoneda.obj W ⟶ Y.obj.obj),
    IsPullback q (yoneda.map r) f.hom.hom p ∧ IsIntegralHom r.left`
  (and `IsFinite r.left` in the second declaration).
  `IsPullback` supplies the universal property, not just commutativity:
  h_W represents Y×_X U, with r its projection to U. Being representable
  by W is exactly “the sheaf fibre product is a scheme”; no presentation
  is fixed or chosen in advance. Presheaf pullbacks compute sheaf pullbacks
  of sheaves; the dependency's fibre-product theorem uses the same convention.
- No quasi-compactness, separatedness, finite-type, or Noetherian condition
  occurs on S, X, Y, U, or p. The two conclusions impose just P on r.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom` (local-affine locally ringed spaces and their maps).
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  and its `IsRepresentableWith`, `IsEtale`, `IsSurjective`. The latter three
  take natural transformations of the underlying presheaves, hence `f.hom.hom`.
- `def-weil-size-convention` is explicitly a metatheoretic convention;
  its record supplies no definition or module. The declarations use explicit u.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`,
  also publicly exposing `IsIntegralHom` from `Morphisms.Integral`; both
  classes extend `IsAffineHom` and assert the ring-map property on affine opens.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`, and
  `etale_fibreProduct_isScheme`. Read signatures/docstrings; import is public
  as a recorded statement dependency. The universal-property representation
  in our right sides avoids making a noncanonical choice of a scheme atlas.

The stated proof dependencies are imported as proof imports: scheme integral
and finite base-change stability is in `Morphisms.Finite` (including Integral);
finite/radicial base-change's remaining scheme property is in
`Morphisms.UniversallyInjective`; fpqc conversion is
`Scheme.fpqcCover_of_smallEtaleCover` in `Sheaf.AlgebraicGeometry.FpqcFinerThanEtale`;
integral descent is `AlgebraicGeometry.isIntegralHom_of_fpqcPrecoverage_pullback`
in `Sheaf.AlgebraicGeometry.Morphisms.FpqcIntegralDescent`; finite descent is
`AlgebraicGeometry.isFinite_of_fpqc_cover` in
`WeilConjectures.AlgebraicGeometry.IsFiniteOfFpqcCover` (upstream preferred).
The proof dependency `lem-sfb-space-affine-locality` has no Lean record or
Mathlib match in the read repository; no import is available. It is needed
only for the postponed proof, not to type either signature, and its ID and
use are retained in both proof docstrings. No prerequisite is assumed as an
extra hypothesis. The node's full five-step proof is in each theorem docstring.

Edge cases checked before drafting:

- Empty X and empty atlas: surjectivity forces the appropriate empty targets;
  scheme tests and the representing empty scheme give the same conditions.
- Identity atlas for a schematic X: the right side is precisely the test
  of the map on X, and both equivalences are the expected scheme property.
- Non-quasi-compact disjoint-union atlas: permitted; no finiteness restriction
  on U or p is present. Singleton étale coverings are fpqc in the recorded sense.
- Integral but not finite maps: the two conclusions remain separate; no
  finite-type assumption is imposed in the integral case.
- Arbitrary nonseparated and non-Noetherian base: nothing in either signature
  excludes it. Test schemes use the same u as S, as in the dependency API.

Searches actually run (logs in `searches.jsonl`):

- LeanFinder via msearch: “A morphism of algebraic spaces is representable
  integral or finite if and only if its pullback to an etale surjective scheme
  atlas is integral or finite”. Eight scheme-level hits (integral base-change
  projections, finite implies integral, etc.); no algebraic-space locality result.
- Loogle via msearch: `"IsIntegralHom", "IsFinite"`. Two hits:
  `IsFinite.instIsIntegralHom` and `IsFinite.iff_isIntegralHom_and_locallyOfFiniteType`;
  neither says this equivalence.
- Mathlib grep via msearch: `IsRepresentableWith|AlgebraicSpace|integral.*[Ee]tale`
  in AlgebraicGeometry: zero hits.
- LeanSearch via msearch: “integral finite algebraic space morphism etale local
  on target”. Eight hits, all scheme or ring notions, not the statement.
- Direct rg in both `lean/WeilConjectures` and `lean/Sheaf` for integral/finite
  locality, `IsRepresentableWith` applied to these properties, and candidate
  theorem names. The relative-Spec correspondence uses these predicates but
  states an algebra equivalence, not étale atlas locality. Integral/finite
  limit and finite-map modules are also different statements. The framework's
  general `IsRepresentableWith` is reused, not copied.
- Exact node-ID grep in `lean/WeilConjectures`: no existing declaration.

No STATEMENT-DISPUTED issue or node fault was found. Both declarations compiled
cleanly with the prescribed scompile.py, separately in sandbox and library mode.

## Second reading by Q23

I reread the original node and final module directly after compilation. This
was a second pass by the same dispatcher worker; no additional agent was started.
The maintainer's independent delivery review remains separate.

The binders preserve S, Y, X, f and the arbitrary scheme U and natural
transformation p. `IsEtale p` and `IsSurjective p` render exactly the atlas
conditions. On the left, unfolding the recorded `IsRepresentableWith` gives
all scheme tests, with a representing pullback and P on the projection. On
the right, the same existential data occur for the one specified U and p:
the pullback square orders its legs as W→Y, W→U, Y→X, U→X. Thus it neither
asserts representability alone nor loses the property on the projection.
The first declaration uses integral on both sides; the second uses finite on
both sides. Both universes and every variable are explicitly bound. There
are no excluded geometric cases or extra assumptions, and no duplicated
notions. I found no mismatch requiring a change on this second pass.
