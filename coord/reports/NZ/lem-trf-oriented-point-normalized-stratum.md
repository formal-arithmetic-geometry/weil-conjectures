## Worker report

The module `Sheaf.TraceFormula.OrientedPointNormalizedStratum` states
`AlgebraicGeometry.OrientedNearbyCycles.oriented_point_normalized_stratum`.
Its only postponed proof is this theorem, with all seven DAG proof steps in its
docstring. The four helper definitions contain actual constructions, without sorry.
No theorem has been proved in this delivery.

Source read: Orgogozo, *Modifications et cycles proches sur une base générale*,
[author PDF](https://www.cmls.polytechnique.fr/perso/orgogozo/articles/Modifications%20et%20cycles%20proches%20sur%20une%20base%20g%C3%A9n%C3%A9rale.pdf),
printed p. 18, Lemma 8.3.1, the point-order paragraph, and proof of Lemma 8.3.2.
The geometric classification precedes the source's component-finiteness argument;
it does not need that argument's finite-type or excellent-base assumptions.

Clause-by-clause rendering:

- The schemes are arbitrary `{X S : Scheme.{u}}`; the morphism is `(f : X ⟶ S)`.
- Noetherian S is exactly `[IsLocallyNoetherian S] [CompactSpace S]`, as specified
  in the node. Its point is `(s : S)`. There are no conditions on X or f.
- The reduced closure Z_s and its normalization in κ(s) are represented by the
  *same canonical construction* in its relative-normalization presentation:
  `(S.fromSpecResidueField s).normalization`, with map
  `normalizedStratumMap S s := (S.fromSpecResidueField s).fromNormalization`.
  This is not an arbitrary integral model supplied as extra input. Read the actual
  `Scheme.Hom.normalizationDiagram`, `normalizationGlueData`, `normalization`, and
  `fromNormalization` in Mathlib, and `Scheme.normalization` in the recorded upstream
  module: both glue spectra of integral closures. More explicitly, for U = Spec A
  containing s, sections of the pullback of Spec κ(s) are κ(s), and the map A → κ(s)
  has kernel p_s. Integrality of elements over A is identical to integrality over
  A/p_s (lift or reduce the coefficients of a monic polynomial). The resulting ring
  is therefore exactly the integral closure of A/p_s in κ(s), the normalization of
  the reduced closure on U. If U misses s, then it misses its closure: an open
  containing any specialization would contain s. Its pullback is empty and the
  integral closure ring is the zero ring. Restrictions in both constructions come
  from localization in κ(s), so the identifications glue compatibly with the map
  to S. Thus the object is N_s as in the node, canonically and without an added
  normality, finite-normalization, or generic-point hypothesis. The source's
  `Scheme.normalization` uses this same relative construction for Spec k(Z_s) → Z_s.
  No assertion about its data is postponed. The required qcqs instances for
  Spec κ(s) → S are inferred from the existing Noetherian and quasi-separated APIs.
- Y_s is literally `pullback f (normalizedStratumMap S s)`; its map to X is literally
  `pullback.fst f (normalizedStratumMap S s)`.
- The vanishing topos and its two projections are the dependencies' actual
  `VanishingTopos.{u,v} f`, `p₁ f`, and `p₂ f`, without a replacement by triples.
- Sets mean `Type (max (u + 1) v)`, the coefficient-set universe already used by
  the recorded vanishing topos. This retains independent u and v, with no imposed
  equality and no restriction to Type 0.
- A point is `GeometricMorphism` from those sets to that vanishing topos. It
  includes both adjoint functors and left exactness of inverse image.
- `HasEtalePointSupport S (p.comp (p₂ f)) s` means that the second projection is
  represented by some algebraically closed field Ω, with an actual scheme map
  `a : Spec (.of Ω) ⟶ S`, `a (IsLocalRing.closedPoint Ω) = s`, and a natural
  isomorphism between the inverse image and its actual geometric stalk. The stalk
  is transported with the existing `etaleSheafEquivalence`, not a copied equivalence.
  An isomorphism of inverse images gives the same geometric point isomorphism by
  adjunction mates. Taking Ω in Type u is the existing geometric representative
  convention (the algebraic closure of a residue field suffices); arbitrary
  topos-point data remain in the subtype, without a smallness assumption on p.
- `FixedSupportPoint f s` is precisely the subtype satisfying this predicate.
  It does not include a chosen geometric representative or an arrow from the
  second coordinate as extra data. Its arrows in the theorem are *all* natural
  transformations of the direct images, hence the full subcategory's arrows.
- `fixedSupportPointSetoid f s` pulls back Mathlib's `isIsomorphicSetoid` on
  direct-image functors along `p ↦ p.val.direct`. Its quotient is therefore the
  node's isomorphism classes; it does not identify mutually related points merely
  because arrows exist in both directions.
- `∃ θ : Quotient (...) ≃ ↥(pullback ...)` states the asserted bijection on the
  actual classes, with surjectivity and injectivity supplied by an equivalence.
- The first conjunct states that the first projection of every p has support
  `pullback.fst ... (θ [p])`. This is exactly compatibility with |X|. The support
  predicate uses actual geometric stalks and cannot be chosen arbitrarily.
- The second conjunct is `Nonempty (q.val.direct ⟶ p.val.direct) ↔
  θ [p] ∈ closure {θ [q]}` for every p and q. This preserves the node's arrow
  direction q ⇒ p and its Zariski closure direction. The arrows are those of
  `def-trf-geometric-morphism`, not only invertible arrows and not arbitrary
  morphisms of geometric scheme representatives.
- The third conjunct says that arrows in both directions imply equality of the
  two quotient classes. This is exactly the stated antisymmetry consequence.
- There is no `LocallyOfFiniteType`, `LocallyOfFinitePresentation`, `QuasiCompact f`,
  or finiteness assumption on the normalization.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`,
  and the existing locally-Noetherian quasi-separatedness instance.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace`, with no Hausdorff axiom.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Mathlib.AlgebraicGeometry.Properties`: `IsReduced` and `IsIntegral`. These
  describe the reduced closure and its integrality; the relative-normalization
  construction above makes it unnecessary to introduce another closed model as a
  Lean parameter or to postpone its construction behind an existence theorem.
- Recorded `WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`:
  `Scheme.normalization`, `Scheme.fromNormalization`; their implementation through
  `Mathlib.AlgebraicGeometry.Normalization`'s `Scheme.Hom.normalization` and
  `Scheme.Hom.fromNormalization` gives the canonical relative presentation used here.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`; schemes have the required pullbacks.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.Hom.residueFieldMap`, `Scheme.fromSpecResidueField`, and
  `Scheme.SpecToEquivOfField`; `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`.
  The latter equivalence describes exactly the inline algebraically closed
  scheme-point convention used in `HasEtalePointSupport`.
- `Sheaf.Paper.OrientedNearbyCycles`: `VanishingTopos`, `p₁`, `p₂`,
  `etaleTopology`, and their actual size signatures.
- `Sheaf.CategoryTheory.Sites.GeometricMorphism`: `GeometricMorphism`,
  `GeometricMorphism.comp`, `inverseMate`, `inverseIso`.
- `Sheaf.Paper.OrientedProductPointsConservative`: `etaleSheafEquivalence`.
  Its already recorded node is added to stmt_deps to cite this existing transport.
  No dependency interface is repaired or restated.
- `Mathlib.CategoryTheory.IsomorphismClasses`: `isIsomorphicSetoid`;
  `Mathlib.Data.Setoid.Basic`: `Setoid.comap`.

The proof-only imports are the recorded modules for the geometric classification,
normal-generic arrow transitivity, reconstruction of set-valued points, strict-local
specialization lift, normalization in a finite residue-field extension, algebraic
closure existence, and scheme sobriety. The support-fibre and integral-middle-base
nodes currently have no recorded module, so no fictitious import was introduced.
They are proof dependencies, not missing notions required to type this statement.

Edge cases checked before and after writing:

- Empty S supplies no s, so that case is vacuous, without requiring Nonempty S.
- Empty X is permitted: its normalized base change and point-class quotient are
  empty; the theorem does not require a point or a nonempty class set.
- Closed s, generic s, and nonnormal reduced closure all use the same normalization
  construction. In particular it keeps all branches of the normalized closure.
- A field base reduces N_s to its normalization in itself; no separability or
  perfectness of residue fields is assumed. Purely inseparable extensions are allowed.
- Nonreduced S is allowed: the kernel A → κ(s) removes the reduced-closure ideal
  before integral closure. No reducedness of S was added.
- Arbitrary non-quasi-compact and non-finite-type X → S, and nonfinite N_s → S,
  are not excluded. No Noetherian hypothesis on Y_s occurs.
- Identity point arrows give reflexive closure. Noninvertible arrows remain in
  the second conjunct; the quotient uses actual isomorphisms, not mutual reachability.
- Universes u and v remain independent. The quotient is allowed to be large; its
  equivalence to the scheme's point type asserts essential smallness rather than
  assuming it as an extra hypothesis.

Searches for an existing statement/notion (all before writing):

- `msearch.py ... leanfinder "Points of vanishing topos over a fixed scheme point
  correspond to normalized closure base change with specialization order"`: eight
  hits, including `Scheme.range_fromSpecStalk`, `Scheme.le_iff_specializes`, and
  `Scheme.Hom.normalizationDiagram`; none is the point classification.
- `msearch.py ... loogle '"normalization", "Specializes"'`: zero hits.
- `msearch.py ... grep 'oriented.*normal|normal.*oriented|vanishing.?topos'`:
  one unrelated Mathlib oriented-angles comment.
- `msearch.py ... leansearch "vanishing topos point isomorphism classes
  normalization specialization"`: unavailable, rate limit exceeded (60/minute).
  No search verdict is inferred from that unavailable service.
- `rg` of the same patterns and the exact node id in the read-only upstream
  `WeilConjectures` and project `lean/Sheaf`: no existing classification; found the
  recorded vanishing topos, maximal-point finiteness, and generic-arrow transitivity.
- Further local `rg` for geometric stalks, point support, `etaleSheafEquivalence`,
  `closure.*singleton`, and normalization read the actual published helpers and
  avoided duplicating the geometric point, site transport, normalization, or setoid.
- Mathlib `rg` for isomorphism setoids found `isIsomorphicSetoid`, which is used.
  The exact node id was also searched in upstream; it has no declaration there.

Validation: the prescribed `scompile.py NZ lem-trf-oriented-point-normalized-stratum
<module>` compiled both sandbox and final library module names cleanly, 2.2 seconds
per file in the reported run, with no warnings or errors. Every universe and variable
is explicitly bound, `autoImplicit` is false, and all Lean lines are at most 100 columns.
No statement correction or disputed mathematical assertion is needed.

## Second reading by NZ

I reopened the node and the complete Lean module after compilation and made this
second pass myself; the dispatcher brief forbids starting another agent, and the
maintainer supplies the subsequent independent review.

The binders retain exactly arbitrary X, Noetherian S, arbitrary f, and s. The
normalization was checked affine by affine against its actual integral-closure
gluing definition, including opens missing s, so the use of relative normalization
neither selects an arbitrary integral scheme nor changes the reduced closure.
The point predicate was checked to quantify over all geometric morphisms, and its
support witness is an actual geometric stalk isomorphism. The subtype carries no
chosen witness as data. The quotient identifies direct-image functors precisely
when naturally isomorphic, as required by the node's notion of point isomorphism.
The first conjunct uses p₁ and the scheme pullback's first projection. The second
uses q.direct → p.direct and closure of θ[q], in exactly the node's directions.
The last conjunct concludes quotient equality, not equality of representatives.
All clauses and the two absence-of-finiteness requirements match. No mismatch
was found and no statement change was made. The only added dependency cites the
already published site-transport helper, and introduces no new definition node.
