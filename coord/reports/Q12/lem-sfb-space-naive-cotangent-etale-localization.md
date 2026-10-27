## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceNaiveCotangentEtaleLocalization` states
`AlgebraicGeometry.AlgebraicSpace.naiveCotangent_etaleLocalization`. Its sole theorem
has proof `sorry`. There are no new definitions, new nodes, dependency repairs, or
statement corrections. Source read: Stacks, spaces-more-morphisms.tex,
lemma-NL-etale-localization (Tag 0D0W), including its proof, and
spaces-properties.tex, lemma-etale-exact-pullback (Tag 03LV).

Clause-by-clause correspondence:

- The scheme S is `{S : Scheme.{u}}`, using Mathlib's actual scheme structure.
- The four algebraic spaces over S are `{X Y U V : AlgebraicSpace S}`. This is the
  existing full subcategory of fppf sheaves with representable diagonal and an
  étale surjective scheme atlas; morphisms are the existing natural transformations.
- The four maps are `(f : X ⟶ Y) (g : U ⟶ V) (p : U ⟶ X) (q : V ⟶ Y)`.
- Étaleness of p and q is `(hp : IsEtale p.hom.hom)` and
  `(hq : IsEtale q.hom.hom)`. The existing predicate is representability with
  étale scheme projections after every scheme base change. It uses Mathlib's
  `AlgebraicGeometry.Etale`; there is no extra chartwise or surjectivity hypothesis.
- Commutativity fp=qg is `(sq : p ≫ f = g ≫ q)`, in Lean's diagrammatic order.
  There is no `IsPullback` assumption.
- `naiveCotangent f` is the existing image under `DerivedCategory.Q` of the
  two-term canonical-presentation complex of f. Likewise `naiveCotangent g`
  is exactly NL_{U/V}, including its differential.
- Restriction of NL_{X/Y} to U_et is
  `(spaceEtaleDerivedRestriction p hp).obj (naiveCotangent f)`. This existing
  functor is termwise exact étale tensor pullback, identified with actual site
  restriction by its owning module and `moduleTensorPullback_etale_restriction`.
  It conjugates the original module categories by the existing affine-basis
  equivalences, retaining the same regular functions and module section universe.
- The conclusion `Nonempty (... ≅ naiveCotangent g)` asserts an isomorphism in
  U's unbounded derived module category, not merely cohomology isomorphisms.
  Its canonical construction is the composite of pullback of the naive complex
  and the ring-map identifications, as specified in the proof docstring and 0D0W.
  No arbitrary chosen replacement complex or map is introduced.
- `[HasDerivedCategory.{w} X.SmallModules]` and the analogous instance for U
  allow arbitrary localization morphism size w. Neither Y nor V needs a derived
  category choice because no derived object on them occurs. Universe u is the
  existing algebraic-space size convention; module sections are not lifted.

Dependencies read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsEtale`, and its actual étale-site restriction `pullback`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`, used
  by the existing representable étale predicate.
- `Sheaf.AlgebraicGeometry.SpaceNaiveCotangentComplex`: `naiveCotangentComplex`,
  `naiveCotangent`, and the underlying real conormal/differential constructions.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`,
  `DerivedCategory`, `DerivedCategory.Q`.
- `Sheaf.AlgebraicGeometry.SpaceDerivedEtaleChartCalculus`:
  `spaceEtaleDerivedRestriction`, `spaceEtaleTensorPullback_exact`, and
  `spaceEtaleDerivedRestrictionFactors`. Its already landed owning node
  `lem-sfb-space-derived-etale-chart-calculus` is added to stmt_deps, as permitted
  by the rule allowing already landed statement dependencies. A read-only traversal
  of statement and proof dependencies found no path from it back to this item.
- Proof imports: `Sheaf.AlgebraicGeometry.SpaceCotangentRingMap`, the recorded
  module of `lem-trf-space-enlarged-etale-ringed-site-model`, and
  `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`, the recorded module of
  `lem-pur-site-restriction-module-adjunction-exact` (`localizedSystemExact`).
  The proof dependency `lem-sfb-topos-naive-cotangent-pullback` has no recorded
  Lean statement, so has no import; the proof docstring records its planned use.

Edge cases checked against the source and interfaces: identity p and q; f and g
identities; empty U or V; étale maps that are not surjective; a noncartesian
commutative square. A direct noncartesian example is X=Y=Spec k, U=V=Spec k ⊔ Spec k,
p and q the two-sheet étale maps, and g mapping both components of U to one
component of V. Both relative complexes vanish, so this case is compatible with
the conclusion and is not excluded by the signature. No finiteness, separation,
flatness of a conormal module, boundedness, or characteristic condition is added.
The empty site and zero modules need no special cases. No statement fault found.

Searches made with the prescribed msearch.py wrapper:

- LeanFinder: `Naive cotangent complex of algebraic spaces commutes with etale
  localization`. Eight hits, including ring-level
  `Algebra.Generators.cotangentCompLocalizationAwayEquiv`; no space/site theorem.
- Loogle: `"Cotangent", "Etale"`. Three ring-level hits:
  `Algebra.FormallyEtale.subsingleton_h1Cotangent`,
  `Algebra.Extension.tensorCotangentSpaceOfFormallyEtale`, and
  `Algebra.Extension.tensorH1CotangentOfFormallyEtale`. No match.
- LeanSearch: `The naive cotangent complex of algebraic spaces restricts under an
  etale commutative square`. Eight ring-level cotangent/differential hits; no match.
- Wrapper grep: `naiveCotangent|naive_cotangent|NaiveCotangent` in Mathlib's
  AlgebraicGeometry: zero hits.
- rg of both `lean/WeilConjectures` and `lean/Sheaf` for
  `naiveCotangent|naive_cotangent|NaiveCotangent|etaleLocalization` found the
  existing naive complex, affine presentation comparisons, unrelated ring
  localizations, and scheme-site localization functors; no duplicate theorem.
- rg of `lean/WeilConjectures` for the exact item id found no match. Name search
  for the proposed theorem in the project and dag/lean_names_upstream.json found
  no existing declaration. Reading the algebraic-space derived-operation modules
  located the shared exact restriction API, which is reused directly.

Validation: scompile.py compiled this module both as a sandbox module and at its
library module name, cleanly (1.7 s and 1.9 s). Every binder is explicit and
`autoImplicit` is false. All source lines are at most 100 characters. The expected
postponed-proof status is confined to the one theorem.

## Second reading by Q12

This is the worker's separate second pass over the node and delivered file; the
dispatcher prohibits starting another agent. The maintainer supplies the independent
review. I compared every binder and the conclusion again with 0D0W: S and all four
spaces/maps occur; hp and hq use representable scheme-test étaleness; sq has the
correct orientation; the comparison lives in D(O_U); and neither cartesianness nor
surjectivity occurs. The hq and sq hypotheses remain explicit even though the
conclusion's endpoints do not mention their proofs. The two cotangent objects are
literally the dependency's `naiveCotangent`, and restriction is literally the
already landed `spaceEtaleDerivedRestriction`. I read its definition, its exactness
statement, and its factorization on complexes, together with its ordinary étale
restriction comparison. No replacement module or extra choice of restriction was
needed. The added landed dependency supplies that notation only; it does not change
the mathematical statement. No mismatch was found or silently corrected.
