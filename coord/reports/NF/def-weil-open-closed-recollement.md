## Worker report

The module defines `finiteRecollementDerivedAdjunction`, canonically obtained from
the recorded sheaf inverse-image/direct-image adjunction, and
`FiniteOpenClosedRecollementTriangle`, the subtype of connecting morphisms whose
triangle with the prescribed open counit and closed unit is distinguished. Both
definitions contain real data; there are no new theorems or sorries.

Validation (2026-10-16): the prescribed `deliver2.py NF
def-weil-open-closed-recollement --no-push` completed with OK: the module compiles
and the preflight passes except for the second reading, which the second reader
supplies. Nothing was pushed. The earlier local stale-export failure is still
visible in the log, but current server confirmation succeeds; it is no longer a
blocker. The successful normal dry-run log is `scratchpad/retry4-dry-run.log`.
An additional control supplying the unchanged comparison source also compiled the
entire new file successfully on the server (`scratchpad/test-exact-comparison.log`).
That temporary comparison copy was removed from the delivery; only this item's
module and node are delivered. No live source, compiler artifact, or launcher code
was directly edited.

Clause correspondence:

- Prime: `(l : ℕ) [Fact l.Prime]`.
- Finite extension: `(E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]`.
- The valuation ring and chosen uniformizer are those of the recorded construction
  `Padic.coefficientExtensionRing l E n`; `(n : ℕ) (hn : 1 ≤ n)` excludes level zero.
  Finiteness is installed inside the definition using
  `Padic.finite_coefficientExtensionRing l E n hn`, not an extra mathematical assumption.
- Schemes: `{Z U X : Scheme.{u}}`; closed and open immersions:
  `(i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j]`.
- Invertibility of l on all three schemes: `_hZ`, `_hU`, `_hX`, each requiring
  `IsUnit (l : W.presheaf.stalk w)` for every point of the corresponding scheme.
- Complementarity: `_hij : Set.range j.base = (Set.range i.base)ᶜ`.
- Ambient category: `proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E n)`,
  the ordinary localization of intrinsic constant-ring module sheaves, not a completed
  category or an etale category. Its site objects have universe u+1 and morphisms u;
  scalar coefficients are canonically lifted inside the recorded ring sheaf.
- The bounded constructibility condition on K is exactly
  `_hK : intrinsicFiniteTorsionConstructible l E n hn X K`.
- Both inverse images are `sfIntrinsicDerivedPullback`, termwise exact descent;
  open extension is `sfIntrinsicDerivedOpen`, the termwise descent of the recorded
  `sfIntrinsicExtensionByZero`.
- The first arrow is `(exceptionalOpenAdjunction j A).counit.app K`. Read its full
  construction: it maps the canonical sheaf adjunction to complexes and localizes it
  with the exact-functor factorization isomorphisms. Its sheaf right adjoint is
  `sfIntrinsicPullback A j`, canonically identified with `sfIntrinsicOpenRestriction`
  using `ProEtale.upperStarIsoOpenImmersionRestriction`. This is the specified open
  counit expressed in the recorded pullback presentation, not a freely chosen map.
- The second arrow is the unit of `finiteRecollementDerivedAdjunction i A`.
  This helper applies `mapDerivedCategoryRightDerivedAdjunction` to the published
  section-normalized `sfIntrinsicConstantModuleAdjunction i A`. Its right adjoint is
  `proEtaleConstantDerivedDirectImage i A`, ordinary K-injective direct image.
- The data is the subtype of morphisms from `Ri_* i^* K` to `(j_! j^* K)⟦1⟧`, whose
  property is `Triangle.mk` of the prescribed counit, prescribed unit and that morphism
  belonging to `distTriang` of the ambient category. No existence, functoriality in K,
  uniqueness, or constructibility preservation is asserted.

Dependency declarations read and reused, directly or through public imports:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`; its imported `CoefficientExtension`:
  `Padic.coefficientExtensionRing` and its valuation-ring/uniformizer construction.
- Mathlib `AlgebraicGeometry.IsClosedImmersion` and
  `AlgebraicGeometry.IsOpenImmersion` in their recorded modules.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`:
  `AlgebraicGeometry.Scheme.proEtaleDerivedCategory`.
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicFiniteOperations`:
  `AlgebraicGeometry.Scheme.sfIntrinsicDerivedPullback`, `sfIntrinsicPullback` and
  `sfIntrinsicModuleEquivalence`.
- `Sheaf.AlgebraicGeometry.ProEtaleOperations`:
  `proEtaleRingDerivedPullback`, the recorded finite-level pullback interface, and
  the exact termwise construction specialized by the intrinsic operations module.
- `Sheaf.Paper.SfDerivedDirectImage`: `WeilConjectures.sfFiniteDerivedDirectImage`,
  which uses `proEtaleConstantDerivedDirectImage` from the publicly imported
  `Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage`.
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`:
  `sfIntrinsicExtensionByZero`; its recorded Exact module:
  `sfIntrinsicExtensionByZero_exact` and exactness instances; its recorded Adjunction
  module: `sfIntrinsicExtensionByZeroAdjunction` and `sfIntrinsicOpenRestriction`.
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`:
  `intrinsicFiniteTorsionConstructible`.
- Mathlib `DerivedCategory`, `Functor.mapDerivedCategory`,
  `Functor.mapDerivedCategoryFactors`, `Localization.liftNatTrans`, and
  `Pretriangulated.Triangle.mk` / `distTriang`, in the recorded derived-category,
  exact-functor, localization and triangulated-category modules.
- `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`:
  `Adjunction.mapHomologicalComplex` and `Adjunction.mapHomotopyCategory`.
- The published canonical coefficient comparison helpers are reused from
  `Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport`; the exact localized
  open adjunction is reused from `Sheaf.AlgebraicGeometry.IntrinsicDerivedOpenAdjunction`.

Edge cases checked before drafting: empty X, empty U or Z, identity open/closed
immersion with empty complement, the zero complex, level n=1, arbitrary prime including
2, and schemes without any Noetherian or quasi-compact-open hypothesis. No existence is
claimed, so the definition also permits a connecting-map subtype to be empty. Bounded
constructibility concerns only K; the other terms are in the ambient derived category.
The definition uses the fixed chosen uniformizer already provided by its coefficient
node, and adds no independent choice. All universes and variables are explicit.

Searches, using the prescribed msearch.py wrapper (also in searches.jsonl):

- LeanFinder, “Open closed recollement distinguished triangle of derived proetale
  modules with prescribed counit and unit”: eight results including
  `DerivedCategory.triangleOfSESIso`, `triangleOfSES_distinguished` and
  `mem_distTriang_iff`; generic ingredients, no exact definition.
- LeanSearch, “open closed recollement distinguished triangle specified adjunction
  counit unit”: eight general adjunction-unit/counit results; no exact definition.
- Loogle, `"Triangle.mk"`: the Mathlib triangle constructor and its projection lemmas;
  these provide the constituent triangle, not this specified pro-etale definition.
- Mathlib grep, `recollement|openClosed|open_closed`, CategoryTheory: no matches.
- Project source rg, `recollement|openClosed|open_closed`: the existing
  `AlgebraicGeometry.Etale.exists_distTriang_openClosed` concerns the etale site and
  is an existence theorem. Read its signature and docstring; it is not this definition.
- Project source and side-library search for the exact blueprint id: no existing
  declaration. Side-library `OpenClosedRecollement.lean` likewise gives an etale,
  bounded-below existence statement; read its full signature and docstring.
- Full Mathlib, upstream and side-library name search for the two proposed declaration
  names: no existing declarations.

Read the full node and its sixteen statement dependencies, their records and relevant
source declarations, the blueprint definition at order 1834, stage-2 brief and contract,
delivery-errors H, the compact-object example, and the pro-etale framework note.
No mathematical statement correction or disputed mathematical claim is proposed.
No new or dependency node is delivered. The draft has no theorem and no sorry.

## Second reading by NF

Independent second reading, 2026-10-16. I read the sandbox node and module together,
the blueprint definition at order 1834, all sixteen statement-dependency nodes,
and the relevant declarations rather than relying on their names. The source is
the blueprint Markdown named by the node, not a Stacks recollement theorem.
For its constructions I also read Stacks `sites-modules.tex`,
`lemma-adjoint-push-pull-modules` (03D3), the localization-of-ringed-sites setup
and `lemma-extension-by-zero` (03DI), and `proetale.tex`,
`definition-extension-zero` (09AE) and `lemma-ses-associated-to-open` (09AH).
The last lemma assumes a quasi-compact complementary open for the short exact
sequence. The blueprint explicitly reserves that assumption for existence;
it is correctly absent from this definition of possible triangle data.

Object, hypothesis, and conclusion checklist:

1. A prime ell is `(l : ℕ) [Fact l.Prime]`. Verdict: exact, including ell = 2.
2. A finite field extension of Q_ell is `(E : Type u) [Field E]
   [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`. Verdict: exact;
   finite-dimensionality is not replaced by finite type or a chosen basis.
3. The valuation ring, chosen uniformizer, and quotient A_{E,n} are the recorded
   `Padic.coefficientExtensionRing l E n`. I read `CoefficientExtension.lean`:
   it uses `coefficientExtensionIntegers`, the chosen
   `coefficientExtensionUniformizer`, and the quotient by the nth power of its
   principal ideal. `(n : ℕ) (hn : 1 ≤ n)` gives precisely positive integral
   levels. The internal `letI` uses the recorded
   `Padic.finite_coefficientExtensionRing`; it is not an extra assumption on E
   or A. Verdict: exact; no new coefficient datum or uniformizer choice.
4. The three schemes and the two maps are `{Z U X : Scheme.{u}}`,
   `(i : Z ⟶ X) (j : U ⟶ X)`. Their structures are the recorded Mathlib
   `[IsClosedImmersion i] [IsOpenImmersion j]`. I read those interfaces:
   closed embedding with surjectivity on stalks, and open immersion of locally
   ringed spaces, respectively. Verdict: the same immersions as the node.
5. Ell invertible on each scheme is `_hZ`, `_hU`, `_hX`, each asserting that
   the natural-number section is a unit at every stalk. This is the usual
   local formulation of invertibility on a scheme. Verdict: all three
   hypotheses are retained, with no characteristic or field-base assumption.
6. Complementarity is `_hij : Set.range j.base = (Set.range i.base)ᶜ`.
   Verdict: exactly j(U) = X minus i(Z), without a choice of a particular
   reduced closed complement or an additional scheme structure on it.
7. The ambient category is `proEtaleDerivedCategory X
   (Padic.coefficientExtensionRing l E n)`. I unfolded the recorded abbreviation:
   it is `DerivedCategory` with `HasDerivedCategory.standard` on intrinsic
   modules over the sheafification of the constant ring, canonically lifted
   to the module universe. Verdict: ordinary, uncompleted, unbounded derived
   category on the small pro-etale site; no etale or adic substitution.
8. K is an arbitrary object of that category subject to
   `_hK : intrinsicFiniteTorsionConstructible l E n hn X K`.
   I read its body: the set of degrees with nonzero cohomology is finite,
   and every cohomology sheaf satisfies the recorded
   `IsConstructibleProEtaleModuleSheaf`. Verdict: precisely bounded finite-torsion
   constructibility; no Tor-amplitude, perfectness, Noetherianity or global
   finite-field datum is required.
9. Both i^* and j^* are `sfIntrinsicDerivedPullback`, the exact termwise
   derived functor of the recorded canonical `sfIntrinsicPullback`.
   `sfIntrinsicDerivedOpen` is the termwise derived functor of the recorded
   `sfIntrinsicExtensionByZero`. I read their bodies and the realization
   equivalences. Verdict: the dependency constructions on the same intrinsic
   module categories, not private replacement operations or arbitrary maps.
10. The first arrow is `(exceptionalOpenAdjunction j A).counit.app K`.
    I read `IntrinsicDerivedOpenAdjunction.lean` and its underived input
    `sfIntrinsicOpenAdjunction`: they transport the canonical site adjunction,
    apply it degreewise, and localize using `mapDerivedCategoryFactors`.
    The fixed-scalar `openImmersionLowerShriekUpperStarAdjunction` uses the
    canonical identification of inverse image with open restriction.
    I also read the recorded intrinsic restriction adjunction, which transports
    the same site adjunction. Verdict: the specified localized sheaf counit,
    expressed using the node's pullback presentation of j^*.
11. Ri_* is `proEtaleConstantDerivedDirectImage i A`, the K-injective right
    derived functor of the canonical constant-module direct image.
    The second arrow is `(finiteRecollementDerivedAdjunction i A).unit.app K`.
    The helper contains the real construction
    `(sfIntrinsicConstantModuleAdjunction i A).mapDerivedCategoryRightDerivedAdjunction`.
    I read both ingredients: the former fixes the direct-image identification
    on scalar-unit sections, and the latter derives the exact left adjoint
    and the K-injective right adjoint. Verdict: the canonical derived unit;
    no freely supplied adjunction or coefficient identification.
12. The data is the subtype `{ δ : Ri_* i^* K ⟶ (j_! j^* K)⟦(1 : ℤ)⟧ // ... }`.
    Its property is `Triangle.mk` of precisely the preceding counit, unit,
    and δ belonging to `distTriang` of the same ambient category.
    I read Mathlib's `Triangle.mk`: its three arrows have exactly those
    sources and targets. Verdict: every clause of the distinguished completion
    is present, in order. There is no existential witness, naturality in K,
    uniqueness, or assertion that the other terms remain constructible.

Edge cases: the schemes may be empty, either immersion may have empty source,
and an identity immersion with empty complement is allowed. There is no
nonemptiness, quasi-compactness, separation, or Noetherianity binder. The zero
derived object is allowed, and the finite cohomology-support predicate allows
the empty set of nonzero degrees. Level n = 1 is included; n = 0 is excluded
exactly as in the node. Every prime, including 2, is included; invertibility
is stipulated locally without an extra common characteristic. All Lean
universes and variables are explicit (`autoImplicit false`). The site has
objects in u+1 and morphisms in u, with module values in u+1; these universes
are not equated to use a specialized API. Scheme and finite-extension data
are taken in one arbitrary common ambient universe, as in their recorded
dependencies. The result may be an empty subtype: its definition does not
claim that a completion exists in these edge cases or in general.

Independent H4 searches (performed again during this reading, with different
semantic wording from the worker):

- LeanFinder via `msearch.py`: "Connecting morphism completing extension by zero
  counit and closed immersion derived unit to a distinguished triangle on small
  proetale sites". Eight results; `DerivedCategory.triangleOfSESδ` was the
  relevant generic ingredient, not the specified pro-etale definition.
- LeanSearch via `msearch.py`: "Distinguished triangle completing prescribed
  adjunction counit and unit for complementary open and closed immersions".
  Eight generic adjunction/triangle results; no matching definition.
- Loogle via `msearch.py`, `"Triangle.mk"`: the generic constructor and its
  projection lemmas, which are already reused here.
- `rg` for `recollement`, `Recollement`, `openClosed`, and open/closed spellings
  in Mathlib's category theory, upstream `WeilConjectures`, the side framework,
  and `lean/Sheaf`. I opened upstream
  `AlgebraicGeometry.Etale.exists_distTriang_openClosed` and side
  `AlgebraicGeometry.Etale.exists_functorial_distTriang_openClosed`. They are
  etale existence statements (the latter on D-plus), not this pro-etale
  definition. The generic/adic recollement material likewise has different
  data and hypotheses. Searches for `sfIntrinsicConstantModuleAdjunction` and
  `mapDerivedCategoryRightDerivedAdjunction` found the reused ingredients,
  but no existing specialized derived adjunction declaration with these
  intrinsic functors and no existing `FiniteOpenClosedRecollementTriangle`.
  A mistyped search-service kind was rejected and immediately rerun correctly;
  it supplied no mathematical evidence.

H5/H6/H8/H9: both definitions contain concrete constructions; the subtype is
not a choice from existence. No theorem is proved and there are no new sorries.
The definition node has an empty proof plan, so no postponed proof docstring
is missing. Both declarations and the module have source/blueprint docstrings,
the names have no `Sheaf` namespace prefix, and the lines meet the width limit.
There are no new nodes or dependency modules to audit under H12/H13 and no
`statement_change` or disputed statement requiring a citer audit.

Mismatches and changes: none found in the Lean or node; both are preserved.
The only change made by this second reading is this independent review section.
The mandated fresh compilation, dry run, and delivery checks are recorded below.

Second-reader validation: `scompile.py NF def-weil-open-closed-recollement
lean/Sheaf/AlgebraicGeometry/FiniteOpenClosedRecollement.lean` exited 0.
The local overlay exposed stale dependency exports; the wrapper then confirmed
the dependency chain and the entire delivered module cleanly against current
server sources (the item took 1.8 s, nice 19, two threads, 60 s limit).
A source check also confirmed the node signature is verbatim, no line exceeds
100 columns, no new `sorry` occurs, and the node differs from the shared base
only in `lean`.
