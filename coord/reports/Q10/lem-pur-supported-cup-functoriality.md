## Worker report

The mathematical statement is an exact existing match: `WeilConjectures.PurityFiniteSetting.supportedCupFunctoriality`
in `Sheaf.Paper.SupportedCupFunctoriality`, originally published at
`lean/Sheaf/Paper/SupportedCupFunctoriality.lean:968`. The shared node already records
this Q67 declaration and its successful independent stage-2 review of 2026-10-18.
The initial existing-only dry run nevertheless failed: both the overlay compile and
server confirmation timed out compiling that published module within 60 seconds.
The delivery therefore repairs that same owning module in the sandbox and records
`existing: false`. It preserves every existing construction, proof and theorem
signature. Only the item's `lean` field and its own module change; the mathematical
statement, dependencies, proof plan and existing review records are unchanged.

The existing signature is:

```lean
theorem supportedCupFunctoriality (P : PurityFiniteSetting.{u}) :
    (∀ pro : Bool, P.FunctorialCupAlgebraLaws pro ∧ P.FunctorialCupLocalizationLaws pro) ∧
      P.FunctorialCupComparisonLaws
```

Hypothesis and clause audit against the existing source:

- `P : PurityFiniteSetting.{u}` supplies the finite-field datum, prime ell distinct
  from the characteristic, chosen finite coefficient extension, and positive level
  `P.level_pos`. `P.Coefficient` is the existing size lift of O_E/(varpi^n).
  `P.diagonalExponent` is ell^n, not ell^(n/e); no divisibility by the ramification
  index is required. `functorialCupTwist` uses the signed finite-root line and its
  comparison inverse image, for every integer twist.
- `pro : Bool` quantifies both actual sites: false is small etale and true is small
  pro-etale. `functorialCupSheaves` uses their published topologies, retaining the
  site object universe u+1 and morphism universe u.
- Schemes are arbitrary `Scheme.{u}`. Their k-structure is an explicit
  `aX : X ⟶ Spec (.of P.field.k)`; a pullback scheme has structure `v ≫ aX`.
  Every morphism `v : Y ⟶ X` is allowed. Closed supports have only
  `[IsClosedImmersion i]`; `ChosenCartesianSquare g j i v` supplies exactly the
  chosen presentation of the pulled-back closed subscheme. There are no finite-type,
  separatedness, Cartier, regularity or exceptional-base-change hypotheses.
- `FunctorialCupH pro i a r` is the supported derived-Hom model from the underived
  closed direct image of the constant coefficient module to A(r)[a]. All degrees
  and twists are integers. `functorialCupPullback` is the specified composite:
  inverse normalized coefficient exchange, exact inverse image of the morphism,
  the canonical shift comparison, then the normalized twist pullback. The exchange
  is fixed uniquely by its equation on restriction of constants; it is ordinary
  coefficient exchange and does not assume a purity exchange is invertible.
- `FunctorialCupAlgebraLaws.identity` and `.composition` state identity and
  composition for arbitrary chosen Cartesian presentations, including the identity
  and arbitrary composable pullback morphisms.
- `FunctorialCupLocalizationLaws.forget_support`, `.open_restriction` and `.boundary`
  are the naturality squares for all three arrows of localization. The open group
  is the actual `Hom_X(j!A_U,A(r)[a])` adjunction model of cohomology on the open
  complement. `functorialCupBoundary` composes with the `singleδ` of the actual
  source short exact sequence `j!A_U → A_X → i_*A_C`, retaining its boundary sign.
  `.full_support` makes forgetting full support bijective; together with
  `.forget_support` this identifies full-support pullback with ordinary pullback.
- `functorialCupKummer` uses exactly `P.frameKummerEtale` and `P.frameKummer`, through
  Ext-to-derived-Hom and the identity direct-image unitor. Thus `.kummer_add` states
  kappa(u*w)=kappa(u)+kappa(w) for the concrete Kummer-boundary class, and
  `.kummer_pullback` uses the actual unit pullback
  `Units.map v.appTop.hom.toMonoidHom`.
- `functorialCup` reuses `ProEtale.cupComposite`, `cupDerivedCoefficientMap`, and
  `cupTensorShiftIso`, followed by normalized twist multiplication. Its true-site
  source multiplication is `ProEtale.cupCoefficientMap`, exactly that of the
  recorded `supportedCup`. Its false-site multiplication is
  `Etale.closedConstantTensorMap`, the prescribed etale analogue. No arbitrary
  product pairing is postulated.
- `.add_left`, `.add_right`, `.smul_left` and `.smul_right` state A-bilinearity.
  `.associativity` includes the canonical reassociation of the triple intersection
  and degree/twist sums. The supplied map over X between the two closed intersection
  presentations is necessarily the canonical one, since the immersions are monic.
- `.pullback` is precisely pullback of alpha cup beta equals the cup of the two
  pullbacks, including the Cartesian presentation of the intersection support.
  `.symmetry` transports along the support swap and degree/twist commutation;
  its scalar is `((-1 : ℤ) ^ (a*b).natAbs)`, which equals (-1)^(ab) by parity for
  every integer a,b. The signed-twist product family retains its symmetry,
  evaluation and unit equations, so this uses the canonical coefficient symmetry.
- `FunctorialCupComparisonLaws.supported_bijective`, `.ordinary_bijective`, and
  `.open_bijective` give the canonical comparison identifications. Its `.pullback`,
  `.ordinary_pullback`, `.open_pullback`, `.cup`, `.kummer`, `.forget_support`,
  `.open_restriction`, and `.boundary` identify every listed operation across sites.
  The closed comparison is normalized on the unit; the open comparison on the
  extension-by-zero counit. These are the actual comparison inverse-image maps.

Recorded statement dependencies read and reused by the existing module:

- `def-pur-conventions`: `Sheaf.Paper.PurityFiniteSetting`, declaration
  `WeilConjectures.PurityFiniteSetting` and its coefficient/constant-sheaf data.
- `def-pur-frame-class`: `Sheaf.Paper.PurityFrameClass`, declaration
  `WeilConjectures.PurityFiniteSetting.frameClass`; its published imports provide
  `frameKummerEtale`, `frameKummer` and the individual-boundary convention.
- `thm-pur-with-support-exactness`: `Sheaf.AlgebraicGeometry.SupportLongExact`,
  `AlgebraicGeometry.exists_support_longExact`, giving the support-kernel localization
  and boundary convention. The Hom model is its injective-representative realization.
- `def-pur-supported-cup`: `Sheaf.Paper.SupportedCup`,
  `AlgebraicGeometry.ProEtale.supportedCup`, together with its exact source
  multiplication, K-flat comparison and sign-normalized composite.
- `def-weil-closed-immersion`: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion`: closed embedding with surjective stalk maps.
- `def-weil-pbc-cartesian-square`: `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`,
  `AlgebraicGeometry.ChosenCartesianSquare`: commutative square with a chosen
  fibre-product isomorphism and both projection equations.

Edge cases checked from these definitions: empty ambient scheme; empty, full,
identical, disjoint and nonreduced supports; arbitrary pullbacks destroying Cartier
properties; non-quasi-compact open complement; zero and negative cohomological degrees;
negative twists; n=1 and ramified positive levels not divisible by e; a=b=1 gives
minus, even degrees give plus, and characteristic two identifies those signs.
All remain in the existing signature. Closed-source uniqueness uses the epic unit
restriction, including empty supports; open-source uniqueness uses its monic counit.

Searches made on 2026-10-18:

- `msearch.py ... leanfinder "Pullback and graded commutativity of supported Kummer
  cup products on etale and pro-etale sites"`: eight unrelated projective-spectrum
  and scheme-pullback hits, no exact Mathlib statement.
- `msearch.py ... leansearch "Supported cup products commute with pullback and are
  graded commutative"`: eight graded tensor-product hits, no supported-site theorem.
- `msearch.py ... loogle "cupProduct,Ext,gradedComm"`: no hits; cupProduct unknown.
- `msearch.py ... grep "supportedCupFunctoriality|supported.*[Cc]up|[Cc]up.*[Ss]upport"`:
  no Mathlib hits.
- `rg` with the same regex in upstream `WeilConjectures` finds
  `Etale.cupWithSupports`; its signature is an exceptional-functor construction with
  adjoint hypotheses, not this both-site statement. Its full signature was inspected.
- `grep -rn "lem-pur-supported-cup-functoriality"` in upstream `WeilConjectures`:
  no node-tag match.
- `rg` in `lean/Sheaf` finds the exact existing declaration in
  `Sheaf.Paper.SupportedCupFunctoriality`, plus the prescribed supported cup and
  downstream uses. Its full structures, canonical constructions and theorem docstring
  were read, not merely its declaration name.

Sources read: the node's full statement and eight-step proof; every recorded statement
prerequisite and its defining declaration/docstring; Stacks local sites-cohomology.tex
at lemma-cup-product-associative (0FPL) and lemma-cup-product-commutative (0FPM);
main-20261015 blueprint lem-pur-frame-independence.proof.md at Unit multiples,
Permutations and Elementary shears. The repair note is resolved stage 1; it asks to
retain this statement and its route, which this delivery does.

No statement correction, new definition node, dependency module or dispute.
No theorem is proved in this delivery. The sole delivered module is compiled using
scompile.py, then checked again by deliver2.py's dry run and delivery gates.

Compilation repair: a diagnostic-only trace.profiler run isolated the large kernel
cost in FunctorialCupAlgebraLaws (about 12 seconds), FunctorialCupComparisonLaws
(about 33-35 seconds), and several canonical maps. That run finished near the limit;
the original dry run timed out twice. For robustness, the repaired module names each
of the 22 algebra/comparison field propositions with an ordinary Prop-valued def,
then uses those names in the two original structures. Each definition's body is
verbatim the old field type, with exactly the same binders. Thus projections,
constructors and the main theorem keep definitionally identical mathematical types,
while the kernel shares the named clauses. Each helper has a source and blueprint
docstring and is listed in lean.declarations. These are clauses of the owning node,
not independent mathematical notions. All canonical map definitions are untouched.
The profiler option is removed from the delivered source.

## Second reading by Q10

This is the dispatcher's single-worker direct-delivery workflow; no independent
second worker is claimed and no agent was spawned. The maintainer supplies the
independent review. On a final author rereading I checked the source at the three
law structures against each clause above, especially full-support normalization,
concrete Kummer classes at all positive levels, arbitrary Cartesian presentations,
negative integer signs and both localization boundary comparisons. No mismatch was
found. The only source changes factor the two law structures through named predicates;
I checked each predicate against the original field text and retained all binders. The existing Q67 declaration also already
has an independent passing review recorded in the shared node.
