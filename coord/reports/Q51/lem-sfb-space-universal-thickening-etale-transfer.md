## Worker report

This is a stage-2 statement delivery. The live node has no Lean record and is queued
in coord/queue.tsv at stage 2. Q10's accepted delivery is a stage-1 split, not a Lean
statement; there is no released repair note. The old unchanged-item refusal therefore
does not settle this stage-2 task (coord/brief-stage2.md §0, stage handoff).

Module: `Sheaf.AlgebraicGeometry.SpaceUniversalThickeningEtaleTransfer`.
The three theorem proofs are `sorry`; the one helper predicate is defined in full.
No theorem is proved. The node statement and accepted proof split are unchanged.

Clause-by-clause correspondence:

- Base scheme S: `{S : Scheme.{u}}` throughout. Algebraic spaces over S are all the
  binders of type `AlgebraicSpace S`; maps are morphisms of that category, hence
  natural transformations of the existing fppf sheaves. The explicit `universe u`
  follows the size convention without a bound beyond the library's existing carrier.
- The composable maps Z → Y → X are `p : Z ⟶ Y`, `f : Y ⟶ X`.
  Representable étaleness is `hp : IsEtale p.hom.hom`.
- A first-order thickening is the existing `IsSpaceFirstOrderThickening`, which is
  `IsRepresentableWith (fun _ _ p ↦ IsFirstOrderThickening p.left)` on scheme tests.
  The scheme predicate is `IsClosedImmersion i ∧ i.ker ^ 2 = ⊥`.
- The node introduces a universal property for a thickening over X. Its helper
  `IsUniversalSpaceFirstOrderThickening f i f'` includes first-orderness of i,
  `i ≫ f' = f`, and quantifies over ALL algebraic-space tests T,T', their thickening
  j and structure map b : T' → X. The reduction a is over X by `a ≫ f = j ≫ b`.
  Its conclusion is `∃! a'`, with both `j ≫ a' = a ≫ i` (restriction) and
  `a' ≫ f' = b` (over X). No formal-unramifiedness assumption occurs.
- Part (1), hypothesis: `hY : IsUniversalSpaceFirstOrderThickening f j f'`.
  `universalSpaceFirstOrderThickening_etale_lift` supplies Z', i and q, with
  `IsEtale q.hom.hom` and `IsPullback p i j q` identifying the reduction with p.
  `IsUniversalSpaceFirstOrderThickening (p ≫ f) i (q ≫ f')` asserts the induced
  immersion is first order and universal over X. For every other étale lift with
  the same reduction square, `∃! e : Z' ≅ Z''` with `i ≫ e.hom = i'` and
  `e.hom ≫ q' = q` gives precisely the unique isomorphism over Y' inducing the
  identity on Z. The competing lift is not assumed universal.
- The consequence of (1) is the separate theorem ending `_etale_canonical`.
  `hW : IsUniversalSpaceFirstOrderThickening (p ≫ f) k w` is any other universal
  thickening. The first conjunct gives existence and uniqueness of the canonical
  X-map q extending p (`k ≫ q = p ≫ j`, `q ≫ f' = w`). The second conjunct asserts
  étaleness and the cartesian square for every map satisfying those equations.
- Part (2) is `_etale_descent`. Besides hp, `hs : IsSurjective p.hom.hom` is the
  node's surjectivity; `hq` is étaleness of the upper map; `hj` and the first
  conjunct in hZ are the two first-order immersions. `hcomm` says Y → Y' is over X,
  `hcart : IsPullback p i j q` gives the cartesian map of thickenings, and hZ says
  Z → Z' is universal over X. Its structure map is q followed by f', as required
  for the map of thickenings over X. The conclusion is universality of Y → Y'.
  The Z' structure map is expressed by this composite, rather than adding a
  redundant free structure map with an equality.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- Sheaf.AlgebraicGeometry.AlgebraicSpace: `AlgebraicSpace`, `IsRepresentableWith`,
  `IsEtale`, `IsSurjective`, with their scheme-test definitions. The category is
  the full subcategory of fppf sheaves with representable diagonal and an atlas.
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion: `IsClosedImmersion`.
- Mathlib.AlgebraicGeometry.Morphisms.Etale: `Etale`, used through `IsEtale`.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`,
  `etale_fibreProduct_isScheme`. Squares are `CategoryTheory.IsPullback` in the
  algebraic-space category, so no alternative fibre-product construction is added.
- Added landed statement dependency `def-sfb-space-square-zero-extension-data`:
  Sheaf.AlgebraicGeometry.SpaceSquareZeroExtensionData,
  `AlgebraicGeometry.AlgebraicSpace.IsSpaceFirstOrderThickening`.
  Its complete signature and docstring were read. This uses the existing
  `IsFirstOrderThickening` in WeilConjectures.AlgebraicGeometry.Thickening.
- The size-convention dependency has no declaration by design; explicit universes
  render it, as its lean.convention record requests.

The stated proof dependencies are imported without `public` for stage 3:
AlgebraicSpaceIdealClosedSubspaceCorrespondence,
WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism,
WeilConjectures.AlgebraicGeometry.FlatUnramifiedFormallyEtale,
WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance,
and ChartwiseEtalePermanence. The proof dependencies
lem-sfb-space-thickening-base-change and
lem-sfb-space-integral-radicial-etale-invariance have no recorded Lean module,
so no import can yet be supplied for them. Their future proof-only imports must
be checked for cycles. Their absence does not affect these signatures.

Sources read: literature/stacks-project/spaces-more-morphisms.tex,
section-universal-thickening (0601), lemma-check-universal-first-order-thickening
(0603), and lemma-etale-morphism-of-universal-thickenings (0605), including its
proof. The docstrings carry the eight accepted proof steps. In particular descent
uses uniqueness into Y' before comparing the overlap composites; it does not repeat
the source's incorrect assertion that the two overlap maps into Z agree.

Edge cases checked: empty spaces, the identity/zero-ideal thickening, empty scheme
base, non-surjective p in (1), identity p, and the surjective case in (2). No
nonemptiness, separation, Noetherian, finite-type or formal-unramifiedness premise
is imposed. Test objects share the actual universe of algebraic spaces, so the
universal quantifier is not made vacuous in a smaller independent universe. The
uniqueness of isomorphisms fixes both the reduced identification and the target.

Searches (msearch.py Q51 and local rg):

- LeanFinder: "Universal first order thickening algebraic space etale morphism
  transfer descent": 8 hits, all scheme/ring étale definitions and permanence;
  no algebraic-space universal thickening transfer declaration.
- Loogle: "AlgebraicGeometry.AlgebraicSpace, IsThickening, IsSquareZero": no hits,
  unknown AlgebraicGeometry.AlgebraicSpace in its Mathlib index.
- LeanSearch: "Universal first order square zero thickening etale algebraic
  spaces": 8 hits, formally étale rings and scheme étale definitions, no match.
- Mathlib grep: "UniversalThickening|IsFirstOrder|first.order thickening" in
  AlgebraicGeometry: no hits.
- rg in lean/WeilConjectures for FirstOrder, firstOrder, UniversalThickening,
  universalThickening, IsUniversalFirstOrder found scheme/ring universal
  thickenings only; the algebraic-space category is a different carrier.
  rg for the item id in lean/WeilConjectures found no match.
- rg in lean/Sheaf/AlgebraicGeometry found the exact first-order immersion
  predicate in SpaceSquareZeroExtensionData, reused rather than copied; no
  universal-space-thickening predicate or transfer theorem was found.
- DAG searches for universal thickenings located the item and its universal
  conormal consumer, but no independently defined universal-space-thickening
  notion. The helper simply packages the universal property this item itself
  introduces, as authorized in the dispatcher brief's missing-helpers paragraph.

No new nodes, no dependency repairs, no statement correction, and no disputed
statement. Only the item's lean record and the authorized addition of a landed
statement dependency are changed.

## Second reading by Q51

A separate rereading pass by the same worker (the dispatcher forbids starting
other agents) compared the live JSON statement, the Stacks source, and all four
declarations. This is not a claim of independent-agent review; the maintainer's
independent review is still required.

The universal property includes both the restriction equality and the X-structure
equality, and tests arbitrary spaces, not just affine schemes. First-orderness is
included in that predicate, so neither hY nor hZ silently omits the thickening
condition. The lift theorem includes existence, representable étaleness, the
actual pullback square, universality, and uniqueness of isomorphisms against all
étale lifts. The consequence explicitly quantifies every other universal W,
asserts the canonical map exists uniquely, then asserts both étaleness and its
cartesian square. The converse includes lower-map surjectivity, upper-map
étaleness, both first-order conditions, commutativity over X and the cartesian
hypothesis, and concludes the full universal property. No mismatch requiring a
statement change was found. The existing space thickening predicate is reused
through its own landed node added to stmt_deps; no duplicate definition is made.
