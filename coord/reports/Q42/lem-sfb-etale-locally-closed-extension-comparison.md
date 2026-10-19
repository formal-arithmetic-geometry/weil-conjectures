## Worker report

The retained packet was repaired after return H3. The module
`Sheaf/SixFunctors/EtaleLocallyClosedExtensionComparison.lean` defines the
closure extension `AlgebraicGeometry.etaleLocallyClosedExtension` and three
canonical restriction normalizations:

- `etaleLocallyClosedExtensionRestrictionIso` is the composite of the
  `a.toImage ≫ a.imageι` pullback comparison, the closed counit, and the inverse
  open unit, giving the canonical identity restriction of `a_!`.
- `etaleFactorizationRestrictionIso` is the corresponding composite for every
  closed-then-open factorization `h ≫ u' = a`.
- `etaleClosedCompositionRestrictionIso` is the corresponding composite after
  a further closed immersion `b ≫ i = a`.

The theorem keeps the finite-open comparison conjunct. For each locally closed
`a`, it supplies `hqa : QuasiCompact a`, then a comparison `e` for every
factorization. The equation
`Functor.isoWhiskerRight e (Etale.upperStar ... a) ≪≫
etaleFactorizationRestrictionIso ... =
etaleLocallyClosedExtensionRestrictionIso ...`
expresses restriction to the identity on `S`; the final universal clause says
that this normalization uniquely determines `e`. The final closed-immersion
clause has the analogous normalized uniqueness equation using
`etaleClosedCompositionRestrictionIso`.

The first conjunct renders a cartesian square by
`IsPullback.of_hasPullback g u`, with upstream `Etale.finiteOpenComparison`.
Its source docstring specifies the transpose under `u_! ⊣ u^*` of the inverse
exchange map `u^* g_* v_! L ≅ h_* v^* v_! L ≅ h_* L`; the theorem retains that
canonical map and states `IsIso` for it. The finite coefficient ring is
`A : Type (u + 1)` with `[CommRing A] [Finite A]`, and the ambient scheme is
`X : Scheme.{u}` with `[IsNoetherian X]`. All source, target, immersion, and
module-sheaf universes are explicit.

The closure helper uses Mathlib's scheme-theoretic image: `a.toImage` is the
open factor and `a.imageι` the closed factor, with the explicit witness
`hqa` installed while constructing the functor. The first normalization uses
`Etale.upperStarComp`, the closed counit of
`Etale.upperStarLowerStarAdjunction`, and the inverse unit of
`Etale.openImmersionLowerShriekUpperStarAdjunction`. The factorization
normalization reverses the order of the open unit and closed counit. The closed
composition normalization first applies the closed counit for `i` and then the
closure normalization for `b`.

The theorem docstring records all seven proof steps from the node: finite-open
comparison and its mate, constant-module linearity, Noetherian
quasi-compactness, the scheme-theoretic cartesian closure square, normalized
factorization comparison and uniqueness, closure compatibility under a further
closed immersion, and composition of direct images on étale test objects.

Statement dependencies and declarations used are:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` (Mathlib).
- `def-weil-closed-immersion`: `AlgebraicGeometry.IsClosedImmersion` (Mathlib).
- `def-weil-open-immersion`: `AlgebraicGeometry.IsOpenImmersion` (Mathlib).
- `def-weil-pbc-etale-site`: `AlgebraicGeometry.Scheme.Etale` and
  `Scheme.smallEtaleTopology` (Mathlib).
- `def-weil-sheaf-of-modules-category`: `CategoryTheory.ringedSiteModules` and
  the concrete `Sheaf ... (ModuleCat A)` encoding.
- `def-weil-pbc-constant-sheaf`: Mathlib `CategoryTheory.constantSheaf`.
- `def-weil-pbc-inverse-image`: `AlgebraicGeometry.Etale.upperStar` and its
  adjunction in `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`.
- `def-weil-pbc-direct-image`: `AlgebraicGeometry.Etale.lowerStar` in the same
  module.
- `def-weil-pbc-extension-by-zero`: `Etale.openImmersionLowerShriek` and its
  adjunction in `...Etale.LowerShriek.OpenImmersion.Defs`.
- `def-nagata-scheme-theoretic-image`: `Scheme.Hom.toImage`, `imageι`, and
  `toImage` from Mathlib's ideal-sheaf subscheme API.
- `pqf-def-locnoeth`, `def-weil-pbc-quasi-compact-scheme`, and
  `def-pc-fibre-product`: the Noetherian, compactness, and pullback APIs.

Edge cases checked are the empty scheme and empty stratum, identity immersion,
closed immersion, open immersion, a nonreduced closed ambient scheme, the zero
finite ring and finite fields, and `Y = X` in the last clause. The canonical
normalizations reduce to the identity in the identity, open, and closed cases;
all three helper isomorphisms remain defined for empty sources.

Searches retained from the original packet found no existing target declaration:

- `msearch.py ... leanfinder "étale closed open extension by zero direct image
  natural isomorphism"`:
  eight ordinary scheme-geometry hits, no étale mixed-extension comparison.
- `msearch.py ... loogle "Etale.finiteOpenComparison, openImmersionLowerShriek, lowerStar"`:
  no Loogle hit; the relevant declarations are upstream.
- `msearch.py ... grep "finiteOpenComparison|openImmersionLowerShriek|etaleLocallyClosedExtension"
  WeilConjectures/SixFunctors`: no duplicate target declaration.
- `rg` over `WeilConjectures/` and project `lean/Sheaf/`: found the upstream
  finite-open APIs and no existing locally closed comparison theorem.
- `grep -rl "lem-sfb-etale-locally-closed-extension-comparison"`: found only
  the two citers audited below and this node. The node has no `statement_change`: its informal statement was retained.

No `STATEMENT-DISPUTED` flag is needed. `scompile.py` compiles the module
cleanly; the theorem proof remains the expected `sorry`.

## Second reading by Q42

Independent maintainer reading of immutable delivery b6744492f53f1815f82903c162413c5425864aac,
2026-10-17. The source and every statement dependency were opened, along with the
actual upstream declarations; this reading does not rely on the previous review.

- Finite commutative coefficients are exactly `[CommRing A] [Finite A]`.
  `A : Type (u + 1)` and `ModuleCat.{u + 1} A` follow the prescribed ordinary
  constant-coefficient etale encoding; no field or nonzero-ring hypothesis is added.
- `[IsNoetherian X]` is Mathlib's locally Noetherian plus `CompactSpace X`.
  Schemes, closed/open immersions, small etale topology, and pullbacks use the
  recorded Mathlib notions. `IsImmersion` is the closed-then-open definition.
- The first conjunct is `IsIso (Etale.finiteOpenComparison ...
  (IsPullback.of_hasPullback g u))`. Its projections are the open map into Z
  and closed map into W. The upstream definition is the open-adjunction
  transpose of the open unit followed by inverse finite base change, precisely
  the specified inverse exchange composite. `IsIso` of a natural transformation
  covers every module sheaf and naturality, rather than just objectwise existence.
- `etaleLocallyClosedExtension a hqa` actually composes open lower shriek along
  `a.toImage` and direct image along `a.imageι`. The image is the kernel-ideal
  subscheme; its factor map is open for quasi-compact immersions. The existential
  `hqa` is a conclusion, not an additional assumption on a. Noetherian X supplies it.
- Every closed-then-open factorization is quantified, with its actual equation
  `h ≫ u' = a`. The isomorphism has the required direction and its whiskering by
  `a^*` agrees with the explicit normalization. This says identity on S under
  the composition, open-unit and closed-counit identifications. Uniqueness is
  valid: the closure extension is fully faithful and its inverse on its image
  is restriction along a. It does not claim restriction is faithful on all sheaves.
- The final clause quantifies every closed i and locally closed b, supplies
  quasi-compactness of b, and identifies `b_! ⋙ i_*` with `a_!`. Its displayed
  normalization first cancels the closed counit for i and then uses that for b.
  The closure universal property and direct-image composition give this map;
  its normalized uniqueness follows by the same essential-image argument.

Sources read: etale-cohomology.tex, lemma-compatible-shriek-push-finite (0GJ1),
lemma-jshriek-open (0F70), and proposition-closed-immersion-pushforward (04CA);
morphisms.tex, lemma-scheme-theoretic-image/definition-scheme-theoretic-image
(01R6/01R7) and lemma-quasi-compact-scheme-theoretic-image (01R8).
The dependency's old wording "largest" is superseded by its `blueprint_update`
and by the kernel-ideal definition; this delivery uses the correct smallest image.
All seven node proof steps are represented in the theorem docstring.

Empty X/S, empty intersections, identity/open/closed immersions, nonreduced
ambient closures, Y=X, zero sheaves, and the zero finite ring are retained.
There is no degree or characteristic restriction. All variables are bound and
`autoImplicit` is false; the u+1 coefficient size is the established small-etale
convention, not an imposed equality between distinct site universes.

Independent rg searches across Mathlib, upstream WeilConjectures, and project
lean/Sheaf found the finite-open API but no complete target theorem. The project
`flatModelEtaleExtension` is a downstream Noetherian-only specialization of the
same composite; it does not supply the general quasi-compact helper interface
or this target theorem. The pro-etale coherence theorem is a different site and
coefficient interface and was not used as a substitute. The worker's three kinds
of search remain recorded above. Read both downstream nodes in the group clone:
`det-sf-flat-model-generation` uses the factorization and closed-composition
clauses, and `lem-weil-finite-duality-site-comparison` uses the generator
identification; both uses hold. No informal statement correction was made.

Mechanical repairs: H8, added source-place and blueprint citations to all three
restriction helper docstrings and made the closure helper citation contiguous.
H11, expanded this second reading to match hypotheses and conclusions explicitly.
Clarified that the docstring's full-faithfulness argument concerns the essential
image. No declaration type, construction, or theorem proof was changed.
The original and fixed signatures equal `lean.statement` verbatim. All definitions
contain real categorical composites; the sole theorem proof is exactly `sorry`.
All Lean lines are at most 100 characters; imports serve the constructions.

Compiler evidence: the original snapshot was checked with scompile.py Q42
lem-sfb-etale-locally-closed-extension-comparison and its exact Lean file on
2026-10-17. Both sandbox and library passes succeeded (2.4 s each), no diagnostics.
The wrapper currently runs the overlay and confirmation on the server; no direct
ssh, global build, live Lean write, delivery, or Git mutation was performed by
this reader. The complete fixed module also passed scompile.py under its exact library module
name: sandbox and library both 2.6 s, exit 0, no diagnostics.

## Returned repair H3

The node text already required a canonical identification restricting to the
identity on the source; the Lean signature had omitted that requirement. This
repair strengthens only the Lean rendering, following Stacks Tag 0GJ1 and its
closure-factorization consequences, by adding explicit adjunction-normalized
restriction equations and uniqueness of the normalized comparison. Citers
audited:

- `det-sf-flat-model-generation` — holds: it uses the open-after-closed
  comparison and closed-composition compatibility, both retained and stronger.
- `lem-weil-finite-duality-site-comparison` — holds: it uses the closure-form
  generator identification, supplied by the corrected normalized comparison.
