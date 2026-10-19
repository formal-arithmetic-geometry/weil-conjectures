## Worker report

Repair of the returned stage-2 delivery at immutable head `a0f2677a3df0`.
The retained packet was inspected first and its prescribed dry run passed mechanically
(`ce5fa2a1b4`, no push). The mathematical self-check still found the maintainer's defects,
so this delivery substantively replaces the incomplete Lean signature and report.
The sandbox node was compared with the current shared node: all fields outside `lean`
are identical. The delivery wrapper refreshes the current `newtargets-dag` base and
builds the delivery in its own worktree; no direct Git operation was run in either
read-only checkout.

`Sheaf.TraceFormula.OrientedNearbySmoothSourcePullback` states
`AlgebraicGeometry.orientedNearby_smoothSource_pullback`. Its conclusion is the
conjunction of invertibility of the specified object-level counit comparison and
`OrientedNearbyCycles.SmoothSourceBaseChangeCompatible h g Λ L`.

Clause-by-clause rendering of the node:

| Node hypothesis or clause | Lean rendering and check |
| --- | --- |
| Schemes S, X, Y and h : X → Y, g : Y → S, f = gh | `{S X Y : Scheme.{u}} (h : X ⟶ Y) (g : Y ⟶ S)`; `f` is written as `h ≫ g`. |
| S Noetherian | `[IsNoetherian S]`, whose class extends `IsLocallyNoetherian S` and `CompactSpace S`. |
| Both maps of finite presentation | `LocallyOfFinitePresentation`, `QuasiCompact`, `QuasiSeparated` instances for each of h and g, exactly the recorded Stacks 01TP convention. |
| h smooth | `[Smooth h]`. |
| Finite commutative Λ | `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`, in the coefficient universe of the recorded D^b_c interface. |
| Λ killed by an integer invertible on S | `[HasInvertibleExponent Λ S]`; this is the existing annihilator/invertibility predicate, with no extra characteristic hypothesis. |
| L in D^b_c(Y_et,Λ) | `L : EtaleDerived Y Λ`, `hL : IsBounded (etaleDatum Y) (Coeff Λ) L`, **and** `hLc : ∀ q : ℤ, ∃ F, Scheme.IsConstructibleEtaleModuleSheaf F ∧ Nonempty (...)`. The linear isomorphism in `hLc` identifies H^q(L), restricted along the constant-ring sheafification unit, with the AsSmall reindexing of the constructible ordinary small-etale module sheaf F. This is the `NearbyProperHyperdescent` hKc transport, at Y instead of X, not an assertion that boundedness implies constructibility. |
| hbar induced by (h,1_S) | `squareModules g (h ≫ g) h (𝟙 S) (by simp)`, obtained from the existing `squareMorphism`/`squareLift`. |
| The ordinary counit-defined comparison | `baseChange g (h ≫ g) h (𝟙 S) (by simp) Λ L`, literally the dependency's adjunction transpose of `nearbySquare` followed by the counit. |
| Isomorphism of objects of the whole vanishing topos | The first conjunct is `IsIso` of that arrow in `VanishingDerived (h ≫ g) Λ`; it is not a property of a sliced cone. |
| No Ψ-goodness hypothesis | The signature has no `IsPsiGood` binder or assumption. |
| Compatibility for further Cartesian base changes of S | The second conjunct expands to a quantifier over every `c : S' ⟶ S` and every Cartesian diagram X',Y',h',g',a,b above it, with `ha : a ≫ h = h' ≫ b`, `hb : b ≫ g = g' ≫ c`, `IsPullback a (h' ≫ g') (h ≫ g) c` and `IsPullback b g' g c`. There is no hypothesis on S'. Its conclusion is the required pasting equality, not the identity-square invertibility assertion. |

In the final clause, a = u, b = w. Read composition in the file from left to right.
The left side is
`v_f^*(β_h(L)) ≫ β_a(h^*L) ≫ RΨ_(h'≫g')(α_et,L)`.
The right side is
`α_V,RΨgL ≫ hbar'^*(β_b(L)) ≫ β_h'(w^*L)`.
Thus it says exactly β_u after v_f*β_h equals β_h' after hbar'*β_w,
with the necessary canonical endpoint identifications. The equality has the same
source and target; it uses the ordinary `baseChange` arrow four times.
The two `IsPullback` conditions describe arbitrary chosen presentations of the base
changes, so canonical pullback objects and all isomorphic presentations are included.

The missing identifications are constructed in this module, not assumed:

- `squareCompositeFirst` and `squareCompositeSecond` compose the actual projection
  identifications of `squareLift`, using `etaleComposition` (itself obtained from
  `MorphismProperty.Over.pullbackComp` and the AsSmall equivalences).
- `smoothSourceVanishingSquare_existsUnique` states the unique isomorphism between
  the direct images of hbar v_f and v_g hbar', fixing **both** projection equations.
  The equations explicitly include ha, the identity laws on c, and those canonical
  site composition maps. Its proof docstring explains how the oriented-product
  universal property applies to the two lifts of the same oriented cone. This is the
  construction asserted in this node's proof step 5, not an independent new notion.
- `smoothSourceVanishingSquare` takes the witness of that unique specification.
  It does not choose from a bare `Nonempty` or an unconstrained existence assertion.
- `smoothSourceEtalePullSquare` is `AdicSites.derivedSquare` applied to the
  inverse-image mate of `squareDirect h h' a b ha`. That direct-image square is
  constructed from etale site composition and the equality ha.
- `smoothSourceVanishingPullSquare` similarly applies the inverse-image mate to the
  unique oriented-product square and then the generator-normalized derived module lift.
- `SmoothSourceBaseChangeCompatible` only expands the node's final compatibility
  clause with these specified identifications. All helpers are recorded in
  `lean.declarations` under the item's own blueprint tag.

Universe diagnosis (returned H3): the base nearby-cycle and comparison constructions
are universe-polymorphic; all the comparison helpers here retain `universe u v` and
`Λ : Type v`. The **bounded constructible input** interface, however, is the recorded
`AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible` in
`WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes`, whose full source
was read using `scompile.py --source`. It explicitly takes `Λ : Type (u + 1)` and
`Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)` for `Y : Scheme.{u}`.
The input binder follows that existing D^b_c convention. `Coeff.{u,u+1} Λ` is
`ULift.{u+1} Λ`, canonically ring-equivalent to Λ in that same universe; the AsSmall
site has size u+1 as well. A finite coefficient ring always has a representative in
this coefficient universe, so this convention excludes no finite coefficient ring
up to the canonical coefficient equivalence. No equality of independent site or
coefficient universes was added to obtain a comparison API. The file documents this
size convention explicitly; it is not attributed to `nearbyCycles`.

Dependency declarations used, with their interfaces read:

- `def-trf-oriented-nearby-cycles`: `Sheaf.Paper.OrientedNearbyCycles`, including
  `EtaleDerived`, `Coeff`, `IsBounded`, `squareLift`, `squareMorphism`, `etaleComposition`,
  `squareDirect`, `nearbyCycles`, `nearbySquare`, `baseChange`, `etaleModules`,
  `squareModules`, and `orientation_universal`.
- `def-weil-pbc-constructible-complexes`:
  `WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes`,
  `AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible` and its full
  subcategory. Its defining boundedness and degreewise constructibility clauses are
  expanded in hL/hLc through the existing AsSmall/Coeff transport. Its constructibility
  predicate is `Scheme.IsConstructibleEtaleModuleSheaf`, not the older stalk predicate.
- `pqf-def-locnoeth` and `def-weil-pbc-quasi-compact-scheme`:
  `Mathlib.AlgebraicGeometry.Noetherian`, `IsLocallyNoetherian`, `IsNoetherian`, and
  `CompactSpace`; the last two supply precisely Noetherian S.
- `def-weil-pbc-scheme-conventions`: no single declaration; its finite-presentation
  convention is rendered by the three standard morphism classes above.
- `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, `Smooth`.
- The stated proof dependencies are imported: `OrientedPointCohomology`,
  `OrientedProductPointsConservative`, `OrientedProductLargeSites`, and Mathlib's
  `mateEquiv_vcomp`/`mateEquiv_hcomp` for `lem-weil-pbc-mate-pasting` clauses 1 and 2.
  The still-unstated strict-local and local-acyclicity lemmas remain named in the
  complete five-step theorem proof docstring.

Source check: reopened [Orgogozo Section 9.3, printed p. 22](https://www.cmls.polytechnique.fr/perso/orgogozo/articles/Modifications%20et%20cycles%20proches%20sur%20une%20base%20g%C3%A9n%C3%A9rale.pdf),
including the smooth-locus use of local acyclicity; read the current node's full five
proof steps and the current blueprint unit `sk-i-curve-zero`. The additional canonical
maps formalize the node's step 5 using ILO XI 1.4--1.5, 1.9 and 4.3.

Edge cases checked against the definitions before finalizing the signature:
identity h; identity g; empty X or Y; the zero finite ring; L = 0 and arbitrary shifts
of a constructible sheaf; identity base change c; a general c with no Noetherian,
finite-type, or Ψ-goodness condition on S'; and arbitrary isomorphic presentations
of the two Cartesian base-change squares. In particular the identity square only
specifies β_h; it does not replace the all-base-changes compatibility quantifier.
Boundedness and constructibility remain separate conditions even for these cases.

Searches retained from the original packet:

- `msearch.py ... leanfinder "Smooth source pullback of the oriented nearby cycle complex equals nearby cycles of the pulled back complex"`: no exact match (ordinary pullback/manifold results).
- `msearch.py ... loogle "Sheaf, IsSmooth"`: no match.
- `msearch.py ... grep "nearby.?cycle|vanishing.?topos|oriented.?product" AlgebraicGeometry`: no Mathlib match.
- `rg` in both named source trees and `lean/Sheaf` found the oriented nearby-cycle
  framework and ordinary smooth base change, but no theorem giving this full statement.

Repair searches:

- `msearch.py ... leanfinder "Canonical composition of oriented nearby cycle base change comparisons under smooth source pullback"`: 8 hits for ordinary scheme/presheaf module pullback composition and manifold vector fields; no oriented nearby-cycle comparison or vanishing-topos square identification.
- `msearch.py ... loogle "nearbyCycles, baseChange"`: 0 hits; Mathlib does not know
  the project-specific identifier nearbyCycles.
- The same Mathlib grep query above: 0 hits.
- `rg` for `squarePsi`, `squareMorphism`, `baseChange`, `AsSmall`, and
  `IsConstructibleEtaleModuleSheaf` located and read `NearbyProperHyperdescent.hKc`,
  `NearbyClosedImage.hKc`, the constant-module square normalization in
  `CompletionMateComparison`, and the oriented-product uniqueness and site composition
  definitions. No existing vanishing-topos square composition identification was found.
- `rg` for all eight delivered declaration names in Mathlib, upstream WeilConjectures,
  and the shared `lean/Sheaf` returned no collision. No new independent notion or
  dependency replacement is introduced, and no node statement is corrected.

Both the helper construction and the full delivered file compile cleanly with the
prescribed `scompile.py` wrapper, within its 60-second limit. Every theorem body is
`sorry`; every definition has real data. The only choice of constructed isomorphism
is determined uniquely by the displayed projection equations. The theorem docstring
now supplies all five proof steps with their dependency references.

## Second reading by Q65

This is a fresh clause-by-clause self-check of the node and repaired file, performed
in this worker session (the dispatcher explicitly prohibits starting other agents).

1. S, X, Y and the typed maps h,g match the node; f is h ≫ g. IsNoetherian includes
   exactly local Noetherianity and quasi-compactness. Both finite-presentation
   hypotheses have all three recorded factors, and h has Smooth.
2. CommRing, Finite and HasInvertibleExponent render exactly the coefficient
   assumptions. I read the complete recorded D^b_c definition to justify the u+1
   coefficient convention, and kept all new comparison helpers polymorphic in v.
3. The old hL only bounded L. I added hLc for **every integer degree**, requiring a
   constructible module sheaf with a **linear** isomorphism to transported H^q(L).
   No claim that boundedness covers constructibility remains.
4. The map in IsIso is still exactly baseChange for (h,1_S); its domain is hbar*RΨ_g L
   and target RΨ_(h≫g)h*L, both whole vanishing-topos derived objects. No Ψ-goodness,
   sliced comparison or cone-vanishing condition has replaced this conclusion.
5. I unfolded the new second conjunct and checked every arrow's domain/codomain.
   The all-S' Cartesian diagram is separate from the identity-source square. The
   equality contains v_f*β_h followed by β_u on the left, and hbar'*β_w followed by
   β_h' on the right, with the canonical etale target identification and vanishing
   source identification. The two Cartesian conditions cover exactly base changes
   of X and Y; ha makes h' the induced source map. No condition on S' was added.
6. I checked the new identifications against the universal-property normalization:
   squareCompositeFirst/Second use squareLift and etaleComposition; the unique
   vanishing square fixes both projection maps, and derivedSquare uses their
   inverse-image mate. They are not arbitrary isomorphisms or Nonempty choices.
7. I compared the proof docstring against all five node steps. It now includes the
   strict-local tubes with S_(t), local acyclicity, point conservativity, and the
   general base-change mate-pasting step. The earlier report's identity-square
   misreading is removed. All returned H3, H8 and H11 points are addressed.

No STATEMENT-DISPUTED issue remains, and no natural-language node field changed.

## Second reading by Q31

Independent maintainer reading, 2026-10-18, of immutable delivery
`af03b46aa1a61a41c37f4e33746ce11b70af9483`. The earlier Worker report and Q65
self-check above describe the delivered version; the corrections below supersede
its statements about the current dependency record and imports.

I opened the packet, item, all six statement-dependency records, delivered module,
module/declaration docstrings and the actual declarations used. Clause checks:

| Node clause | Lean and verdict |
| --- | --- |
| S,X,Y schemes and X → Y → S | Scheme.{u}, h, g; composition is h ≫ g. Exact. |
| S Noetherian | IsNoetherian extends IsLocallyNoetherian and CompactSpace. Exact. |
| h,g finite presentation | Each has LocallyOfFinitePresentation, QuasiCompact, QuasiSeparated, as the recorded convention requires. Exact. |
| h smooth | Mathlib Smooth, the affine-local smooth-ring-map definition. Exact. |
| finite commutative coefficients with invertible annihilator | CommRing, Finite, HasInvertibleExponent. The latter asks for a positive annihilating integer unit in global sections; negative annihilators may be replaced by their absolute values. Exact. |
| L bounded constructible | The former hL and hLc are precisely the two conjuncts of the now-recorded IsBoundedConstructible Y Λ L: unfold orgogozoModuleSections and orgogozoConstantScalars. The isomorphism is ModuleCat-linear, not merely an underlying-set isomorphism. Fixed to use that predicate directly. |
| hbar from (h,1_S) | squareMorphism/squareModules g (h ≫ g) h (𝟙 S), built by squareLift from the canonical orientation. Exact. |
| ordinary comparison is an isomorphism | IsIso of the dependency's actual baseChange counit mate in VanishingDerived (h ≫ g) Λ. It is an object-level assertion, with no sliced cones or Ψ-goodness assumption. Exact. |
| further Cartesian base changes | SmoothSourceBaseChangeCompatible quantifies over all S', X', Y', a,b,c,h',g',ha,hb and the two IsPullback witnesses. There is no Noetherian or finiteness hypothesis on S'. Exact. |

For the compatibility equation, the left path is v_f*β_h, then β_a, then RΨ of
the etale endpoint identification. The right path is the vanishing endpoint
identification, then hbar'*β_b, then β_h'. Both have the same source and target.
The projection-normalized unique isomorphism supplies the vanishing identification;
the etale identification uses squareDirect and the published derivedSquare.
The equations in smoothSourceVanishingSquare_existsUnique fix both projections,
including ha and the two identity laws on c. ILO XI 1.4 uniqueness applies to the
same oriented cone. Thus this is an admissible uniquely determined helper, not a
hollow choice of an unspecified map. Both theorem bodies are only sorry; the six
definitions contain real compositions, a uniquely specified choice, or a predicate.
All eight declarations are listed in lean.declarations with source/blueprint docs.
The main proof docstring matches all five node steps, including S_(t) tubes and
mate pasting for arbitrary S'.

Sources read: Orgogozo §9.3, printed p.22 (PDF p.21), especially the smooth-locus
identification; ILO XI 1.1, 1.3–1.9 and 4.1–4.3; Stacks 0GJQ, 0EZU and 0EYU.
The general constructible-complex assertion follows the node's smooth base change
and bounded devissage argument; the Orgogozo display itself uses constant
coefficients. No extra excellence, properness, separatedness, or Ψ-goodness is
needed. The strict-local tube is formed with S_(t), not just the geometric fibre.
The affine map Y_(y) ×_{S_(s)} S_(t) → Y_(y) is qcqs, as needed by 0EZU/0EYU.

Universes: Scheme.{u}, module sheaves in u+1 and Λ : Type (u+1) follow the recorded
bounded-constructible interface. Coeff is the canonical ULift ring and AsSmall is
a site-equivalence transport. No independent site universes are equated; the
square helpers retain arbitrary v. Every finite coefficient ring is represented
in this convention. All variables/universes are explicitly bound.

Edge cases checked: X or Y empty, S empty, zero finite ring, L=0, arbitrary shifts,
h or g identity, h etale, identity c, non-Noetherian S', and isomorphic presentations
of both Cartesian squares. No Nonempty scheme, nonzero ring or positive relative
dimension condition excludes these cases. IsPullback conditions determine the
induced h' uniquely via the Y' pullback; no additional restriction is hidden there.

Searches: independent rg searches for nearby/smooth, vanishing/pullback and all
helper names across project Sheaf, upstream WeilConjectures and Mathlib found
only this module and relevant framework/consumers, no distinct duplicate theorem.
An independent msearch leanfinder query “smooth inverse image commutes with
vanishing topos nearby cycle functor” returned eight manifold/open-immersion hits,
none this assertion. The worker's LeanSearch, Loogle/LeanFinder and grep records
are present. The canonical constructibility transport already exists and is reused.

Findings and mechanical fixes:

- H1/H11: the exact Q31 second-reading heading contained only a disclaimer. This
  independent reading replaces the placeholder while retaining the Worker report.
- H4/H9 dependency-interface hygiene: import the recorded
  Sheaf.TraceFormula.BoundedConstructibleTransport and use its predicate directly,
  replacing the definitionally identical expanded hL/hLc binders. No second notion,
  changed category, coefficient restriction, or new hypothesis results.
- H9: import the now-stated proof modules OrientedNearbyStrictLocalDescription
  and SmoothSourceConstructibleLocalAcyclicity; the old report called them unstated.
- H2: supply the complete updated lean record with the exact normalized theorem
  signature. No natural-language statement, dependency list or proof is changed;
  no §1(C) correction or citer audit is required.

The route-pivot dropped list has empty intersection with the item's statement and
proof dependencies. The named repair-note path is absent on origin/newtargets-dag;
there is no route-pivot note to compare. This is the ordinary derived/K-injective
route, with no infinity/dg/model-category machinery and no pro-etale substitute.
No live files, repository, branch or global build were changed.

Compilation: the immutable file passed scompile.py's sandbox and library invocations
in 5.0 s and 18.3 s, with no diagnostics. The corrected file passed the same wrapper separately as sandbox (5.3 s) and
library module (27.2 s), exit code 0, no errors or warnings, under the default
60-second per-file limit.
