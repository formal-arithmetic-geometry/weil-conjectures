## Worker report

The module `Sheaf.AlgebraicGeometry.RelativeDualityPolynomialChart` states
`AlgebraicGeometry.exists_relativeDualityPolynomialChart`. Its only postponed proof is
that theorem. The helper definitions in the six definition modules below have real data. They define chart and coefficient
objects, the actual coinduced models, the prescribed normalization predicates, the
presentation system, canonical restriction mates, normalized affine realization and
their compatibility equations. No target or natural-language statement
has been changed.

Hypotheses and clauses are rendered as follows.

- Schemes and morphism: `{X S : Scheme.{u}} (f : X ⟶ S)`.
- Separated, flat, locally finitely presented: `[IsSeparated f] [Flat f]
  [LocallyOfFinitePresentation f]`. Properness, quasi-compactness, regularity and a
  dimension bound are not imposed.
- Locally Noetherian base: `[IsLocallyNoetherian S]`, precisely the existing affine-local
  Noetherian condition. There is no global Noetherian hypothesis.
- Existence of the pair: the conclusion quantifies `K : schemeDerivedCategory X` and
  the specified diagonal morphism `ξ` on the entire `pullback f f`.
- Pseudo-coherence, locally finite relative Tor amplitude, and invertibility of
  multiplication by ξ: `IsCoherentRelativeDualizingPair f K ξ`. This is the existing
  predicate, not a new definition: its three conjuncts are `Scheme.IsPseudoCoherent`,
  the pointwise-open `Scheme.HasFiniteTorDimensionOver` condition, and
  `IsIso (relativeDualizingClassMap f K ξ)`. That map is the transpose of the actual
  diagonal multiplication followed by ξ under the existing tensor–Hom bijection.
- The chart quantifier ranges over `RelativeDualityPolynomialChart f`. Its fields are
  an arbitrary open `U : X.Opens`, `n : ℕ`, an ambient scheme P with an open immersion
  into `AffineSpace (ULift (Fin n)) S`, a closed immersion `i : U.toScheme ⟶ P`, and
  the factorization equality. It has no regular-sequence, constant-dimension,
  invertibility or complete-intersection field.
- The coefficient is the sheaf exterior power of the existing relative differential
  sheaf, placed in degree `-n` by `[n]`. This is
  `RelativeDualityPolynomialChart.coefficient`.
- The model has its natural O_U-action: `polynomialChartCoinduction i` selects the
  ordinary functor in the existing **proved** sheaf-coinduction adjunction. That
  theorem specifies its multiplication/precomposition action, its underlying internal
  Hom, and evaluation-at-one counit. The right derived functor of this fixed functor
  computes `C.model hAdd`. Thus the model is an object over the actual ringed space
  `(P, i_*O_U)`, not an unspecified ambient derived object with a forgotten action.
  The conclusion identifies it with the derived direct image of `K|U` to that same
  ringed space. A closed immersion gives the usual equivalence with modules on its
  closed source. Forgetting the action gives precisely
  `RHom_P(i_*O_U, Omega^n[n])`.
- `PolynomialDualityChartAtlas.exactData` supplies additivity of coinduction and
  finite-limit/colimit preservation of the scalar-forgetting functor. These are
  conclusion data, not additional hypotheses on f. `identification` supplies a
  specified isomorphism on every chart, with all these identifications in one atlas.
- Affine models are quantified over every `R, A : Type u`, their commutative-ring and
  algebra structures, open charts `jA`, `jR`, and the commuting factorization square.
  The conclusion supplies one M with `K|Spec A ≅ polynomialAffineTilde A M`,
  shared by **all** polynomial presentations on that affine chart.
- The `identification` field of `PolynomialDualityPresentationSystem` includes every
  finite polynomial surjection p with `p.comp C = algebraMap R A`. Its target is
  `polynomialDualityModel n p`, namely actual derived coinduction of
  `polynomialDualityCoefficient R n`. Thus the source action is retained in D(A).
- One-variable refinement: `polynomialDualityRefinement R n g` evaluates the **last**
  variable at g and retains all old variables. `polynomialDualityEquationMap` is
  multiplication by `X_last - rename castSucc g` on the top-form coefficient line.
  `IsPolynomialDualityContraction` requires an actual short exact sequence with that
  multiplication map and a quotient map carrying the ordered new volume to the old
  volume. The adjoint of its shifted `ShortExact.singleδ` must equal `e.inv`.
  Consequently the map is fixed by the two-term resolution; an arbitrary isomorphism
  cannot satisfy the normalization. Since wedging the old n differentials with dg is
  zero, the last differential can equivalently be written d(t-g). For n=0 this is
  exactly dual(t-a) tensor d(t-a) mapping to 1.
- `polynomialDualityRefinementMap` uses the two actual derived-coinduction counits and
  the exact restriction-of-scalars composition comparison. The `refinement` field
  equates the presentation transition with this map for every g, including different lifts.
- Coordinates and signs: `IsPolynomialDualityCoordinateComparison` prescribes the
  coefficient map on every wedge of universal derivatives. It includes all polynomial
  algebra automorphisms, hence permutations and their determinant signs. The shifted
  boundary, shift addition isomorphism and derived adjunctions use the existing
  cohomological conventions. Iteration uses composition of these normalized maps.
- Comparisons and composition: `PolynomialDualityPresentationSystem.comparison`
  compares any two presentations through their shared M. The intervening
  identification cancels on composition. The refinement/coordinate fields identify
  these comparisons with the independently specified counit maps. Common polynomial
  refinements therefore give the same comparison after further refinements.

- Geometric restrictions: `PolynomialDualityChartAtlas.restriction` equates restriction
  of its specified identification with an independently defined model map. The inputs
  are open immersions r on source charts and a on polynomial ambients, the actual
  ringed-space algebra map b, and the two commuting direct-image squares. The coefficient
  isomorphism q must send **every local wedge** to the wedge under the canonical
  differential restriction (`IsPolynomialChartCoefficientRestriction`). The model arrow
  `polynomialGeometricRestriction` is the coinduction adjunct of the restriction of its
  evaluation counit. The other side `polynomialGeometricSourceRestriction` uses the
  original unit of exact open restriction and the native restriction composition map.
  Neither arrow uses the atlas identification. The equation is therefore nontrivial.
- The pullback F on the direct-image algebra space can be any left adjoint to its
  actual derived pushforward; the formula uses that same adjunction on both sides.
  Its exchange map is the mate of the actual direct-image square. On open localization
  squares this map is invertible. Its inverse occurs explicitly in the Hom comparison;
  an arbitrary isomorphism between Hom models is never substituted for it.
- Affine restrictions: `IsPolynomialAffineAtlasCompatible` ties the **composite** of e
  and each F.identification to the specified geometric atlas identification. On an
  affine chart, `IsPolynomialTildePushforward` fixes the ordinary tilde/pushforward
  isomorphism by the actual tilde/Gamma unit. `IsPolynomialDerivedImageComparison` fixes
  its derived version on EVERY homotopy complex by the original right-derived units.
  `IsPolynomialAffineCoefficient` fixes the top-form comparison on the ordered global
  volume. `polynomialAffineModelMapForModule` is then the sheaf coinduction adjunct of the actual
  module coinduction evaluation. It has no K, ξ, e or F input. The compatibility equation
  equates the atlas identification with the resulting expression containing e and
  F.identification. Localizing two such equations and applying atlas.restriction forces
  the affine localization square to commute. A presentation-dependent unit rescaling
  now violates these equations.
- Identity and composition: exact restriction uses native `restrictFunctorId` and
  `restrictFunctorComp`; the direct-image squares are made with the comparisons
  normalized by their original right-derived units. Their mates and evaluation counits
  compose. Applying the atlas equation twice identifies a two-step model restriction
  with the direct restriction through the native composition isomorphism, and the
  identity case identifies it with the native identity. Similarly affine realization
  identifies F.comparison with the same geometric transition, so its identity/cocycle
  cancellation is the canonical comparison cocycle, rather than a free family of arrows.


The affine exactness and composite-image additivity proofs in the compatibility clause
are existential proof data. They express only properties of the specified native
functors; no additional geometric or algebraic hypotheses are introduced. This avoids
repeated expensive native/shared-category proof transports during elaboration.

The localization choices for ringed spaces and their open sites are explicit, with
independent universes u and w. Ordinary module derived categories use their existing
Grothendieck localization in universe u. There is no equality imposed between site
object/morphism universes. All variables and universes are explicitly bound, and
`autoImplicit` is false.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsSeparated` (not `IsProper`).
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`: `LocallyOfFinitePresentation`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, used through the locally
  Noetherian dependency; no new ring Noetherian assumption is introduced.
- `WeilConjectures.AlgebraicGeometry.DerivedCategory`: `schemeDerivedCategory`.
- `WeilConjectures.AlgebraicGeometry.DerivedPullback`: `derivedPullback`.
- `WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex`: `Scheme.IsPseudoCoherent`.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`: the recorded generic Hom API,
  used through the existing coherent-pair construction and its canonical Hom.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Mathlib.LinearAlgebra.ExteriorAlgebra.Basic`: `exteriorPower`, `exteriorPower.ιMulti`.
- `Mathlib.RingTheory.Kaehler.Basic` and `.Polynomial`: `KaehlerDifferential`, its
  universal derivation and the polynomial-differential interpretation.
- `Sheaf.AlgebraicGeometry.RelativeDualizingPair`: `IsCoherentRelativeDualizingPair`,
  `relativeDualizingDiagonalComplex` and the canonical class-map construction.
- `WeilConjectures.AlgebraicGeometry.Modules.Differentials`:
  `Scheme.Hom.relativeDifferentials`.
- `Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf`: `Scheme.Modules.exteriorSheaf`.
- `Sheaf.Algebra.Homology.DerivedCoinductionAdjunction`: `ModuleCat.derivedCoinduction`,
  `ModuleCat.derivedCoinductionAdjunction`.
- `WeilConjectures.AlgebraicGeometry.DirectImageAlgebraDerivedCategory`:
  `directImageAlgebraSpace`, `toDirectImageAlgebraSpace`.
- `WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage`:
  `RingedSpace.derivedModuleDirectImage`.
- `WeilConjectures.AlgebraicGeometry.SheafCoinductionAdjunction`:
  `sheafHom_restrictScalars_adjunction` with its full action and counit specification.
- `Mathlib.AlgebraicGeometry.Modules.Tilde`: `tilde`, `tilde.functor`, `tilde.adjunction`,
  `tilde.toOpen`. `polynomialAffineTilde` derives this actual exact functor, and does not
  use the unowned `relativeDualizingAffineTilde` definition.
- `WeilConjectures.AlgebraicGeometry.TildePreservesFiniteLimits`:
  `tilde_preserves_finite_limits`.
- `WeilConjectures.AlgebraicGeometry.Modules.PullbackTilde`:
  `Scheme.Modules.pushforwardSpecMapCompΓIso` (identity on global-section elements).
- `WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImageComposition`:
  `RingedSpace.exists_derivedModuleDirectImageComposition`, including its all-complex
  original-unit normalization.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory`:
  `Functor.rightDerivedFunctorIsoMapDerivedCategory`, exact derived adjunctions.
- `Mathlib.AlgebraicGeometry.Modules.Sheaf`: native `restrictFunctor`,
  `restrictAdjunction`, `restrictFunctorComp`, `restrictFunctorCongr`, `restrictAppIso`.
  All restrictions are actual sectionwise open restrictions, with native adjunctions.
- `Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle`: `ShortExact.singleδ`.

Every already-recorded proof dependency is imported with an ordinary `import`; all
statement dependencies are imported publicly. The theorem docstring follows all nine
natural-language proof steps, including the diagonal gluing off its closed support,
augmented-resolution lift homotopy and the common-refinement argument.

Edge cases checked before writing and again in the second pass:

1. The empty scheme/open/chart is allowed; the asserted complexes are zero there.
2. n=0 uses the empty exterior wedge, Omega^0 and shift zero; refinement still gives
   the one-variable evaluation exact sequence.
3. The zero ring is allowed; no nontriviality or domain binder occurs. The monic
   graph equation exactness is also valid in this case.
4. Non-lci flat finite presentations and varying fibre dimensions are included.
5. X and S need not be quasi-compact and there is no finite affine-cover binder.
6. Every g is included; neither a preferred lift nor uniqueness of a presentation is
   assumed. Polynomial automorphisms include coordinate permutations.
7. The diagonal class is on the full fibre product, and relative Tor bounds are
   pointwise local, not a single bound over a non-quasi-compact scheme.

Searches for an existing statement:

- `msearch.py ... leanfinder "relative dualizing complex polynomial chart derived Hom
  top differentials and canonical refinement comparison"`: eight hits, concerning
  Kaehler differential polynomial equivalences, submersive-presentation differential
  maps and presheaf differential restrictions. None states coherent relative duality.
- `msearch.py ... loogle '"dualizing"'`: zero hits.
- `msearch.py ... grep 'relativeDualiz|RelativeDualiz|dualizing' AlgebraicGeometry`:
  zero Mathlib hits.
- `rg -l 'RelativeDualiz|relativeDualiz|relative_dualiz'` over the project and upstream
  algebraic-geometry sources finds the existing pair, rigidity and affine comparison
  modules. Their signatures were read in full. They concern supplied pairs and
  comparisons; none supplies the global existence plus polynomial normalization.
- `rg` for this node id and for `polynomialDuality`, `RelativeDualityPolynomial` in
  the upstream sources finds no existing declaration of the item or name collision.
- The DAG already owns coherent-pair data, derived coinduction, relative differential
  sheaves, sheaf exterior powers, direct-image algebra spaces and ringed-space derived
  direct images. These existing definition nodes were added to stmt_deps and reused.
  The six new definition nodes below own the additional comparison data packages.

Sources read directly from the supplied Stacks checkout: duality.tex Definition 0E2T
and existence/gluing proof 0E2X; dualizing.tex Section 0BZI and its canonical coefficient
footnote, and the full one-variable/common-refinement proof 0BZJ. No mathematical
statement fault or STATEMENT-DISPUTED issue was found.

## Repair of return L

F1: replaced bare pointwise geometric model existence by the shared
`PolynomialDualityChartAtlas`, with the canonical restriction equation. Added the affine
compatibility equation described above. The affine e and presentation identifications
are no longer independent of the geometric model identifications. This follows the
return's alternative of specifying canonical model restriction equations, rather than
introducing a second construction of ξ for each model.

F2: deleted the unused free-arrow helper `polynomialDualityRestriction`. Its replacement
is the actual mate of the independently normalized direct-image square and evaluation
counit, and this replacement occurs in the atlas restriction field. The presentation
system itself now occurs in `IsPolynomialAffineAtlasCompatible`, which uses its
identifications. Thus its derived comparisons control the geometric gluing.

F3: added the existing coinduction-adjunction node to stmt_deps. Removed all use of the
plain `relativeDualizingAffineTilde` definition. The new affine realization uses native
Mathlib tilde termwise, with its real adjunction unit and the existing exactness lemma;
its source nodes and the proved affine global-sections comparison node are cited in
stmt_deps. The coinduction functor and its adjunction are selected together from one
proved witness; its normalization field retains the underlying Hom identification,
the multiplication/precomposition action and evaluation-at-one counit specification. No data is selected from a sorry.

Consumer validation: reread `lem-trf-flat-lci-canonical-adjunction`, proof steps 5–6.
Step 5 uses atlas.identification to obtain the actual action-bearing Hom model. For
step 6, atlas.restriction provides the independently normalized restriction comparison,
and affine compatibility identifies its chart realization with the presentation system.
The existing refinement and coordinate equations therefore compute the same transition
used on geometric overlaps. The last-variable boundary normalization and the ordered
wedge normalization still give the determinant contraction needed in that step.

Additional repair searches: leanfinder for “Canonical restriction comparison for relative
duality polynomial chart models by coinduction adjunction and affine associated sheaf”
returned eight open-restriction and tilde-section lemmas, not the atlas compatibility
statement. Loogle `AlgebraicGeometry.tilde.adjunction` returned that adjunction and its
invertible-unit instance. Source grep found the existing normalized direct-image
composition and affine global-sections comparison used here; no existing chart atlas
or coinduction-restriction construction matched this statement. Mathlib grep for `coinduction.*[Rr]estrict|[Rr]estrict.*coinduction|[Dd]uality.*[Cc]hart`
in AlgebraicGeometry returned zero hits. The new helper packages are the definition nodes listed below; their primitive component
maps reuse the existing nodes.

## Second reading by Q42

A fresh second pass by this dispatcher-started worker reads the repaired statement
against Stacks 0E2T, 0E2X, 0BV2, 0BZI and 0BZJ, and checks the consuming lci proof's
steps 5–6. No other agent was started. The geometric hypotheses, full-product diagonal
class, pair predicate, chart type, action-bearing model, monic graph exact sequence,
boundary contraction, lift quantifiers, coordinate determinant normalization and
independent localization universes are retained. The previous report's assertion that
an unused free-arrow constructor imposed compatibility was incorrect; the repaired
statement instead contains the actual independent restriction and affine realization
equations. Their sources, targets and inverse directions have been checked separately.

The normalization of ordinary σ is a tilde/Gamma adjunction equation, derived τ is
constrained on every homotopy representative, and q sends the polynomial volume to
the wedge of the images of the actual coordinate functions. The affine model comparison
is defined from module evaluation and the sheaf coinduction adjunction before any atlas
identification is supplied. The atlas restriction equation compares it to restriction
of K; the affine compatibility equation makes F's presentation identifications the
ones used by that atlas. All equations include zero variables and empty/zero charts.
No mathematical hypothesis, original node statement or proof plan has been changed.

Validation is performed with the prescribed scompile.py and deliver2.py wrappers.

## New nodes

`def-trf-polynomial-duality-presentation-data`, module
`Sheaf.AlgebraicGeometry.PolynomialDualityPresentationData`, owns the arbitrary geometric
chart, top differential coefficients, actual coinduction model, monic graph contraction,
coordinate normalization and polynomial presentation system. Its definition statement
spells out those data and equations without asserting existence. It uses the existing
coinduction, differential and exterior-power nodes. Its source is Stacks 0BV2 and the
normalized polynomial calculation in 0BZI–0BZJ. The package was not an existing separate
DAG definition or Mathlib package; its searches are recorded in the node.

`def-trf-polynomial-duality-restriction-atlas`, module
`Sheaf.AlgebraicGeometry.PolynomialDualityRestrictionAtlas`, owns the geometric atlas equation and the differential/coefficient restriction. The independently
normalized categorical mates have their own primitive definition owner below. It builds on the first
node, native exact open restriction, the actual evaluation adjunction and the proved
original-unit direct-image composition. Its source is 0E2X and the restriction of the
0BV2 Hom model. The same search pass found the component APIs but no such atlas package.

`def-trf-polynomial-duality-affine-atlas-comparison`, module
`Sheaf.AlgebraicGeometry.PolynomialDualityAffineAtlasComparison`, owns coefficient volume normalization,
the actual affine model arrow for any ambient affine module coefficient, and the source
restriction unit. It builds on the restriction atlas and native tilde, global sections and
coinduction. Its source is the affine comparison 0E2U used in 0E2X, with 0BZI's volume
normalization. The searches found its existing primitive adjunctions, but no package
imposing this equation. These definition modules contain no postponed proofs.

`def-trf-polynomial-duality-affine-compatibility`, module
`Sheaf.AlgebraicGeometry.PolynomialDualityAffineCompatibility`, owns the full and
principal-open compatibility predicates. On P_h it uses the concrete localization ring
and the quotient Q=P[t] -> P_h, t -> h inverse. Multiplication by ht-1 gives the actual
two-term resolution. The normalized volume quotient is h inverse times the old localized
volume, since dx wedge d(ht-1)=h dx wedge dt. Its shifted boundary defines the coefficient
contraction; the two actual coinduction counits then compare the presentation model over
Q with the localized ambient model over P_h. The compatibility equation uses exactly
this composite with F's identification for Q. This closes the principal-open case in
which localizing the source requires a new inverse coordinate. Sources: 00CM and 0C0H,
and the 0BZI–0BZJ differential normalization. The existing localization definition node
is cited; the comparison package itself was not already a DAG definition.

The second reading explicitly checks the principal-open case: h=1 recovers a redundant
inverse coordinate, h=0 gives the empty ambient chart, and n=0 still has the same shifted
boundary formula. For arbitrary h, the localized top coefficient is ordinary scalar
extension of the original exterior line, with volume one tensor the old volume. Thus
all geometric principal restrictions are tied to the affine presentation system on the
smaller source, rather than just to another bare geometric isomorphism. These principal
charts form a basis of every open polynomial ambient, so the canonical restriction
and normalized refinement comparisons control the general geometric chart transitions.

The definition packages are separate files so that each can compile independently
under the unchanged 60-second bound. Their declarations were moved, not duplicated;
all blueprint ownership markers and lean.declarations records were updated. The original
module contains only the existence theorem and its complete proof plan. The second
reading covers each definition-node statement together with its owning module.

`def-trf-polynomial-duality-restriction-primitives`, module
`Sheaf.AlgebraicGeometry.PolynomialDualityRestrictionPrimitives`, owns exact native
open restriction, its derived adjunction, original-unit direct-image composition and
its square, and the exchange/coinduction mates. These were moved unchanged out of
the atlas module after its retry reached the 60-second limit. The source is Stacks
0D5T, 0BUZ and 0E2X. LeanFinder found native restriction adjunction lemmas, which are
reused; grep in Mathlib and both project source trees and the DAG found no owner of
this package. The node records all searches verbatim by tool/query/result.

`def-trf-polynomial-duality-affine-realization`, module
`Sheaf.AlgebraicGeometry.PolynomialDualityAffineRealization`, owns exact-realization
proof data and ordinary/derived affine comparison normalization. These were moved
unchanged out of the affine-model module to reduce its compilation cost. The source
is Stacks 01I7, 01I9, 06Z0 and 079V. Loogle finds the actual tilde adjunction that is
reused; the combined package has no existing node or source declaration. Both new
node statements were checked against their modules in the second reading; these
splits change no mathematical declaration, quantifier, equation or existence claim.

The dry-run metadata check requested the separate LeanSearch search kind. Running
`msearch.py ... leansearch` for “Canonical polynomial relative duality models,
derived coinduction restriction mates, exact affine tilde realization, and normalized
comparison on localizations” returned eight hits: five polynomial integer-normalization
lemmas, representation coinduction, general derived adjunctions, and multivariate
polynomial localization. None defines these comparison packages. The query, hit names
and verdict have been added to each new node's mathlib_searches. All seven modules
already passed their sandbox and library compiles without errors or non-sorry warnings.
