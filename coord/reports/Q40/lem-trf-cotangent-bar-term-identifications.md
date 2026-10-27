## Worker report

Item: lem-trf-cotangent-bar-term-identifications. The main module is
`Sheaf.RingTheory.CotangentBarTermIdentifications`; its theorem
`Algebra.CotangentBarTerms.identifications_nonempty` asserts the proposition `Identifications`, whose existential clauses give the
three canonical isomorphisms. Its clauses have source labels in comments. Every theorem proof in this delivery is `sorry`.
All helper definitions have actual data. The exactness and additive instances simply
reuse Mathlib's composition lemmas and existing exact ULift/scalar-restriction
instances; they introduce no postponed proof.

The natural-language item is unchanged. No flatness assumption is made on the
ring map B → C. There are no new DAG nodes.

Clause-by-clause rendering:

- Commutative rings A → B → C: the explicit binders `{A B C : CommRingCat.{u}}`,
  `(f : A ⟶ B)` and `(g : B ⟶ C)`.
- The full identity-cover polynomial and pair sites: the existing
  `CotangentSites.Site f`, `Site (f ≫ g)`, `Site g` and `PairSite f g`.
  `low : LowerShriekData f g bar` supplies exactly their specified projections,
  constant-coefficient lower-shriek comparisons and bar representatives.
- F1, F2 and F3: the existing `SiteCoefficients f`,
  `SiteCoefficients (f ≫ g)` and `SiteCoefficients g`. Their `terms` and `formula`
  fields identify the actual differential tensors and every restriction map.
  There is no arbitrary coefficient presheaf hypothesis.
- M1, M2 and M3: `first`, `second`, `third` use the existing
  `firstModule`, `secondModule`, `thirdModule` of the differential-sequence
  dependency. The scalar extension in `firstModule` is actual extension of
  scalars. Unfolding it gives precomposition of F1 extended by C: the source's
  sectionwise equality, including restriction maps, is definitional here.
- X_i in D(C): `barObject bar` is exactly `DerivedCategory.Q.obj` of the
  corresponding `bar.models ... .bar.obj` complex. The statement uses derived
  isomorphisms, not only isomorphisms on individual cohomology modules.
- Universe encodings: the full sites are small in universe u+1, whereas their
  coefficient values and original rings are in u. `largeModules` is the actual
  `ModuleCat.uliftFunctor` followed by restriction along
  `ULift.ringEquiv : ULift B ≃+* B`. The target ring is thus ULift B or ULift C.
  `largeCotangent` is Q of this termwise transport of the already recorded
  standard differential complex. This is the same object in a containing
  coefficient universe, not a new definition of the cotangent complex.
  `scalarTransport` and `scalar_formula` specify the canonical tensor transport,
  sending up(c ⊗ x) to up(c) ⊗ up(x); the presheaf map in `alpha1_eq` is its
  whiskering, so this transport is not silently assumed or an arbitrary map.
- Each F1(P) is free and flat: `free` and `flat`, universally over the actual
  full presentation site. `coordinates` quantifies over every polynomial
  coordinate isomorphism respecting A, and gives exactly the direct sum `S →₀ B`
  with each c dx_s sent to `Finsupp.single s c`. `tensor_exact` states preservation
  of every short exact sequence by tensoring with this value. `largeFlat` is
  the same flatness after the explicit coefficient transport and is the input
  needed for the recorded change-of-rings bar comparison.
- The canonical three isomorphisms: `alpha1`, `alpha2` and `alpha3` have exactly
  the three specified X_i as sources. Their targets are respectively
  `change.point.functor.obj (largeCotangent coh (Arrow.mk f))`,
  `largeCotangent coh (Arrow.mk (f ≫ g))`, and
  `largeCotangent coh (Arrow.mk g)`. `change.point` is the universal normalized
  derived scalar extension from the recorded change-of-rings dependency.
- alpha2 = theta(C/A)c2 and alpha3 = theta(C/B)c3: `alpha2_eq` and `alpha3_eq`
  are these literal hom equalities, preceded only by the bar model inverse
  because X_i were stated as Q of the actual bar complexes. `fullTheta m2` and
  `fullTheta m3` are the normalized full-site presentations of the sheaf-model
  dependency's theta.
- alpha1's prescribed composite: `alpha1_eq`, using the explicit predicate
  `IsFirstComposite` with its full equality. Its right side first applies
  scalarTransport, the bar model inverse, c1 on F1 extended by C, the target bar
  model and Q of `change.barIso`. Its left side is alpha1 followed by derived
  theta1 inverse, the original bar model, and the flat-bar computation counit.
  That last composite is invertible by `change.flatBar` applied to `largeFlat`.
  Cancellation therefore says precisely that alpha1 is c1, the flat-presheaf
  comparison, then derived theta1. This equation avoids a local instance or an
  implicitly chosen inverse and fixes the actual morphism rather than just
  asserting that some isomorphism exists between its endpoints.
- The middle generator formula: `middle_formula` uses the actual
  `change.barIso` and `bar.models ... .generator`. It sends a chain with z ⊗ x
  to z ⊗ the same chain with x, in every nonpositive degree. The symmetric order
  C ⊗_B M agrees with all recorded dependency interfaces; symmetry translates
  it into the node's order M ⊗_B C.
- The standard free bounded-above representative: `standard_bound`,
  `standard_free` and `standard_flat` apply to the actual transported
  `differentialComplex (coh.differentials (coh.standard (Arrow.mk f)))`.
  `standard_representation` asserts an isomorphism from the derived extension
  to Q of its termwise scalar extension, with hom equal to the universal
  `change.point.counit` at that very complex. Thus its representative is
  prescribed canonically; no replacement complex or arbitrary isomorphism is
  substituted.
- No flatness of B → C: there is no such binder in either theorem or proposition.
  The model parameters coh, bar, low, m1/m2/m3 and change are the specified data
  furnished by their dependency theorems, not additional algebraic hypotheses.

Dependency declarations read and used:

- `Sheaf.RingTheory.CotangentDifferentialPresheafSes`:
  `Algebra.CotangentSheaf.SiteCoefficients`, `tensorTerm`, `tensorD` and
  `Algebra.CotangentDifferentialSequence.firstModule`, `secondModule`,
  `thirdModule`, with the Sequence signature and its differential formulas.
- `Sheaf.RingTheory.CotangentLowerShriek`:
  `Algebra.CotangentSites.Site`, `PairSite`, `Projections`,
  `LowerShriekData.comparison`, `.represented`, `.comparisonIso`, and `reindex`.
- `Sheaf.CategoryTheory.DerivedColimitBar`:
  `CategoryTheory.CategoryColimitBarSystem`, `CategoryColimitBarModel.bar`,
  `.model`, `.generator`, and the standard derived localization instances.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `DerivedCategory.Q`, `HasDerivedCategory` and its standard localization.
- `Sheaf.RingTheory.CotangentSheafModel`: `Coefficients`, `Model`, `theta`,
  `ResolutionComparison`, `evaluation` and their normalization formulas.
  Its landed record and its entire interface are preserved byte-for-byte.
  The item owns the additional full-site helpers described below.
- `Sheaf.CategoryTheory.DerivedColimitChangeRings`:
  `CategoryTheory.CategoryColimitChangeRings`, `.point`, `.barIso`, `.formula`,
  `.flatBar`, `.represents`, and `categoryBarExtend`.
- `Sheaf.RingTheory.CotangentResolutionCoherence`:
  `Algebra.CotangentResolution.Coherence`, `cotangentComplex`,
  `differentialComplex`, `complexGenerator`, `.standard`, `.standard_resolution`
  and `.comparison`.
- Proof imports: `Mathlib.RingTheory.Kaehler.Polynomial` contains the exact
  arbitrary-variable leaf `KaehlerDifferential.mvPolynomialBasis`, its generator
  and coordinate formulas; `Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients`
  supplies `SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite`;
  `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings` supplies the universal
  ordinary derived pair and publicly retains the general sheaf cochain model;
  `Sheaf.TraceFormula.OnePointDerivedRingIdentification` supplies
  `CategoryTheory.one_point_derived_ring_identification`. These imports preserve
  the node's proof plan; their theorems are not proved in this stage.

Edge cases checked: arbitrary and empty S in `coordinates`; the base ring as a
zero-variable polynomial algebra; zero coefficient rings (no Nontrivial binder);
identity ring maps; nonflat B → C; degree zero and every negative degree of the
bar comparison; the zero positive standard-complex terms; arbitrary coefficient
presheaf restriction maps, rather than coordinate-preserving maps. Universes
remain independent where the source's site encoding requires the containing
universe: no equality of u and u+1 or countability restriction is imposed.

Searches made with the prescribed msearch.py wrapper:

- LeanFinder: `Derived colimit polynomial pair cotangent complex bar term identification`.
  Eight hits concerned presentation cotangent linear maps, submersive
  presentations and H1Cotangent; none was this derived comparison.
- Loogle: `"cotangent"`. Twelve hits concerned Ideal.Cotangent,
  IsLocalRing.CotangentSpace and their instances; none was the statement.
- Mathlib grep: `cotangent.*(bar|colimit)|bar.*cotangent`, RingTheory.
  Five hits concerned an unrelated gbar in Extension/Cotangent/Basis.
- LeanSearch: `Derived colimit of polynomial differential presheaves is the cotangent complex with flat bar tensor comparison`.
  Eight hits concerned ordinary presheaf colimits, presentations and universal
  differentials; none identified these three derived bar terms.
- Project rg and item-id search in `lean/WeilConjectures`: no item-id hit and no
  matching comparison; incidental syntomic gbar/cotangent hits were unrelated.
- Project rg in `lean/Sheaf`: the existing cotangent dependency models and
  unrelated determinant/cotangent arguments were found, but no declaration of
  these three specified bar-term identifications. The exact helper namespaces
  were checked against Mathlib, WeilConjectures and Sheaf before naming them.

Source checked directly: `literature/stacks-project/cotangent.tex`,
lemma-compute-cotangent-complex (08PU), lemma-triangle-compute-lower-shriek (08QW),
and proposition-triangle (08QX), especially its three displayed identifications.
The tag mapping was read from `literature/stacks-project/tags/tags`.

No STATEMENT-DISPUTED issue or correction to the item's mathematical statement.

## Repair of return L (immutable head 8442c6f60169)

H13 repaired using the return's explicitly permitted helper option. The saved
packet's initial dry run passed at 5d6c8ed7148, but that packet still rebound
`lem-trf-cotangent-sheaf-model`; mechanical acceptance did not resolve the return.
The repaired packet restores that dependency JSON byte-for-byte from live,
including Q37's `CotangentSheafModel/exists_model` primary, all 28 declarations,
and its existing review. It is unchanged and is excluded from the delivery diff.
No live source was edited and no Git command was run directly.

The 16 declarations formerly in `CotangentFullSiteModel.lean` now are helpers in
`CotangentBarTermIdentifications.lean`, listed in this item's `lean.declarations`.
This item owns `Algebra.CotangentSheaf.fullModel_nonempty` as its auxiliary
existence theorem, with source and complete natural-language proof docstring;
its blueprint markers now name this item. The other postponed theorem is the
unchanged primary `Algebra.CotangentBarTerms.identifications_nonempty`.
The standalone full-site module is removed from the packet. There are 24 owned
source declarations in one module, and no new DAG node or dependency rebinding.
The item's mathematical statement, statement dependencies, proof and proof
dependencies remain unchanged.

The helper interface supplies precisely the full-site comparisons used by this
item's three theta composites. It does not purport to restate the full Q37 node:
the arbitrary-square base-change theorem and naturality for maps of augmented
resolutions remain owned by Q37's unchanged `exists_model` and `Model`.
The import path is item → CotangentDifferentialPresheafSes →
CotangentSheafModel. Moving these helpers into the item adds no import to
CotangentSheafModel and creates no import cycle.

Full-site helper clauses checked against the source and their consumer:

- `largeModules` is actual ULift followed by restriction along the ring
  equivalence. Its exactness instances reuse Mathlib. `fullLowerShriek` is the
  existing bar system's derived colimit on the actual full presentation site.
- `largeDifferentialComplex` transports the recorded differential complex
  termwise, and `largeCotangent` applies the derived localization to its standard
  resolution. Neither selects an object from the postponed existence theorem.
- `FullResolutionLift` records the diagram, ring isomorphism, base equality and
  augmentation equality. `fullEvaluation` applies the alternating-face complex;
  `fullEvaluationElement` specifies the degree -n coordinate transport.
- `FullResolutionComparison.iso` is natural in every coefficient presheaf.
  Its augmentation sends degree-zero generators to their actual colimit
  inclusions, and `normalization` fixes its derived comparison to the bar
  system's universal counit. `exact` and `FullPreservesBoundary` specify
  preservation of short exact sequences and their connecting morphisms.
- `FullModel.lift` covers every polynomial resolution.
  `differentialIso` and `FullDifferentialFormula` fix its comparison on each
  pure differential tensor; `agrees` identifies every resolution comparison
  with the recorded coherence comparison to the standard resolution.
  `fullTheta` is the actual composite at that standard resolution.
- `fullModel_nonempty` provides this helper data for any ring arrow and the
  already recorded `SiteCoefficients`. Its docstring explains polynomial
  generator lifting, representable contractibility, the normalized derived
  comparison, exact evaluation, differential tensors and ULift transport.
  Its role here is to supply the models m1, m2 and m3 used in the main assertion.

Repair searches: `blueprint_refs.py search 'full polynomial site'` returned
zero blueprint nodes; `rg` for `FullModel`, `fullModel_nonempty` and full-site
cotangent comparisons in dag/nodes, lean/Sheaf and lean/WeilConjectures found no
landed full-site interface. The prescribed msearch wrapper was also rerun:
LeanSearch query `Normalized derived colimit comparison on the full polynomial
presentation site with the standard simplicial cotangent complex` returned eight
unrelated presentation/colimit/Dold–Kan hits; LeanFinder query `Full polynomial
presentation site cotangent sheaf comparison normalized by colimit augmentation`
returned eight ordinary presentation/cotangent-module hits; Mathlib RingTheory
grep `FullModel|fullModel_nonempty|cotangent.*(colimit|resolution)` returned zero
hits. These searches confirm the helpers are absent from the live library;
the existing Q37 interface is reused through its public import, not replaced.

## Second reading by Q40

A separate agent was not started, as the dispatcher explicitly prohibits it;
this is a second self-reading, with independent maintainer review still required.
I reread the unchanged node alongside the complete expanded proposition. The full-site
versus coordinate-site and coefficient-universe mismatch is supplied by helpers
owned by this item, as explicitly allowed by the return. No §1(B) rebinding remains.
The reading checked all three sources/targets, the use of
exactly the lower-shriek comparison, all three theta composites, the sectionwise
first-module equality, polynomial-coordinate freeness, tensor exactness, the
middle generator formula and the prescribed standard-complex counit. It also
checked that the parameters supply existing canonical dependency constructions,
that no flatness assumption on g was added, and that no per-degree-only result
was substituted for a derived isomorphism. The coefficient transport is explicit
and normalized on pure tensors. No change to the node statement was needed.

Elaboration repair: the main assertion is a Prop-valued definition with explicit
existentials and conjunctions, avoiding generated large-record projections. The
long first-composite equation and boundary/differential formulas have named
Prop-valued definitions with actual formulas. No clause was removed.

Repair validation: scompile.py compiled the consolidated item against current
server sources in 51.4 seconds, at nice 19 with two threads and the unchanged
60-second limit; exit 0 and no errors or unexpected warnings. Its initial
sandbox attempt timed out and the wrapper's current-source confirmation passed.
A structural self-check verified the unchanged mathematical node and primary
signature, all 24 unique owned declarations, only the two named theorem sorries,
all blueprint markers owned by this item, and the 100-character Lean line limit.
The restored Q37 node was checked byte-for-byte against live.
