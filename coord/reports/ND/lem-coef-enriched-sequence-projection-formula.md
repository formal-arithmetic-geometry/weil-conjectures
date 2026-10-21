## Worker report

The module `Sheaf.CategoryTheory.EnrichedSequenceProjectionFormula` states
`SheafOfModules.EnrichedSequenceProjection.enrichedSequenceProjectionFormula`.
The node statement, proof, and proof dependencies are unchanged. The already landed
`def-coef-hom-zero-cycle-class` is the statement dependency for the final conclusion.
The existing `def-coef-semilinear-system-models` is now also a direct statement
dependency: its `Models` and `ScalarTensorComparisonModel` fix the actual evaluated
tensor-pullback comparison on pure tensors and K-flat total-complex representatives.
Its `coefficientHomZeroEquiv` fixes the 08JA identification uniquely by naturality
and the formula taking a cycle for a chain map g to Q(g), followed by the inverse
localized resolution augmentation. The unnormalized existential comparison is not used
to choose either endpoint identification.
There are no new nodes and no repaired dependency records. The public helper declarations
are constructions of the maps and presentation transports occurring in this node, rather
than replacement definitions of tensor, internal Hom, derived categories, or systems.

The file contains four postponed theorems: `ordinaryEvaluationIso_exists`,
`ordinarySectionsIso_exists`, `sectionsH0Comparison_exists`, and
`enrichedSequenceProjectionFormula`. The first three specify unique presentation
transports belonging to this node, with formulas on every section or every K-injective
resolution. Each has the owning node's blueprint/source docstring and a natural-language
proof. Every definition has real data. Choices of presentation transports use `∃!`,
which determines the natural isomorphism up to equality. The 08JA identification uses
the existing normalized dependency definition directly; no new derived Hom definition
is introduced.

### Hypotheses and objects, clause by clause

* A small site is `{C : Type c} [Category.{v} C] (J : GrothendieckTopology C)` and
  `[EssentiallySmall.{max c v r} C]`. This is the topology associated to the covering-site
  convention of `def-weil-pbc-sites-and-cohomology`. Site object and arrow universes remain
  independent. The sheafification and locally-bijective instances at `max c v r` are the
  standard ringed-site infrastructure. No condition on a geometric scheme is introduced.
* The inverse ring sequence is `B : ℕ → Sheaf J CommRingCat.{max c v r}` and
  `τ : ∀ n, B (n+1) ⟶ B n`, assembled by the dependency's `rings = Functor.ofOpSequence τ`.
  Index `0` denotes the node's first positive level; all indices are included.
* Strict systems are the recorded `Systems J B τ`, actual module sheaves over `systemRing`
  on `coefficientSequenceTopology J`. Their ordinary unbounded derived category is `DS`.
  `toStrict` is the exact derived functor of `sequenceToStrictSystemFunctor` from
  `strictSystemSequenceEquivalence`. It transports to `StrictRingSystem (rings J B τ)`;
  the identity-on-sections comparison `ordinaryEvaluationIso` and its derived compositor
  `toStrictEvaluation` connect the already existing evaluations. There is no replacement
  of the ordinary derived category by diagrams of derived objects.
* The semilinear calculus is `d : SemilinearSections.Data J B τ`, as supplied by
  `semilinearDerivedSections`. Its `closed`, `levelClosed`, `tensorEvaluation`, `scalar`,
  `homEvaluation`, and `homEvaluation_evaluation` are the dependency's specified operations.
  Its recorded total-complex/K-flat models remain part of `d`; they are not reconstructed.
* The base coefficient ring is `A : Sheaf J CommRingCat.{max c v r}`, with compatible
  structural maps `α : (Functor.const ℕᵒᵖ).obj A ⟶ rings J B τ`. Naturality of `α`
  expresses every compatibility with the coefficient transitions.
* `D J A` is the dependency's ordinary unbounded derived module category. `a` is the
  closed structure for its recorded `internalHom`, not a free Hom bifunctor. Its tensor
  is characterized by the tensor-Hom adjunction. The scalar models
  `σ n : ScalarData (α.app (op n))` retain their actual ordinary sheafified tensor
  constructions, universal derived pairs, section-normalized units and chain transposes.
  They require no flatness of any coefficient map.
* The actual right derived sequence projection is presented by
  `s : SequenceSectionsComparisons (rings J B τ) A α`, `_hs : s.Normalized`, and
  `p : SequenceSectionsDerivedPair (sequenceProjectionDirectImage s)`.
  `sequenceProjectionDirectImage s` is exactly scalar restriction followed by ordinary
  inverse limit. `limitPushforward = toStrict ⋙ p.functor` is its sequence-site realization.
  `hL : L ≅ limitPushforward ...` allows any equivalent presentation of this specified
  functor. These are the existing dependency's universal derived pairs; `L` is not an
  arbitrary map used in place of inverse limit.
* `πP` and `_hπP` are the actual strict-system projections: the displayed equation with
  `p.unit`, exact restriction/evaluation factorization maps, and `Q(lim.π)` is precisely
  the normalization in `coefficientSequenceSectionsLimitComparison`. `_hπ` defines the
  projections `π` for `L` by `hL` and the explicit `projection` transport. It imposes no
  additional hypothesis on the rings or on the derived input objects.
* `R ⊣ L` presents `Lp* ⊣ Rlim U`. A left adjoint to this specified right derived functor
  is uniquely the derived ringed sequence pullback, up to its adjunction comparison.
  `ρ n : R ⋙ e n ≅ (σ n).T` presents its canonical finite scalar extension. `_hunit`
  fixes the adjunction/level identification by requiring the nth projection of its unit
  to be the normalized scalar unit, exactly as in
  `pushforwardLimitProjections`. This excludes a twisted adjunction normalization.
* `μ : a.tensor ⋙ R ≅ (R.prod R) ⋙ d.closed.tensor` has the orientation opposite
  to the comparison used to define `b`. Its actual evaluation at level n, conjugated
  by `ρ` and followed by `d.tensorEvaluation`, is `evaluatedTensorComparison n`.
  `aModels : Models J A a` supplies the recorded K-flat model including its
  `uncurry_model`, which fixes closed transposition relative to the existing Hom.
  `_hμModel n : ScalarTensorComparisonModel ... (evaluatedTensorComparison n)`
  fixes the ordinary map by `ordinary_pure`, its chain map by `summand`, and this very
  derived map by `derived`, using the scalar model's actual counits and both tensor
  models. Thus it specifies the canonical 07A4 comparison, including its sign.
  `_hμ` then equates that evaluated comparison to `ν n`; ν is not free up to sign.
  These are representative normalizations of the specified tensor-pullback operation;
  they do not assume the projection formula or any clause of the conclusion.
* `P : D J A`, `N : DS J B τ`, `hP : Normalized ... (R.obj P)`, and
  `_hN : Normalized ... N` retain both stated normalization hypotheses. `Normalized`
  is exactly invertibility of every derived transition-adjoint reduction, including
  repeated indices. There is no normalization hypothesis on the internal Hom system.

### Conclusions and specified arrows, clause by clause

* `sourceHom ... P N` is `V = H_A(P,L N)`, `systemHom ... P N` is
  `J = H_B(R P,N)`, and `levelHom ... P N n` is
  `H_(B_n)((σ n).T P,e_n N)`.
* `comparison` calls the recorded `ClosedAdjunctionComparison.comparison` on the actual
  closed structures, pullback comparison and adjunction. It is precisely the closed
  transpose of reduced evaluation followed by the counit. `delta` calls the recorded
  `adjointComparison`, so it is exactly the unit followed by `L(b)`.
* `homIdentification` uses `d.homEvaluation` for the normalized first input and the
  contravariant map of the existing internal Hom along `ρ`. It identifies the actual
  evaluation of `J` with `levelHom`; it does not extend both Hom inputs.
* `finiteProjection` is `delta ≫ π_n(J) ≫ Res(homIdentification)`. Thus it refers to the
  actual nth projection of the actual enriched map, rather than an independently chosen
  arrow satisfying a desired equation.
* `uncurried` is inverse scalar transposition followed by inverse closed transposition.
  The first conclusion sets `uncurried finiteProjection = reducedEvaluation`.
  `reducedEvaluation` is `ν_n⁻¹`, then scalar extension of `a.evaluation`, then
  `counitLevel`. Here `counitLevel = ρ_n⁻¹ ≫ e_n(adj.counit)` is exactly `e_(N,n)`.
  This renders all three arrows of the displayed formula, with their canonical tensor
  reassociation.
* The second conclusion quantifies over every `q` with the stated source and target and
  says the same uncurrying equation forces `q = finiteProjection`. Together with the
  first conclusion this is existence and uniqueness of the specified A-linear map.
* The third conclusion is `finiteProjection = internalScalarMap`.
  `internalScalarMap` is the recorded `H_A.map (id,π_n)` followed by the inverse of
  `ClosedScalarHom.component`. That component is the existing five-bijection scalar
  internal-Hom comparison used by `ScalarInternalHomAdjunction`; hence this is precisely
  the equivalent internal formulation, rather than an integral Hom/tensor base-change map.
* The theorem supplies `rl`, its actual `πL`, and `κ`, with the derived-unit equations
  of the sections/limit comparison. These fix the specified natural comparison, rather
  than allowing an arbitrary natural isomorphism. The fourth conclusion applies sections
  to `delta`, transports through `hL` and `κ`, projects by `πL`, applies
  `s.finiteEvaluation`, and transports the evaluated internal Hom by the actual
  `toStrictEvaluation` and `homIdentification`. The result equals global sections of
  `internalScalarMap`, followed by inverse scalar restriction comparison `s.scalar`.
  This is the global derived mapping-complex scalar-adjunction formula after `(π_n)_*`.
* The last conclusion quantifies over every `h : P ⟶ L.obj N`. It starts with
  `(coefficientHomZeroEquiv J A P (L.obj N)).symm` applied to `h`,
  thus the actual class `[h]`. It transports that class by `sectionsH0Comparison.inv`
  to the H0 of `(s.finite A).functor`, applies `DerivedCategory.homologyFunctor ... 0`
  to `globalProjection`, transports by `sectionsH0Comparison.hom` over `B n`, and applies
  `coefficientHomZeroEquiv J (B n) ((σ n).T.obj P) ((e n).obj N)`. The equality says the resulting derived morphism
  is `(σ n).T.map h ≫ counitLevel ... N n`. Thus it asserts the action of the actual
  projected `RΓ(delta)`, including `hL`, `κ`, `πL`, both finite evaluation transports,
  and `homIdentification`. It cannot be recovered from just the scalar unit and counit
  normalization while forgetting `delta` and the sections/limit comparison.
* `homSections` abbreviates the existing rank-one-module Hom functor. The unique
  `ordinarySectionsIso` compares the dependency's limit-of-sections presentation to it:
  the equation evaluates both at every `U` and every `x`. `sectionsResolutionIso` is
  constructed from the existing K-injective computation of the derived Hom-sections
  functor. The unique `sectionsH0Comparison` compares the arbitrary universal derived
  pair to the canonical hypercohomology used by 08JA, using the displayed equation
  on every K-injective complex. These normalize changes of presentation and impose
  no additional mathematical hypothesis on `P`, `N`, the site, or the coefficients.

The normalizations above describe the operations already specified in the node's setup.
They do not restrict the site, coefficient maps, P or N beyond the node's hypotheses.
The theorem is uniform in these presentations and therefore retains arbitrary equivalent
choices of universal derived pairs.

### Dependency declarations read and used

* `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor`, retained by
  the calculus' total tensor models.
* `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`:
  `CategoryTheory.derivedInternalHomOfUniverses`, used by `internalHom`.
* `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `HasDerivedCategory`,
  `DerivedCategory.Q`, used by `D`, `DS`, the universal pairs and normalization equations.
* `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings`, retaining the site's associated topology.
* `Sheaf.CategoryTheory.ClosedAdjunctionEnrichedIsomorphism`:
  `CategoryTheory.ClosedAdjunctionComparison.enriched_isomorphism`; its public constructions
  `comparison` and `adjointComparison` define this node's exact arrows.
* `Sheaf.Paper.SemilinearDerivedSections`:
  `WeilConjectures.SemilinearSections.semilinearDerivedSections`, with publicly imported
  `Data`, `ScalarData`, `Normalized`, `internalHom`, `Systems`, `DS`, `e`, `resD`,
  `homEvaluation` and `tensorEvaluation`.
* `Sheaf.CategoryTheory.SequencePushforwardLimitProjections`:
  `SheafOfModules.SequenceProjection.pushforwardLimitProjections`, the source of the
  projection-normalized unit and scalar-adjunct conventions.
* `Sheaf.CategoryTheory.CoefficientSequenceSectionsLimit`:
  `SheafOfModules.coefficientSequenceSectionsLimitComparison`,
  `sequenceProjectionDirectImage`, `sequenceSectionsLimitOrdinary`.
* `Sheaf.CategoryTheory.SystemLevelLeftExtension`:
  `SheafOfModules.systemLevelLeftExtensionTheory` and its recorded exact evaluations.
* `Sheaf.CategoryTheory.SystemRingedSequenceSite`:
  `SheafOfModules.strictSystemSequenceEquivalence`, `sequenceToStrictSystemFunctor`.
* `Sheaf.Paper.CoefficientHomZeroClass` publicly supplies
  `WeilConjectures.coefficientHomZeroEquiv` and its `coefficientHomZeroEquiv_exists`.
  Its signature identifies H0 of `coefficientGlobalSections` of the existing internal Hom
  with derived morphisms. `ringedSiteZerothHypercohomologyOfUniverses` is definitionally
  `coefficientGlobalSections ⋙ H0`; the existing `sectionsH0Comparison` therefore has
  precisely this codomain.
* Proof imports retain every already-stated proof dependency: the sequence derived
  adjunction and global-sections evaluation are public imports of the projection/sections
  modules; `CoefficientHomZeroClass` publicly imports `rhom_global_sectionsOfUniverses`
  for the unchanged proof dependency, while the final signature uses `coefficientHomZeroEquiv`,
  `sheafRingDerivedCoefficientAdjunction`, `ringedDerived_closed_symmetric_monoidal`,
  `scalarInternalHomAdjunction_exists`, and
  `CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`.
  `ClosedScalarHom.component` is imported from `ClosedScalarHomComparison`; its existing
  definition supplies the finite internal scalar comparison, without duplicating it.

### Edge cases checked

First positive level (`n=0`), identity coefficient maps, constant towers, nonflat and
zero coefficient maps allowed by ring homomorphisms, zero P or N, empty sites, arbitrary
unbounded complexes and independent site object/Hom universes all remain admitted.
No terminal object of the site, transition surjectivity, perfectness, dualizability,
finite Tor amplitude, coefficient flatness, or componentwise K-injectivity is assumed.
N is explicitly normalized as the node requests; J need not be normalized. Every derived
map equality is in the actual ordinary derived category. Evaluations are not used as a
faithful functor to infer equality of arbitrary derived morphisms.

### Searches and source checks

* `msearch.py ... leanfinder "Finite projection of enriched sequence adjunction internal
  Hom scalar extension counit"`: eight hits, including `ihom.ihom_adjunction_counit`,
  `Enriched.FunctorCategory.homEquiv_apply_π` and module scalar-adjunction counits. None
  states this strict-system enriched projection and its sections/limit comparison.
* `msearch.py ... loogle "CategoryTheory.Adjunction.homEquiv,
  CategoryTheory.ClosedAdjunctionComparison.adjointComparison"`: zero hits; the project
  construction is not indexed by Mathlib's Loogle. Its recorded source was read directly.
* `msearch.py ... grep "enriched.*projection|projection.*enriched" CategoryTheory`:
  one hit in `Mathlib/CategoryTheory/Enriched/FunctorCategory.lean`, concerning a functor
  category enriched end projection, not derived semilinear systems.
* `rg` over `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json` for the
  node id and prospective declaration names found no existing statement.
  Broader sequence/enriched/projection searches located the dependencies used above.
* Read the actual dependency signatures/docstrings, not just the node names. Opened
  Stacks `sites-cohomology.tex`, `lemma-adjoint` (07A6) and
  `lemma-derived-pushforward-composition` (0D6E), and checked the current blueprint's
  integral exceptional-adjoint source. The present node is an extracted agent calculus
  statement, not the statement of its blueprint unit.

No `STATEMENT-DISPUTED` flag, statement correction, or unusable dependency was found.
Single-file validation uses only the prescribed `scompile.py` wrapper. No live source or
repository Git state was modified directly.

## Repair of returned head 4dac5291bc35

F1/H3: replaced the isolated scalar-adjunct identity with the H0 action of the actual
clause-four global composite, factored into `globalProjection`. Clauses one through
four retain their original expressions (the fourth uses this definition verbatim).
The two extra sections presentation transports are fixed uniquely, rather than left
as arbitrary isomorphisms. Added the already landed 08JA node to `stmt_deps` and made
its import public. No statement correction is needed: the informal node already
requires precisely this degree-zero action.

F2/H11: replaced the earlier one-paragraph audit with the following fresh reading
against the open informal node, dependency sources, and revised module.

## Historical self-reading before return 039c5222568d

This second pass re-read the node from its first hypothesis to its last clause,
then followed each Lean expression through its defining helpers:

1. The small site and coefficient tower are `C`, `J`, `B`, `τ`, with separate `c`, `v`,
   and coefficient universe `max c v r`. These retain the empty site and level `n=0`.
   `rings` assembles all transitions; compatible base coefficient maps are the natural
   transformation `α`. No flatness or transition-surjectivity assumption appears.
2. Strict systems are the sequence-site module category `Systems`, with `toStrict`
   induced by the recorded exact equivalence. `ordinaryEvaluationIso` is fixed on each
   section; `toStrictEvaluation` uses its exact derived comparison. Both sides are
   ordinary unbounded derived categories. No category of diagrams in derived categories
   is substituted. `D`, `DS`, `e`, tensor and internal Hom come from recorded dependencies.
3. The ringed projection's actual direct image is `sequenceProjectionDirectImage s`.
   Its universal derived pair is `p`, identified with `L` by `hL`. The equation `_hπP`
   fixes its projections on every complex; `_hπ` transports them to `π`. The adjunction
   `adj : R ⊣ L`, the level comparisons `ρ` and `_hunit` are exactly the node's
   projection-normalized derived adjunction. An arbitrary right adjoint is not used.
4. `a`, `d`, `σ`, `μ`, `ν` retain the closed and scalar structures. `_hμ` asserts the
   compatibility of the system tensor comparison with the finite tensor comparison.
   The repair below adds the previously missing representative normalization of the
   actual evaluated μ: compatibility alone did not fix its sign. The models add no
   perfectness, boundedness, dualizability or normalization of the Hom system.
5. Both normalization hypotheses are present: `hP` for `R.obj P` and `_hN` for `N`.
   `sourceHom` is exactly `H_A(P,L N)`; `systemHom` is `H_B(R P,N)`; `levelHom` is
   `H_(B_n)(S_n P,N_n)`. The first input changes contravariantly along the inverse of
   `ρ`. The second Hom input is evaluated, rather than extended from an integral Hom.
6. The node's `b` is `comparison`, built with `ClosedAdjunctionComparison.comparison`.
   `delta` uses its recorded adjunct construction, the unit followed by `L(b)`.
   `finiteProjection` projects this very delta and applies `homIdentification`.
7. The first conclusion's scalar adjunct and closed transpose are `uncurried`.
   `reducedEvaluation` is the inverse tensor comparison, scalar extension of evaluation,
   and `counitLevel`. Its source is `S_n V ⊗ S_n P`; its target is `N_n`. This matches
   every arrow of the displayed informal composite, in its stated order.
8. The second conclusion quantifies over all A-linear derived arrows of precisely that
   source and target. Equality of their uncurrying with `reducedEvaluation` forces
   equality with `finiteProjection`. Together with conclusion one this gives exactly
   the stated existence and uniqueness; neither an extra isomorphism nor a weaker
   object-only formula is asserted.
9. The third conclusion compares `finiteProjection` with `internalScalarMap`.
   That definition is `H_A(P,π_n)` followed by the inverse `ClosedScalarHom.component`.
   The finite scalar internal-Hom adjunction has the same orientation as the node.
10. The fourth conclusion uses `globalProjection`. Expanding it gives sections of delta,
    sections of `hL`, `κ`, the actual `πL`, `finiteEvaluation`, `toStrictEvaluation` and
    `homIdentification`, in that order. Its right side is sections of `internalScalarMap`
    followed by inverse scalar comparison. The existential `rl`, `πL`, `κ` satisfy the
    two original derived-unit normalizations, so the limit comparison is specified.
11. The final conclusion now applies H0 to that same `globalProjection`. The input class
    is the inverse normalized `coefficientHomZeroEquiv` image of `h`; the output uses
    the same normalized construction over `B_n`. The
    intervening sections transports have the unique resolution formula checked above.
    The output equals `S_n(h)` followed by `counitLevel`. The previous final conjunct
    mentioned neither delta nor H0, a mismatch found in the return and now removed.
12. Rechecked zero objects, identity coefficient maps, constant towers, nonflat maps,
    arbitrary unbounded complexes and the empty site. The new comparison uses K-injective
    resolutions in the individual module category, never fiberwise K-injectivity of an
    evaluated varying-coefficient system. For identity maps the last formula still states
    the action of the projected global map, rather than merely a triangle identity.

The earlier second-reading paragraph did not match clauses individually; it is replaced
by the checks above. This is a separate reading pass by the dispatched worker, as the
brief prohibits starting other agents. Independent acceptance remains the maintainer's
review; no second person or agent is claimed.

### Repair validation and added searches

Read Stacks `sites-cohomology.tex`, `lemma-section-RHom-over-U` (08JA), including the
K-flat/K-injective proof and its global form, and the current source of
`rhom_global_sectionsOfUniverses`. Read `ringedSiteZerothHypercohomologyOfUniverses`,
`SequenceSectionsDerivedPair`, `SequenceSectionsComparisons`, their normalization
signatures, `unitHomEquiv`, and the universal right-derived comparison APIs.
Searches by `rg` for existing sections/Hom comparison isomorphisms in project and
Mathlib found `SheafOfModules.unitHomEquiv`, the existing ordinary type-level
identification, and `Functor.rightDerivedFunctorObjQIso`, used directly here; no existing
comparison with this dependency's arbitrary universal derived pair was found.
The earlier three search kinds and source checks recorded above remain applicable.
The saved packet's first dry run passed as commit `73120667db9` without pushing.
The repaired module then compiled separately under both wrapper validation modes.
All final delivery checks use the prescribed wrappers.


## Repair of returned head 3e255f21b94a

H3/H5: both independent choices from `rhom_global_sectionsOfUniverses` have been
removed from the degree-zero conjunct. Naturality alone allowed e and -e independently
at the two rings, so the old expression did not specify the node's class(g) to Q(g) map.
The source and target now use respectively
`coefficientHomZeroEquiv J A P (L.obj N)` and
`coefficientHomZeroEquiv J (B n) ((σ n).T.obj P) ((e n).obj N)`.
Read their full definition and `coefficientHomZeroEquiv_exists`: this is an ∃!-normalized
natural additive equivalence whose representative formula sends the specified cycle
class to Q(g) followed by the inverse localized resolution augmentation. A sign twist
fails that representative formula. Its H0 source is definitionally the hypercohomology
used by `sectionsH0Comparison`, as the clean compilation also checks.

The import `Sheaf.Paper.CoefficientHomZeroClass` is public. The statement-dependency
entry `lem-pur-rhom-global-sections` is replaced by the already existing definition node
`def-coef-hom-zero-cycle-class`, exactly as the return requests. The former remains
an unchanged proof dependency and a nonpublic proof import. Step 6 of the theorem's
proof docstring now names the normalized cycle-class construction. The JSON signature
has been regenerated verbatim from the repaired file. No informal statement, proof step,
proof-dependency field, helper construction, or other node record is changed.

Self-check against the return: the full degree-zero composite still contains H0 of
`globalProjection`, its section presentation transports, and both normalized endpoints.
Clauses 1–4 and the unique ordinary-sections/H0 transports have been retained.
`μ` remains universally quantified, subject to the displayed `_hμ` compatibility;
no extra selection or uniqueness assumption on μ has been introduced. Both `hP` and
`_hN` and all universe binders remain. The zero-object and identity-coefficient cases
use the same cycle-normalized map; there is no independent sign choice at either ring.
The second reading above is a self-reading by ND; it is not an independent agent review.
This repair follows the maintainer's independent finding and leaves acceptance to that
review.

The prescribed initial dry run of the saved packet passed as `be971bd7a97`, but the
explicit returned semantic fault still required this change. Compared the retained
packet with the current read-only main node: only its `lean` and the authorized
statement dependencies differ. The delivery wrapper prepares the commit on current
main. The repaired Lean compiled without errors or unexpected warnings using
`scompile.py` in both sandbox and library modes (15.8 s and 15.9 s).


## Repair of returned head 039c5222568d

H3/H5 F1: the return's counterexample is valid. The preceding repair fixed both
08JA endpoints but left (μ,ν) free under simultaneous negation. This repair adds
`aModels` and `_hμModel`, using the already landed generic representative definitions
in `Sheaf.Paper.SemilinearSystemModels`; no new node or dependency module is needed.
The new public helper `evaluatedTensorComparison` is a composite of actual natural
isomorphisms, with no choice and no postponed data. Its component is

    rho_tensor^-1 ; e_n(mu) ; d.tensorEvaluation ; tensor(rho_X,rho_Y).

`_hμModel n` is explicitly a `ScalarTensorComparisonModel` for this composite,
not a model for another freely chosen comparison. Its `ordinary_pure` fixes
(x tensor y) tensor 1 to (x tensor 1) tensor (y tensor 1). Its `summand` fixes each
chain total-summand map to the inverse ordinary comparison followed by the actual
summand inclusion. Its `derived` identifies the inverse evaluated comparison,
conjugated by `scalarEpsilonIso` and the two `tensorModelIso`s, with Q of that chain
map on flat-term K-flat representatives. These are exactly the representative
normalizations in the proof of Stacks 07A4, lemma-pullback-tensor-product, which was
opened in full. The source and target tensor models include `uncurry_model`, so a
simultaneous re-signing of a tensor model and its closed evaluation cannot undo this
normalization relative to the fixed Hom localization and coefficientHomZeroEquiv.

The existing `_hμ` equation then makes ν equal to this actual evaluated comparison.
Thus μ is pinned after every finite evaluation by the specified tensor-pullback
representative formula. This is precisely the part of μ entering every assertion
of this node. No claim that evaluations detect equality of arbitrary derived maps
is used: naturality of the actual projection and the normalized unit express the
finite projection of delta as restriction of its evaluated closed transpose after
the scalar unit. The clauses about globalProjection use the projection-preserving
sections comparison for that same map. Possible invisible differences between
system maps cannot alter these projected composites.

Sign check at A=B_n=Z, P=Z[0]: the normalized ordinary pure tensor 1 tensor 1 maps
to 1 tensor 1. The (0,0) total summand gives the positive identity. The K-flat
`derived` square forces the actual evaluated μ to be the positive canonical
comparison. Replacing both μ and ν by their negatives violates that square; changing
the ordinary map instead violates `ordinary_pure`. Over characteristic two the signs
are already equal. For zero objects the same square holds, with no artificial
nonzero hypothesis. Nonflat maps such as Z to Z/2, arbitrary unbounded complexes,
the first level n=0, empty sites and independent site universes remain covered.
Flatness is required only of resolution terms, not of coefficient ring maps or P,N.

Advisory repaired: removed the unused direct nonpublic import of
`RhomGlobalSectionsOfUniverses`. The unchanged proof dependency remains publicly
available through `CoefficientHomZeroClass`. Added the existing definition node
`def-coef-semilinear-system-models` to stmt_deps and its module as a direct public
import because its representative models now occur in the signature. No informal
statement, proof, proof_deps, or existing dependency node is changed. The informal
statement already specifies canonical tensor reassociation; this repairs the Lean
rendering of that specification and requires no statement_change.

## Second reading by ND

This is a self-reading by ND, as the dispatcher forbids other agents; it does not
claim independent review. The maintainer's immutable-head review remains independent.

1. Read the informal node and current module together. Site, coefficient sequence,
   sequence-site/strict-system identification, exact evaluations and ordinary unbounded
   derived categories retain the original explicit universes and imported declarations.
2. A and its compatible maps are still A and α. `σ n` remains the existing scalar model
   with its actual sheafified extension, unit-section formula and K-flat transpose.
3. R, L, adj, hL, πP, `_hπP`, π, `_hπ` and `_hunit` retain exactly the same specified
   sequence pullback, total-limit projections and normalized adjunction equations.
4. The new `aModels` supplies the actual base tensor representative model, not a new
   tensor functor. The already supplied `d.levelTensorModels n` supplies its finite
   counterpart. Their `uncurry_model` ties closed transposition to chain evaluation.
5. Expanded `evaluatedTensorComparison`: rho inverse transports its input, e_n(mu)
   is the actual comparison, tensorEvaluation evaluates its target, and tensor(rho,rho)
   transports the two factors. Its source and target are exactly those of ν n.
6. Read all five fields of `ScalarTensorComparisonModel`. `_hμModel n` applies their
   pure tensor, total summand and K-flat localization normalization to the composite
   in point 5. `_hμ` then fixes ν to that composite. This closes the returned sign fault.
7. Both normalization hypotheses hP and `_hN` are unchanged. There remains no
   normalization of the Hom system J and no coefficient-flatness or boundedness premise.
8. V, J, b and delta retain their existing definitions. `homIdentification` evaluates
   only a normalized first Hom input and applies its actual contravariant rho transport.
9. The first two conjuncts retain the displayed reduced evaluation and its uniqueness
   among all A-linear derived arrows via the same scalar and closed Hom bijections.
10. The third conjunct retains internalScalarMap, H_A(P,π_n) followed by the existing
    inverse scalar-Hom comparison; the second input is not extended.
11. The fourth conjunct retains globalProjection with every actual delta, sections,
    hL, κ, πL and finite-evaluation transport. The two universal-unit normalizations of
    rl and κ remain unchanged. No arbitrary alternative global map has been substituted.
12. The fifth conjunct retains H0 of that very globalProjection, both uniquely
    resolution-normalized sections transports, and both ∃!-normalized
    coefficientHomZeroEquiv endpoints. Its result is the same scalar(h) followed by
    counitLevel. The new representative normalization fixes the comparison that acts
    on these classes, removing the remaining sign freedom identified by the maintainer.

A textual check confirms the entire conclusion from ∃ rl through the final Hom
equation is verbatim unchanged from the saved returned packet. There are now 26
recorded declarations, including the new constructed helper; the only four sorrys
are the same named theorems as before. The JSON signature was regenerated from the
file and all lines remain within 100 characters. All binders remain explicit.

### Searches and validation for this repair

Read the full live `ScalarTensorComparisonModel` source with `scompile.py --source`,
as well as the local `Models`, `CoefficientTensorModels.uncurry_model`,
`tensorModelIso`, `ScalarTensorPure`, `scalarEpsilonIso`, Data.tensorEvaluationModel,
Data.tensorEvaluationModel_ordinary and Data.levelTensorModels definitions. Read the
full canonical ringed-topoi representative theorem and its chosen comparison; the
existing scalar interface gives the same 07A4 normalization without imposing an
unnecessary equality between site object and morphism universes.

* `msearch.py leanfinder "K-flat representative normalization of canonical scalar
  extension tensor comparison for sheaves of modules"`: eight hits about flat modules
  and underived scalar extension; no statement of this node. Reused the project's
  exact `ScalarTensorComparisonModel` instead of introducing a second definition.
* `msearch.py loogle "CategoryTheory.Functor.isoWhiskerLeft, CategoryTheory.NatIso.prod"`:
  zero hits. Opened Mathlib Whiskering.lean and Products/Basic.lean directly and used
  their existing constructions in evaluatedTensorComparison.
* `msearch.py grep "ScalarTensorComparisonModel|KFlat.*TensorComparison"`: zero Mathlib
  hits. `rg` in the named upstream and project source directories located the existing
  generic model in SemilinearSystemModels and its uses in SemilinearDerivedCalculus.
* Compared saved node with current read-only main: the changes are lean and authorized
  additions/replacement of landed statement-dependency nodes. No Git command or direct
  mutation was performed in the shared repository. The prescribed first dry run passed
  unchanged as ae3f98053aa; the semantic defect was nevertheless repaired above.

The first repaired compile completed cleanly in sandbox mode (18.4 s) and library
mode (15.5 s). Final delivery validation is performed again after the direct public
import and final records/report are in place, through the prescribed wrappers only.

Final explicit scompile: clean sandbox (18.1 s) and library (19.4 s). The repaired
packet passed server preflight and per-file compilation in the prescribed dry run
as commit 8b63836a27e. The report headings now identify the fresh self-reading clearly.
