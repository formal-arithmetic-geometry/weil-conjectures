## Worker report

The module `Sheaf.AlgebraicGeometry.MonoschemeTowerComparisonCoherence` states
`AlgebraicGeometry.Monoscheme.TowerComparison.exists_coherentComparisons`. Its only new
postponed proof is that theorem, whose docstring reproduces the seven proof steps and
names their DAG dependencies. The auxiliary records belong to this comparison assertion;
they have actual structure data and no postponed definition bodies. The theorem asserts
existence of the complete comparison system with its equations, not an arbitrary map or
an isomorphism selected from an unspecified existence assertion. No new independent notion
or definition node is needed. There is no statement correction or mathematical dispute.

Clause-by-clause correspondence (names below are in `Monoscheme.TowerComparison`):

* “Use the monoschemes, toric realizations, centered towers and contraction”: the module
  publicly imports `Sheaf.AlgebraicGeometry.MonoschemeToricRealization`, and uses its
  `Fine`, `Hom`, `Hom.IsSmooth`, `Fine.IsTorsionFree`, `Tower`, `PullbackTower`,
  `Contraction`, `NormalizedTower`, `NormalizedPullback`, `NormalizedContraction`,
  `pullbackAlong`, `wholeIdeal`, `ringIdeal`, `realization`, `realizationMap`,
  `IsRealizationMap`, and `IsTorusEquivariant` unchanged. Full signatures and docstrings
  were read, including the local affine-chart description of saturated blowups.
* “Every Q[M] for fine torsion-free M with finite affine cover, including finite disjoint
  unions”: `Input := {M : Fine // M.IsTorsionFree}`. `Fine.finiteCover` already permits any
  finite atlas and the empty atlas. No connectedness or nonemptiness is imposed. The
  field is `ULift.{u} ℚ`, so the rational base fits the arbitrary monoscheme universe.
* “A rule assigning a finite normalized blowup tower”: `SchemeRule.tower`, with
  `SchemeTower.length`, `.tower`, and `.base`. There is no terminal regularity or
  desingularization hypothesis. All centers and their original order are retained by
  the dependency's normalized tower.
* “Each center coherent and torus invariant”: coherence is precisely the affine finite
  generation condition of `NormalizedTower.blowup`/`IsNormalizedBlowup`;
  `LiftRule.invariant` tests equivariance of each actual scheme center transported by
  its canonical toric identification. This tests the same ideal on the same scheme;
  it does not introduce a substitute torus or merely identify supports.
* “Every smooth scheme morphism between these schemes”: `SchemeRule.comparison` takes
  any scheme map `a` and a proof of `Smooth a`; it is not restricted to maps induced
  by monoids. `SchemeComparison.pulled`, `.pullback`, `.contraction`, `.baseMap` and
  `.baseIso` specify the recursive contracted pullback over the given base map.
  `NormalizedPullback.centers` and `NormalizedContraction.keptCenter` preserve actual
  ordered ideals. The four `SchemeRule.identityIndex`, `.identityMap`,
  `.compositionIndex`, and `.compositionMap` fields are the assumed identity and
  composition compatibilities, including the index contractions.
* “Unique centered saturated lift through canonical identifications”: `LiftRule.lift`
  supplies a `Lift`. Its `.tower` is the existing saturated chart-defined tower,
  `.base` identifies the base, `.torsionFree` applies at every level, and each level
  is already a `Fine` with finite cover. `.iso`, `.baseIso`, `.arrows` and `.centers`
  identify realization, actual canonical monomial maps, and ideals. `LiftRule.unique`
  gives existence and uniqueness of the centered, realization-preserving `LiftIso`
  to any other such lift; uniqueness is up to the specified isomorphism, not literal
  equality of presentations. `LiftIso.localHom`/`.localInv` enforce local monoscheme
  morphisms in both directions. Canonical blowup-chart identifications are forced by
  the dependency's exact `IsSaturatedBlowup` charts and compatibility with arrows.
* “For every smooth a there is a canonical comparison”: `CoherentComparisons.comparison`
  supplies `Comparison T a (...)` for every `Hom` and its smoothness proof.
  `CoherentComparisons.realizationSmooth` supplies the consequence that Q[a] is
  smooth; thus scheme smoothness is not an extra assumption on the user of the result.
  `Comparison.pulled` identifies the full scheme pullback with a saturated lift,
  `.pullback` is recursive pullback, `.contraction` identifies the contracted tower
  with the assigned lift. The inverse direction of its level isomorphisms is the
  displayed comparison T(N) ≃ (a*T(M))^c. `.baseMap` and `.baseIso` impose the given
  base map and identity over N. `CoherentComparisons.unique` states uniqueness of
  the induced centered level maps for any two presentations of that comparison.
* “Its realization is the specified comparison”: `Comparison.pullbackRealizes` and
  `.contractionRealizes` give `IsRealizationMap` of the actual maps and the supplied
  scheme comparison maps, transported through the lift identifications. `.index`
  equates the contraction maps themselves. Localness of the isomorphisms and their
  inverses is explicit in `.contractionLocal`.
* “Each retained ideal recursively pulled back, order unchanged”: the supplied
  `PullbackTower.centers` imposes exactly `pullbackIdeal` at every original index;
  `Contraction.keptCenter` transports that actual ideal to every retained stage.
  Its monotone surjective index map and adjacent-index condition preserve order.
* “Both deletion conditions respected, retaining nonidentity normalization/saturation”:
  `Comparison.unitCenter` is equivalence of the whole monoid ideal with the unit
  ring ideal; `.isoStage` separately equates the two isomorphism tests. The existing
  `Contraction.deleted` and `NormalizedContraction.deleted` require their conjunction.
  Consequently a whole-ideal nonisomorphism remains, as does a proper principal
  ideal stage even when its arrow happens to be an isomorphism.
* “Identities and composition, including successive contractions”: the four
  `CoherentComparisons.identityIndex`, `.identityMap`, `.compositionIndex` and
  `.compositionMap` fields give the index and level-map equations. They quantify over
  arbitrary supplied local maps whose underlying morphisms are the identity/composite,
  so proofs of localness do not choose a different comparison. `HEq` transports only
  the explicitly equated source index. `.successiveContraction` additionally gives
  actual isomorphisms between each full single-pullback level and the corresponding
  successive-pullback level after the first contraction, compatible with both
  contraction isomorphisms and the maps to the original tower. Thus the successive
  contraction identification is data with equations, not only equality of lengths.

Edge cases checked before writing: empty atlas and empty input; length zero; identity
and rank-zero smooth maps; arbitrary disconnected finite covers; consecutive deleted
stages; all stages deleted; whole ideal with nonidentity normalization (e.g. saturation
of the cusp monoid); proper principal ideal with identity blowup; unequal tower lengths
after contraction. `Fin 0` makes center/arrow assertions vacuous for length zero, while
`Fin 1` retains the base and coherence conditions. There is no global normality,
regularity, surjectivity, nonempty-input or connectedness assumption. Every universe
and variable is explicit, with both auto-implicit settings false.

Searches for an exact existing statement:

* `msearch.py leanfinder`: “Smooth pullback comparisons of centered monoscheme saturated
  blowup towers respect identities composition and contraction” returned 8 ordinary
  scheme-pullback identities (`Scheme.Pullback.t'_snd_snd`, etc.); none has monoid
  centers, saturated towers, or descent of a specified comparison.
* `msearch.py leansearch`: “Canonical comparisons of toric normalized blowup towers
  descend to saturated monoscheme towers with identity and composition coherence”
  returned 8 normalization factorization identities; no match.
* `msearch.py loogle`: `Monoscheme, PullbackTower, NormalizedContraction` returned zero
  hits, with unknown Mathlib identifier `Monoscheme`.
* `msearch.py grep`: `Monoscheme|NormalizedContraction|PullbackTower` in
  `Mathlib/AlgebraicGeometry` returned zero hits.
* `rg` on `lean/WeilConjectures` found no monoscheme declarations or node-id match.
  `rg` on `lean/Sheaf` located the existing realization/tower definitions and the
  specialized desingularization rule. The latter includes terminal regularity and
  additional center and surjectivity conditions, and therefore is not the general
  rule in this node. The fan rule is for sharpened fans, not monoschemes. The
  `NormalizedTower.CenterIso` definition is for synchronized scheme towers and
  cannot express the mixed monoid/ring comparison here.
* `tools/blueprint_refs.py search 'monoscheme tower comparison'`: zero blueprint
  matches. The assigned node already owns the particular descended-comparison
  assertion, and the auxiliary records merely unpack its hypotheses and conclusion.

Source read: the local ILO PDF, physical pages 111--112 = printed pp.105--106,
including 3.2.14--3.2.20 and its description of descent and contracted functoriality.
The supplied node expands that source into the seven precise induction/coherence steps.
No outside mathematical assertion is used to change the statement.

The stated proof dependencies are imported without `public`. The saturated monoscheme
blowup universal-property node has no recorded Lean declaration, so there is no module
of that node to import; its planned use is retained explicitly in the proof docstring.
The item has a complete statement using the already recorded chart-defined blowup
notion and needs no missing theorem as a statement hypothesis.

## Dependency modules

The required module-mode compile initially failed with:
`cannot import non-module Sheaf.AlgebraicGeometry.ToricMonoidComparison from module`.
The server sources, read using `scompile.py --source`, confirm that the proof-dependency
closure has eight legacy files. This packet repairs their module interfaces only:
`module`, `public import` and `@[expose] public section` are added. All mathematical
signatures, declarations, definitions and proofs are preserved. Each dependency node
changes only `lean`, with its exact signature reread from the delivered file and a
`note` explaining this failure. Every file is compiled separately in dependency order.

* `lem-trf-toric-monoid-comparison`: `Sheaf.AlgebraicGeometry.ToricMonoidComparison`,
  chiefly `AlgebraicGeometry.Monoscheme.toric_ideal_comparison`,
  `.toric_blowup_comparison`, and `.realizationMap_smooth`.
* `lem-trf-affine-monoid-algebra-normalization`:
  `Sheaf.RingTheory.AffineMonoidAlgebraNormalization`,
  `MonoidAlgebra.affine_monoid_algebra_normalization` and its canonical maps.
* `lem-trf-toric-realization-finite-type`:
  `Sheaf.AlgebraicGeometry.ToricRealizationFiniteType`,
  `AlgebraicGeometry.Monoscheme.toric_realization_finite_type` and its torus bundlings.
* `lem-trf-integral-support-saturation`: `Sheaf.RingTheory.IntegralSupportSaturation`,
  `MonoidAlgebra.support_subset_saturation_of_isIntegral` and its helpers.
* `lem-trf-integral-support-weighted-initial-degree`:
  `Sheaf.RingTheory.IntegralSupportWeightedInitialDegree`,
  `AddMonoidAlgebra.not_isIntegralElem_of_negative_support_weight` and its helpers.
* `lem-trf-monoid-algebra-domain-fraction`:
  `Sheaf.RingTheory.MonoidAlgebraDomainFraction`,
  `AddMonoidAlgebra.domain_fraction_of_fg_generating_submonoid` and its helpers.
* `lem-trf-monomial-integrality`: `Sheaf.RingTheory.MonomialIntegrality`,
  `AddMonoidAlgebra.monomial_integrality` and its helpers.
* `lem-trf-saturated-monoid-algebra-normal`: `Sheaf.RingTheory.SaturatedMonoidAlgebraNormal`,
  `MonoidAlgebra.saturated_monoid_algebra_normal` and its helpers.

`Sheaf.AlgebraicGeometry.NormalizedBlowupCalculus` was already usable and is imported
unchanged for `AlgebraicGeometry.Scheme.IdealSheafData.normalizedBlowup_calculus`.

## Second reading by Q47

I reread the complete node and module clause by clause after the first draft. An initial
interface required the caller to supply smoothness of Q[a]; this would have exposed an
extra assumption rather than the desired consequence. The final system includes
`realizationSmooth` and uses its proof internally. I also added uniqueness of the induced
comparison maps and explicit `successiveContraction` isomorphisms with equations, so
canonicity and the final identification of successive contractions are not merely
implied by an index-count equality. The first compile's unused-argument warning was
removed by the same smoothness correction. No mathematical statement was changed.
The module-only dependency repairs were compared with the live server sources and
preserve all their mathematical content. No independent subagent was started, as the
worker brief expressly prohibits starting other agents; independent maintainer review
remains the delivery's external check.

Validation: `scompile.py Q47 lem-trf-monoscheme-tower-comparison-coherence` with all nine
modules passed (exit 0) with no compiler diagnostics or warnings. The wrapper compiled
the modules separately in dependency order, under both sandbox and library module names,
against the published server build. A direct source round-trip check against the server
confirmed each of the eight dependency edits is module-format-only.
