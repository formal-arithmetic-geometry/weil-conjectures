## Worker report

The module `Sheaf.SixFunctors.KunnethSecondOpenSubstitution` states
`AlgebraicGeometry.ProEtale.KunnethSecondOpen.kunneth_second_open_substitution`.
It has one postponed theorem, with all five natural-language proof steps in its
docstring, and real definitions for its specified arrows. No statement correction,
dependency repair or extra mathematical hypothesis is used. The repair adds definition-node ownership for the already published proper/open mate.

Hypotheses and definitions, clause by clause:

- The distinct primes, positive finite-field exponent, algebraic closure of the
  finite field, and fixed coefficient extension are the existing `D : FiniteFieldDatum`,
  `C : D.CoefficientDatum`, `E`, `[Field E]`, `[Algebra (Padic C.l) E]`, and
  `[FiniteDimensional (Padic C.l) E]`. The positive coefficient level is `{n}`,
  `{hn : 1 ≤ n}`. `S : SixFunctorDatum D C E n hn` is precisely the recorded datum.
  The coefficient in fixed-scalar coordinates is
  `ULift.{u + 1, u} (Padic.coefficientExtensionRing C.l E n)`; the existing
  `Padic.finite_coefficientExtensionRing` supplies finiteness. There is no field
  coefficient substitution or unrelated scalar ring.
- `B₀ X₀ Y₀ Yb₀ : SixFunctorSpace D` means the finite-type schemes in the fixed
  field setting. Each has its explicit structural `[IsSeparated ...obj.hom]`.
  `a₀`, `b₀` are proper; `k₀` is an open immersion. Morphisms between these
  finite-type separated schemes have the required finite-type/separated properties.
- `Diagram a b k U W` retains chosen product cones: `barSquare` is W, `square`
  is U, `openSquare` is the Cartesian square (w,s,Q,k), and `left` is w P = r.
  The open w is the unique induced product open, as specified by these projection
  equations. These cone data are choices of the two products, not extra geometry.
  `Diagram.properQ` and `.properS` derive properness by base change of a.
  The source Y is Noetherian since it is finite type over the field, so k is
  quasi-compact; `.quasiCompactW` derives quasi-compactness of w by base change.
  No such properties occur as additional hypotheses of the theorem.
- M and L have exactly types `finiteTorConstructibleCategory ... X₀.obj.left`
  and `... Y₀.obj.left`. `FiniteAssertion` applies the inverse of
  `sixFunctorFiniteRealization` to their underlying objects. This is the canonical
  fixed-scalar presentation of the recorded intrinsic categories, used already by
  `OpenExternalTensor.FiniteAssertion`, not a restriction to a different category.
- Pullbacks are `FiniteOpenProduct.pull` (exact inverse image with its canonical
  total-derived comparison); tensors, their maps, and signed symmetries are the
  recorded `tensor`, `tensorMap`, and `sigma`. Direct images are the existing
  `lowerStar ... .rightDerivedFunctor`, open extensions are `finiteShriek`.
- `ambient d M` is H = P_P M and `inside d M L` is N = P_w H tensor P_s L.
  `external` is exactly `tensorMap identity beta.hom` followed by `rho`;
  `beta` is the normalized canonical open base change and `rho` inserts both
  signed symmetries around the existing gamma. Thus this is the specified e2,
  the one-open external tensor map, rather than an arbitrary endpoint isomorphism.
- `openExchange d C` is E_C: canonical `derivedBaseChangeMap` conjugated by the
  exact/derived inverse-image identifications, with no chosen exchange arrow.
  `inner` is T = PF_s (E_H tensor identity).
- `gamma d C` uses the already published `properOpenMate` on (w,s,Q,k).
  Assertion's first conjunct is its defining open-adjunction characterization:
  unit_k; P_k(Gamma_C); E_(J_w C) = S_s(unit_w,C).
  Since E and unit_w are invertible, this says precisely that Gamma is the
  J_k-adjoint of inverse E after the specified unit identification. It includes
  no hypothesis that the desired projection square already commutes.
- `properCoordinates` and `openCoordinates` are the canonical identity-open and
  identity-direct-image isomorphisms for the proper and open compactifications.
  `alphaKS` and `alphaQW` use `coherenceProEtaleCompositor` at (identity,s),
  (k,identity), and (w,identity), (identity,Q), respectively. Their common target
  is (w,Q). Assertion's second conjunct is
  Gamma_C; alpha_Qw,C = alpha_ks,C, equivalently the node's
  Gamma_C = inverse(alpha_Qw,C) alpha_ks,C. It is stated for every bounded-below
  etale-origin presentation (O,e) of C; these only evaluate the canonical
  compositor. They are not extra inputs of the main theorem, nor arbitrary maps.
- Assertion's third conjunct says exactly
  PF_Q; S_Q(e2) = Theta_k; J_k(T); Gamma_N.
  `squareLeft` expands the left side and the right uses the recorded `rho` for
  the signed open projection Theta_k. The two signed swaps are retained.
- Assertion's final conjunct is `substituted = extended`. This is the final
  lambda equality in the specified iterated target S_b S_Q J_w N, before the
  common outer invertible compositor alpha_(b,Q). Naturality of that compositor
  gives the version with its single-shriek target. `substituted` uses the actual
  `projectionMapOfCompactification` for (k,b), thus PF_(bk) itself, preceded
  and followed by the signed symmetries. It then applies Ex_(a,bk), PF_s, the
  canonical w P = r pullback comparison and S_b(Gamma_N). `extended` uses
  Theta_b, Ex_(a,b), PF_Q and S_b S_Q(e2). Suppressing the common invertible
  outer alpha is an equivalent equality, not a weakened conclusion.

Recorded dependency declarations read and used:

- `Sheaf.Paper.SixFunctorDatum`: `WeilConjectures.SixFunctorDatum`, its actual
  finite operation datum, and `sixFunctorFiniteRealization` from its public imports.
- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`:
  `CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionStage`, its
  `.exchange`, `.compactExchange`, `.projection` mate composites. At finite
  coefficients their concrete specializations are `derivedBaseChangeMap`,
  `rightDerivedLowerStarProjectionMap`, and `projectionMapOfCompactification`.
- `Sheaf.Paper.SixFunctorDualNotation`: `SixFunctorDatum.finiteCoefficientDual`
  and the documented concrete finite projection notation publicly reexported there.
- `Sheaf.Paper.CanonicalOriginCompactSupportComposition`: `originComposition`,
  `originCompositionAmbient`, `originCompositionWitnessed`; their canonical
  chosen-compactification evaluation is `coherenceProEtaleCompositor` from the
  publicly imported `CompactSupportSiteCoherence` interface.
- `Sheaf.Paper.ProEtaleConstructibleOrigin`:
  `constructible_proEtale_origin`, identifying the bounded constructible domain
  with its etale-origin presentation. It justifies evaluating alpha in this domain.
- `Sheaf.SixFunctors.OpenTensorNormalization`: `openTensorNormalization`,
  the public finite `finiteShriek` and `finiteGamma`, and the beta/gamma unit
  normalizations used by the proof plan.
- `Sheaf.SixFunctors.OpenExternalTensorNormalization`:
  `OpenExternalTensor.finite_open_external_tensor_normalization`, its `Diagram`,
  `comparison`, and `FiniteAssertion`; the one-open specialization supplies e2.
- `Sheaf.SixFunctors.ProperOpenProjectionMate`: `properOpenMate` and
  its plain helpers listed by `def-sf-proper-open-mate`. This new definition node
  replaces the returned theorem dependency in stmt_deps. No conclusion of
  `properOpenProjectionMate` is needed to type the statement; tensor compatibility
  remains a proof dependency exactly as in the original DAG.

Proof imports are `ExchangeFunctoriality`, `CartesianOpenAdjunctionRestriction`,
`CompositionProjectionMate`, and `ProperOpenProjectionMate` (the last is public
because it also supplies Gamma), together with Mathlib's proper-base-change
instances. `prop-sf-pf-coherence` has no Lean declaration/module yet, so there is
no module to import for that proof dependency. The downstream
`ProductCompactificationIdentity` module is deliberately not imported: its proof
cites this very node; importing it would close that planned proof-import cycle.
Its coordinate helper composites were read; this module only specializes and
composes the already recorded operations, and defines no replacement operation.

Edge cases checked: k = identity gives the identity-open comparison and the usual
proper compositor; Y empty gives the zero open extension and zero maps; M = 0 or
L = 0 gives zero composites. The same applies when Xbar, W or U is empty. Level
n = 1 is allowed, with no extra regularity or characteristic assumption. There is
one explicit scheme universe u and the existing u+1 coefficient-module convention;
no site object/morphism universe equality or arbitrary smaller universe is imposed.
The quantification in the compositor formula is limited to its actual etale-origin
domain, whereas the defining open adjunct equation is on arbitrary C as in the node.

Searches made (raw remote search output is also in searches.jsonl):

- LeanFinder via msearch.py: "The compact support Kunneth exchange projection
  composite is compatible with extension by zero in the second factor". Eight
  hits about compactly supported functions, no sheaf/derived statement match.
- Loogle via msearch.py: `"projectionFormula", "baseChange"`. Zero hits.
- Mathlib grep via msearch.py: `secondOpen|second_open|kunneth.*open`. Zero hits.
- LeanSearch via msearch.py: "The proper open projection square gives
  compatibility of compact support Kunneth map with extension by zero in the
  second factor". Eight hits, concerning function support, ordinary proper
  topological maps, complex embeddings and trivial square-zero extensions; no match.
- rg in both project roots and Mathlib for
  `secondOpen|second_open|kunneth.*[Oo]pen|[Oo]pen.*[Kk]unneth`: no matching theorem;
  project hits are other Kunneth constructions and the downstream proof citation.
- rg for the exact node id in WeilConjectures and Sheaf: only the downstream
  ProductCompactificationIdentity proof documentation. No existing declaration.
- `tools/blueprint_refs.py search 'Kunneth composite'`: zero matches;
  `ancestor` identifies `lem-sf-kunneth-coherence`, whose current latest proof
  was read, including its compactification reduction and canonical PF/Ex route.

Validation: scompile.py compiles this module in sandbox and library module modes.
The final clean run has no warnings except the expected postponed-theorem warning
(which the wrapper suppresses). No global build or local Lean compiler was run.
No disputed statement or node fault was found.

## Second reading by Q30

I reread the node, its current blueprint proof and every assertion conjunct after
writing the module. This is a second pass by the same dispatched worker; no separate
agent was started. The maintainer's independent review remains the delivery review.
The comparisons were checked from their actual source signatures: both open signed
swaps are present; beta has orientation P_Q J_k to J_w P_s; inner has E_H before
PF_s; Gamma points J_k S_s to S_Q J_w; the first compositor equation has alpha_Qw
on the right of Gamma in Lean's left-to-right order; and the final equation uses
PF_bk of the chosen compactification rather than assuming projection composition.
The exact adjunct equation uses the units on both sides, rather than replacing
Gamma by a freely chosen isomorphism. The proper/open and exact/derived coordinate
comparisons are actual named natural isomorphisms. Initial compiler diagnostics
found two missing explicit public imports, an omitted identity-map argument, and a
coefficient-finiteness helper with an uninferable positivity argument; these were
repaired, with the helper removed in favor of the existing local finite instance.
The public theorem has no QC/proper projection premises beyond the node's a,b,k
assumptions. All helpers are real composites; the only sorry is the named theorem.


## Repair H2

The independent review of immutable head `747a44a035d9` accepted the mathematics
and returned the added theorem stmt_dep used solely for the plain `properOpenMate`.
Replaced that added edge by `def-sf-proper-open-mate`, an `existing: true` record
on `Sheaf.SixFunctors.ProperOpenProjectionMate`. The module and its named theorem
are byte-identical to the returned delivery (SHA256
`bd62f1c913938f15b0f0fbae8f6467dc2d0d02584b55dd30b72b73201133360d`).
The item's statement, proof, proof_deps and original seven stmt_deps are unchanged.
Against current main, the only added stmt_dep is the new definition node.

## New nodes

`def-sf-proper-open-mate` records the existing ordinary constant-coefficient
proper/open adjunction mate, its categories, pull/push/open functors, open adjunction
and compositors, canonical beta, clopen projection and alpha. Its signature is
verbatim from the published source. It uses the unit-alpha-counit construction of
Stacks 0F7B and the normalized clopen geometry already recorded in
`def-cbc-strict-tower-proper-open-arrows`; it claims no projection compatibility.
The new node cites the owners of the operations its bodies use, including the
derived adjunction, exact/derived identification, open adjunction, inverse-image
composition, ordinary open base change, geometric clopen lift and abstract mates.
LeanSearch (canonical proper/open derived mate) returned eight generic topology
and adjunction hits; Loogle (`"mateEquiv"`) returned twelve abstract mate hits;
Mathlib grep returned generic adjunction mates. The raw search results are stored
in the node. DAG/project/blueprint searches found the exact existing Sheaf
construction, but no definition node owning it. There is no duplicate Lean module.

Repair second reading by Q30: checked the new node against every listed plain
definition. Alpha has beta followed by the clopen projection and normalized
compositors; Gamma has unit_p, alpha, counit_r in that order. Both horizontal
opens retain quasi-compactness and both vertical maps retain properness; no
Cartesian hypothesis is imposed in the new general definition. The item's
Cartesian specialization and all previously reviewed edge cases are unchanged.
