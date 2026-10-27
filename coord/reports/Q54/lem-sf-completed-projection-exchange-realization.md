## Worker report

The delivery states the completed projection/base-change diamond in
`Sheaf.SixFunctors.CompletedProjectionExchangeRealization`, namespace
`WeilConjectures.CompletedProjectionExchange`. It defines the actual two strict-system
composites and their normalized realizations, not arbitrary maps with assumed equalities.
All data definitions have explicit bodies. The three theorems
`completedProjectionExchangeRealization`, `completedProjectionExchangeRational`, and
`completedProjectionExchangeCommonStage` have only `sorry` proofs and belong to this node.
`Statement` is a transparent conjunction introduced to avoid repeated expansion of a
large theorem signature during compilation. No new mathematical notion or new node is needed.

Clause-by-clause correspondence:

- The global finite field, characteristic, closure and geometric base are `D : FiniteFieldDatum`.
  The coefficient prime is `l` with `[Fact l.Prime]` and `_hl : l ≠ D.p`. `E`, its field,
  Padic-algebra and finite-dimensional instances supply precisely the finite coefficient
  extension. The existing coefficient constructions fix its valuation ring, uniformizer,
  positive quotients and completed sheaf; they are not redefined here.
- The square is the existing `SixFunctorCompactifiedSquare D`: six finite-type objects
  over `Spec D.k`, four maps, two factorization equations, the Cartesian square, and the
  Cartesian open and proper compactification squares. The four displayed relative
  separated/finite-type hypotheses use `IsSeparated`, `LocallyOfFiniteType`, and
  `QuasiCompact` on f,g,f',g'. There is no absolute separatedness hypothesis on any scheme.
- `K : Integral ... X` with `_hK : sfIntegralConstructible ... K` is exactly bounded
  constructible derived-complete K. `_hL : finiteTorConstructibleIntegral ... L` is
  exactly the specified finite-Tor L. No Tor condition on K is assumed.
- `o : Operations l E` and `ρ : Realizations l E D o` are the recorded canonical
  sequence-site operations and normalized realization package. They retain derived
  system categories, actual reduction/limit adjunctions, quotient transitions,
  K-flat tensor/pullback comparisons, normalized open comparisons and ringed models.
  Their existence is the recorded dependency theorem. They are supplied presentation
  data, not a new unrelated operation package or an assumption of the desired diamond.
- `word Q : Fin 4 → Expression ...` records all four vertices, with input family
  `inputs K L` on `ULift Bool`. Its first word is G(f!K tensor L); second is G f!
  (K tensor f*L); third is f'!g'*K tensor g*L; fourth is f'!(g'*K tensor f'*g*L).
  `Statement` CONCLUDES geometricity and `Expression.domain` for each word.
  The recursive domain includes hidden open intermediates, actual normalization,
  compatible origin witnesses and uniform cohomology/Tor intervals at all positive
  quotient levels. No domain conclusion is moved into a hypothesis of the main theorem.
- `diamondLeft = diamondRight` is equality inside `System l E Y'`, before total limit
  or evaluation. `diamondLeft` is pullback of the specified projection, then specified
  compactification exchange, then the target tensor/square comparison. `diamondRight`
  inserts the source tensor/pullback comparison, exchange tensor identity and the
  primed specified projection. Both use the recorded `compactificationProjection`
  and `compactificationExchange` and have the same source and target.
- `OpenLaw` at K's reduction and p*L's reduction states each open-factor restriction
  equals `openSource`, an independently written composite of square/tensor comparisons
  and the inverse ACTUAL open unit. In particular the remaining map is the identity
  under these normalizations. It retains the necessary primed open pullback U'.
- `ProperLaw` at J(reduction K) and reduction L states separately that the transpose
  of `properFirst` and of `properSecond` is `commonTranspose`. The latter is theta,
  H(mu_F), mu_H, then H(epsilon_p,M) tensor theta_N inverse. No inverse of a projection
  or proper exchange is used.
- The root source and target integral constructibility predicates are conclusions.
  `integralLeft` and `integralRight` are the images of the two system routes under
  total limit, conjugated by precisely the SAME `ρ.comparison` endpoint isomorphisms.
  `CanonicalPair` for both routes asserts these are exactly the specified completed
  generator composites. Their equality is the displayed completed integral diamond.
  The concluding universally quantified `CanonicalPair` intertwining equation includes
  every finite expression context (pull, push, open, compact support, either tensor slot).
  `Realizations.comparison` already gives naturality in the original input family.
- `rationalLeft` and `rationalRight` apply exactly
  `sfRationalConstructibleLocalization` to the full-subcategory integral arrows.
  Their equality is included. `completedProjectionExchangeRational` covers any two
  integral representatives without a Tor assumption on either: raw localization has
  the same objects, so these are all rational inputs. It also concludes the domains
  and constructibility needed to form the representatives, avoiding a vacuous conditional.
- `completedProjectionExchangeCommonStage` works at ANY finite coefficient stage F of
  ANY fixed algebraic closure Ω. It applies the existing
  `GeneralAlgebraicallyClosedCoefficients.inclusion` to the same two rational arrows.
  The endpoint/domain arguments name properties already concluded by the preceding
  rational theorem. Its input L needs only integral constructibility. These are common
  finite-field representatives of arbitrary common-stage input pairs after enlargement;
  inclusion is the actual Hom-colimit functor, so identity fields and further scalar
  extensions retain their prescribed cocycles. No idempotent completion is used.
- The finite-affine-cover argument is retained in proof steps 2--6: restrict the same
  bounds, use the locality theorem, then take finite extrema. The conclusion is the
  resulting global recursive domains. Empty schemes use interval [0,0]. There is no
  separate assumed affine-cover bound or assumed origin of an intermediate object.
- No rational-to-finite reduction, evaluation faithfulness, or detection of equality
  by finite reductions occurs in any definition or conclusion. All equality transport
  is forward functoriality and conjugation by normalized realization isomorphisms.

The complete twelve-step natural-language node proof is reproduced in the main theorem
 docstring, including the proper scalar-mate transition formula, finite-extrema
 globalization, open restriction, proper transpose, explicit pasting and field transport.
The rational and common-stage theorem docstrings give their corresponding subproofs.

Dependency declarations used (recorded modules, not private replacements):

- `def-fix-six-functor-datum`: `Sheaf.Paper.SixFunctorOperationDatum`, `WeilConjectures.SixFunctorOperationDatum`; its reexported `SixFunctorCompactifiedSquare` supplies the geometric square.
- `def-sf-integral-system-operations`: `Sheaf.SixFunctors.IntegralSystemOperations`, `WeilConjectures.IntegralSystemRealization.Operations`.
- `def-weil-derived-complete-integral-detailed`: `Sheaf.Paper.SfIntegralConstructible`, `WeilConjectures.sfIntegralConstructible`.
- `def-weil-finite-tor-amplitude`: `Sheaf.Paper.FiniteTorAmplitudeSites`, `WeilConjectures.finiteTorConstructibleEtale`.
- `def-weil-pbc-etale-origin-witness`: `Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness`, `AlgebraicGeometry.Scheme.FixedEtaleOriginWitness`; retained through the recorded `Origins` in `Good`.
- `lem-sf-integral-compactification-system-realization`: `Sheaf.SixFunctors.IntegralCompactificationSystemRealization`, `WeilConjectures.IntegralSystemRealization.integralCompactificationSystemRealization`.
- `def-exchange-projection`: `Sheaf.Paper.ExchangeProjectionSuppliedDomains`, `CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionStage`.
- `def-weil-rationalization-karoubi`: `Sheaf.Paper.SfRationalizationKaroubi`, `WeilConjectures.sfRationalConstructibleCategory`.
- `def-weil-algebraically-closed-coefficients`: `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`, `WeilConjectures.generalAlgebraicallyClosedConstructibleCategory`.
- `def-coef-normalized-dvr-tower`: `Sheaf.Paper.NormalizedDVRTower`, `WeilConjectures.NormalizedDVRTower`; actual strict normalization is the recorded `IsNormalizedCoefficientSequence`.

All recorded proof-dependency modules are imported without `public` unless they are also
statement dependencies. Public imports expose all statement dependencies. The fixed
module-mode header is used in every compile probe.

Edge cases: f or g identity (all square and unit comparisons remain the canonical ones),
empty schemes/empty opens (no nonemptiness or point chosen), zero input (all displayed
maps remain well typed), coefficient exponent 1 (the existing zero index denotes exponent
1), identity quotient and repeated quotient transitions (the actual normalized tower
cocycles are retained), ramified coefficient extensions (no unramifiedness or flatness of
cohomology assumed), and arbitrary scheme universe u (ULift Bool gives two inputs in
Type u). The algebraic closure universe v is independent. Tensor target retains U'.

Searches:

- `msearch.py leanfinder`: "completed integral projection formula base change exchange
  diamond strict semilinear systems" returned eight unrelated adic-completion/profinite
  results, no such theorem.
- `msearch.py loogle`: "CategoryTheory.Adjunction.rightAdjointProjectionMap,
  CategoryTheory.mateEquiv" returned unknown identifier/no hits. The project source
  supplies the projection mate, used through the recorded dependency.
- `msearch.py grep`: "projection.*[Ee]xchange|exchange.*[Pp]rojection" in Mathlib
  CategoryTheory returned no hits.
- `rg` in `lean/WeilConjectures` found the etale finite-level projection/exchange theorem,
  cup-product exchange, and coefficient-reduction comparisons; none state the strict
  semilinear-system equality plus completed integral realization and both field stages.
- `rg` in `lean/Sheaf` found `IntegralCompactificationSystemRealization`,
  `ProjectionIntegralCoherenceRealization`, and `FiniteProjectionExchangeTransposes`.
  The first supplies the canonical generators/realizations, the second concerns
  projection composition/refinement, and the third concerns finite coefficients.
  None is the present node. Exact item-id search in WeilConjectures and Sheaf found
  no existing declaration.
- Read the current blueprint at latest/sec-six-functors/sk-thm-sf-compatibility/
  fix-prop-coherence.proof.md and sk-rem-sf-pf-done/fix-prop-projection-formula.proof.md.
  The old source path in the node has moved; no node field is changed for that move.

No statement correction, dependency repair, new node, or STATEMENT-DISPUTED flag.
Validation uses only the prescribed scompile.py and deliver2.py wrappers.

## Second reading by Q54

This is a second pass by the same dispatcher worker, not an independent agent review:
the assignment expressly prohibits starting agents; the maintainer supplies the
independent delivery review. Reopened the node and module and checked each clause
against the mapping above. Corrected the initial omission of unrestricted rational
inputs by adding `completedProjectionExchangeRational`, which derives their Tor bounds;
removed the analogous extra Tor hypothesis from the common-stage theorem. Restricted
the open/proper normalization assertions to the actual inputs in this node, instead
of silently asserting those stronger calculations for arbitrary unrelated systems.
Kept all four intermediate-domain assertions as conclusions. Checked the target
pullback comparison orientation and the required primed open pullback. No original
statement or DAG field other than lean is changed. Every helper is owned by this node
and listed in lean.declarations; every definition has real data and a source docstring.
