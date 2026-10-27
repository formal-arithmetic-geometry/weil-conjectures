## Worker report

The module `Sheaf.Paper.IsomorphismFiniteExchangeCoherence` states the node in eight
named theorems in `WeilConjectures.FiniteExchangeCoherence`. Every theorem proof is
`sorry`. The small helper definitions have actual data: they package the existing
constant ring sheaves and coefficient squares, descend existing identity/open
compositors, form the adjoint-conjugate proper compositor, and assemble the specified
proper/open mate. No arbitrary transformation or non-unique existence choice is supplied.

Hypotheses and clauses, checked against the node:

- `P : PurityFiniteSetting.{u}` retains the finite-field datum (including the fixed
  algebraic closure), the distinct prime ell, its fixed coefficient closure, the finite
  intermediate extension E and the positive level n. `P.Ring` is the recorded
  `Padic.coefficientExtensionRing`; `P.Coefficient` is its prescribed site-size ULift.
  `ringFinite` is exactly `finite_coefficientExtensionRing`, not an added hypothesis.
- The geometry section explicitly includes `Xbase`, `Ybase`, `Xft`, `Xqc`, `Xsep`,
  `Yft`, `Yqc`, `Ysep`, `fbase`, `fsep`, `fft`, `fqc`. These are the k-structures,
  separated finite-type structure maps, and separated finite-type k-morphism f.
  The primed and twice-primed schemes in the pasting statements also have the stated
  separated finite-type k-structures. Vertical composition includes the analogous
  structure on Z and the k-morphism condition on h. No `g.IsOver`, `h.IsOver` for
  horizontal base isomorphisms, or `x.IsOver` condition is imposed. The vertical
  base map g (the node's u) is also only an underlying scheme isomorphism.
- A chosen compactification is literally `Compactification f`, with `i=j`, `g=p`,
  and its factorization and open/proper fields. `sp` and `sj` are the Cartesian
  proper and open faces, with the actual arrows x and z. Together they present the
  specified pullback compactification and its projection-preserving identification.
  This allows arbitrary Cartesian realizations, including `c.baseChange` and
  `c.ofIsPullback`; the comparison is invariant under their unique identification.
  The chosen-square notion is not redefined. The outer square is the pasting of
  the two faces, and x and z are consequently isomorphisms when the base map is.
- `canonicalAgreement` identifies the formula used in all equations, `ordinaryH`,
  with `finiteChosenExchange`. The latter is the recorded
  `compactificationExchangeFromData`, applied to canonical pullback/direct-image
  adjunctions, `sourceSquare`, and the specified `singleBeta`. Thus this is exactly
  the proper-square mate followed by proper pushforward of open exchange.
- `identity` is e_1=1. The right hand side inserts `pullId`, the two functor unitors,
  and the inverse source identity comparison. Its supplied identity Cartesian faces
  are unique witnesses of the identity square, not extra mathematical assumptions.
- `horizontal` is e_(gh)=(e_h G_x)(G_h e_g). `paste` is the dependency's existing
  composition of transformations; `ordinaryGComp` inserts both canonical pullback
  compositors. `IsIso g` and `IsIso h` are the two underlying isomorphisms.
- `vertical` uses `Compactification.Triangle` and `CompositionBaseChange` for the
  supplied compatible tower and all its Cartesian base-change faces. It states
  `(G_u D); e_hf = (e_h F_f); (F_h' e_f); (D' G_x)`, with Lean's left-to-right
  composition order. The helper `composition` is the actual `singleDerivedGamma`
  whiskered by J_c and R_q, followed by open and proper compositors; no arbitrary D
  is quantified over. QuasiCompact assumptions on the displayed opens are precisely
  the compatible-tower conditions in the node and its dependency.
- `compositionIsIso` is the bounded-below etale-origin clause. Its input is the
  published `DerivedCategory.Plus`, with a retained `FixedEtaleOriginWitness` w.
  The input to D is its existing `etaleOriginRealization` in constant-ring coordinates.
  This is the same category via the recorded exact realization equivalence; the
  antecedent and comparison are retained. The theorem applies also to T' and its
  retained witness, giving both D and D'. Its docstring explains the constant strict
  tower and normalized evaluation identifying this very map with the dependency's D.
- `lower P m hm` changes only the positive level. `quotient P m hm h` is the
  site-size lift of `Ideal.Quotient.factor (Ideal.pow_le_pow_right h)` for the
  uniformizer ideals. Thus `hm : 1 ≤ m` and `h : m ≤ P.level` give every requested
  quotient A_n -> A_m, including m=n. `tensorQuotient` is the existing K-flat
  derived coefficient extension `pbcDerivedExtend` along the actual constant map.
- `properCoefficient` states the proper-factor square from proof step 4 using the
  existing `properComparison` and `scalarPull`. The former is the coefficient
  adjunction mate, with the proper counit characterization supplied by
  `coefficientOperationMateEquations`. No invertibility of this map is asserted.
- `openCoefficient` states the open-factor square from proof step 5 using the
  existing `openComparison` and `scalarPull`, and the existing `ordinaryBeta`.
  `openComparison` is the mate of the open-unit-normalized restriction square.
  These factor identities are identities of the constituent transformations on
  their ambient domains, as the node explicitly specifies.
- `coefficient` states the assembled quotient square from proof step 6. Its
  `hK : finiteTorConstructible ... K` is exactly the recorded finite constructible
  finite-Tor condition, rather than mere bounded constructibility. The compact-support
  coefficient arrow is the existing `PurCompactSupport.comparison`, with its fixed
  proper/open restriction-mate normalization. The existing operation-reduction
  theorem supplies its coefficient comparison and unit/counit compatibility.
- All equations concern ordinary unbounded pro-etale derived module categories.
  Site objects remain in u+1 and morphisms in u, and the standard localization is
  retained. Removing the globally imported `IntegralHom.derivedCategory` instance
  from instance search resolves an ambiguous coefficient universe; no site or
  coefficient universe equality was added.

Dependency declarations read and used (including proof imports):

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`, `.Ring`,
  `.Coefficient`, and their coefficient structures.
- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`:
  `AlgebraicGeometry.ChosenCartesianSquare` (the projection-preserving Cartesian
  presentation; faces are recorded by Mathlib `IsPullback`).
- `WeilConjectures.Compactification.RefinementCategory`:
  `AlgebraicGeometry.Compactification.Refinement` and `.category`, with the original
  `Compactification` definition from `.Defs`.
- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`:
  `CategoryTheory.SuppliedExchangeProjection.compactificationExchangeFromData`.
- `Sheaf.AlgebraicGeometry.CompactifiableCompatibleTower`:
  `AlgebraicGeometry.exists_compactifiable_compatible_tower` and the supplied
  `Compactification.Triangle` interface.
- `Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus`:
  `AlgebraicGeometry.ProEtale.StrictTower.normalizedProperOpenCalculus`.
- `Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness`:
  `AlgebraicGeometry.Scheme.FixedEtaleOriginWitness` and the publicly imported
  `etaleOriginRealization` from `RingedEtaleOriginWitness`.
- `Sheaf.AlgebraicGeometry.StrictTowerCompositionPasting`:
  `AlgebraicGeometry.ProEtale.StrictTower.compositionPastingCoherence`; its public
  `StrictTowerCompositionMaps` supplies `CompositionBaseChange`.
- `Sheaf.Paper.FiniteTorAmplitudeSites`:
  `WeilConjectures.finiteTorConstructible` (the retained pro-etale declaration).
- `Sheaf.Paper.BasicOperationsCoefficientReduction`:
  `WeilConjectures.basicOperationsCoefficientReduction` and the publicly imported
  `PurCompactSupport` coefficient data, `comparison`, `properComparison`,
  `openComparison`, `scalarPull`, and their defining adjunction formulas.
- `Sheaf.Paper.RelativeCompactSupportPasting`: `ordinaryH`, `ordinaryE`,
  `ordinaryBeta`, `ordinaryAdj`, `ordinaryGComp`, `paste`, `ordinaryPasting`,
  `quotientDomainAgreement`, and `ConstantCompactificationExchange.finiteChosenExchange`.
- `Sheaf.AlgebraicGeometry.TowerMateEvaluationScalars`: `coefficientMap`,
  `coefficient_square`, `singleDerivedGamma`, and the evaluation normalization laws.
- `Sheaf.AlgebraicGeometry.TowerOpenBetaNormalization`: `openBetaModuleGId` and
  `openBetaModuleJComp`; `singleJCongr` is the already constructed open-adjoint transport.
- `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`:
  `CategoryTheory.RingedDerivedComparisons.ringedDerivedMonoidalComparisons`.
- `Sheaf.CategoryTheory.Adjunction.CoefficientExchange`:
  `CategoryTheory.Adjunction.coefficient_exchange_of_counit`.
- `Sheaf.SixFunctors.OpenTensorNormalization`: `SheafOfModules.openTensorNormalization`.
- The mathlib mate-pasting leaf is the node's `mathlib_match`, namely
  `CategoryTheory.mateEquiv_vcomp`, `mateEquiv_hcomp`, and the conjugate/identity
  lemmas in `Mathlib.CategoryTheory.Adjunction.Mates`; no missing Lean record is needed.

The two already landed dependencies `lem-pur-relative-compact-support-pasting` and
`lem-cbc-tower-mate-evaluation-scalars` are added to stmt_deps because their canonical
operations occur in the statements and helper definitions. They were already proof
 dependencies; their nodes and modules are unchanged. No dependency repair, new node,
statement correction, or STATEMENT-DISPUTED issue is needed.

Edge cases checked before and during writing: identity base maps; both horizontal
maps identities; m=n; n=m=1; zero complexes; empty X; identity open immersion; identity
proper factor; and the identity compatible tower. The identity formula retains both
pullback unitors; the quotient uses the quotient factor even when m=n, and tensor
is not silently replaced by identity. Empty and zero inputs impose no nonemptiness
condition. No proper coefficient projection is inverted even in the factor equations.
The etale-origin witness is required only for invertibility, not for vertical equality.

Searches for reuse:

1. `msearch.py NJ lem-pur-isomorphism-finite-exchange-coherence leanfinder` with
   `Compactification exchange along scheme isomorphisms identity horizontal vertical pasting and quotient coefficient extension`:
   8 hits about gluing/pasting scheme morphisms, no whole-item theorem.
2. `msearch.py ... loogle 'CategoryTheory.Adjunction.mateEquiv, NatTrans'`:
   0 hits (the qualified name was unknown); reading the actual Mathlib module found
   the correct namespace `CategoryTheory.mateEquiv` and its pasting lemmas.
3. `msearch.py ... grep 'compactification.*exchange|exchange.*coefficient' CategoryTheory`:
   0 hits. Direct rg in Mathlib's `CategoryTheory/Adjunction/Mates.lean` found the
   generic mate laws, not this geometric finite quotient assembly.
4. `rg` in `lean/WeilConjectures` and `lean/Sheaf` for finite exchange, isomorphism
   finite exchange, semilinear coherence, and quotient exchange found component
   tools (especially `RelativeCompactSupportPasting`) and other strict/completed
   coefficient results, but no theorem with all these finite clauses.
5. `grep -rn 'lem-pur-isomorphism-finite-exchange-coherence' lean/WeilConjectures`:
   no attachment. `rg 'FiniteExchangeCoherence|isomorphismFiniteExchangeCoherence'`
   in both library roots and `dag/lean_names_upstream.json`: no name collision.

Source read: the current `literature/blueprint/latest/` proof of
`prop-pur-weil-equivariance-compatibilities`, together with this node's six explicit
reviewed proof steps and the cited dependencies' statements, signatures and docstrings.
The current blueprint's short assembly paragraph is supplemented by the node's
specified Stacks mate/open calculations; the blueprint unit is unchanged.

Validation: every compile used only the prescribed `scompile.py`. The final module
compiled in both sandbox and library coordinates with no warnings or errors, each
well within 60 seconds. The only postponed proofs are the eight named theorems above.

## Second reading by NJ

A separate self-audit reopened the node, all eight theorem statements and all helper
bodies. This is not represented as an independent worker review; the dispatch brief
forbids spawning agents and provides independent maintainer review at delivery.

The audit caught a context-retention issue: Lean drops unused section instances, so
all original geometric instances are now named and explicitly included. The audit
also added the missing Z and primed geometric binders, the actual chosen-exchange
agreement, and the retained bounded-below witness clause. The coefficient diagram
was checked arrow by arrow: first T(e), then kappa' at G_x K, then F'_m(chi_x),
versus chi_g at F_n K, G_g(kappa), and e_m at T(K). The proper and open squares
have the same orientations as the node's proof steps 4 and 5. Vertical composition
uses exactly R_q gamma J_c and its canonical compositors, with no arbitrary
isomorphism substituted. Identity, horizontal, vertical, invertibility and all three
coefficient clauses are present. No further mismatch was found.
