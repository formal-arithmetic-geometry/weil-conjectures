## Worker report

Item: lem-pur-etale-support-exchange-right-mate. Module:
Sheaf.AlgebraicGeometry.EtaleSupportExchangeRightMate. Namespace:
AlgebraicGeometry.Etale.EtaleSupportExchange. Main declaration: rightMate_eq.
The lean.declarations list records all five helpers and all six theorem clauses.
Every theorem has exactly the proof by sorry. Every helper is an explicit
composite of existing canonical maps, with no sorry or arbitrary iso choice.

Source read: literature/stacks-project/etale-cohomology.tex, Tag 03S6
(lemma-shriek-base-change), including its proof by comparison of adjunctions;
literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-prop-cohsm/
lem-pur-co-smooth-etale-locality.proof.md, Step 1; the full DAG statement and
five proof steps; every statement dependency's statement and recorded interface.
The theorem docstrings carry the corresponding proof steps and dependencies.

Hypothesis-by-hypothesis correspondence:

- Finite commutative coefficients: A : Type (u + 1), CommRing A, Finite A.
  This uses the existing ordinary small-etale ModuleCat encoding, includes the
  zero ring, and imposes no characteristic or nontriviality hypothesis.
- U, X, X' : Scheme.{u}; e : U ⟶ X; w : X' ⟶ X. Each scheme has precisely
  IsLocallyNoetherian and CompactSpace. This is equivalent to the node's finite
  affine cover by Noetherian spectra: Mathlib.AlgebraicGeometry.Noetherian
  defines IsNoetherian as local Noetherianity plus compactness and proves
  isNoetherian_iff_of_finite_affine_openCover.
- Etale e, IsSeparated e, QuasiCompact e express separated etale finite type.
  Etale supplies LocallyOfFiniteType. There is no etaleness or flatness of w.
- U' is pullback w e; e' is pullback.fst w e; w' is pullback.snd w e.
  The library uses the swapped product order, with its specified square
  (IsPullback.of_hasPullback w e).flip. This is the same fibre product up to
  its canonical product-symmetry identification, respecting both projections.
  U' inherits Noetherianity from etale finite type over X'; no additional
  Noetherian hypothesis on the fibre product is imposed.
- c : Compactification e supplies its open immersion and proper structure
  morphism; c' initially is c.ofIsPullback of that square. No finite c.g or
  additional assumption on c.Z occurs.
- DerivedCategoryModule A T is definitionally DerivedCategory of small-etale
  sheaves valued in ModuleCat.{u + 1} A. It is the ordinary unbounded category.
- F is the recorded rightDerivedLowerShriekOfCompactification (ModuleCat A) c,
  definitionally degreewise open extension followed by total derived direct
  image. G, G', adj, adj' quantify arbitrary right adjoints and adjunction
  structures, including their exact chosen counits.
- S is (etaleLowerShriek (ModuleCat A) e inferInstance).mapDerivedCategory.
  Its adjunction and evaluation are the existing
  derivedEtaleLowerShriekUpperStarAdjunction and its counit.
- d is canonicalEtaleCompactSupportComparison A e c: the inverse of the
  constructed descended graph-extension morphism. This is the graph/derived-unit
  normalized proper-support/sum comparison, never a free iso parameter.
  The already landed node lem-asd-compact-support-graph-derived-isomorphism
  is added to stmt_deps to name this existing canonical map explicitly.

Clause-by-clause correspondence:

- exchangeIso assembles exactly the three factors of the existing
  exactCompactSupportExchange: exact-to-left-derived inverse-image transport,
  rightDerivedLowerShriekOfCompactificationBaseChangeMap, and transport back.
  Its middle map is made an iso using the existing named unbounded proper
  base-change theorem with isAddTorsion_of_finite. Its hom is the specified C.
- b^Sigma is exactEtaleSumExchange A e w, whose existing definition descends
  the specified etaleLowerShriekBaseChangeMap degreewise, inverts it, and
  inserts the canonical derived-composition identifications.
- inverse_comparison states (J d' inverse) followed by C inverse equals
  b^Sigma inverse followed by (d inverse H). Lean composition is diagrammatic,
  so this is exactly the node's first displayed inverse-comparison equation.
  Equality of isos is equivalent to equality of their forward morphisms.
- rightAdjointIso is conjugateIsoEquiv adj sumAdj d.symm, so its hom is
  precisely the conjugate rho = (d inverse)^c with the required direction.
- rightMate is mateEquiv adj adj' applied to the actual inverse exchange.
  The existing mate definition makes its component the adjunct of
  C.inv.app (G.obj K) followed by H.map (adj.counit.app K), exactly B.
- rightMate_eq is the natural-transformation identity B followed by H(rho')
  equals (rho J) followed by chi, on the whole unbounded D(X_et,A).
  Chi is the inverse of exactDerivedSquareUpperStarIso (ModuleCat A) sq:
  the existing square iso goes H then e'^* to e^* then J; its inverse has
  exactly the node's direction J e^* to e'^* H.
- common_transpose quantifies arbitrary K : DerivedCategoryModule A X.
  Its left side is d' inverse at JGK, then C inverse at GK, then H(epsilon_K).
  Its right side is S'(J(rho_K) followed by chi_K), then evaluation at HK.
  These are precisely the displayed common-transpose morphisms in the node.
- counit_characterization says that for any natural transformation rho the
  counit equation at every K holds iff rho equals the specified conjugate.
  This includes both satisfaction and uniqueness, and specializes to a=e
  and a=e' without extra hypotheses. Invertibility is supplied by the
  constructed rightAdjointIso, not a separate assumption.
- rightAdjointIso_refinement says theta followed by rho(c) equals rho(d);
  theta is the actual adjunction conjugate of the canonical compactification
  comparison. Arbitrary c,d include every proper refinement and common
  refinement identification.
- exchangeWithTarget transports C to any c' by the existing canonical
  common-refinement iso. rightMateWithTarget takes its actual adjunction mate.
  rightMate_refinement says J(theta) followed by B(c,c') equals B(d,d')
  followed by H(theta'), for arbitrary c,d,c',d' and all four adjunctions.
  This is the node proof Step 5 formula and covers any chosen compactifications.
  Together with rho compatibility, the common transpose and counit
  characterizations transport by the same comparisons.
- All identities are of natural transformations or natural isomorphisms,
  except the explicitly componentwise common transpose and counit formula,
  which quantify every unbounded input.
- No finite-r, flat-w, etale-w, dimension, boundedness, constructibility,
  or nonzero-coefficient condition is present.

Dependency declarations used (several are exposed by the public transitive
imports of their recorded modules):

- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme, Scheme.Hom.
- Mathlib.RingTheory.Noetherian.Defs: IsNoetherianRing. Its scheme version uses
  Mathlib.AlgebraicGeometry.Noetherian.IsLocallyNoetherian and IsNoetherian.
- Mathlib.AlgebraicGeometry.Morphisms.Etale: AlgebraicGeometry.Etale.
  The scheme-property collection node has no declaration of its own:
  its named IsSeparated, LocallyOfFiniteType, QuasiCompact are reused.
- Sheaf.AlgebraicGeometry.ChosenCartesianSquare: ChosenCartesianSquare.
  The concrete canonical product and square use Mathlib pullback and IsPullback.
- WeilConjectures.Compactification.RefinementCategory:
  Compactification.Refinement and Compactification.category.
- WeilConjectures.AlgebraicGeometry.DerivedCategories and
  WeilConjectures.SixFunctors.Etale.Derived.Coefficients: DerivedCategoryModule,
  with Mathlib DerivedCategory.
- WeilConjectures.SixFunctors.Etale.Derived.LowerShriek:
  rightDerivedLowerShriekOfCompactification and its canonical Iso.
- WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint:
  isLeftAdjoint_rightDerivedLowerShriekOfCompactification supplies existence;
  the statements quantify arbitrary such adjunctions.
- WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap: etaleLowerShriek.
- Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality exposes
  derivedEtaleLowerShriekUpperStarAdjunction, actually defined upstream in
  WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMapProjection.
- Sheaf.AlgebraicGeometry.QuasiFiniteCompactSupportExact:
  quasifiniteCompactSupportExact supplies the proper-support/sum identification
  and independence used in the proof plan. It is publicly imported.
- Mathlib.CategoryTheory.Adjunction.Mates: conjugateEquiv, conjugateIsoEquiv,
  mateEquiv and their counit characterizations.
- Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons:
  unboundedEtaleCompactSupportExchange and its normalization/refinement package.
  The chosen-product exactCompactSupportExchange is defined in
  Sheaf.AlgebraicGeometry.EtaleCompactSupportNormalizationData.
- WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeMap:
  etaleLowerShriekBaseChangeMap; and EtaleLowerShriekBaseChangeModules:
  isIso_etaleLowerShriekBaseChangeMap. Their derived inverse is the existing
  exactEtaleSumExchange in EtaleCompactSupportNormalizationData.
- WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact:
  AlgebraicGeometry.etaleInverseImageModulesExact. The exact ModuleCat inverse
  image is the existing upperStar and its mapDerivedCategory. The canonical
  exactDerivedSquareUpperStarIso is from
  Sheaf.AlgebraicGeometry.ExactUnboundedExchange.
- Sheaf.AlgebraicGeometry.EtaleCompactSupportGraphDerivedIso:
  canonicalEtaleCompactSupportComparison, the added landed dependency.
- Proof dependency Sheaf.AlgebraicGeometry.EtaleSupportMapCompatibility:
  etaleSupportMapCompatibility, imported as a plain proof import.
  The proof-only node lem-pur-etale-sum-exchange-counit currently has no Lean
  record or Mathlib match, so it has no module to import. Its precise derived
  counit identity is retained in the natural-language proof docstrings.
  It is not needed to type this statement, and no prerequisite node is restated.

Edge cases checked before writing: identity e, fold map from a disjoint union,
empty U, empty X', zero coefficient ring, K zero, arbitrary unbounded K,
and independently rescaled adjunction counits. For a fold, evaluation is
the sum-fold map, not an accidental identity. Rescaling changes B and rho
coherently; the quantification over adj and adj' retains that case. Non-finite
proper compactification factors and non-flat/non-etale w are included.
No choice of bounded representatives or cohomology-level equality occurs.
The universe is exactly the established small-site encoding, with no new
equality between site object and morphism universes.

Searches for an existing statement:

1. msearch.py leanfinder: "For etale compact support the right adjoint base
   change mate agrees with pullback under the proper support sum comparison
   on all unbounded complexes". Eight generic hits, including
   Scheme.Modules.pullbackPushforwardAdjunction, conjugateEquiv_pullbackComp_inv
   and SheafOfModules pullback formulas. None is this normalized small-etale
   compact-support exchange identity.
2. msearch.py loogle: "CategoryTheory.conjugateEquiv, CategoryTheory.mateEquiv".
   Four hits: conjugateEquiv_mateEquiv_vcomp, mateEquiv_conjugateEquiv_vcomp,
   iterated_mateEquiv_conjugateEquiv and its symm. These are generic tools,
   not the normalized geometric exchange theorem.
3. msearch.py grep: "conjugateEquiv.*counit|mateEquiv_counit" in CategoryTheory.
   Eight hits including mateEquiv_counit, mateEquiv_counit_symm,
   conjugateEquiv_counit and unrelated monoidal applications.
4. rg of lean/WeilConjectures and lean/Sheaf for the item id and
   supportExchangeRightMate found no statement. Concept searches for
   etaleSupport, exactEtaleSum, compactSupportComparison and
   rightDerivedLowerShriekOfCompactificationIso located the existing helpers.
   EtaleSumRightAdjointCoherence.etaleSumRightAdjoint_baseChange and
   etaleSumRightAdjoint_evaluation concern only constantComplex, so they
   do not match this all-unbounded-input node.
5. Searches for the new namespace and declaration found no collision.

No statement correction, new node, dependency repair or STATEMENT-DISPUTED issue.
Only lean and the authorized addition of the already landed comparison node
to stmt_deps change. The source, statement, proof and proof_deps are preserved.

Validation: scompile.py compiled sandbox and library-path forms against the live
server library, with default 60-second limits (6.7 and 7.5 seconds), without
errors or unexpected warnings. Initial elaboration feedback was repaired by
explicitly invoking the existing proper-base-change theorem and providing
QuasiCompact e on the helpers using the compactification comparison.

## Second reading by Q105

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
