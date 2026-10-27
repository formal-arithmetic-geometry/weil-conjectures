## Worker report

The module Sheaf.Algebra.Homology.SignedDoubleRoosTensorExchange states
CategoryTheory.SignedDoubleRoos.signed_double_roos_tensor_exchange, with sorry as its
only postponed proof. The supporting declarations are transparent aliases, functorial
rearrangements, coordinates and actual canonical maps belonging to this statement.
There is no replacement Roos cone, tensor construction, Koszul tower or module category.
No existing node field other than lean is changed, and there are no new nodes.

Hypotheses and clauses, in statement order:

- The site is C : Type uC with Category.{vC} C and EssentiallySmall.{r} C. Coefficients
  and modules live in r, independently of both site universes. J is its topology and
  R : Sheaf J CommRingCat.{r}. The HasSheafCompose instance is the standard forgetful
  sheaf transport, available on an essentially small site; it imposes no mathematical
  hypothesis. Modules R is exactly ringedSiteModules.{r} of that underlying ring sheaf.
- Complex R is CochainComplex (Modules R) ℤ, with no bounds. Tower R is
  ℕᵒᵖ ⥤ Complex R. A strict double tower is ℕᵒᵖ ⥤ Tower R; functor naturality
  is precisely commutation of the two transitions.
- HasExactLimitsOfShape (Discrete ℕ) (Modules R) is exact countable products. The
  products themselves and the Abelian instance are supplied by module sheaves on the
  small site. No assumption about t, torsion, K-flatness or boundedness is introduced.
- roos is towerComplex R ⋙ roosF. towerComplex uses koszulTowerComplex and
  koszulTowerComplexMap, not a new rearrangement of data. Thus it is the stipulated
  Cone(1-s)[-1] with the published maps. evaluation uses roosEval.
- rows takes the inner then outer Roos; columns first flips the indices. The existential
  β : rows R ≅ columns R is an isomorphism of functors, including chain-map inverse
  identities and strict-map naturality for every double tower.
- The first conjunct specifies every component by every product projection:
  β.hom.f k followed by columnCoordinate is rowCoordinate, negated exactly if p && q.
  Bool false and true denote Roos degrees zero and one. Therefore the four coordinates
  are exactly (a,b,c,h) ↦ (a,c,b,-h), with no ambiguity of choice or cone signs.
  coordinate false is the published evaluation; coordinate true is mappingCocone.snd
  followed by Pi.π in degree k-1. columnCoordinate's eqToHom only identifies the two
  equal integer degrees k-q-p and k-p-q.
- The next two conjuncts are the full chain-map squares with evaluation at n and at j.
  innerEvaluation packages the published Roos evaluation naturally in the other index.
- The derived conjunct takes any two comparison isomorphisms ρnj and ρjn out of the
  localized iterated strict models and provides an isomorphism δ with
  ρnj.hom ≫ δ.hom = Q.map (β.hom.app X) ≫ ρjn.hom. In particular these can be the
  outer normalized comparisons supplied by strictRoosComparison using inner Roos
  representatives, exactly as the node's proof step 5 specifies. This is the derived
  isomorphism itself, not only a statement on cohomology. derivedInterchange constructs
  precisely ρnj.symm ≪≫ Q.mapIso β ≪≫ ρjn. No arbitrary map is substituted for it.
  The two evaluation squares above transport along these comparisons, whose evaluation
  normalization is already part of the dependency's recorded theorem.
- The quantified t is a section of SheafOfModules.unit, the published global-section
  type. principalKoszul R t j uses exponent j+1, so j=0 denotes the first positive
  index. This is exactly the published positive Koszul tower, with transitions (t,1).
- tensorTower R t uses the existing total tensor on complexes, with P as left input
  and principalKoszul as right input. completion is tensorTower ⋙ roos.
  strictAugmentation composes the published koszulStrictAugmentation with the inverse
  standard signed tensor braiding. On Koszul degree zero this is p ↦ p tensor 1.
  augmentation uses the published roosAugment with precisely that compatible family;
  its shifted component is zero. Thus u_P is actual data, not an unconstrained map.
- η is natural and is pinned at every P by η.app P = augmentation R P t. The auxiliary
  τ j is the natural level inclusion, pinned at every P to strictAugmentation.app j.
  Its existence asserts the needed naturality of these already constructed inclusions.
- γ Q is an isomorphism of strict j-towers from H0 tensor L_j to Roos_n(Q_n tensor L_j).
  Its being a tower isomorphism includes compatibility with all j-transitions. The next
  conjunct gives naturality in every strict map f : Q ⟶ Q'.
- The γ coordinate conjunct tests each total-tensor summand a+b=k and both Roos degrees.
  It specifies identity on the tensor coordinate: project the H0 factor to Q_n in
  degree a-p and tensor the identity of L_j^b, then include that total summand. This
  pins both γ and its inverse, not merely their existence. All integer a,b are allowed;
  Koszul terms outside -1,0 are zero, rather than an added boundedness hypothesis.
- The following conjunct is the chain-map evaluation square for every j,n. The next
  is the degree-zero inclusion square, using τ j and applying roos to its strict
  n-tower map. Thus γ commutes with evaluations and the prescribed inclusions.
- The penultimate conjunct is precisely Roos_n(u_Qn) ≫ β ≫ Roos_j(γ⁻¹) = u_H0.
  Q.rightUnitor.inv only identifies Q with Q ⋙ identity to type the natural map.
- The last conjunct gives all four coordinates after β: q=true gives zero for either
  p; q=false gives the p coordinate of H0 followed by strictAugmentation in degree
  k-p. Its eqToHom only identifies k-p with k-p-q when q=0. No sign or map is hidden
  in that degree identification.

Dependency declarations read and used:

- Sheaf.CategoryTheory.RingedSiteModules: CategoryTheory.ringedSiteModules, a direct
  abbreviation for Mathlib SheafOfModules, including its inherited abelian category.
- Mathlib.Algebra.Homology.DerivedCategory.Basic: DerivedCategory, HasDerivedCategory,
  DerivedCategory.Q; the derived comparison is an isomorphism in this category.
- Sheaf.CategoryTheory.StrictRoosModel: roosF, roosU, roosEval, roosEval_natural,
  roosAugment; signatures, constructions and coordinate lemmas were read in full.
- Mathlib.Algebra.Homology.BifunctorShift / Bifunctor / Monoidal: the existing total
  tensor, curriedTensor and HomologicalComplex.ιTensorObj. CochainTensorUniverses supplies
  the independent-universe sheaf tensor instances; the underlying tensor is unchanged.
- Sheaf.CategoryTheory.StrictRoosComparison: strictRoosComparison; read its full
  signature/docstring, including descent κ, normalized ρ, both evaluation maps and
  strict augmentation clause. It is imported as the proof dependency for the normalized
  derived interpretation, rather than choosing a second derived-limit construction.
- Sheaf.Algebra.Homology.PrincipalKoszulQuotientTowers: principalKoszul,
  principalKoszulTower, koszulTowerComplex, koszulTowerComplexMap,
  koszulStrictAugmentation. Read the exponent convention, full signatures and docstrings.
- Proof leaves: Mathlib's Abelian, Pi.π/Pi.lift/Pi.map/HasCountableProducts and
  PresheafOfModules.sheafification. Their signatures/docstrings were read, and their
  modules are imported. The sheaf tensor dependency is imported publicly because the
  statement uses its existing monoidal instance.

Edge cases checked before writing and again against the final signature: zero complexes,
zero and identity transitions, a zero section, an invertible section, characteristic two
(where negation agrees with the positive map), the first positive Koszul level j=0,
and complexes unbounded in both directions. The sign test concerns only p=q=true.
All indexing categories are the stipulated countably infinite towers, so there is no
unmentioned nonemptiness assumption or finite-index restriction. The two independent
site universes remain independent of the coefficient universe; no universe equality was
imposed. The Koszul complexes remain honest two-term cones even when t is zero.

Searches (2026-10-24):

- msearch.py leanfinder, query: Signed interchange of iterated Roos cones and tensor
  with a two term Koszul complex. Eight hits: HasGoodTensor, ιTensorObj, HasTensor and
  tensor differentials; ingredients only, no exact interchange/augmentation statement.
- msearch.py loogle, query: HomologicalComplex₂.totalFlipIso,
  CochainComplex.mappingCone. Zero hits for this combined query.
- msearch.py grep, query Roos|roos|totalFlipIso, Mathlib Algebra/Homology. Nine hits in
  BifunctorFlip and TotalComplexSymmetry, general total-flip ingredients only.
- msearch.py leansearch, query: Iterated shifted cones of commuting countable tower
  transitions admit a signed interchange isomorphism compatible with tensor augmentation.
  Eight hits on cone shift isomorphisms and totalShift₁Iso_trans_totalShift₂Iso, no match.
- rg in lean/WeilConjectures and lean/Sheaf for doubleRoos, DoubleRoos, signed Roos,
  Roos tensor and KoszulRoos. The existing PowerTorsionSheafLimitComplete module has a
  related specialized β clause under torsion, scheme and coefficient assumptions. Its
  theorem does not give this general statement or γ; importing it would also reverse
  the dependency direction. PrincipalKoszulRoosPresentationComparison defines a unit
  but in the left-tensor presentation on a small site; this statement constructs the
  right-tensor unit using the published augmentation and standard symmetry directly.
- rg for the exact item id in lean/WeilConjectures: no matching declaration.
- Read Mathlib BifunctorFlip and TotalComplexSymmetry: totalFlipIso is not this shifted
  product-cone interchange with the specified simultaneous tensor and unit identities.

Source check: read literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-lem-sp-tower/sk-lem-sp-tower.proof.md, its completeness sentence, and Stacks
014E (derived.tex definition-cone), 012Z (homology.tex definition-associated-simple-complex),
0941 (sites-cohomology.tex lemma-derived-limit-is-ok). The eight-step proof docstring
follows the node's complete coordinate proof, including the double-shift sign.
No statement dispute or correction was needed.

Validation: scompile.py passed both the sandbox module and its library module on the
server with no errors or warnings (32.8 s and 28.7 s). Final import-only updates are
checked again by the required delivery dry run.

## Second reading by Q119

Final clause-by-clause self-check against the opened node and module: the four sign
coordinates and both evaluation squares are explicit; β is natural for all double
strict towers; the derived clause gives the conjugate isomorphism itself; γ is pinned
on all tensor/Roos coordinates, natural in Q and a strict j-tower isomorphism; both
inclusion and evaluation squares are present; the full unit composite and both
vanishing q=1 coordinates are explicit. One typing mismatch found during this reading
was the arithmetic identification k-p=k-p-q at q=0; it now uses eqToHom of that integer
equality. The level inclusion τ was separated from the completion unit η so that its
naturality has the correct target before applying the n-Roos functor. No node content
was changed. The dispatcher explicitly prohibits starting another agent, so this is a
self-check; the maintainer's independent review remains the independent second reading.
