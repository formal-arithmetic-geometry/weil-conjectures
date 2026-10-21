## Worker report

Item: lem-pur-finite-free-completion-exchange-coherence. The delivery states the
composition and identity clauses in
`Sheaf.Algebra.Homology.FiniteFreeCompletionExchangeCoherence`, namespace
`CategoryTheory.PrincipalQuotientCompletion`. Both theorems have only `sorry` proofs.
The five helper declarations specify the scalar associator, scalar unit and actual
representative equation. They belong to the canonical maps named by this node;
no replacement tensor, module category, completion or Roos construction is introduced.
No node statement is changed and no new or dependency node is needed.

Hypothesis and clause correspondence:

- A site small in the module universe is `{C : Type u} [Category.{v} C]`, `J`, and
  `[EssentiallySmall.{r} C]`, with the recorded sheafification and locally bijective
  equivalence instances. `u`, `v` and `r` are independent. The topology is the existing
  Grothendieck topology encoding, not an additional condition on covers.
- The three sheaves of commutative rings are `R S V : Sheaf J CommRingCat.{r}`;
  their maps are `a : R ⟶ S`, `b : S ⟶ V`, and `a ≫ b`. The unbounded derived
  categories have separately chosen morphism universes `wR`, `wS`, `wV`.
- `_hfreeS` and `_hfreeV` assert the required finite coproduct isomorphisms for the
  restrictions of the unit module. The existential `d : ℕ` includes zero.
- `t`, `vS` and `w` are compatible families of sections of the respective unit
  modules, i.e. global ring sections without assuming a terminal object of the site.
  `_ht`, `_hv`, `_hw` are `Mono (globalSectionMultiplication ... ...)`, the precise
  sheaf-theoretic injectivity condition, with no extra sectionwise flatness assumption.
- `uS`, `z`, `_hu`, `_hz`, `_ha`, `_hb` encode exactly the units and the two section
  equations. Inverses of pointwise units respect restriction and hence are global.
  `e f : ℕ`, `_he : 1 ≤ e`, `_hf : 1 ≤ f` are the positive integer exponents.
  The composite uses `e * f`; the equation with unit `b(uS) * z^e` follows from
  `_ha`, `_hb` and the ring-map axioms and is not imposed as an extra hypothesis.
- Four `HasExactLimitsOfShape (Discrete ℕ)` instances are exactly the countable
  product exactness assumptions for R-, S-, V-modules and abelian sheaves.
- `Fa`, `Fb`, `Fba` are the recorded cochain models for derived scalar extension.
  Their ordinary functors are prescribed on objects and maps; their derived functors
  have universal cochain counits and K-flat computations. These are choices of the
  functors named by the statement, rather than a new tensor theory.
- `BalancedScalarAssociator.ordinary` is pinned by `.balanced`, using the actual
  sheafification image `scalarTensorSection`. It sends nested tensor sections to
  `b(s) * q` tensor x. `.derived` is a natural isomorphism and `.computes` fixes
  its K-flat normalization through `Fa.ε`, `Fb.ε`, `Fba.ε`. The theorem asserts
  existence of this normalized associator, rather than assuming an arbitrary map.
- `CR`, `CS`, `CV : Model ...` are the recorded principal quotient completions.
  Their counits identify the actual quotient Roos complexes, their `.coordinates`
  fix the quotient augmentation with zero shifted-product component, and their
  universal properties describe the unbounded derived functors. The n-th level in
  Lean is the paper's n+1-th level, so `index e` selects `e*(n+1)-1`.
- The three `RepresentativeComparison` conditions identify precisely the stipulated
  exchanges: the balanced quotient maps, canonical product map and inverse of the
  specified selection/weighted-block arithmetic quasi-isomorphism. They restrict
  the notation epsilon to the maps named by the source; they impose no new condition
  on R, S, V, or Q. Existence of these exchanges is already the dependency theorem.
- The first conclusion of `finiteFreeCompletionExchangeCoherence`, read left to
  right in Lean's composition convention, is exactly
  `C_V(alpha_Q) ∘ epsilon_b ∘ T_b(epsilon_a) = epsilon_ba ∘ alpha_(C_R Q)`.
  All factors are components of natural transformations, giving naturality in Q.
- The next three conjuncts are the augmentation equations for each stipulated
  exchange. They use the same `.unit` transformations as the completion models.
- The representative conclusion supplies `ra`, `rb`, `rba` satisfying the existing
  exchange specifications and `RepresentativeComposition`. Its `.coordinates`
  compares the actual chain maps, with output tower reassociated by the recorded
  quotientTower functor. Equality of actual chain maps is equivalently equality
  on both signed Roos coordinates; there is no unspecified completion of a triangle.
  The predicate is stated for additive functors and towers to prevent repeated
  unfolding of the total-tensor construction; its arguments in the theorem are
  precisely the source, intermediate, and target quotient towers and the canonical
  quotientTower image of the balanced associator.
  `.selected_quotients` pins the second comparison on the restricted source tower;
  `.arithmetic_coordinates`, `.arithmetic_square`, `.arithmetic_composition` record
  the selected-coordinate/weighted-block maps, their additive scalar square, and
  the precise equation r_e(Z^(f)) r_f(Z) = r_(ef)(Z).
- The final conjunct transports that same equality through any natural identification
  `ρ : CV.completion ≅ D`. In particular it holds for the specified normalized
  strict-derived-limit identification: this is a transport of the same fixed maps,
  not a second choice of exchanges. Intermediate normalized comparisons cancel by
  naturality, as in proof step 10 and the imported strict-Roos comparison theorem.
- `finiteFreeCompletionExchangeIdentity` states the identity clause for an arbitrary
  one of the ring sheaves (the symbol R is arbitrary). `BalancedScalarUnit.balanced`
  is multiplication `s • x`, and `.computes` pins its derived identification. With
  exponent exactly 1 and the same section and completion model on both sides, the
  displayed equation says the conjugated exchange is identity. The second conjunct
  retains the quotient augmentation equation. No finite-free hypothesis is needed
  for identity extension: the unit module is free of rank one automatically.
- Q has no boundedness, completeness, constructibility or perfectness binder.
  K-flat conditions occur only in the specifications of representative computations.

Dependencies read and used:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`,
  `CategoryTheory.Precoverage.IsSiteForCoverings`: site convention; topologies and
  sheaves remain Mathlib's.
- `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`:
  transparent abbreviation for Mathlib's `SheafOfModules`, with its canonical abelian
  structure, not a chosen instance.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`: unbounded localization.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`,
  `SheafOfModules.DerivedChangeOfRingsCochainModel` and its existence theorem:
  the exact ordinary scalar extension and its universal derived pair.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`,
  `CategoryTheory.ringedStrictTowerHomotopyLimitIndependentCoefficients`: total
  derived strict limit with independent site and coefficient universes.
- `Sheaf.Algebra.Homology.FiniteFreeCompletionExchange`,
  `finiteFreeCompletionExchange`, `RepresentativeComparison`,
  `RepresentativeRoosComparison`, `sourceTower`, `targetTower`, `extendedComplex`:
  the precise stipulated exchanges, quotient maps and product-coordinate formulas.
- `Sheaf.Algebra.Homology.PrincipalQuotientCompletionModel`, `Model`,
  `quotientTower`, `quotientMap`, `quotientRoos`: the actual strict quotient completion
  interface used by the preceding dependency, retained without a private copy.
- `Sheaf.CategoryTheory.CompactSupportRoosCofinality`,
  `CategoryTheory.compactSupportRoosCofinality`: read its complete signature,
  including the identity and composition equations. Its constant-ring restriction
  is not applied to the nonconstant sheaves R, S, V. The general-site exchange
  interface and additive Roos comparison supply the needed nonconstant maps.
- `Sheaf.CategoryTheory.StrictRoosComparison`, `CategoryTheory.strictRoosComparison`:
  the fixed natural descent and normalized comparison with every K-injective tower
  resolution, including strict augmentations.
- Proof imports retain the recorded K-flat resolution, K-flat predicate, cochain
  sheaf tensor, strict Roos model, and additive Roos comparison declarations.

Edge cases checked before writing and again after elaboration repairs:

1. Rank zero is allowed for either finite-free extension; its scalar functor and
   target module category are zero as appropriate. No nonzero-ring assumption occurs.
2. Identity coefficients, identical sections, e=f=1 and all three equal rings are
   retained; each selected block then contains one identity transition.
3. For e=2, f=3, the composite selects original paper level 6n, and the weighted
   blocks partition precisely [6n,6(n+1)-1]. Units change only the quotient ideal.
4. The index n=0 is paper level 1; the arithmetic selection is e-1, so no initial
   levels are incorrectly included or discarded.
5. A zero section on a nonzero ring fails the stated monomorphism hypothesis;
   a zero section on the zero ring remains permitted. Arbitrary unbounded complexes,
   including zero and acyclic complexes, have no additional restrictions.
6. The site object and morphism universes and the three derived morphism universes
   remain independent; there is no equality imposed to fit a specialized API.

Searches for an existing statement or notion:

- msearch.py / LeanFinder: "Finite free change of rings commutes with principal
  derived completion and the exchange is compatible with composition and identity".
  Eight hits concern ordinary adic completion, finite product completions, and
  completion of finite modules; none is a derived ring-sheaf exchange coherence.
- msearch.py / Loogle: "SheafOfModules, tensorProduct, associator". No hits; service
  reported unknown identifier tensorProduct. This was supplemented by source grep.
- msearch.py / grep in Mathlib Algebra: "completion.*[Cc]oher|[Ee]xchange.*[Cc]oher|
  changeOfRings.*[Aa]ssoc". No hits.
- msearch.py / LeanSearch: "Coherence of finite free scalar extension with principal
  derived completion under composition of ring sheaf maps, including identity and
  Roos arithmetic subsequences". Eight hits include ModuleCat.extendScalarsComp,
  extendScalars_assoc and ordinary module pseudofunctor coherence. None states
  the ring-sheaf derived completion equation or its specified Roos maps.
- rg in Mathlib's ModuleCat/Sheaf, the project's Sheaf, and WeilConjectures searched
  changeOfRings, scalar associators, completion exchange and coherence. The project
  has the single-step FiniteFreeCompletionExchange and specialized finite-field
  scalar-composition theorems, which do not cover arbitrary ring sheaves or the
  actual quotient-tower equation here. All proposed full declaration names
  were searched as well; there was no collision.
- An additional Loogle query "ModuleCat.extendScalarsComp, AdicCompletion" returned
  zero matches.
- rg for this exact node id in WeilConjectures had no match. The compact-object
  example is withdrawn; its node now points to the upstream declaration, which
  was read rather than recreated.

No STATEMENT-DISPUTED flag or source correction is needed.

## Second reading by NG

This is the author's separate second pass, as required by the direct-delivery brief;
no independent reviewer or second agent was started. I reread the node and the full
module, and checked every binder and conclusion against the correspondence above.
The main orientation is T_b(epsilon_a), then epsilon_b, then C_V(alpha); the other
route is alpha followed by epsilon_ba. The b-comparison on the e-restricted tower
uses the original b-stage at level en and has target exponent ef, not e+f or a
reversed block order. The reassociation on its output tower is the quotientTower
image of the balanced cochain associator, so the C_V(alpha) factor is retained.
Both coordinates are equality of actual chain maps. The generic coordinate
predicate keeps the ring-sheaf tensor definitions opaque during elaboration;
HEq is used for the standard arithmetic reindexing identifications only.
`arithmeticRoosMap` is a real definition applying the existing map-of-square
constructor to the existing selection, block and telescoping-square theorem. The multiplication formula in the identity statement
uses the same ring, section, exponent 1 and completion on both sides. No hypothesis
of completeness or a bound on Q was introduced. No noncanonical associator or
arbitrary exchange is an input: the former is constructed with normalization in
the conclusion and the latter must satisfy the existing representative formulas.

Validation: prescribed scompile.py passed for the sandbox module (44.9 s) and
its final library module name (33.7 s), with no errors or warnings. Exactly the
two named theorem proofs are postponed. The node differs from the repository
only in lean, its recorded signature is verbatim, every declared name was
searched for collisions, and all Lean lines are at most 100 characters.
deliver2.py --no-push passed preflight and compilation (dry-run commit
ed74d862aba); final delivery uses the same prescribed wrapper.
