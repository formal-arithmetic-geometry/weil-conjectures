## Worker report

The module `Sheaf.Paper.PolynomialRankOneDifferenceModel` states the full finite-stage
polynomial presentation. Its only postponed theorem is
`Profinite.CondensedAction.PolynomialRankOne.polynomial_rank_one_difference_model`.
All other declarations are concrete formulas or specifications; no definition chooses
an object from an existence theorem and no auxiliary theorem is postponed.

Hypotheses and clauses, matched individually:

- The prime is `(ℓ : ℕ) [Fact ℓ.Prime]`. The final theorem binds the normed algebraic
  closure `Ω`, `[NormedAlgebra ℚ_[ℓ] Ω]`, `[IsAlgClosure ℚ_[ℓ] Ω]`, and the intermediate
  field `E₀` with `[FiniteDimensional ℚ_[ℓ] E₀]`. The normed-algebra structure records
  the extended norm topology; the intermediate field inherits it. The two conjuncts
  are exactly `F = E₀` and `F = Ω`; no completeness hypothesis is added to Ω.
- Every `r ≥ 1` is uniquely `k+1`, with `k : ℕ`; `m : ℕ` allows no spectators.
  `Residual ℓ k = Fin k → IntegerGroup ℓ` is the residual product G; H is the recorded
  `IntegerGroup ℓ`. Its multiplicative identity means additive zero. `generator ℓ`
  means additive one. The continuous homomorphism π is specified coordinatewise as
  `Fin.cases g.2.toAdd.down (fun i ↦ (g.1 i).toAdd.down)`, placing H first.
- The coefficient sheaf is the recorded all-continuous `normContinuousRing F` in
  the system and realizations, and the definitionally equal underlying monoid of
  `continuousScalarRing F` in the existing polynomial model. Universes are explicit:
  parameters and coefficient fields have universe u, section groups u+1. Vector
  spaces use the existing `ModuleCat.{u+1}` convention. No extra size equality or
  test-object exclusion is introduced.
- The actual T and its action are the existing `PolynomialTranslation.Model`:
  `T.ι`, `T.isColimit`, and `T.translation` prescribe the monomial internal coproduct
  and its substitution action for every profinite S, varying continuous group
  parameter and varying coefficient section. This is not a replacement by the
  underlying abstract group action or by locally constant sections.
- `Variables k m = Fin (k+1) ⊕ Fin m`. `Indices k m n` is exactly the exponents of
  total degree at most n. `PolynomialSystem.embed`, `injective` and `image` identify
  the stage with the bounded-support polynomials; `basis` and `monomials` give its
  precise monomial basis. This is the same span V_n as the node, represented up to
  its explicitly normalized linear identification rather than a private polynomial
  notion. `finiteIndices` includes the finiteness of the monomial index set.
- `PolynomialSystem.system : IndUnipotent.System` contains finite dimension,
  injective linear transitions, nilpotence, positive exponents, joint continuity in
  `moduleTopology`, compatibility with the operators, G-commutation, transition
  equivariance, and the full finite Taylor sum. `inclusion` makes the transition
  the actual polynomial inclusion; `derivative` makes its operator precisely the
  negative recorded `MvPolynomial.pderiv (Sum.inl 0)`; `exponent` fixes e_n=n+1.
- `translate` is actual `MvPolynomial.aeval`, sending y_i to y_i minus the scalar
  parameter and fixing z_j. `PolynomialSystem.translation` identifies the action
  with this substitution. `polynomialEntries` supplies a polynomial representing
  each matrix entry as a function of all coordinates. `matrixContinuous` states
  continuity in that matrix topology; `System.continuous` also gives joint
  continuity. `System.exponential` and e_n=n+1 are the displayed Taylor identity
  for every t, including n=0.
- `PresentationAssertion` uses exactly `IndUnipotent.Presentation`: its stages are
  the existing `ContinuousRepresentation.Realization` of the actual tensor product
  `Extended E F (Q.system.V n)` and its tensor-extended action, with the existing
  finite-dimensional module topology. Its `sections`, `scalar`, `restriction`,
  and `action` fields assert all continuous sections and their pointwise formulas.
  Its transition field is postcomposition with the actual `baseChange F` inclusion.
- The maps `j n` present each realization as the finite internal coproduct of
  regular A-modules; `IsColimit (Cofan.mk ... (j n))` gives its universal property.
  The injection section formula is exactly a(s) tensor the monomial basis vector.
  `tensorPolynomial` is the actual base-changed embedding followed by Mathlib's
  `scalarRTensorAlgEquiv`; the section formula for `p n d` is exactly its coefficient
  projection. `j n d ≫ (w n).val = T.ι d.val` identifies that finite coproduct with
  the prescribed finite sub-sum of T. Each w is an action morphism, hence these
  identifications are equivariant, including varying group parameters. The displayed
  equation with `P.diagram.map (homOfLE (Nat.le_succ n))` gives compatibility with
  the successive scalar-extended inclusions.
- The cocone c is a colimit in the action category and its image under
  `forgetAction` is a colimit in internal modules. Thus it is the module colimit
  equipped with its induced action. The action isomorphism `e` identifies it with
  T, with `c.ι.app n ≫ e.hom = (P.identify n).hom ≫ w n`; the previous injection
  normalization ensures every monomial coprojection is preserved.
- D is the induced stage derivative: for every realized continuous section v,
  its image is the section v' whose values are `operator n` base-changed to F.
  The monomial formula then identifies D with negative partial derivative on T.
  `expD` restricts to the stage action of `(1,generator ℓ)`, hence to the finite
  exponential by `System.exponential`. `expD - 𝟙 _ = delta` and the all-section
  formula identify delta with τ-1. Its final monomial equation is exactly
  f(y_1-1,y_2,...,z)-f(y_1,y_2,...,z), a finite polynomial expression.

Dependency declarations read and used:

- `Sheaf.Topology.ContinuousMapCondensedRing`:
  `Profinite.continuousMapRingSheafOfUniverse`, its underlying ring object and
  recorded canonical monoid structure (through the existing coefficient bundles).
- `Mathlib.Algebra.MvPolynomial.Basic`, `.Eval`, `.PDeriv`:
  `MvPolynomial`, `MvPolynomial.aeval`, `MvPolynomial.algHom_ext`,
  `MvPolynomial.pderiv` and its monomial formula.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod`, `ModObj`,
  `Mod.regular`; these are the actual internal modules and their regular object.
- `Sheaf.CategoryTheory.CondensedActionModule`: `Modules`, `sectionModule`,
  `ActionModule`, `inflate`, `forgetAction` and its sectionwise action category.
- `Sheaf.Paper.IndUnipotentSystem`: `IntegerGroup`, `generator`, `System`,
  `Presentation`, and its exact tensor-transition specification.
- `Sheaf.Paper.ContinuousRepresentationCondensation`:
  `ContinuousRepresentation.Realization` and `PrimeToEll.Extended`, its module
  topology and `extendedRepresentation` through Presentation.
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`:
  `CategoryTheory.InternalAbelianSheafModule.sectionModuleEquivalence` and its
  section functor, via the existing section-module and realization interfaces.
- `Mathlib.RingTheory.TensorProduct.MvPolynomial`: `scalarRTensorAlgEquiv`.
- The already-landed polynomial translation `Model` and `translatedMonomial`
  are registered on the new definition node below.
- Proof-only imports: `Mathlib.Data.Nat.Choose.Sum` (`add_pow`) and
  `Mathlib.Topology.Algebra.Module.FiniteDimension`
  (`LinearMap.continuous_of_finiteDimensional`), the two Mathlib proof leaves.
  The recorded filtered-colimit-creation proof dependency has no Lean record on
  this read snapshot, so there is no recorded module of that node to import.
  This delivery does not need to introduce its general theorem in order to state
  the particular polynomial colimit universal properties.

Edge cases checked before finalizing: k=0 gives r=1 and the unique residual G-action;
m=0 permits the empty spectator list; n=0 has only constants, derivative zero,
exponent one and identity action. The zero polynomial satisfies the support condition.
Empty profinite test sets are still quantified. An arbitrary monomial occurs at its
own total degree, with no uniform bound on T. Tensoring never completes F. The
translation has negative sign: exp(-t∂)f=f(y_1-t), so the generator gives the stated
forward difference. No mathematical statement correction or disputed statement.

Searches (see searches.jsonl for the wrapper's complete recorded results):

1. LeanFinder, “Finite degree multivariate polynomial translation filtration negative
   partial derivative exponential and condensed colimit”: eight unrelated complexity,
   Witt-vector and partial-derivative hits; no theorem matching this node.
2. Loogle, `MvPolynomial.restrictTotalDegree, MvPolynomial.pderiv, MvPolynomial.aeval`:
   zero hits. Wrapper grep for `restrictTotalDegree|totalDegree.*pderiv|pderiv.*totalDegree`
   under Algebra/MvPolynomial: zero hits. Direct source inspection found totalDegree
   and degreesLE, but no exact finite-stage condensed presentation.
3. LeanSearch, “Finite degree polynomial subspace monomial basis tensor product scalar
   extension”: univariate degreeLT bases, MvPolynomial.basisMonomials and unrelated
   symmetric-algebra bases. These do not give the internal equivariant colimit.
4. Searches for the missing definition node are recorded verbatim in its
   mathlib_searches: LeanSearch gives abstract DirectSum declarations, LeanFinder
   gives PolynomialLaw/PolynomialModule, and wrapper grep gives zero Mathlib hits.
5. `rg` in the prescribed WeilConjectures and Sheaf sources located the exact existing
   `PolynomialTranslation.Model` helper and no upstream version of this theorem.
   `grep -rn` for this item's id in WeilConjectures returned no matches.
   DAG definition searches found no owner of this polynomial translation model;
   `tools/blueprint_refs.py search 'polynomial translation'` returned zero blueprint
   matches. `ancestor` returns None, retained in the new node's provenance.

## New nodes

`def-sfb-polynomial-translation-model` registers, with `existing: true`,
`Profinite.CondensedAction.PolynomialTranslation.Model` and its existing
`translatedMonomial` formula from `Sheaf.CategoryTheory.PolynomialTranslationAcyclic`.
It defines exactly T and its action on varying continuous generalized elements.
There is no new Lean module and no duplicate notion. The existing acyclicity node
records this as a helper but asserts a different statement, namely positive derived
vanishing; that theorem is downstream of this item. The new definition node avoids
introducing that theorem as a cyclic statement dependency. Its source is the same
polynomial translation obligation under latest blueprint direct-image proof (3).
The search results, exact definition, coefficient universes and zero-rank cases were
checked against the existing module.

## Second reading by Q04

The maintainer's independent second reader (cc review service, 2026-10-25) wrote
this section. It replaces the author's self-check, which was not an independent
reading (delivery-errors H11). The Lean module, the item node and the new node
record are unchanged.

Each clause of the node statement, matched against
`Profinite.CondensedAction.PolynomialRankOne`:

| Node | Lean | Verdict |
|---|---|---|
| prime ℓ | `(ℓ : ℕ) [Fact ℓ.Prime]` | exact |
| Ω algebraic closure of ℚ_ℓ, extended norm topology, no completeness | `[NormedField Ω] [NormedAlgebra ℚ_[ℓ] Ω] [IsAlgClosure ℚ_[ℓ] Ω]`. Over a field the norm restricts to the ℓ-adic norm. A multiplicative norm on an algebraic extension of ℚ_ℓ is the unique extension | exact, no `CompleteSpace` |
| E finite intermediate field | `(E₀ : IntermediateField ℚ_[ℓ] Ω) [FiniteDimensional ℚ_[ℓ] E₀]`, subspace norm | exact |
| F = E or F = Ω | the two conjuncts `PresentationAssertion … E₀ Q` and `… Ω Q`, with the same Q | exact |
| A(S) = C(S,F), all continuous functions, size convention | `normContinuousRing F` (= `continuousMapRingObjOfUniverse.{u,u} F`, the recorded ring of def-sfb-ind-unipotent-system). Model uses `continuousScalarRing F`, with the same X and mon. Profinite.{u}, sections in u+1 | exact |
| r ≥ 1, m ≥ 0 | r = k+1, `k m : ℕ` | exact, r = 1 and m = 0 included |
| G = ℤ_ℓ^{r-1}, H = ℤ_ℓ, inverse-limit topology | `Residual ℓ k = Fin k → IntegerGroup ℓ`, `IntegerGroup = Multiplicative (ULift ℤ_[ℓ])` | exact |
| T is the monomial direct sum with its action | `∀ T : PolynomialTranslation.Model ℓ F (k+1) m`: coproduct cofan `T.isColimit`, action formula on every S for varying g ∈ C(S,L) and varying c; pulled back along π | exact |
| y_1 ↦ y_1 − t, y_{i+1} ↦ y_{i+1} − g_i, z fixed | π is pinned by `(π g).toAdd.down = Fin.cases t g`. Model's `translatedMonomial` substitutes `X i − g_i`. `translate` uses `coordinates` in the same order | exact sign and order |
| V_n = span of monomials of degree ≤ n | `embed` is injective, with image the polynomials whose support has degree ≤ n; `basis` is normalized by `monomials` | exact up to the pinned identification |
| i_n is the inclusion, injective and equivariant | `inclusion` + `System.injective`, `System.equivariant` | exact |
| D_n = −∂/∂y_1 | `derivative`: `−MvPolynomial.pderiv (Sum.inl 0)` (def-weil-pbc-polynomial-partial-derivative) | exact |
| e_n = n+1, D_n^{n+1} = 0 | `exponent`, `System.nilpotent` | exact |
| ρ_n given by the same translations | `translation`: `embed (action g v) = translate g (embed v)` | exact |
| matrix entries polynomial in the group coordinates | `polynomialEntries` (∃ p ∈ E[t, g]) | exact |
| ρ_n continuous; matrix continuity | `System.continuous` (joint, moduleTopology = norm topology for finite dimension over the complete E₀) and `matrixContinuous` | exact |
| i_n D_n = D_{n+1} i_n; D commutes with G | `System.compatible`, `System.commutes` | exact |
| Taylor identity for all t ∈ ℤ_ℓ | `System.exponential` with range (n+1) = 0..n | exact |
| M_n(S) = C(S, F ⊗_E V_n), product topology, induced action | `P.stage n : Realization … (Extended E F (V n)) (extendedRepresentation …)` inside `IndUnipotent.Presentation` | exact |
| equivariant coefficient isomorphisms with ⊕_{|α|≤n} A | `j n d`: IsColimit cofan, section formula a(s) ⊗ basis d. `p n d`: coefficient formula via `scalarRTensorAlgEquiv` (N ⊗_R R[σ] ≃ N[σ]). `w n`: action morphism with `j n d ≫ w n = T.ι d` | exact; w n uniquely pinned |
| compatible with F ⊗ i_n and the sub-sum inclusions | `Presentation.transition` + the w-compatibility equation | exact |
| M = colim M_n in internal modules, with the induced action, ≅ T, coprojections preserved | `c` is IsColimit in ActionModule and `forgetAction.mapCocone c` is IsColimit; `e` satisfies `c.ι.app n ≫ e.hom = identify ≫ w n` | exact, e pinned |
| D on M is −∂/∂y_1 on T | D is pinned on stage sections by `(operator n).baseChange F` and on every `T.ι d` section by `polynomialSection (−pderiv …)` | exact |
| τ − 1 = exp(D) − 1 = Δ | expD is pinned to the stage action of τ = (1, generator), which is exp(D_n) by `System.exponential`; `expD − 𝟙 = delta`. On all sections delta = τ·v − v; on each coprojection it is translate(1,gen) monomial − monomial | exact (finite sums only) |

Edge cases:
- k = 0: G is trivial (`Fin 0 →` product).
- m = 0: `Fin 0` spectators.
- n = 0: Indices = {0}, D_0 = 0, e_0 = 1, trivial action.
- Empty profinite S: all section clauses are ∀ S.
- Every monomial lies in the stage of its own degree, so T has no uniform degree bound.
- Noncomplete Ω: no completeness instance appears anywhere.

Universes: Ω, E₀, G and H are in u, the site is Profinite.{u}, and sections and V_n
are in u+1, as in the dependency nodes. No extra universe equality is imposed.

Dependency records read:
- def-sfb-ind-unipotent-system (System, Presentation, IntegerGroup, generator);
- def-sfb-continuous-representation-condensation (Realization, Extended);
- def-sfb-condensed-action-module (ActionModule, inflate, forgetAction);
- def-weil-pbc-mv-polynomial-ring (MvPolynomial);
- def-weil-pbc-polynomial-partial-derivative (pderiv);
- the new existing:true node def-sfb-polynomial-translation-model (Model,
  translatedMonomial), checked against PolynomialTranslationAcyclic.lean lines 41-75;
  `check_existing` is clean.

No other DAG node or Mathlib declaration owns the polynomial translation model.

Advisories for the maintainer (no change made):
- The item reaches normContinuousRing and Extended through
  def-sfb-ind-unipotent-system instead of citing their owners directly.
- The item module imports the module of the downstream
  lem-sfb-polynomial-translation-acyclic. The later proof import of this item into
  that module must therefore be omitted (stage-2 rule 7), or Model must be moved to
  its own module.
- The ∀ T formulation does not itself assert that a Model exists. The acyclicity node
  asserts that.

Author's validation, retained: the per-file server compile built the delivered file
both as a sandbox module and as its final library module. It exited 0 with no errors
or warnings, and one named theorem has sorry. The author's dry run returned OK
(commit ce456dc49d2).
