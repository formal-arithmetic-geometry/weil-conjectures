## Worker report

Q51 stage 2, repair of immutable returned head ce78ae458867.

The module is `Sheaf.SixFunctors.ProductNormalizationRealizationTransport`, with
main theorem
`WeilConjectures.IntegralSystemRealization.ProductNormalization.productNormalizationRealizationTransport`.
There is one `sorry`, in that named theorem; its docstring retains the seven-step
natural-language proof. All other delivered declarations have real data.

### Returned points and changes

1. **L H2, definition ownership.** The item now cites the existing definition
   owners `def-zl-ringed-derived-closed-symmetric-monoidal-data`,
   `def-coef-ringed-sequence-site`, `def-coef-semilinear-proper-open-mate`,
   `def-sp-semilinear-constant-ring-operations`, and
   `def-cbc-strict-tower-proper-open-arrows`, exactly as requested. It also cites
   `def-cbc-finite-constant-coefficient-transport`,
   `def-sf-integral-system-canonical-bridge`, and
   `def-sf-integral-system-expression-domain` for the actual scalar-origin,
   bridge, and expression interfaces used by the repaired signature.
   Four new definition nodes, listed under “New nodes”, give the remaining
   theorem-owned notions definition owners. They all use `existing: true` and
   the unchanged published declarations: there is no duplicate construction or
   dependency module. `Word` still uses `PrimitiveCounit.RoosRealization`,
   `TensorModel`, and `NormalizedTensorTransport.contraction/quotientAssociator`,
   now with definition ownership. The unused `Kind`, `quotientMap`, `beta*`,
   `gamma*`, and `systemMap` references disappeared with `TensorLaws`.
2. **L H4/H3, wrong generic restatements and missing generator link.** Removed
   `TensorLaws`, `ProperOpenScalarLaws`, and `TowerLaws` completely. The main
   theorem no longer reasserts the three dependency theorems over arbitrary
   schemes, arbitrary ring sequences, or arbitrary `(A,I)`. The new
   `ProperOpenLaws l E r` is on the item's finite expression domain and the
   actual coefficient sequence `scalarRings l E` / `scalarTransitions l E`.
   Its first nontrivial comparison begins with the actual
   `(r.properOpen.gamma ...).app M`. It retains all canonical-bridge components,
   applies the actual constant-O_E scalar-restriction functor, and equates the
   result with the normalized constant-tower `properOpenOpenAdjunct`.
   That adjunct is identified with `StrictTower.gamma`, and its actual finite
   evaluation on supplied etale-origin inputs is stated. A separate equation
   identifies the total-limit transport of the same `r.properOpen.gamma`
   with its specified localized completed-ring counterpart under the recursive
   completion maps. The proof docstring now says explicitly to paste
   `r.properOpen.canonical` with `gamma_scalarRestriction`, then use
   `properOpenTowerComparison` and `StrictTower.gamma_evaluation`.
3. **Universe issue named in H4/H3.** `constantIntegers l E` is the canonical
   `ULift.{u+1} (Padic.coefficientExtensionIntegers l E)`, with its inherited
   ring operations. `constantCoefficient n` is the actual O_E quotient map
   lifted on both sides. Thus O_E is admitted by the published tower API,
   whose coefficient universe is `u+1` for schemes in `u`. No universe equality,
   arbitrary replacement ring, or hypothesis that O_E already lies in `u+1`
   is imposed. `constantRestriction`, `constantPush`, and `constantOpen` are
   precisely the dependency's `rho`, `rhoR`, `rhoJ` specialized to those maps;
   their compatibility proof is the definitional quotient-factor equation.
4. **Accepted clauses.** `Word`, `WordLaws`, `OpenLaws`, `NaturalityLaws`, and
   `ProductIdentityLaws` are retained. The scalar clause was advisory, described
   by L as consistent with the recorded definition. It is retained using
   `exchangeProjectionCoefficientRepresentative` and the actual endpoint
   cocycle; it asserts persistence of the item's already established equations
   under their prescribed coefficient representatives.

The sandbox was repaired from the returned delivered module. The item JSON is
rebased on the current shared main node: outside `lean`, only authorized additions
to `stmt_deps` are made. Its mathematical statement, proof, proof dependencies,
source, and review fields are unchanged. No source correction is needed.

### Hypotheses and clause correspondence

* **Finite-field and coefficient setting.** The section binds `l : ℕ`,
  `[Fact l.Prime]`, a field `E : Type u`, its `Padic l` algebra, and finite
  dimensionality. The main arguments `D : FiniteFieldDatum.{u}` and
  `_hl : l ≠ D.p` give exactly the recorded finite-field closure and invertible
  prime. All quotients and transitions are the recorded positive quotients of
  O_E. `constantIntegers` only changes their universe presentation.
* **Specified operations and comparisons.** `o : Operations l E` and
  `r : Realizations l E D o` retain the dependency's operation package and
  its comparisons. `comparison e g K h` is literally
  `(r.comparison e g).app ⟨K,h⟩`. No unrelated endpoint isomorphism replaces it.
* **Compactification geometry.** `ProductDiagram D` contains the two actual
  product squares and their projection equations, the open maps `j,k,u`, the
  proper maps `a,b`, and separated finite-type structure maps. Its `ambient`,
  `inside`, and `extended` are respectively the external tensor of open
  extensions, the tensor of projection pullbacks, and its extension by `u`.
  `ProductIdentityLaws` uses `c = d.qb ≫ d.b` and the actual proper-image functor.
* **Inputs and every intermediate.** A finite input family
  `K : ∀ i, Integral l E (X i).left` accommodates K,L and the optional M.
  `inputReduction.obj K` is their actual strict reduction family.
  Every `Expression.domain` proof is the existing predicate: integral
  constructibility of the inputs, normalized reductions, compatible retained
  etale origins, and uniform finite cohomological and Tor intervals at each
  intermediate occurrence. Geometry proofs are the existing `Expression.geometric`.
* **Actual words, not finite evaluations.** `Word.canonical` reuses
  `CanonicalPair` with every field of `r` supplied, hence the actual units,
  counits, compositors, exchange, projection and open arrows. Its `coefficient`
  constructor is a whole-system coefficient square. Its symmetry and associator
  letters retain the published actual signed braiding and quotient-model
  associator; the primitive tensor model fixes their comparison normalization.
  Composition records intermediate domain proofs; the inverse and context
  constructors retain the prescribed functors.
* **Transport formula and all words.** `transport` is
  `c_source.inv ≫ L.map m ≫ c_target.hom`.
  `Intertwines` is `L.map m ≫ c_target.hom = c_source.hom ≫ q`.
  `WordLaws` states intertwining, equality with this transport, invertibility,
  transport of equal system paths, and the composition equation. This is the
  universal word clause in the node.
* **Canonical completed natural open isomorphism.** `OpenLaws` characterizes the
  inverse system and ringed open maps by open adjuncts of explicitly defined
  restriction comparisons, composed from the two open units, projection squares,
  and tensor-pullback constraint. Its completion square and transport formula
  identify the actual completed map, while its restriction/unit equation is the
  identity normalization. `NaturalityLaws` transports the actual input-family
  naturality square. The inverse case in `WordLaws` gives the inverse transport.
* **Signed symmetry and triple associativity.** Two `Word` paths with the same
  endpoints and the actual whole-system equality `m = m'` give equality of the
  completed paths in `WordLaws`. The actual signed braiding and quotient-model
  associator are letters, including in contexts. No separate generic
  normalized-tensor theorem is reasserted: the dependency theorem supplies the
  generator comparison in the proof.
* **Proper/open generator, scalar restriction, and Gamma_Q.** In
  `ProperOpenLaws`, for each proper/open square in these words, `M` is the
  specified expression evaluated on the actual reductions, and
  `N = (constantRestriction l E U.left).obj M`. The canonical `lam` has its hom
  equal to the actual `properOpenRestrictionMap`; its open adjunct is
  `StrictTower.gamma`. The displayed square starts with scalar restriction of
  `r.properOpen.gamma`, then the bridge/direct-image/open scalar comparisons.
  Its other route uses the bridge at the source and this very adjunct at `N`.
  Thus it relates the word generator itself to the tower map, rather than just
  asserting scalar preservation for an unrelated generic gamma.
* **Finite etale-origin normalization.** The final clause of `ProperOpenLaws`
  quantifies the supplied `ScalarEtaleOrigin` of the actual nth evaluation of
  `N`. Its `w.Λ = scalarRings l E n` and
  `HEq w.φ (constantCoefficient l E n)` pin the actual finite coefficient ring
  and its scalar action. The equation is the canonical `finiteSource.hom`,
  evaluation of this same tower adjunct, and `HD.map finiteGamma` followed by
  `finiteTarget.hom`. It retains `w.origin.L`, so it uses the supplied etale
  antecedent and comparison, with no replacement coefficient lift. There is
  no extra arbitrary `(A,I)` or theorem about unrelated towers.
* **Completed counterpart of that same generator.** `ProperOpenLaws` also
  asserts that the source completion map followed by transport of
  `(r.properOpen.gamma ...).app M` equals the actual
  `r.ringedProperOpen.gamma` followed by target completion. This is the required
  total-limit realization equation under the specified expression comparisons.
* **Lambda identity.** `ProductIdentityLaws` takes actual word witnesses and the
  whole-system identity `lam = lamProper ≫ push c.map es.hom`, and concludes
  `lamC = lamProperC ≫ ringedPush c.map ec.hom`. The ordered lambda recipe is
  the imported product-compactification recipe: Psi has both signed symmetries,
  then exchange tensor identity, projection, and the final compositor. Its
  contexts and compactification identifications are retained by `Word`.
* **Rational/common-stage maps and field enlargement.** `ScalarLaws` uses the
  exact `exchangeProjectionCoefficientRepresentative` prescribed by
  `def-exchange-projection`. Every established equality persists under this
  representative. Its second equation identifies direct and successive
  representatives under the stipulated two endpoint composition cocycles.
  The coefficient target categories have independent universes. The supplied
  rationalization and common-stage comparison functors specialize these laws;
  the imported basic-operation theorem gives their generator identifications.
  No rational object is reduced modulo a finite quotient and no faithfulness of
  finite evaluation is invoked.

### Dependencies and proof sources

All original recorded dependency signatures and docstrings were read and reused:
`FiniteFieldDatum`, the coefficient-extension construction and finiteness,
`ExchangeProjectionStage` and its coefficient representative/cocycle,
`exchangeFunctoriality`, `Compactification.Refinement`,
`finiteTorConstructibleIntegral` / `finiteTorConstructibleEtale`,
`integralCompactificationSystemRealization` and its `Realizations` /
`CanonicalPair`, `ProductCompactification.lambda` / `psi` / `chain` /
`properLambda`, `properOpenTowerComparison`, and
`basicOperationsCoefficientReduction`.

For the repair I additionally read the full scalar restriction and `gamma_scalarRestriction`
interfaces in `Sheaf.SixFunctors.SemilinearProperOpenMatePasting`, the
`CanonicalBridge` and `ProperOpenCoherence.canonical` interfaces, the
`properOpenRestrictionMap` and `properOpenOpenAdjunct` definitions, and
`StrictTower.gamma_evaluation` with `finiteSource`/`finiteTarget` and
`ScalarEtaleOrigin`. Their exact module paths are public imports of this module.
The theorem proof dependencies already cite normalized tensor transport,
contextual intertwining, open normalization, semilinear mate pasting, strict-tower
proper/open calculus, product identity and basic-operation reduction. Their
statements are used as tools, not copied as additional generic conclusions.

Sources reread: current blueprint
`literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-kunneth-relative/lem-sf-kunneth-coherence.proof.md`,
its proper-reduction sentence; `fix-prop-coherence.proof.md`, the maps-used and
inherited-equations sentences; Stacks `sites-cohomology.tex`, Tag 0941,
`lemma-derived-limit-is-ok`; and `more-etale.tex`, Tags 0F7B / 0F7F,
`lemma-shriek-proper-and-open` / `lemma-shriek-proper-and-open-base-change`.
These give the source normalization, while the strict-system and quotient-roof
notions are explicitly agent-extracted constructions as the parent nodes say.

Edge cases retained: empty finite input type when an expression exists, zero
objects and empty schemes, identity opens and proper maps, empty/identity words,
inverse and composite words, two or three factors with parentheses retained,
Koszul sign for odd degrees, first positive level `n+1`, and identity and composed
field extensions `E=F=H`. The scalar quotient map is the actual one even in the
identity-field case. No arbitrary realization or comparison is selected to force
an equation, and no faithfulness of derived evaluation is assumed.

## New nodes

`def-sf-primitive-tensor-realization-data` records the existing projection- and
K-injective-normalized `PrimitiveCounit.RoosRealization` and the existing
`PrimitiveCounit.TensorModel` predicate in
`Sheaf.Paper.CompletedPrimitiveCounitComparison`. It describes exactly their
comparison/projection/resolution fields and simultaneous K-flat quotient-model
normalization, without claiming existence. Source: Stacks 0941 and the recorded
strict-Roos comparison. No definition node owned these precise notions; adjacent
strict-Roos, reduction-presentation and coefficient-site nodes are cited. No Lean
file is added for this node.

`def-sf-completed-tensor-constraint-roofs` records the unchanged
`NormalizedTensorTransport.contraction` and `.quotientAssociator` in
`Sheaf.Paper.NormalizedTensorConstraintTransport`. It states their actual
reduction/counit contraction and the left-contraction, associator,
right-inverse-contraction roof, with the same invertibility condition. Source:
Stacks 0941 / 07A4 and the parent quotient-roof construction. It asserts no
transport equation. No definition node owned these operations. No Lean file is
added for this node.

`def-sf-semilinear-scalar-restriction-data` records the existing `rho`, ordinary
restriction, and adjunction-normalized `rhoP`, `rhoR`, `rhoJ` constructions in
`Sheaf.SixFunctors.SemilinearProperOpenMatePasting`. It retains the component
section identities and actual horizontal maps for any compatible scalar family,
without asserting gamma preservation. Existing semilinear operation, proper/open
mate and evaluation nodes do not define these scalar-restriction comparisons.
Source: scalar restriction and mate adjunction normalizations in Stacks 03CZ /
07A7, as in the published module. No Lean file is added for this node.

`def-sf-strict-tower-proper-open-evaluation-data` records the unchanged canonical
restriction map and open adjunct in `Sheaf.Paper.ProperOpenTowerComparison`, plus
`finiteGamma`, `finiteSource`, `finiteTarget` in its public dependency
`Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus`. It defines their
canonical composites and retained finite-origin coordinates, not the theorem
that they equal gamma. Existing proper/open-arrow and scalar-origin nodes
supply the constituents but did not own these composites. Source: Stacks 0F7B /
0F7F / 0941 and the explicit tower normalization in the published modules.
No Lean file is added for this node.

Searches for all four definition nodes were performed before recording them:
`blueprint_refs.py search Roos` found the adjacent Roos statements;
`blueprint_refs.py search 'tensor contraction'` returned no blueprint node;
a scan of every definition node's `lean.declarations` found no owner for the
precise recorded declarations. Direct `rg` in `lean/WeilConjectures` and
`lean/Sheaf` found the exact published declarations above, which are reused.
The new node `mathlib_searches` records the actual queries/results from
`msearch.py`: LeanSearch queries for projection-compatible Roos tensor models,
termwise scalar restriction, and proper/open finite etale evaluation; LeanFinder
queries for the quotient associator and K-flat tensor model; Mathlib grep
`RoosRealization|quotientAssociator|rhoJInv` (zero hits). Search results were only
ordinary tensor associators, adic completions, scalar restriction on modules, or
ordinary scheme restrictions, with no match for these normalized derived-system
notions. The exact query log is retained by the prescribed search wrapper.

Validation: the revised generator/constant-ring statement was compiled through
`scompile.py` against the live published build. The module retains explicit
universes and `autoImplicit false`; the unrelated competing derived-category
instance is disabled only while elaborating and restored at the end. Every
existing declaration recorded by the new nodes is also checked by the delivery
wrapper's module-mode probes. No global build or live source mutation is used.

## Second reading by Q51

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
