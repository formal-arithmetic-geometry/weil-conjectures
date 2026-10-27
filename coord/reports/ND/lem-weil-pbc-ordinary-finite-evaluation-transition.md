## Worker report

Existing-statement delivery for lem-weil-pbc-ordinary-finite-evaluation-transition.
No module is added. Only the item's `lean` field changes; its reviewed stage-1
statement, seven proof steps, dependencies and review remain untouched.

The exact statements already exist in `Sheaf.Paper.CompletedPullbackReduction`:
`AlgebraicGeometry.Scheme.completedReductionOrdinaryComparison_exists`
(lines 638-648) and
`AlgebraicGeometry.Scheme.completedReductionOrdinaryTransition_exists`
(lines 1477-1485). Both are public theorems, with no private or file-local binder.
The module was read locally and checked against the live server source using
`scompile.py --source Sheaf.Paper.CompletedPullbackReduction`.
The existing proofs are reused, not copied or replaced by new sorry declarations.

Clause-by-clause correspondence (names in namespace `AlgebraicGeometry.Scheme`):

| Node hypothesis or clause | Existing Lean rendering |
| --- | --- |
| Arbitrary scheme morphism g:T'→T | Section binders `{X Y : Scheme.{u}} (g : X ⟶ Y)`, with X=T', Y=T. There is no properness, nonemptiness or Noetherian assumption on the schemes. |
| General Noetherian adic A,I with finite perfect positive quotients and additive torsion A/I | `{A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)`; `AdicCoefficientDatum` extends `CompleteCoefficientDatum`, retaining its ring/ideal conditions, and adds `quotientFinite`. This is the recorded dependency's datum, not a coefficient-field specialization. |
| P_n, S_(W,n), completed limit B_W, projections and quotient maps | `reductionCoefficient W d n`, `pbcAdicCompletion W d`, `completedReductionProjection W d n`, `reductionCoefficientMap W d b a h`. The adic datum's convention is that Lean n means positive exponent n+1. |
| Ordinary completed pullback G and its strict-tower version | `completedModulePullback g d` and `completedTowerModulePullback g d`, constructed in `Sheaf.Paper.CompletedTowerPullback` from the canonical completed coefficient structure map. |
| Ordinary strict quotient tower R_T^0 and E_n^0 | `completedReductionModuleTowerFunctor Y d ⋙ completedTowerModulePullback g d ⋙ (CategoryTheory.evaluation ℕᵒᵖ (pbcModules X (pbcAdicCompletion X d))).obj (op n)`. |
| F_n, finite pullback of ordinary scalar extension | `reductionChange Y (completedReductionProjection Y d n) ⋙ completedReductionFiniteModules g d n`. These are ordinary module functors, with no derived localization in either existence statement. |
| Sheafified scalar tensors and g_f^-1 from the adjunction unit | `pbcTensorSection`/`reductionTensorSection`, `completedReductionInverseImageGenerator`, and `completedReductionFiniteTensor`. The inverse-image generator definition explicitly applies the module-adjunction unit and restricts along `f`. The outer tensor definition applies the module sheafification unit to a presheaf scalar tensor. |
| [s,z,m]_n | `completedReductionFiniteGenerator g d n M V U f s z m`, defined using exactly those inner tensor, inverse-image and outer tensor constructions. |
| For every n≥1, a unique natural isomorphism E_n | `completedReductionOrdinaryComparison_exists (n : ℕ)` has conclusion `∃! e : E_n^0 ≅ F_n ⋙ SheafOfModules.restrictScalars ... , HasCompletedReductionOrdinaryComparisonNormalization g d n e`. Both existence and uniqueness are present; a natural isomorphism is used, not a family of objectwise isomorphisms. |
| Normalization for every M,V,U,f,b,m on the quotient unit | `HasCompletedReductionOrdinaryComparisonNormalization` quantifies over exactly these variables. Its input is `reductionTensorSection X (completedCoefficientMap g d) ... b (completedReductionInverseImageGenerator ... (completedReductionModuleUnit ... m))`. Its output is `completedReductionFiniteGenerator ... ((completedReductionProjection X d n).hom.app (op U) b) 1 m`. |
| Equality in B_(T')-module sections | `completedReductionSectionEquation X (completedReductionProjection X d n) (e.hom.app M) (op U) ... ...` is the equality of the underlying section functions of the map into the scalar-restricted target. |
| For every b≥a≥1, a unique natural transformation t^0_(b,a) | `completedReductionOrdinaryTransition_exists (a b : ℕ) (h : a ≤ b)` asserts `∃! τ` from F_b to F_a followed by scalar restriction along `reductionCoefficientMap X d b a h`. |
| Transition sends [s,z,m]_b to [q'(s),q(z),m]_a | `HasCompletedReductionOrdinaryTransitionNormalization g d a b h τ` quantifies over all M,V,U,f,s,z,m. Its section equation compares the image of `completedReductionFiniteGenerator ... b ... s z m` with the a-generator using `((reductionCoefficientMap X d b a h).hom.app (op U) s)` and `((reductionCoefficientMap Y d b a h).hom.app (op V) z)`. |
| All B_T-module sheaves; no flatness or finiteness on M | In both normalization predicates M is arbitrary in `pbcModules Y (pbcAdicCompletion Y d)`. There are no flatness, finite-generation, derived-completeness or cohomological-boundedness binders. |
| Exactly the fixed ordinary maps, no arbitrary automorphism | `completedReductionOrdinaryComparison` is definitionally `(completedReductionOrdinaryComparison_exists g d n).exists.choose`; `completedReductionOrdinaryTransition` is definitionally `(completedReductionOrdinaryTransition_exists g d a b h).exists.choose`. Their `.choose_spec` gives the stated normalization and uniqueness excludes composition with an unnormalized automorphism. Both fixed maps are also recorded in `lean.declarations`. |

Dependency declarations read and reused:

- `def-weil-pbc-adic-coefficient-datum`: recorded module
  `Sheaf.Paper.AdicCoefficientDatum`, including `reductionCoefficient`,
  `reductionCoefficientMap`, `completedReductionProjection`,
  `completedReductionModuleTowerFunctor`, `reductionChange`, and
  `reductionTensorSection`; its imported `CompletedAdicCoefficientDatum` supplies
  the exact `AdicCoefficientDatum` structure.
- `def-weil-pbc-completed-pullback`: recorded module
  `Sheaf.Paper.PbcQbarCompletedPullback` publicly retains the integral tower
  interface, as its `lean.note` specifies. The general datum-based declarations
  actually used here are `completedModulePullback`,
  `completedTowerModulePullback`, `completedCoefficientMap`, and
  `completedFiniteCoefficientMap` in the retained
  `Sheaf.Paper.CompletedTowerPullback`. No Qbar hypotheses are imported into the
  existing theorem signatures and no dependency replacement is needed.
- `def-cbc-completed-reduction-finite-interfaces`: recorded existing module
  `Sheaf.Paper.CompletedPullbackReduction`, with
  `completedReductionFiniteModules`, `completedReductionFiniteGenerator`, and
  `completedReductionOrdinaryTransition`. The existing normalization predicates
  and comparison in this same module are exactly the fixed constructions named
  in the node statement. This is not the derived transition-coherence assertion
  of `FiniteQuotientOrdinaryComparison`.
- `def-pur-sheaf-tensor-product`: recorded module
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses` and its public
  imports retain the existing sheafified tensor and its independent universe
  support. Its `SheafOfModules.cochainModulesMonoidal` instance is not redefined.
  The concrete scalar tensor representatives in this statement are the same
  recorded scalar-extension/sheafification operations, not sectionwise tensors
  substituted for sheaf tensors.

Sources read: the item's seven-step reviewed proof; the current blueprint's
`sk-prop-pbc-complete/lemma-weil-pbc-completed-pullback-reduction.proof.md`;
`sites-modules.tex`, `lemma-adjoint-pullback-pushforward-modules` (03D7) and
`section-tensor-product` (03EK); and the full signatures, normalization predicates,
generator definitions and docstrings in `CompletedPullbackReduction.lean`.
The node's source explicitly identifies the two existence theorem names and lines.

Edge cases checked against signatures and definitions: Lean n=0 is positive
exponent 1; arbitrary positive exponents are covered. Equal indices a=b are
allowed by `h : a ≤ b` and the coefficient map is identity. M=0 and arbitrary
nonflat modules remain in the quantified category. The identity morphism and
empty schemes/site objects have no excluded binder. The zero coefficient ring
(and I=A when the datum permits it) is not excluded. The small site object and
morphism universes remain those of `Scheme.{u}` with coefficients in `Type (u+1)`;
no site-universe equality or extra size restriction is introduced.

Searches on 2026-10-22:

- `msearch.py ... leanfinder`, query "ordinary finite coefficient sheaf pullback
  comparison and quotient transition uniquely normalized by tensor generators":
  8 hits, including `SheafOfModules.pullbackObjFreeIso`, presentation generators
  and relations, and free-generator pullback formulas. None states the adic
  quotient comparisons with these two normalizations.
- `msearch.py ... loogle`, query
  `SheafOfModules.pullback, SheafOfModules.restrictScalars`: 0 hits.
- `msearch.py ... grep`, regex
  `pullback.*restrictScalars|restrictScalars.*pullback`, directory
  `Algebra/Category/ModuleCat`: 0 hits.
- `msearch.py ... leansearch`, query "ordinary finite coefficient sheaf pullback
  scalar extension quotient natural comparison unique tensor generators":
  8 hits, including `PresheafOfModules.pullback`,
  `PresheafOfModules.pullbackPushforwardAdjunction`,
  `SheafOfModules.sheafificationCompPullback`, and free pullback isomorphisms;
  general ingredients, no exact match.
- `rg` in `lean/WeilConjectures` for the two existence names and ordinary finite
  evaluation/quotient transition: only unrelated formal-functions finite quotient
  transition hits. `grep -rn` for this node's id: no hits.
- `rg` in `lean/Sheaf` for the two existence theorem names finds their definitions
  at lines 638 and 1477 of `CompletedPullbackReduction.lean` and uses in
  `FiniteQuotientOrdinaryComparison.lean`. These are the exact existing matches.
  The node therefore records them with `existing: true` rather than duplicating
  their statements in a new module.

No new nodes, dependency modules, statement corrections or disputed statements.
The previous worker's unchanged-item preflight failure is addressed by adding the
missing `lean` binding, without touching the already reviewed stage-1 split.
The delivery wrapper checks all four existing declaration names on the server
through `scompile.py` before its server preflight.

## Second reading by ND

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
