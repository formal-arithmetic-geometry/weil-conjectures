## Worker report

The delivery states `IsDiscreteValuationRing.epp_weak_solution_descent` in
`Sheaf.RingTheory.EppWeakSolutionDescent`. Two further theorems state the node's
explicit reduced-tensor and normalization compatibility clauses:
`epp_reduced_tensor_assoc` and `epp_normalization_branchwise`. All three proofs
are exactly `sorry`; their source and step-by-step proofs are in the docstrings.
All helper definitions have actual data. The node is unchanged except for `lean`.

Hypotheses and clauses, read against the node:

- An injective local ring map is encoded by `Algebra`, `Function.Injective
  (algebraMap ...)`, and `IsLocalHom`. `IsDiscreteValuationRing` together with
  `IsDomain` gives exactly the nonfield local PID convention. The main theorem
  binds these for A, B, and C, with `IsScalarTower A B C` for the composite.
- The fraction fields K, L, M are actual fields with `IsFractionRing A K`,
  `IsFractionRing B L`, and `IsFractionRing C M`. The field algebras and the
  seven scalar-tower binders identify all displayed ring/field inclusions.
  They express compatibility of the given inclusions, not further arithmetic
  assumptions. `Module.Finite L M` states the finite extension M/L.
- Completeness is `IsAdicComplete (IsLocalRing.maximalIdeal R) R` for each of
  A, B, C, using the recorded adic-completeness definition. `Module.Finite K K₁`
  is the finite-dimensional coefficient extension K₁/K. Its compatible A action
  is specified by `IsScalarTower A K K₁`.
- `eppReducedTensor E Q E'` is the existing quotient of `Q ⊗[E] E'` by its
  nilradical. The existing `eppUpperClosure S E Q E'` is exactly its integral
  closure over S, while the lower normalization is `integralClosure R E'`.
  The existing `eppNormalizationMap` is the restriction of the canonical
  `a ↦ 1 ⊗ a` followed by reduction, not a supplied arbitrary map.
- The definition `eppIsWeakSolution` includes finite dimensionality and
  quantifies over EVERY maximal ideal q of that upper normalization. Its
  `eppWeakBranch` first requires `(q.comap f).IsMaximal`. The next two conjuncts
  require the lower and upper prime localizations to be domains and DVRs.
  The lower prime instance is quantified explicitly; it exists by comapping
  the given prime q, so this condition is not vacuous. The final conjunct is
  precisely `Ideal.map (localizationMap.comp f) (q.comap f) =
  Ideal.map localizationMap q`, that is n S'_q = q S'_q. Mapping n directly
  into S'_q is the same extension as first extending n to R'_n.
- The first conclusion says the actual A₁ is a complete DVR, using
  `eppIsCompleteDVR`; the next gives a ring equivalence of actual C₁ with
  `∀ i : Fin n, D i`, every D i a complete DVR. `CommRingCat.{u}` packages the
  rings in the same universe as C₁. The formulation permits an empty index,
  but C₁ is nonzero and hence no witness can actually have n=0. No arbitrary
  replacement for the normalization is introduced.
- Clause (i) is the third conjunct: `eppIsWeakSolution A C K M K₁ →
  eppIsWeakSolution A B K L K₁`.
- The last conjunct quantifies over every finite K₂/K₁, with compatible K and
  A structures. The first subclause identifies the lower iterated integral
  closure in K₂ with `integralClosure A K₂` as subrings of the SAME field.
- Clause (ii) is the next subclause. It retains the node's weak-solution
  premise for A→B. For every maximal q of C₁ it assumes
  `eppBranchContinuation A C K M K₁ K₂ q`, then concludes weak solvability of
  K₂/K for A→C. The continuation predicate installs the actual canonical map
  A₁→(C₁)_q by `eppNormalizationLocalizationAlgebra` and tests weak solvability
  with the fraction field of this localization. It universally quantifies
  over compatible field presentations; these are equivalent presentations
  of the unique fraction field, not additional hypotheses on the extension.
  Their universe is at least that of the localized ring and all coefficient
  fields, so the condition is not vacuous for size reasons. No DVR or
  completeness condition on the localization has been added as a hypothesis.
- The final subclause is the node's single-parent assertion. It assumes a
  continuation only at one specified q, then quantifies over all final maximal
  r whose contraction along `eppUpperCoefficientMap C K M K₁ K₂` equals q.
  It concludes the full `eppWeakBranch` condition at r, including exactly the
  ramification-index-one ideal equality used in the node's definition. It
  makes no assertion about other parents. The coefficient map is constructed
  with `Algebra.TensorProduct.map`, quotienting by nilpotents and restricting
  to integral elements; it cannot select a different parent map.
- The theorem `epp_reduced_tensor_assoc` states the successive reduced tensor
  isomorphism for finite E₁/E and E₂/E₁. Its equation on all `(x ⊗ a) ⊗ b`
  specifies the canonical map to `x ⊗ (a b)`. This determines the isomorphism,
  including its structural maps, rather than merely asserting that the two
  rings happen to be isomorphic.
- `epp_normalization_branchwise` states normalization compatibility on every
  first-stage field factor F and every further field factor H. Surjective ring
  maps from the actual reduced tensors select those field factors; both maps
  are constrained on all pure tensors to be the structural products. In H it
  identifies `integralClosure (integralClosure R F) H` with
  `integralClosure R H` as SUBRINGS, so the identity on H respects every map.
  It also states that the intermediate normalization is a complete DVR.
  Here Q, not E, is the fraction field of R: taking (R,Q)=(C,M) or (B,L) and
  E=K gives the upper and intermediate lower cases requested in the node.
  Together with the canonical tensor isomorphism, this identifies precisely
  the corresponding direct-base-change branch. The main theorem gives the
  remaining lower A₁/A₂ equality directly.

Dependency declarations used:

- `Mathlib.Algebra.Algebra.Defs`: `Algebra` and `algebraMap` (field extensions).
- `Mathlib.RingTheory.DiscreteValuationRing.Basic`: `IsDiscreteValuationRing`.
- `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`: `integralClosure` and
  `IsIntegral`; the integral-element predicate supplies the actual subalgebra.
- `Mathlib.LinearAlgebra.TensorProduct.Defs`: `TensorProduct`; the algebra
  tensor operations are in `Mathlib.RingTheory.TensorProduct.Maps`.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`.
- `Mathlib.RingTheory.AdicCompletion.Basic`: `IsAdicComplete`.
- Existing helpers in `Sheaf.RingTheory.EppEssentiallyFiniteTypeTraits`:
  `IsDiscreteValuationRing.eppReducedTensor`, `eppUpperClosure`, and
  `eppNormalizationMap`, whose full signatures, definitions and docstrings
  were read. This import uses only those concrete constructions, not the
  essentially-finite-type existence theorem. No duplicate constructions or
  new definition nodes are needed. The DAG's statement dependencies stay
  unchanged; adding the downstream existence THEOREM as a dependency would
  create a cycle and is unnecessary for these already defined constructions.

Stated proof dependencies are imported privately: NagataOfCompleteLocal,
FiniteOverCompleteLocalProduct, the Mathlib integral-closure/tower, lying-over,
maximal-contraction, uniformizer and PID results. The two proof dependencies
`lem-sfb-dvr-algebraic-normalization-structure` and
`lem-sfb-finite-normalization-local-dvr` have neither a Lean record nor a
Mathlib match locally, and are not needed to type the statement; no unpublished
module was invented for them.

Edge cases checked: identity maps and K₁=K or K₂=K₁; A=B=C; purely inseparable
coefficient extensions (nilpotents are explicitly removed, never assuming
separability); separable split tensors with several parents (single-parent
conclusion is filtered by contraction); arbitrary residue characteristic;
possibly infinite M/K, with only M/L required finite; distinct ring and field
universes; and nonzero normalized products versus empty finite products.
There is no counterexample, statement dispute, or statement correction.

Searches and sources:

- msearch LeanFinder, "Weak solutions of complete discrete valuation rings
  descend along a finite upper field extension and compose through normalized
  reduced tensor branches": eight hits about galLift/galRestrict, none this
  assertion.
- msearch Loogle, "Ideal.ramificationIdx_tower, Algebra.TensorProduct.assoc,
  integralClosure": zero hits.
- msearch grep, `weak.?solution|weakly.?unramified|ramificationIdx_tower`,
  RingTheory: five ramification-tower hits; these assume a given tower and do
  not state descent over all normalized branches.
- msearch LeanSearch, "normalization reduced tensor base change discrete
  valuation rings weak solution": eight hits concerning DVR characterizations,
  base change and unramified maps; no matching assertion.
- msearch LeanSearch and LeanFinder for the reduced-tensor normalization map
  returned `TensorProduct.toIntegralClosure` and integral-restriction maps.
  They do not directly construct this reduced generic tensor normalization.
  msearch grep `eppReducedTensor|eppNormalizationMap|toIntegralClosure`
  returned five hits in Smooth/IntegralClosure. Project rg found the three
  exact canonical helpers above and they are reused.
- rg in WeilConjectures and Sheaf for WeakSolution/weakSolution/weak.solution,
  ReducedTensor/reducedTensor and the node id found no existing statement.
  rg also checked every new declaration name. DAG searches and
  `tools/blueprint_refs.py search 'weak solution'` found no blueprint node
  defining a separate weak-solution predicate. The existing Epp theorem only
  writes its branch condition inline. No parallel definition was copied.
- Read Stacks More on Algebra, remark-construction (09EM), definition-solution
  (09EN), and lemma-solutions-go-down with proof (09ES). The latest blueprint
  direct-image unit has no Epp subargument, agreeing with the node's historical
  provenance. This auxiliary node is not the unit's own statement.

Validation: `scompile.py` successfully compiled both its sandbox and module-path
forms with no warnings or errors. The final dry run and delivery results follow
in the tool output.

## Second reading by Q87

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Maintainer review fix (cc second reader, 2026-10-24)

The delivered module public-imported `Sheaf.RingTheory.EppEssentiallyFiniteTypeTraits` to
reuse `eppReducedTensor`, `eppUpperClosure` and `eppNormalizationMap`. That is the module of
the theorem node lem-sfb-epp-essentially-finite-type-traits. Its proof_deps reach this item
through lem-sfb-epp-weak-perfect-residue and lem-sfb-epp-finite-coefficient-triple, so
stage 3 would hit an import cycle. The siblings Q119 (weak-perfect-residue) and
Q01 (artin-schreier-degree-p) were repaired the same way.

Fix: the import is replaced by Mathlib imports. The three helpers are restated in this
module as `eppWeakReducedTensor`, `eppWeakUpperClosure` and `eppWeakNormalizationMap`, with
the same bodies and with source and blueprint docstrings. A check file compiled in the same
call proves each equal to the original by `rfl`, and a broken-copy control fails. The
mathematics, the hypotheses and the clause structure of all three theorems are unchanged.
Only the helper names in `lean.statement` and `lean.declarations` change; stmt_deps are
unchanged.
