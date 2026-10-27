## Worker report

The module `Sheaf.TraceFormula.FixedTensorKernelStalkCriterion` states
`LocalizedModule.fixedTensor_kernel_stalk_criterion`, with its only proof `sorry`.
Two public proposition abbreviations expand clauses of this same node; they introduce no
independent mathematical object and need no new node. All construction data is real.
The existing node is changed only in `lean`.

Hypotheses and clauses, checked against the original node:

- The arbitrary ring homomorphism R → A is `[CommRing R] [CommRing A] [Algebra R A]`.
  Its map is `algebraMap R A`. Any commutative-ring homomorphism gives this algebra
  structure; there is no injectivity, flatness, or finiteness restriction on the map.
- Arbitrary A-modules M and M′ are `[AddCommGroup M] [Module A M]` and the analogous
  structures for M′. Their restricted R-actions are `[Module R M] [Module R M′]` with
  `IsScalarTower R A M` and `IsScalarTower R A M′`. The tower condition forces precisely
  restriction along the given ring map, rather than an additional mathematical condition.
- The A-linear map u is `f : M →ₗ[A] M′`. The fixed arbitrary R-module N is
  `(N : Type y) [AddCommGroup N] [Module R N]`.
- T_N is `TensorProduct.AlgebraTensorModule.rTensor R N f`, an A-linear map with the
  A-action on the first factor; K is its actual `LinearMap.ker`, an A-submodule.
- Every prime is `q : PrimeSpectrum A`; p is literally
  `q.asIdeal.comap (algebraMap R A)`. Localizations are `LocalizedModule` at `primeCompl`,
  and the scalar rings are `Localization.AtPrime`.
- Both public abbreviations install the canonical R_p → A_q map using
  `Localization.localRingHom ... rfl`. `Module.compHom` restricts the A_q-actions on
  M_q and M′_q along this very map; `IsScalarTower.of_compHom` supplies compatibility.
  These structures are constructed inside the abbreviation body, not hypotheses.
- The localized tensor test tq is heterobasic `AlgebraTensorModule.rTensor` over R_p
  applied to `LocalizedModule.map q.asIdeal.primeCompl f` and test module N_p.
  The result is A_q-linear. Its underlying function is exactly
  u_q tensor_{R_p} 1_{N_p}, as the dependency’s naturality clause specifies.
- The first conjunction quantifies over every prime and asserts
  `ContractedPrimeTensorKernelComparison ... q`: an A_q-linear equivalence
  `e : LocalizedModule q.asIdeal.primeCompl T.ker ≃ₗ[A_q] tq.ker`, with for EVERY z
  `(e z).val = β (α (LocalizedModule.map ... T.ker.subtype z))`.
  The right side localizes the actual kernel inclusion and then applies c = β ∘ α.
  This equation is the required normalization, not merely existence of some isomorphism.
- Here α and β are extracted using `Classical.choose` and `Classical.choose_spec` from
  the exact recorded theorem `contractedPrime_tensor_comparison R A M M′ N q`.
  They are uniquely determined by its pure-fraction formulas: pure tensors generate,
  all localized tensors have a fraction representative, and linearity determines sums.
  Thus this use of an unproved theorem chooses objects determined up to equality, as
  authorized by AGENTS.md §5; it does not choose an arbitrary uncharacterized map.
- The second conjunction is precisely `Function.Injective T ↔ ∀ q, ...Injective ... q`.
  It does not assert an invalid equivalence at an individual prime.
- The third conjunction is `Function.Injective T ↔ ∀ q, q.asIdeal.IsMaximal → ...`.
  Every maximal ideal occurs because it is prime; contraction is still to a prime,
  with no incorrect assumption that its contracted ideal is maximal.
- Universes u,v,w,x,y are explicit and independent. No `Nontrivial`, flatness,
  finite-generation, finite-presentation, or smallness hypotheses appear.
  `set_option autoImplicit false` checks all bound identifiers.

Dependency declarations read and used:

- `Mathlib.Algebra.Module.LocalizedModule.Basic`: `LocalizedModule`, `mk`,
  `mkLinearMap`, `map`, and the fraction criterion. Its localized-ring scalar
  structures come through `Mathlib.RingTheory.Localization.Module`, publicly exposed
  by the comparison dependency.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Spec.map`; their
  underlying points are `PrimeSpectrum`. Only the underlying spectrum is needed here.
- `Mathlib.LinearAlgebra.TensorProduct.Defs`: `TensorProduct`; also read `lift`, `ext′`
  in Basic and `LinearMap.rTensor` in Map. The heterobasic A-linear form used here is
  `TensorProduct.AlgebraTensorModule.rTensor` in Tower, exposed by the dependency.
- `Sheaf.RingTheory.ContractedPrimeTensorComparison`:
  `LocalizedModule.ContractedPrimeTensorComparison` and
  `LocalizedModule.contractedPrime_tensor_comparison`. Read the full expanded statement,
  canonical scalar structures, four pure-generator formulas, naturality, and the
  already-localized N clause. The kernel comparison directly uses the theorem’s α and β.
- Proof-only imports: `Mathlib.Algebra.Module.LocalizedModule.Exact` for the recorded
  `LocalizedModule.map_exact`, and `Mathlib.RingTheory.Ideal.Maximal` for the recorded
  `Ideal.exists_le_maximal`. The theorem docstring gives all four DAG proof steps.

Sources checked: Stacks `literature/stacks-project/algebra.tex`, label
`lemma-universally-injective-check-stalks` (Tag 05CL), including the displayed tensor
identities, exact localization, and its fixed-N kernel argument. This is a supporting
node of the inherited flatification chain, not a blueprint unit’s own statement.

Edge cases checked mathematically before finalizing:

- A is the zero ring: every unital A-module is zero, the prime and maximal families
  are empty, and all tensor tests are injective. No nontriviality binder excludes it.
- N = 0 or M = 0: both tests have zero source, and the normalized kernel equivalence
  has zero source and target. The arbitrary zero map with nonzero M is also covered.
- R = A = integers, f multiplication by 2, N = integers/2: T is zero and not injective;
  its test at (2) is not injective, while tests at odd primes are injective. This
  specifically checks that the criterion is over ALL primes, not one fixed prime.
- Integers → rationals, q = (0): contraction is (0), and the canonical localized
  scalar actions and tensor test retain their literal meaning.
- A maximal ideal may contract to a nonmaximal prime (as above); only q’s maximality
  is tested. Different ring and module universes remain unconstrained.

Searches for existing statements (msearch.py, group Q82, item id):

- LeanFinder: “The kernel of a fixed tensor map localized at algebra primes is identified
  with the kernel of the tensor map over the contracted prime, and injectivity is
  detected at maximal ideals”. Eight hits, including `Algebra.kerTensorProductMapIdToAlgHomEquiv`,
  `Module.Flat.ker_lTensor_eq`, `LinearMap.tensorKerEquiv` and ordinary algebra-localization
  kernels. None states this fixed module test and normalized contracted-prime criterion;
  the flatness hits also impose extra hypotheses.
- Loogle: `LinearMap.toKerLocalized_isLocalizedModule`. One exact ordinary-localization
  kernel result, but no contracted-base tensor comparison or injectivity equivalences.
- Mathlib grep: `toKerLocalized_isLocalizedModule|injective_of_localized_maximal`.
  Four hits in LocalizedModule/Submodule and LocalProperties/Exactness. Read their
  statements: they support the proof but do not state the complete node.
- LeanSearch: “Kernel of a tensor test at a contracted prime and injectivity detected
  at maximal ideals”. Eight hits including `injective_of_localized_maximal`,
  `LinearMap.tensorKer`, `LinearMap.tensorKerEquiv`, and maximal-spectrum inclusion.
  No complete match; ordinary localization must be combined with the existing comparison.
- Project/upstream rg: `fixed.*[Tt]ensor.*[Kk]ernel|[Tt]ensor.*[Ss]talk|contractedPrime`
  returned the comparison dependency and unrelated geometric stalk tensor statements.
  Exact item-id search of `lean/WeilConjectures` had no hits. Exact final declaration-name
  search in WeilConjectures, Sheaf, and `dag/lean_names_upstream.json` had no hits.

No statement dispute, correction, new node, or dependency repair was needed.
Validation: prescribed scompile.py compiled both the sandbox and actual library module
cleanly, with all five universes independent and auto-implicit binding disabled.

## Second reading by Q82

This is a worker self-check; the dispatcher brief forbids starting other agents and assigns
independent review to the maintainer. I reopened the node and final file and checked every
clause listed above. I corrected preliminary elaboration mistakes before the clean compile:
use the A_q-linear localized map for the heterobasic tensor map; use `LocalizedModule S K`
for the kernel localization. The final kernel clause includes the equation specifying the
localized inclusion followed by the dependency’s c, and both injectivity clauses quantify
over the whole indicated family. No individual-prime equivalence is asserted. I checked
the α/β extraction order against the four existential binders in the dependency, and the
maximal test only adds `q.asIdeal.IsMaximal`. No node statement or dependency fields changed.
