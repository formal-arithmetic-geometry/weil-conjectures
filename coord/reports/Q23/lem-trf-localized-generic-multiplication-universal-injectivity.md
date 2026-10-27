## Worker report

The module `Sheaf.RingTheory.LocalizedGenericMultiplication` states
`Algebra.localized_genericMultiplication_universally_injective`. Its only postponed proof
is that theorem. Four auxiliary declarations construct the tuple linear map, its actual
range quotient, the localized quotient arrow, and the canonical map to the generic fibre.
These are constructions belonging to this node, not independent additional notions.
There are no new nodes, dependency replacements, statement corrections, or disputed statements.
The shared repository was read only; all authored files are in the prescribed sandbox.

Sources read: Stacks `more-morphisms.tex`, Tag 0573,
`lemma-scheme-theoretically-dense-generic-fibre`, especially lines 6596–6642, and
`algebra.tex`, Tag 00HL, `lemma-flat-tor-zero`, lines 9035–9072. The first source
constructs exactly the multiplication tuple and cokernel, embeds the flat algebra in
its generic fibre, and tensors the resulting short exact sequence. The second source
allows every module N. Finite type in 0573 is used earlier to obtain simultaneous
flatness, which this node already assumes; it is not a hypothesis of this algebraic
subargument. Read the complete node and all five proof steps.

Hypothesis and clause correspondence:

- A is a commutative integral domain: `(A : Type u) [CommRing A] [IsDomain A]`.
- K is its fraction field: `(K : Type w) [Field K] [Algebra A K]
  [IsFractionRing A K]`. This is localization at all nonzero elements.
- B is an arbitrary commutative A-algebra: `(B : Type v) [CommRing B] [Algebra A B]`.
  No finite type, presentation, Noetherian, or nontriviality assumption on B occurs.
- The nonnegative finite tuple is `(m : ℕ) (g : Fin m → B)`, allowing m = 0.
- The map μ is `genericMultiplicationTuple A g`, constructed with `LinearMap.pi`
  and `LinearMap.mulLeft A (g i)`. It sends b to the tuple `(g i * b)`.
- The actual M is `genericMultiplicationCokernel g`, namely
  `(Fin m → B) ⧸ LinearMap.range (genericMultiplicationTuple B g)`.
  This range has the same underlying image as the A-linear tuple map: the
  B-linear map is the identical function. Its range is stable under B, so the
  quotient has its usual B-module structure and the restricted A-module structure.
  Thus this is precisely the stated cokernel over A, not an arbitrary module.
- Generic injectivity is `hgeneric : Function.Injective
  (genericMultiplicationTuple A (fun i => g i ⊗ₜ[A] (1 : K)))`.
  Multiplication is the ordinary algebra tensor-product multiplication.
- The element is `(a : A) (ha : a ≠ 0)`.
- The actual B_a is `Localization.Away (algebraMap A B a)`. Its A-action is
  through A → B → B_a. The first flatness hypothesis is exactly
  `[Module.Flat A (Localization.Away (algebraMap A B a))]`.
- The actual M_a is `LocalizedModule.Away (algebraMap A B a)
  (genericMultiplicationCokernel g)`, with its restricted A-action. Localizing a
  B-module at the image of a has fractions m/(image(a))^n with exactly the same
  relations as localization of its underlying A-module at a. This is the node's
  specified localization, not a localization of an unrelated quotient. The second
  hypothesis is `Module.Flat A` of exactly this module.
- The first conclusion is `Function.Injective
  (genericMultiplicationToFractionTensor A B K a ha)`. This is an explicit
  `IsLocalization.Away.liftAlgHom` of `Algebra.TensorProduct.includeLeft`.
  The invertibility input comes from the nonzero image of a in K, mapped by
  `includeRight`; the two `AlgHom.commutes` equalities identify it with the
  image under `includeLeft`. Its value is therefore b/a^n ↦ b ⊗ a^(-n),
  including when the target tensor algebra is zero. No arbitrary map is assumed.
- The localized μ_a is `genericMultiplicationTuple A
  (fun i => algebraMap B (Localization.Away (algebraMap A B a)) (g i))`.
- The specified q_a is `genericMultiplicationLocalizedQuotient A g a`. This is
  the sum, over the coordinates i, of the localized linear map of
  `range(μ).mkQ.comp (LinearMap.single B (fun _ : Fin m => B) i)`, composed
  with the i-th projection, then restricted to A. Mathlib's
  `IsLocalizedModule.map` with the ring localization map on B and the module
  localization map on M makes each summand send b/s to q(e_i b)/s. Thus a tuple
  with common denominator s goes to q((b_i)_i)/s, exactly the node's q_a.
- The short exact sequence is rendered by its three substantive conditions:
  `Function.Injective μ_a`, `Function.Exact μ_a q_a`, and
  `Function.Surjective q_a`. These conditions include both zero endpoints.
- For every A-module N the next conjunct quantifies
  `(N : Type (max u v w x)) [AddCommGroup N] [Module A N]` and asserts
  `Function.Injective (μ_a.lTensor N)`, literally id_N ⊗ μ_a with target
  `N ⊗[A] (Fin m → B_a)`. There is no flatness or finiteness condition on N.
- For every commutative A-algebra C the final conjunct quantifies
  `(C : Type (max u v w y)) [CommRing C] [Algebra A C]`, assumes just
  `IsUnit (algebraMap A C a)`, and asserts injectivity of
  `genericMultiplicationTuple A (fun i => g i ⊗ₜ[A] (1 : C))` on B ⊗ C.
  The indices x and y are independent universes. The common max convention
  keeps test universes above the base; smaller modules/algebras are represented
  by the equivalent universe lifts, without imposing a mathematical restriction.

Dependencies used, with their recorded declarations inspected:

- `def-weil-pbc-module-tensor-product`: `TensorProduct`,
  `Mathlib.LinearAlgebra.TensorProduct.Defs`, and its ordinary algebra structure
  and inclusions from `Mathlib.RingTheory.TensorProduct.Basic`.
- `def-weil-pbc-flat-ring-map`: `Module.Flat`,
  `Mathlib.RingTheory.Flat.Basic`, imported publicly through the recorded
  `Mathlib.RingTheory.RingHom.Flat` (`RingHom.Flat` is the ring-map version).
- `def-weil-ring-localization-away`: `Localization.Away`,
  `Mathlib.GroupTheory.MonoidLocalization.Away`, and `IsLocalization.Away`
  and `IsLocalization.Away.liftAlgHom` from
  `Mathlib.RingTheory.Localization.Away.Basic`.
- `def-weil-pbc-module-localization-away`: `LocalizedModule.Away`,
  `LocalizedModule.mkLinearMap`, and `IsLocalizedModule.map` from
  `Mathlib.Algebra.Module.LocalizedModule.Basic`; the compatibility of ring
  and module localization is supplied by
  `Mathlib.Algebra.Module.LocalizedModule.IsLocalization`.
- Proof dependencies: `LocalizedModule.map_exact` and
  `IsLocalizedModule.map_exact` from `Mathlib.Algebra.Module.LocalizedModule.Exact`;
  `Module.Flat.lTensor_preserves_injective_linearMap` from
  `Mathlib.RingTheory.Flat.Basic` (already publicly available);
  `LinearMap.lTensor_injective_of_exact_of_flat` from
  `Mathlib.RingTheory.Flat.Equalizer`; `TensorProduct.piLeft` from
  `Mathlib.LinearAlgebra.TensorProduct.Pi`. The three additional proof-only
  modules are plain imports, not public imports. No dependency interface is replaced.

Edge cases checked before drafting and again against the final file:

- m = 0: the product, range quotient, and sum defining q_a are zero modules.
  Generic injectivity forces B_K = 0, and flatness of B_a embeds it into B_K,
  forcing B_a = 0. Every claimed injection and exactness statement then holds.
- B = 0 or C = 0 is permitted by CommRing, and `IsUnit 0` holds in the zero
  ring. The tensor products and localized constructions are zero, as required.
- A a field and a any nonzero scalar: localization does not change B or M;
  the theorem reduces to the flat-quotient tensor argument.
- a = 1: the maps are the unlocalized maps; a = 0 is explicitly excluded.
- N = 0, and nonflat N, remain included; flatness is required only on M_a.
- B = A[x], g = (x): the conclusion is valid; M = A is flat. By contrast,
  over A = ℤ, B = ℤ, g = (2), a = 1 the cokernel is ℤ/2 and is not flat;
  tensoring with ℤ/2 destroys injectivity. This verifies the quotient-flatness
  hypothesis does meaningful work and has not been replaced by a hollow condition.

Searches actually run with the prescribed `msearch.py` wrappers:

- LeanFinder: “A generically injective multiplication tuple over a domain is
  universally injective after localization when the localized algebra and cokernel
  are flat.” Eight results including `IsLocalization.mapₐ_injective_of_injective`,
  `Algebra.Generators.liftBaseChange_injective_of_isLocalizationAway`, and
  `TensorProduct.toIntegralClosure_injective_of_flat`. None states this node:
  localization-map preservation assumes an injection already, and the integral
  closure theorem concerns another map.
- Loogle: `"lTensor_injective_of_exact_of_flat"`. Found
  `LinearMap.lTensor_injective_of_exact_of_flat`; its full signature requires
  an already short exact sequence and only supplies the tensor conclusion.
- Mathlib grep: `piEquiv|pi_equiv|pi.*[Ll]ocaliz|[Ll]ocaliz.*pi|awayLift|Away.lift`
  in `Algebra/Module/LocalizedModule`. Two unrelated header matches in Away.lean;
  no finite-product localization equivalence to reuse.
- Mathlib grep for all four proposed full helper/main names: zero matches.
- `rg` of both `lean/WeilConjectures` and `lean/Sheaf` for
  `localized-generic-multiplication|localizedGeneric|generic.*[Ii]nject|[Mm]ultiplication.*[Tt]uple`:
  related generic-basis, flat-quotient, and generic-field material but no exact
  tuple-map theorem. A further grep for localized cokernel and tuple helper names
  found generic quotient transports, none constructing this node's tuple and maps.
  The item id has no upstream module match. No existing declaration states all
  clauses of the item. The foundational tensor/localization/flatness notions are
  reused, not duplicated.

Validation uses only the authorized scompile.py wrapper. The first pass found
explicit arguments needed by LinearMap.single and a map-zero normalization in
its invertibility certificate; both were corrected using the inspected signatures.
A subsequent pass compiled both sandbox and library modules, with only two long
lines to wrap; these were wrapped before the final clean compile and delivery.

## Second reading by Q23

I reread the final module against the unchanged JSON statement, independently of
its drafting sequence. This is the worker's self-check; the maintainer supplies
the independent delivery review, as specified in the dispatch brief. No additional
agent was started.

The binders include precisely the domain A, its fraction field K, arbitrary
A-algebra B, m ≥ 0, the tuple, its generic injectivity, nonzero a, and both actual
localized-module flatness assumptions. The cokernel quotient uses the same
multiplication function over B, with its canonical restricted A-structure; thus
it is the cokernel over A intended by the node. In particular the second flatness
binder is about the localization of the ORIGINAL cokernel, not an unrelated
quotient introduced after localization. The localized quotient is constructed
coordinatewise and summed, so for common denominators it is exactly the specified
quotient map. The target of the universal tensor map is the tensor of the finite
product, while the algebra clause correctly uses the product of the base-changed
algebra. These are distinct clauses in the node and both are retained.

The main conclusion has every clause: injective canonical generic map; injective
localized tuple; exactness with q_a; surjectivity of q_a; injectivity for arbitrary
N; and injectivity of the specified tuple after every unit-inverting C. No finite
presentation/finite type/Noetherian assumptions or extra algebra hypotheses were
introduced. I checked the zero algebra and empty tuple cases again. The only
changes identified during typing were helper arguments, normalization of map zero,
and line wrapping, not mathematical changes. All helper data is supplied by explicit
Mathlib constructions; the only sorry is the main node's theorem, with all five
proof steps in its docstring.
