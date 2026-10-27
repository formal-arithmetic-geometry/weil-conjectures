## Worker report

The module `Sheaf.RingTheory.QuotientFlatnessDirectedLimit` states
`Module.exists_flat_quotient_of_directed_iSup`, with its whole proof `sorry`.
It introduces no definition and changes only the item's `lean` record.

Source read: `literature/stacks-project/flat.tex`, Situation
`situation-flat-at-point` (05MK) and Lemma `lemma-flat-at-point` (05MN), part (2),
and `literature/stacks-project/more-algebra.tex`,
`lemma-limit-preserving-flat-at-primes` (05LT), including its essentially
finitely presented case. In the quotient situation the local algebra remains
local, so the closed set of tested primes is its unique closed point. The
node's six-step proof expands this specialization without a Noetherian
assumption; the declaration docstring records all six steps and their inputs.
The example CompactObject module is now withdrawn; its node points to the
upstream declaration. The new module follows the current `module`, public
imports, and exposed public section format of the upstream statement modules.

Hypothesis and conclusion correspondence:

- The commutative local rings are `[CommRing A] [CommRing B] [IsLocalRing A]
  [IsLocalRing B]`. The map is `algebraMap A B`, for `[Algebra A B]`, and
  `[IsLocalHom (algebraMap A B)]` states that it is local. The maximal ideal
  is Mathlib's `IsLocalRing.maximalIdeal A`.
- The hypothesis that B is a localization of a finitely presented A-algebra
  is exhibited by `{C : Type w} [CommRing C] [Algebra A C]
  [Algebra.FinitePresentation A C]`, `(S : Submonoid C)`, `[Algebra C B]`,
  and `[IsLocalization S B]`. `IsScalarTower A C B` requires this presentation
  to induce the specified A-algebra structure on B. C and S are witnesses
  for the localization hypothesis already present in the node, not an
  assumption that B itself is finitely presented. Given the node's existence
  hypothesis one chooses its witnesses and applies this statement.
- P is `[AddCommGroup P] [Module B P] [Module.FinitePresentation B P]`.
  `[Module A P] [IsScalarTower A B P]` express restriction of its B-action
  along the specified map. This adds no independent condition: the restricted
  action always supplies these instances. No finite presentation over A is
  assumed.
- An arbitrary set of indices is `{L : Type l}`. `[Nonempty L]` requires an
  index; `(J : L → Ideal A)` is the family; `hJ : Directed (· ≤ ·) J` means
  that each pair has an upper bound under ideal inclusion. No linear order,
  monotone enumeration, or antisymmetry of indices is required.
- `hJmax : ∀ i : L, J i ≤ IsLocalRing.maximalIdeal A` is exactly the
  containment in the maximal ideal for each member.
- The union J is written `⨆ i : L, J i`. For a nonempty directed family,
  `Submodule.coe_iSup_of_directed` identifies its underlying set with the
  ordinary union, so this does not replace the union by a larger ideal.
- For any ideal K, the module `P/KP` is encoded by `(A ⧸ K) ⊗[A] P`, with
  the standard left `A ⧸ K` action. The existing canonical equivalence
  `TensorProduct.quotTensorEquivQuotSMul P K` identifies it with
  `P ⧸ (K • (⊤ : Submodule A P))`, sending `(a+K) ⊗ x` to `a • x + KP`.
  Its inverse sends `x+KP` to `1 ⊗ x`. Thus the submodule killed is exactly
  the finite sums of products specified in the node, with the canonical
  quotient-ring action. This is the quotient module's standard tensor
  construction, with no arbitrary map or chosen module structure.
- `hflat : Module.Flat (A ⧸ (⨆ i : L, J i))
  ((A ⧸ (⨆ i : L, J i)) ⊗[A] P)` states flatness of the union quotient.
  `∃ i : L, Module.Flat (A ⧸ J i) ((A ⧸ J i) ⊗[A] P)` states exactly
  existence of a member quotient flat over its corresponding base quotient.
  There is no eventual-flatness or additional conclusion.
- There are no henselian, Noetherian, characteristic, finite-generation-of-
  ideals, or module-nonzero hypotheses. All five carrier/index universes
  `u v w p l` are explicit and independent. Here the family is represented
  directly by ideals and their supremum, without a category of rings whose
  size would force an index-universe restriction.

Dependency interfaces read and used:

- `def-weil-pbc-finitely-presented-algebra`: `Algebra.FinitePresentation`,
  `Mathlib.RingTheory.FinitePresentation`, class given by a finite polynomial
  presentation with finitely generated relation ideal. Used on A → C.
- `def-sc-finitely-presented-module`: `Module.FinitePresentation`,
  `Mathlib.Algebra.Module.FinitePresentation`, class given by a finite
  generating set with finitely generated kernel, equivalent to the node's
  finite free presentation. Used over B.
- `def-weil-pbc-flat-ring-map`: its recorded `Module.Flat` declaration,
  supplied through `Mathlib.RingTheory.RingHom.Flat` (definition in
  `Mathlib.RingTheory.Flat.Basic`). Its injectivity-of-tensor criterion is
  exactly the node's module-flatness notion. The ring-map part `RingHom.Flat`
  is not substituted for module flatness.

All three dependency node records and the complete declaration signatures
and docstrings were read. No dependency repair was necessary. The public
imports also give the standard local-ring, localization and quotient tensor
interfaces. The already stated proof dependencies are imported privately:

- `Mathlib.Algebra.Module.LocalizedModule.Exact`: `LocalizedModule.map_exact`
  for `lem-weil-pbc-localization-module-exact`; it also supplies the recorded
  module localization construction from `LocalizedModule.Basic`.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`
  for `def-weil-pbc-localization-at-prime`.
- `Mathlib.RingTheory.Localization.Ideal`: the quotient-localization instance,
  prime contraction and ideal extension interfaces in the mathlib matches of
  `lem-weil-pbc-localization-at-prime-of-quotient` and
  `lem-weil-pbc-localization-quotient-by-prime`.
- `Mathlib.RingTheory.Flat.Localization`: `Module.flat_of_isLocalized_maximal`,
  the existing match for `lem-sfb-base-flatness-maximal-localizations`.
- `WeilConjectures.RingTheory.OpenFlatLocus`:
  `Module.isOpen_setOf_flat_localizedModule`, the recorded openness theorem.
- `WeilConjectures.AlgebraicGeometry.AffineFlatModuleDescent`:
  `AlgebraicGeometry.exists_eventually_flat_of_finitePresentation`, the
  recorded finite-presentation flat-module descent input.

Edge cases checked: P may be zero (all quotients are zero and hence flat);
the family may be a singleton, contain repeated ideals, or consist entirely
of zero ideals; it need not have a largest element. Its nonempty condition
is essential for the existential conclusion and for literal union=supremum.
Every member and the directed union are proper because they lie in the
maximal ideal; local rings here use the source's nonzero convention. S can
be `{1}`, permitting B already finitely presented. Nothing requires C to be
local. Arbitrary characteristic and arbitrary non-Noetherian local A are
admitted. In particular, the statement does not accidentally ask that P be
finitely presented over A.

Searches performed with the prescribed `msearch.py NF
lem-sfb-fp-quotient-flatness-directed-limit` wrapper:

- `leanfinder`: "A finite presentation module over a localization of a
  finitely presented local algebra flat modulo a directed union of ideals is
  flat modulo one ideal". Eight hits: local tests such as
  `Module.flat_of_isLocalized_span`, `Module.flat_of_isLocalized_maximal`,
  and `Module.flat_of_localized_maximal`, plus flatness of localizations,
  Noetherian smoothness and adic completion. None is quotient-base descent.
- `loogle`: `Module.FinitePresentation, Module.Flat`. Six hits: base change
  of Hom, projectivity of flat finitely presented modules, finite-free
  factorization, basis existence, and rank at stalks. None descends flatness
  along the directed quotient-base family.
- `grep`: `flat.*(limit|colimit|quotient)|((limit|colimit|quotient).*flat)`
  in `RingTheory`. Six hits in Flat/Tensor, Flat/CategoryTheory, Flat/Basic
  describe tensor preserving finite limits, not this assertion.
- `rg` in both project roots, then focused searches in
  `lean/WeilConjectures/RingTheory` and `lean/Sheaf/RingTheory`, for essential
  finite presentation, directed/quotient flatness, and `flat.*iSup` found
  general colimit flatness, finite-presentation module descent, local
  injectivity criteria, and other flat quotient theorems; no duplicate of
  this local directed-ideal statement. The general affine module descent
  theorem is reused as a proof dependency. The literal blueprint-id search
  in `lean/WeilConjectures` found no declaration for this item.

No statement correction, new node, hollow definition, or disputed assertion.

Validation: the prescribed `scompile.py` compiled both its sandbox view and
`Sheaf.RingTheory.QuotientFlatnessDirectedLimit` against the live published
library with exit code 0 and no warnings. All declaration variables and
universes are explicitly bound, and the maximum Lean line length is 89.

## Second reading by NF

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
