## Worker report

The module `Sheaf.RingTheory.CompletionKaehlerDifferentialComparison` states
`Algebra.completion_kahler_differential_comparison`, with its sole theorem proof `sorry`.
`IsCompletedDifferentialExtension` abbreviates exactly the extension and continuity
conditions occurring in that statement. The companion definition module
`Sheaf.RingTheory.ContinuousKaehlerDifferential` constructs the inverse-limit module
and its actual canonical derivation; none of its data is postponed.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The field is `{k : Type u} [Field k]`. The finite-type algebra is
  `{S : Type v} [CommRing S] [Algebra k S]` with
  `hS : (algebraMap k S).FiniteType`. This uses the recorded `RingHom.FiniteType`;
  it is equivalent to `Algebra.FiniteType k S` by `RingHom.finiteType_algebraMap`.
- The maximal ideal is `(p : Ideal S) [p.IsMaximal]`; the actual local ring is
  `Localization.AtPrime p`, throughout. Its maximal ideal is
  `IsLocalRing.maximalIdeal (Localization.AtPrime p)`, the extension of `p`.
- The residue field is `p.ResidueField`, definitionally the quotient of this
  local ring by its maximal ideal. Since `p` is maximal it is canonically `S/p`:
  `IsLocalization.AtPrime.equivQuotMaximalIdeal p (Localization.AtPrime p)` is
  the explicit ring equivalence, with the original-ring quotient maps matched
  by `equivQuotMaximalIdeal_apply_mk`. This changes only the carrier presentation.
- The completed ring is `Algebra.LocalCompletion (Localization.AtPrime p)`, the
  already recorded abbreviation for `AdicCompletion m A` from
  `Sheaf.RingTheory.FormalLocalPresentation`; its residue projection is
  `AdicCompletion.evalOneₐ m`.
- Finite separability is `[FiniteDimensional k p.ResidueField]` and
  `[Algebra.IsSeparable k p.ResidueField]`. Neither perfection of `k` nor a
  restriction on characteristic occurs.
- The chosen section is encoded by the input instance
  `[Algebra p.ResidueField (LocalCompletion A)]`. Its algebra map is σ.
  `[IsScalarTower k p.ResidueField (LocalCompletion A)]` says that σ is a
  `k`-algebra map, for the fixed structural `k`-action on the completion.
  `hσ` says precisely `evalOneₐ m (σ c) = c` for every residue-field element.
  Thus the input ranges over all the specified `k`-algebra sections; it makes
  no existence assumption beyond the section the node explicitly chooses.
- The continuous differential module is
  `KaehlerDifferential.Continuous p.ResidueField (LocalCompletion A) J`, where
  `J = m.map (algebraMap A (LocalCompletion A))`. At component `n : ℕ` it uses
  `KaehlerDifferential p.ResidueField (LocalCompletion A ⧸ J^(n+1))` with the
  induced action of the section. The transition `adicTransition` is constructed
  using `Ideal.Quotient.factorₐ` and `KaehlerDifferential.map`, not an arbitrary
  linear map. `continuousSubmodule` is the actual submodule of compatible
  families; requiring adjacent compatibility is equivalent to all quotient
  transitions by induction. Component `n=0` is the quotient by `J`, so no first
  positive quotient is lost. `continuousD` is an actual `Derivation`, given
  componentwise by differentiation after the quotient map.
- The completed tensor module is the existing `Algebra.CompletedDifferentials k A`,
  from `Sheaf.RingTheory.CompletedJacobianPresentation`. It writes the completed
  ring on the LEFT: `Â ⊗[A] Ω[A/k]`. The node writes the factors on the right.
  Tensor symmetry identifies these modules canonically, with `da ⊗ 1` going to
  `1 ⊗ da`; the completion-linear structure and every specified image agree.
  This reuses the shared tensor carrier rather than introducing another one.
- Clause (i): the first existential introduces `D : Derivation k Â
  (CompletedDifferentials k A)`. `IsCompletedDifferentialExtension` requires
  `D (algebraMap A Â a) = 1 ⊗ da` for EVERY `a : A` and the zero-neighbourhood
  criterion `∀ r, ∃ N, ∀ x ∈ J^N, D x ∈ J^r • ⊤`. For additive maps this is
  exactly continuity for the stated adic topologies. The following universal
  quantifier over `D'` gives uniqueness among ALL continuous extensions,
  independently of the comparison isomorphism.
- Clause (ii): the next existential is a linear EQUIVALENCE `e : ... ≃ₗ[Â] ...`.
  Its first property prescribes the image of `1 ⊗ da` for every `a : A` as
  `continuousD F Â J (algebraMap A Â a)`. The universal quantifier over `e'`
  gives uniqueness among all linear equivalences with just those prescribed
  generator images; no continuity or compatibility condition is added to that
  uniqueness test. Finally `∀ x : Â, e (D x) = continuousD F Â J x` asserts the
  compatibility on ALL elements, including those outside the image of `A`.

Dependency declarations inspected and used:

- `Mathlib.RingTheory.FiniteType`: `RingHom.FiniteType` (and its relation to
  `Algebra.FiniteType`), for def-weil-pbc-finite-type-algebra.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`;
  `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`: `Ideal.ResidueField`, for
  def-weil-pbc-localization-at-prime. The displayed maximal-ideal quotient
  equivalence verifies the maximal-ideal specialization.
- `Mathlib.FieldTheory.Separable`: `Algebra.IsSeparable`, for
  def-weil-pbc-separable-algebraic-extension.
- `Mathlib.RingTheory.AdicCompletion.Basic` and `.Algebra`: `AdicCompletion`,
  its compatible-family construction, `evalOneₐ`, and its algebra structure,
  for def-weil-pbc-adic-completion.
- `Mathlib.RingTheory.Kaehler.Basic`: `KaehlerDifferential`, `D`, `map`,
  `map_D`, and `linearMapEquivDerivation`, for def-weil-pbc-kahler-differentials.
- `Mathlib.LinearAlgebra.TensorProduct.Defs`: `TensorProduct` and pure tensors,
  for the mathlib leaf def-weil-pbc-module-tensor-product.
- `Sheaf.RingTheory.FormalLocalPresentation`: `Algebra.LocalCompletion`, owned
  by the landed def-trf-formal-local-presentation, added to `stmt_deps`.
- `Sheaf.RingTheory.CompletedJacobianPresentation`:
  `Algebra.CompletedDifferentials`, owned by the landed
  def-trf-completed-jacobian-presentation, added to `stmt_deps`.
- The newly defined `KaehlerDifferential.Continuous` and `.continuousD` are
  cited through def-trf-continuous-kahler-differentials, added to `stmt_deps`.
  No dependency record needed repair.

The proof docstring includes all seven steps of the node: Noetherianity and
finite differentials; quotient-coordinate construction and unique continuity;
vanishing of residue-field differentials; the maps α; shifted maps β; both
composites at every positive index; and compatibility on arbitrary completed
ring elements plus generator uniqueness. Recorded proof leaves are available
through the Mathlib imports `AdicCompletion.AsTensorProduct`,
`AdicCompletion.Completeness`, `Etale.Kaehler`, `Unramified.Field`,
`Localization.Submodule`, and `FiniteType` (and their defining imports).

Edge cases checked before writing: maximality excludes the zero algebra as a
local point, with no unnecessary nontriviality binder on `S`. If `S=k` and `p=0`,
the maximal-ideal completion is `k` and both differential modules are zero;
the unique derivation and zero-module equivalence are included. More generally
finite separable residue extensions and zero cotangent modules are allowed.
All characteristics are allowed. There is no bound on the number of algebra
generators. The inverse limit includes the first positive quotient even when
its differential module is zero. The continuity criterion includes `r=0`;
that harmless neighbourhood is automatic, while every positive exponent is
also required. Both universes `u v` are bound independently and may differ.

Searches made for the item: msearch LeanFinder, “completion of a local finite
type algebra Kahler differentials continuous differentials inverse limit”,
returned finite-presentation and ordinary Kähler results only. Loogle
“KaehlerDifferential, AdicCompletion” returned zero hits. Mathlib grep
“completion.*[Dd]ifferential|[Dd]ifferential.*[Cc]ompletion” in RingTheory returned
zero hits. Source grep for the item id returned no match. LeanSearch for the
inverse-limit description found ordinary Kähler differentials and ordinary
module completion, without this comparison. Grep of `WeilConjectures` and
`lean/Sheaf` found no comparison theorem; it did locate the existing
`CompletedDifferentials`, which this delivery reuses. Declaration-name checks
in Mathlib, upstream and side sources found no conflicts in the chosen namespaces.
The new node retains the full verbatim search outputs in `mathlib_searches`.

No statement correction or disputed mathematical statement was needed. The only
changes to the original node are its `lean` record and the three added statement
dependencies. Definitions have real data and structural verification only;
the comparison theorem alone is postponed.

## New nodes

`def-trf-continuous-kahler-differentials` defines continuous differentials for any
commutative algebra and ideal as compatible families of the ordinary quotient
differentials, with its canonical derivation. It serves the inverse limit in
this item's statement (Curves Tag 0C4D; Algebra Tags 07BK and 00RO). Searches with
LeanSearch, LeanFinder, Mathlib grep, upstream grep, side-source grep, DAG grep,
and `tools/blueprint_refs.py search continuous differentials` found no existing
node or declaration constructing this generic module. The existing completed
Jacobian node defines the finite tensor module, which is the OTHER side of the
comparison and cannot supply this definition. The source's other mentions in
formal-power-series comparison statements are consumers, not definitions.
This new node contains no theorem and no postponed data. Its canonical quotient
transition, compatible-family submodule, carrier abbreviation, and canonical
actual derivation are all listed in `lean.declarations`.

## Second reading by Q31

Author's second pass, not an independent reviewer: reread the original node,
its six statement dependencies, the new node and both finished module texts.
The node specifies a chosen `k`-algebra section; the algebra instance, scalar
tower, and `hσ` express respectively its action, `k`-linearity, and residue
section condition. The independent uniqueness quantifiers for `D'` and `e'`
match the two distinct uniqueness assertions, and the final universal
quantifier includes all completed elements. The tensor order is reversed only
by the canonical symmetry already used by the landed shared carrier. The
residue-field carrier is the localization quotient canonically identified
with `S/p` at a maximal ideal. Neither identification adds a hypothesis.
The new inverse-limit definition uses precisely the quotient differentials,
not the completion of ordinary differentials; identifying those is the
comparison theorem's content. Its indices begin at the first positive power.
No missing clause, stronger assumption, arbitrary comparison map, or data
chosen from an unproved existence assertion was found. Initial elaboration
failures in structural scalar actions were repaired by explicit quotient
algebra types and `IsScalarTower.algebraMap_smul`. The compiler's single line
length warning was fixed by wrapping the statement; no linter was disabled.
