## Worker report

The module `Sheaf.FieldTheory.HenselianKrasnerNeighbourhood` states
`FieldTheory.henselianKrasnerNeighbourhood`, with its sole proof `by sorry`.
It introduces no definitions. The theorem docstring gives all five proof steps,
including the finite-order argument converting invariance of the valuation ring
into invariance of valuation values. The natural-language node is unchanged;
only its `lean` field is set.

The previous worker stopped because this node had already been split and
maintainer-reviewed for Q11. Reading the current node shows that this is its
stage-1 `reviewed` record, not a `reviewed_lean` record: there is no `lean` field.
That completed split is precisely the prerequisite for the present stage-2
statement. No stage-1 fields have been changed or delivered again.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- A field F and a field extension N/F are `(F : Type u) (N : Type v)` with
  `[Field F] [Field N] [Algebra F N]`. The structure map is `algebraMap F N`.
- The valuation and its topology are `[vF : Valued F Γ]`, with
  `[LinearOrderedCommGroupWithZero Γ]`. The chosen prolongation is
  `[vN : Valued N Γ]`; `h_prolong` says exactly that its restriction along
  `algebraMap F N` is `vF.v`. The common group is the codomain of the
  prolongation, also used for its restriction. No restriction on the rank of
  that ordered group is imposed; `a`, `u`, and `v` are independent universes.
- The nontrivial valuation hypothesis is
  `h_nontrivial : ∃ x : F, x ≠ 0 ∧ vF.v x ≠ 1`. The nonzero restriction
  prevents zero, whose multiplicative valuation is zero, from witnessing
  nontriviality of a trivial valuation.
- The henselian valuation ring is `[HenselianLocalRing vF.v.integer]`.
  `Valuation.integer` is the actual subring `{x | vF.v x ≤ 1}`, hence the
  additive ring `{x | w x ≥ 0}`; it is not henselianity of the field F itself.
  `Valuation.valuationSubring` has this same underlying subring, equipped with
  the valuation-ring property.
- Finiteness is `[FiniteDimensional F N]`. `[IsGalois F N]` consists exactly
  of `Algebra.IsSeparable F N` and `Normal F N`. The former entails algebraicity;
  the latter says every minimal polynomial splits after mapping to N. Thus no
  part of the node's expanded finite-Galois hypothesis is lost.
- Both elements are universally quantified: `∀ α : N` and, in the first
  conjunct, `∀ β : N`. All F-automorphisms are `σ : N ≃ₐ[F] N`, and the
  nonidentity conjugates are selected by `σ α ≠ α`.
- The node's additive inequality
  `w(α - β) > w(α - σ(α))` is
  `vN.v (α - β) < vN.v (α - σ α)`. Multiplicative valuations reverse the
  additive order, put the value of zero at zero rather than infinity, and
  replace minimum by maximum. This is a change of convention, with no norm,
  Archimedean, discreteness or completeness hypothesis.
- The membership conclusion is
  `α ∈ IntermediateField.adjoin F ({β} : Set N)`. Reading its definition
  confirms this is the subfield closure of the union of the image of F and
  `{β}`, exactly the smallest subfield F(β).
- The neighbourhood clause is `∃ U : Set N, IsOpen U ∧ α ∈ U ∧ ...` in
  the valuation topology supplied by `vN`. Its next conjunct says that every
  `β ∈ U` has the same field-membership property. There is no extra inequality
  required of such β and no externally chosen topology.
- The final clause
  `α ∈ Set.range (algebraMap F N) → U = Set.univ`
  expresses that the chosen neighbourhood can be N when α is in F. The
  pointwise Krasner implication remains unconditional on this membership, so
  its empty-automorphism-condition case is also present.
- The sentences specifying the valuation axioms, balls and valuation ring are
  rendered by the existing `Valuation`, `Valued` and `Valuation.integer`, as
  explained in the module docstring. There is no extra hypothesis corresponding
  to the node's explicit absence of completeness and rank restrictions.

Dependency declarations read and used:

- `def-trf-valuation-ring`: its Mathlib match is `ValuationRing` and
  `ValuationRing.TFAE` in `Mathlib.RingTheory.Valuation.ValuationRing`, read at
  lines 62 and 407. The integer subring of a field valuation is precisely
  this ring, also bundled by `Valuation.valuationSubring` in
  `Mathlib.RingTheory.Valuation.ValuationSubring` (line 439). No copy of the
  valuation-ring notion is defined here.
- `def-weil-pbc-henselian-terminology`: the recorded module
  `WeilConjectures.Mathlib.RingTheory.Henselian` is publicly imported.
  Its docstring identifies the local-ring notion with Mathlib's
  `HenselianLocalRing`, whose full signature and simple-root-lifting condition
  were read in `Mathlib.RingTheory.Henselian` (line 108). The dependency's
  additional `HenselianRing` and `IsStrictlyHenselianLocalRing` notions were
  read too; this node only uses its henselian-local-ring notion.
- `def-pc-field-extension`: `Algebra` in `Mathlib.Algebra.Algebra.Defs`,
  read at line 95, is used on the two fields. `IntermediateField.adjoin`
  was read in `Mathlib.FieldTheory.IntermediateField.Adjoin.Defs`, line 34.
- `def-weil-pbc-separable-algebraic-extension`: `Algebra.IsSeparable` in
  `Mathlib.FieldTheory.Separable`, line 549, is the separability component of
  `IsGalois`. Its docstring and algebraicity consequence were read.
  `IsGalois` (`Mathlib.FieldTheory.Galois.Basic`, line 57) and `Normal`
  (`Mathlib.FieldTheory.Normal.Defs`, line 34) were checked as well.

All stated proof dependencies are imported without `public` when not already
needed by the statement: `Sheaf.FieldTheory.HenselianFiniteExtensionTopology`
provides `Valuation.henselian_finite_extension_topology` (only its valuation-ring
uniqueness clause is needed); `Mathlib.FieldTheory.Galois.Infinite` provides
`InfiniteGalois.fixedField_fixingSubgroup`. The publicly imported Galois Basic
module already supplies `IsGalois.mem_range_algebraMap_iff_fixed`,
`IsGalois.card_aut_eq_finrank`, and the finite automorphism-group instance
`AlgEquiv.fintype` from `Mathlib.FieldTheory.Fixed`. Their signatures were read.
No missing or unusable dependency interface required repair.

Edge cases checked before finalizing the statement:

- If α belongs to F, every automorphism fixes it. The first implication has
  an empty inequality condition; F is contained in F(β) for every β. The last
  conjunct permits and requires the chosen U to be the entire space.
- If β = α, its difference value is zero, strictly below every nonzero
  conjugate-difference value, and α belongs to F(α).
- If N = F, all α are in the base field and U = N handles the whole theorem.
  Also α = 0 is included in the base-field case.
- For a ramified quadratic extension of a p-adic field (p odd), the
  nontrivial conjugate supplies the usual strict Krasner bound; its direction
  agrees with the Lean inequality. Equality at the bound is not asserted.
- A rank-two valuation is allowed, and only finitely many nonzero difference
  values need a minimum. No numerical radius, real-valued norm, or supremum
  over an infinite set is used. In positive characteristic the Galois
  hypothesis retains the separability needed for the fixed-field argument.
- A trivially valued field cannot satisfy `h_nontrivial`; the theorem does
  not silently admit it by choosing x = 0. Fields are nontrivial by their
  standard Lean definition.

Source checked: the local ILO PDF, PDF page 380 / printed page 374, Exposé XX
section 4.4. It invokes forms of Krasner's lemma for the dense henselian field
comparison and refers to Bourbaki AC VI §8 exercises 12 and 14(a). It does not
supply this node's detailed proof; the node correctly labels that proof
agent-written. The docstring retains that provenance. Stacks 09EI is not used
as a source for an arbitrary-rank theorem.

Searches made using `msearch.py`, with complete logged records in the sandbox:

- LeanFinder query: `Krasner lemma over henselian valued fields of arbitrary
  valuation rank finite Galois extension neighbourhood`. Eight hits, including
  `Field.henselian`, p-adic `hensels_lemma`, and Krull-topology facts; no match.
- Loogle query: `IsKrasner`. Six hits. Read the actual source signatures of
  `IsKrasner`, `IsKrasner.krasner`, `IsKrasner.of_completeSpace_of_normal`,
  and `IsKrasner.of_completeSpace` in
  `Mathlib.Analysis.Normed.Field.Krasner`. These use a normed field or assume
  `IsKrasner` itself; the available complete-space results add completeness
  and a real-valued norm. None states the arbitrary-rank henselian result.
- Mathlib grep query: `krasner|henselian.*valu|valu.*henselian`. Eight hits,
  all in normed-field Krasner and Dense.lean; no additional candidate.
- LeanSearch query: `Krasner lemma henselian valued field arbitrary ordered
  value group finite Galois extension close elements generate containing field`.
  Eight hits on finite-Galois fields and Krull topology, no valuation assertion.
- `rg -n 'Krasner|krasner|henselianKrasner|henselian.*[Vv]alu|[Vv]alu.*henselian'`
  in upstream `WeilConjectures` and side `lean/Sheaf`: the upstream Padics
  Extension module uses normed-field Krasner; the side finite-extension-topology
  and dense-field-comparison modules provide or use neighbouring results,
  without stating this lemma. `grep -rn` for the exact node id in the upstream
  tree returned no match. Exact-name `rg` in upstream declarations metadata,
  Mathlib, the upstream source, and the side source returned no match.

Validation: `scompile.py Q80 lem-per-henselian-krasner-neighbourhood` compiled
this file individually against the published library and side overlay. The
wrapper compiled its required finite-extension overlay, the sandbox file,
and the library-form file successfully, with no errors or warnings. All
variables and universes are explicit and `autoImplicit` is disabled.

No statement dispute, statement correction, new node, or dependency repair.

## Second reading by Q80

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
