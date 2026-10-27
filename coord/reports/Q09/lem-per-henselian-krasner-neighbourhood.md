## Worker report

The module `Sheaf.FieldTheory.HenselianKrasnerNeighbourhood` states
`FieldTheory.henselian_krasner_neighbourhood`, with one postponed theorem proof and no
new definitions. The item's only changed field is `lean`.

The previous worker ending concerned stage 1, not this stage-2 assignment. The current
node is split and independently reviewed PASS by Q142 on 2026-10-24, but has no Lean
record. The repair note is stage 1, state resolved. The maintenance stage-handoff paragraph
in coord/brief-stage2.md explicitly permits this stage-2 statement work and forbids treating
the inherited stage-1 unchanged-split refusal as a stage-2 blocker. The accepted split,
statement, dependencies, proof and source are preserved.

Hypothesis and conclusion correspondence:

- The field F is `{F : Type u} [Field F]`; N is `{N : Type v} [Field N]`.
  The base embedding is `[Algebra F N]`, with `algebraMap F N`.
- Finiteness is `[FiniteDimensional F N]`. Galois is `[IsGalois F N]`, whose actual
  Mathlib definition consists of `Algebra.IsSeparable F N` and `Normal F N`.
  Separable includes algebraicity; `Normal` says every mapped minimal polynomial splits.
  This renders exactly the node's finite, separable algebraic and normal clauses.
- The totally ordered abelian value group is `{Γ : Type w} [AddCommGroup Γ]
  [LinearOrder Γ] [IsOrderedAddMonoid Γ]`. No Archimedean or rank assumption is made.
  The independent universes u, v, w are explicitly declared.
- The base additive valuation is `vF : AddValuation F (WithTop Γ)`; the prolongation is
  `wN : AddValuation N (WithTop Γ)` and `hw : wN.comap (algebraMap F N) = vF`.
  The base valuation is expressed in the ambient value group of the prolongation:
  any prolongation allows this by composing its base value group with the canonical
  inclusion. Surjectivity onto the ambient group is not assumed.
- Nontriviality is `[vF.toValuation.IsNontrivial]`: Mathlib's definition is an element
  with multiplicative value different from zero and one, hence additive value different
  from infinity and zero. This is not the automatically henselian field F itself.
- Henselianity is `[HenselianLocalRing vF.toValuation.integer]`, applied to the actual
  valuation subring. `AddValuation.toValuation` uses `Multiplicative (WithTop Γ)ᵒᵈ`;
  consequently `Valuation.integer`, defined by multiplicative value at most one,
  is exactly the subring with additive value at least zero.
- Mathlib's `AddValuation` supplies w(0)=infinity, w(1)=0, the product equality and the
  ultrametric inequality. Over a field its `top_iff` gives finite values on nonzero inputs.
- Alpha is `(α : N)`; beta ranges over all of N in the first conjunct.
  The node's automorphisms are exactly `σ : N ≃ₐ[F] N`. Its exclusion of fixed conjugates
  is `σ α ≠ α`. Its strict inequality is
  `wN (α - σ α) < wN (α - β)`.
- The first conclusion is `α ∈ IntermediateField.adjoin F {β}`, the smallest intermediate
  field containing beta. It is asserted for every beta satisfying all those inequalities.
- The second conjunct provides `∃ U : Set N`. Its `IsOpen` uses `TopologicalSpace.generateFrom`
  on exactly `{B | ∃ a : N, ∃ γ : Γ, B = {x | (γ : WithTop Γ) < wN (x - a)}}`.
  These are precisely the balls prescribed by the node. They cover N and finite
  intersections are refined by smaller balls, so generating a topology from them
  gives the stated basis topology. Using this literal family also covers an ambient
  value group larger than the value image; no cofinality assumption is inserted.
  `α ∈ U` makes it a neighbourhood; `∀ β ∈ U, α ∈ IntermediateField.adjoin F {β}`
  is the containment for every nearby beta.
- The final conjunct `α ∈ Set.range (algebraMap F N) → U = Set.univ` records that U can be
  all of N when alpha is in F. In that case all base automorphisms fix alpha and the
  first conjunct's strict-inequality premise is an empty condition.
- There is no completeness, normed field, discreteness, valuation-rank or characteristic
  restriction anywhere in the signature.

Dependency declarations read and reused:

- def-trf-valuation-ring: `Mathlib.RingTheory.Valuation.ValuationRing`, `ValuationRing`
  and `ValuationRing.TFAE`. The actual subring in the signature is the existing
  `Valuation.integer` from `Mathlib.RingTheory.Valuation.Integers`; it has exactly the
  nonnegative additive-value carrier. No private valuation-ring construction is introduced.
- def-weil-pbc-henselian-terminology: public import
  `WeilConjectures.Mathlib.RingTheory.Henselian`, exposing its recorded
  `HenselianLocalRing` from `Mathlib.RingTheory.Henselian`. Its recorded strictly
  henselian class is not imposed; the node only requires henselianity.
- def-pc-field-extension: `Mathlib.Algebra.Algebra.Defs`, `Algebra`, via the public
  Galois import, with fields specialized exactly as the dependency's record explains.
- def-weil-pbc-separable-algebraic-extension: `Mathlib.FieldTheory.Separable`,
  `Algebra.IsSeparable`, via the public Galois import and `IsGalois.to_isSeparable`.
- Proof dependency lem-weil-pbc-finite-galois-fixed-field uses existing Mathlib
  `IsGalois.mem_range_algebraMap_iff_fixed`, `IsGalois.card_aut_eq_finrank` and
  `AlgEquiv.fintype` through the public Galois import needed by the statement.
- Proof dependency lem-exc-etale-galois-fixed-field-subgroup is the existing
  `InfiniteGalois.fixedField_fixingSubgroup`, imported privately from
  `Mathlib.FieldTheory.Galois.Infinite`.
- Proof dependency lem-per-henselian-finite-extension-topology currently has neither a
  usable Lean record nor Mathlib match. Its module is therefore not imported: the stage-2
  import rule includes proof dependencies that are stated. Its use remains explicitly
  described in the theorem docstring and unchanged DAG proof; this theorem does not
  require that proof theorem to elaborate its own statement.

Source checked: opened the local ILO PDF at PDF page 380, printed p.374, where the dense
henselian valued-field comparison refers to forms of Krasner's lemma and Bourbaki AC VI
§8 exercises 12, 14(a). As in the reviewed DAG, the proof docstring is an agent reconstruction,
not an attribution of a read Bourbaki proof. The current blueprint/latest search for Krasner
finds the complete p-adic application, not another arbitrary-rank statement of this node.

Edge cases checked mathematically against the exact signature:

- N=F: all automorphisms are identity and every element is in every generated field.
- Alpha in F, including alpha=0: no moving conjugate; U=univ satisfies the final clause.
- Alpha=beta: w(alpha-beta)=infinity; every moving-conjugate difference is nonzero and
  has finite value, so the inequality is satisfied and alpha lies in F(alpha).
- Beta in F with alpha outside F: the Krasner inequalities cannot all hold; no false
  unconditional containment is claimed.
- Arbitrary characteristic and rank-two lexicographic ordered value groups satisfy the
  same bound and finite-maximum argument. No real norm is substituted.
- The singleton value group has no nontrivial valuation, so is properly excluded only by
  the source's explicit nontriviality hypothesis, not by an extra typeclass assumption.
- Larger ambient value groups are allowed; the literal ball topology preserves the node's
  convention without identifying it with Mathlib's value-image topology.

Searches (all before writing the theorem):

- msearch.py leanfinder: `Krasner lemma for a henselian field with valuation of arbitrary
  rank and a finite Galois extension`. Eight results include `Field.henselian`,
  `HenselianLocalRing.TFAE` and valuation inertia subgroups; no matching Krasner theorem.
- msearch.py loogle: `AddValuation, HenselianLocalRing`. Zero hits.
- msearch.py grep in RingTheory/Valuation: `Krasner|AddValuation|henselian.*valuation`.
  Fourteen hits locate `AddValuation` and its operations, reused here, but no result.
- rg in lean/WeilConjectures and lean/Sheaf:
  `Krasner|krasner|AddValuation|additive valuation`. Only complete normed/p-adic Krasner
  applications and unrelated additive-value references, not this statement.
- rg of the item id in lean/WeilConjectures: no hits.
- Read `Mathlib.Analysis.Normed.Field.Krasner` in full: `IsKrasner.krasner` requires
  a normed field and an `IsKrasner` assumption, and its available complete-space
  instances add completeness and rank-one norm data. None states this arbitrary-rank result.
- rg for `henselian_krasner_neighbourhood|HenselianKrasnerNeighbourhood` in Mathlib,
  both project roots and dag/lean_names_upstream.json: no collision before delivery.

No statement correction, new node, unusable statement dependency, or disputed statement.
Validation: scompile.py compiles the final module in sandbox and library modes with no
errors or warnings (12.6 s and 2.4 s respectively); every theorem proof is exactly `sorry`.

## Second reading by Q09

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
