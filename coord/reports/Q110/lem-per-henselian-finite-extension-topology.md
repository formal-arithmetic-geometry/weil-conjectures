## Worker report

The module `Sheaf.FieldTheory.HenselianFiniteExtensionTopology` states
`Valuation.henselian_finite_extension_topology`, with its proof `sorry`.
There are no new definitions, new nodes, dependency repairs, or statement corrections.
Only the assigned node's `lean` field changes. All six steps of its accepted proof
are included in the declaration docstring for stage 3.

Source read: ILO, *Travaux de Gabber*, XX 4.4, printed p. 374 (PDF page 380),
which invokes forms of Krasner's lemma for dense henselian valued fields and
refers to Bourbaki, Algèbre commutative VI §8, exercises 12 and 14(a).
The latter book is not locally available; this report does not claim to have
read it. This item is the admitted valued-algebraic prerequisite, with the
six-step agent-written reconstruction in its node, rather than a verbatim
lemma printed on that page. The latest blueprint's
`sec-deligne-laumon-a1/sk-p-dl-a1-perverse/lem-per-artin-gabber-affine-curve.proof.md`
and the Q112 strict-completion input boundary were also read. The resolved
stage-1 repair note withdraws the historical Lean attachment; this delivery
writes the current accepted statement anew, without restoring a historical
proof graph.

Hypotheses and clauses, matched individually:

- The fields F and E are `{F : Type u} {E : Type v} [Field F] [Field E]`.
  `[Algebra F E]` supplies the structural field embedding `algebraMap F E`.
  Its injectivity follows from the field domain; no separate embedding or
  an arbitrary auxiliary map is introduced.
- Finite algebraic extension is `[FiniteDimensional F E]`. Over fields this
  is precisely finiteness of the extension degree and implies algebraicity.
  No separability is imposed on the existence or uniqueness assertions.
- The valuation is `(v : Valuation F Γ₀)` with
  `{Γ₀ : Type w} [LinearOrderedCommGroupWithZero Γ₀]`. Mathlib uses
  multiplicative notation, zero as the value of zero, the inequality
  `v (x + y) ≤ max (v x) (v y)`, and the ring condition `v x ≤ 1`.
  Replace the additive ordered value group by its order dual, written
  multiplicatively, and send infinity to zero: these are exactly the
  additive axioms and ring in the node. This is a change of notation, not
  a rank-one or real-valued restriction.
- Nontriviality is `[v.IsNontrivial]`: some value is neither zero nor one.
  On a field this is the node's nontriviality condition.
- Henselianity of the original valuation ring is
  `[HenselianLocalRing v.valuationSubring]`, using the recorded henselian
  terminology and Mathlib's canonical valuation subring.
- The balls and topology in the node are represented by
  `v.subgroups_basis.topology`. Its radii range over nonzero elements of
  `MonoidWithZeroHom.ValueGroup₀ (.ofClass v)`, the actual value group,
  even when the ambient Γ₀ is larger than the image. Its zero balls are
  `v x < γ`; translations give `v (x - a) < γ`. Under the preceding
  order reversal these are exactly the additive balls `v(x-a) > γ`.
- Existence of a prolongation up to the node's equivalence is
  `∃ W : ValuationSubring E, W.comap (algebraMap F E) = v.valuationSubring ∧ ...`.
  The valuation itself is Mathlib's canonical, surjective `W.valuation`,
  whose valuation subring is W. Its restriction has the given valuation
  subring, hence is equivalent to v. Equivalently, the actual value group
  of F embeds as its ordered subgroup in the value group of E, giving
  the usual group identification in a prolongation. Thus existentially
  quantifying W retains all the valuation data up to exactly the
  equivalence stipulated in the node.
- Henselianity of the prolonged ring is `HenselianLocalRing W`.
- Uniqueness up to equivalence is
  `∀ W' : ValuationSubring E, W'.comap (algebraMap F E) = v.valuationSubring → W' = W`.
  Equality here is equality of valuation subrings, exactly as specified.
  Every valuation of E determines such a subring, and every such subring
  carries its canonical valuation, so this does not omit alternate value
  groups or normalizations.
- The induced topology on F is specified by the equality
  `TopologicalSpace.induced (algebraMap F E) W.valuation.subgroups_basis.topology =
  v.subgroups_basis.topology`. This states the entire subspace topology,
  rather than just continuity of the embedding.
- The last clause starts with `Algebra.IsSeparable F E →`. This recorded
  predicate says every element's minimal polynomial is separable, that
  is, coprime to its derivative. Finiteness has already supplied algebraicity.
- Every competing valuation topology is represented by
  `∀ T : ValuationSubring E`. No prolongation-ring equality and no
  nontriviality hypothesis on T is imposed. The sole condition is that
  `TopologicalSpace.induced (algebraMap F E) T.valuation.subgroups_basis.topology`
  equals `v.subgroups_basis.topology`. Every valuation topology is
  represented, because the canonical surjective valuation of its
  valuation subring is equivalent to it and has the same actual-value
  balls. The conclusion is precisely equality of the two topologies on E,
  `T.valuation.subgroups_basis.topology = W.valuation.subgroups_basis.topology`.
  It does not assert that T = W.
- No completeness, rank-one, discreteness, characteristic, or Noetherian
  hypothesis occurs. The field and ambient value-group universes u, v, w
  are explicitly bound and independent. Canonical extension value groups
  are formed from E itself, so there is no existential universe restriction.

Recorded dependency declarations read and used:

- `def-trf-valuation-ring`: Mathlib's `ValuationRing` and `ValuationRing.TFAE`,
  in `Mathlib.RingTheory.Valuation.ValuationRing`. The embedded formulation
  is `ValuationSubring` in `Mathlib.RingTheory.Valuation.ValuationSubring`;
  its `valuation`, `valuation_surjective`, `valuationSubring_valuation`,
  `valuation_le_one_iff`, and `comap` give the canonical representation.
  Its instances include `ValuationRing`, `IsLocalRing`, and `IsFractionRing`.
- `def-weil-pbc-henselian-terminology`: `HenselianLocalRing` from
  `Mathlib.RingTheory.Henselian`, publicly imported through the recorded
  `WeilConjectures.Mathlib.RingTheory.Henselian` module. Its full class
  definition and the recorded strictly henselian class were read.
- `def-pc-field-extension`: `Algebra` from `Mathlib.Algebra.Algebra.Defs`.
- `def-weil-pbc-separable-algebraic-extension`: `Algebra.IsSeparable`
  from `Mathlib.FieldTheory.Separable`; its definition and the supporting
  `IsSeparable`, `IsSeparable.isIntegral`, and `Algebra.IsSeparable.isAlgebraic`
  signatures were read.
- The topology infrastructure is Mathlib's `Valuation.subgroups_basis`
  and its `topology`, from `Mathlib.Topology.Algebra.Valued.ValuationTopology`.
  The basis uses the image value group, not all elements of an arbitrarily
  enlarged value codomain.
- The one proof dependency currently carrying a Lean declaration is imported
  with plain `import`: `Sheaf.RingTheory.IntegralComponentHenselianPermanence`,
  declaration `HenselianLocalRing.integral_component_henselian_permanence`.
  Its complete signature and proof docstring were read; the domain C in
  the proof supplies the connectedness/idempotent hypothesis.
- The other four proof dependencies currently have neither a Lean record
  nor a Mathlib match: `lem-per-valuation-normalization-localizations`,
  `lem-per-algebraic-valuation-coarsening-correspondence`,
  `lem-per-valuation-topology-common-coarsening`, and
  `lem-per-henselian-valuation-coarsenings`. Their statements were read,
  and their exact roles are retained in the proof docstring. They are not
  required to type the statement; no duplicate or invented import is supplied.

Edge cases checked before writing:

- E = F: take W = v.valuationSubring; the structural embedding is the
  identity. The final conclusion asserts equal topologies, and allows
  different valuation rings giving that same topology.
- Purely inseparable finite extensions in positive characteristic: the
  first four assertions still apply; the last clause is conditional on
  separability, which is not assumed globally.
- Higher-rank valuations, including a rank-two valuation and a nontrivial
  rank-one coarsening inducing the same topology: the competing T is not
  required to equal W, preventing the false stronger conclusion.
- The trivial competing valuation T = top is included in the quantifier.
  Its topology is discrete and cannot restrict to the nontrivial
  v-topology in a finite algebraic extension. Thus it is excluded by the
  actual induced-topology condition, not by an added hypothesis.
- No ambient-surjectivity or cofinality hypothesis is accidentally imposed:
  Mathlib's basis uses the actual value group, and `W.valuation` is
  canonically surjective. F and E are arbitrary universes, and no fixed
  codomain universe for all competing valuations is needed.
- Fields are nonzero by their class; the impossible zero-field case is not
  an omitted extension case. A finite field cannot carry the required
  nontrivial valuation, correctly leaving the hypotheses unsatisfied there.

Searches actually performed:

1. `msearch.py`, leanfinder:
   "A nontrivial henselian valuation extends uniquely up to equivalence to a finite field extension and its topology is the unique valuation topology extending the base topology".
   Eight hits, including `IsNonarchimedeanLocalField`, `Field.henselian`,
   `Valued.extension_extends`, `Valued.completable`,
   `IsNonarchimedeanLocalField.toIsValuativeTopology`,
   `IsNonarchimedeanLocalField.instIsRankLeOne`, `Tilt.instField`, and
   `Valued.extensionValuation`. None states the assigned assertion.
   The completion declarations extend to a completion; local-field
   declarations impose rank/local-compactness hypotheses; `Field.henselian`
   concerns a field as a ring, not its valuation subring.
2. `msearch.py`, loogle: `ValuationSubring, HenselianLocalRing`.
   Successful search with zero hits.
3. `msearch.py`, grep: `henselian|[Uu]nique`, subdirectory
   `RingTheory/Valuation`. Six hits: `Integral.lean`, `ValuationRing.lean`,
   `LocalSubring.lean`, and `Discrete/Basic.lean`; no matching theorem.
4. `msearch.py`, leansearch:
   "A henselian valuation ring has a unique extension to a finite algebraic field extension and the extension is henselian".
   Eight hits, including `HenselianLocalRing.TFAE`, `HenselianLocalRing`,
   `HenselianRing`, `Valuation.HasExtension.ofComapInteger`,
   `instHenselianRingMaximalIdeal`, `HenselianLocalRing.casesOn`,
   `HenselianRing.is_henselian`, and `Valuation.HasExtension.mk`.
   Henselian definitions, criteria, and extension-definition interfaces do
   not state existence, uniqueness, or the topology assertion.
   `Mathlib.RingTheory.Valuation.Extension` was read: `HasExtension`
   identifies equivalence of the restriction, and `ofComapInteger`
   confirms the equality-of-subrings rendering of prolongation.
5. Ripgrep over the project's `WeilConjectures/` and `Sheaf/` sources for
   `henselian_finite_extension_topology`, the exact node id, valuation/topology,
   and henselian/valuation combinations; also the upstream-name index.
   No declaration of the assigned statement was found. Henselian DVR
   extension results are discrete specializations; other hits concern
   coefficient-field topology or cohomology, not this arbitrary-rank result.
6. Read Mathlib's valuation-subring, valuation-topology, valuation-extension,
   henselian, algebra, separability, and local-field source declarations.
   These give all required notions, so no new notion or dependency
   interface is needed.

No statement is disputed and no source/node correction was needed.

Validation: the prescribed `scompile.py` compiled the sandbox and module
successfully, with no errors or warnings. Delivery preflight and the per-file
compile are run by the prescribed `deliver2.py` dry run and delivery.

## Second reading by Q110

This section replaces the earlier note that no second reading took place. It is
the maintainer reviewer's independent clause-by-clause reading of the delivered
statement `Valuation.henselian_finite_extension_topology`; the Lean is unchanged.

| Node clause | Lean | Verdict |
|---|---|---|
| F a field, E/F a finite algebraic extension [def-pc-field-extension] | `[Field F] [Field E] [Algebra F E] [FiniteDimensional F E]` | exact (finite over a field implies algebraic) |
| v : F → Γ ∪ {∞} with the additive axioms; Γ = v(F^×) | `(v : Valuation F Γ₀)`, `[LinearOrderedCommGroupWithZero Γ₀]` | exact up to the multiplicative order-reversed convention; Γ₀ may exceed the image, but every clause below uses only the image |
| v nontrivial | `[v.IsNontrivial]` (some value ≠ 0, 1) | exact |
| O_v = {v ≥ 0} henselian [def-weil-pbc-henselian-terminology, def-trf-valuation-ring] | `[HenselianLocalRing v.valuationSubring]` | exact |
| topology with balls v(x−a) > γ, γ ∈ Γ | `v.subgroups_basis.topology`; Mathlib `Valuation.subgroups_basis` (Topology/Algebra/Valued/ValuationTopology.lean:58) indexes radii by units of `ValueGroup₀ (.ofClass v)` | exact: radii in the actual value group |
| a prolongation of v to E exists | `∃ W : ValuationSubring E, W.comap (algebraMap F E) = v.valuationSubring` | exact up to the node's equivalence (= equality of valuation subrings); `W.valuation` is the canonical valuation with ring W |
| unique up to equivalence | `∀ W', W'.comap … = v.valuationSubring → W' = W` | exact |
| its valuation ring is henselian | `HenselianLocalRing W` | exact |
| prolonged topology induces v-topology on F | `TopologicalSpace.induced (algebraMap F E) W.valuation.subgroups_basis.topology = v.subgroups_basis.topology` | exact (whole subspace topology) |
| if E/F separable [def-weil-pbc-separable-algebraic-extension] | `Algebra.IsSeparable F E →` | exact, conditional on the last clause only |
| every valuation topology on E inducing the v-topology equals the prolonged one | `∀ T : ValuationSubring E, induced … T.valuation… = v… → T.valuation.subgroups_basis.topology = W.valuation.subgroups_basis.topology` | exact: every valuation on E is equivalent to the canonical valuation of its ring, and equivalent valuations have the same topology; equality of topologies only, not T = W |

Edge cases: E = F (W = O_v); purely inseparable E (first four clauses unconditional,
the last one not assumed); T = ⊤ (discrete topology, excluded by the hypothesis since
v is nontrivial); T a dependent valuation of different rank (same topology, T ≠ W,
allowed by the conclusion); finite F (no nontrivial valuation, hypotheses empty);
universes u, v, w independent and all bound.

Mathematics: the six-step proof (integral closure henselian by Stacks 092X; quotient
valuation; cofinality via torsion; common henselian coarsening; uniqueness of lifted
coarsenings over the henselian coarsening; same topology for dependent valuations)
is correct and is carried in the theorem docstring.

Records: only the item's `lean` field changes; `lean.statement` equals the file
signature verbatim; the four stmt_deps are Mathlib/recorded declarations used as
recorded. No new definition, no hollow construction, only `sorry`; module and theorem
docstrings carry ILO XX 4.4 p.374 and `(blueprint: lem-per-henselian-finite-extension-topology)`.
