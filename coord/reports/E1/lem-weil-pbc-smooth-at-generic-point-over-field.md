## Worker report

The module `Sheaf.RingTheory.SmoothAtGenericPointOverField` states
`Algebra.smoothAtPrime_bot_of_isSeparable_fractionRing`; its only proof is `sorry`.
The node is unchanged except for its `lean` record. No new nodes or dependency modules
are needed, and no statement fault was found.

Source read: Stacks [07ND](https://stacks.math.columbia.edu/tag/07ND), reverse implication,
[00TV](https://stacks.math.columbia.edu/tag/00TV), and
[00TB](https://stacks.math.columbia.edu/tag/00TB). The local literature checkout is absent,
so these official pages were opened. The declaration docstring records the node's two
proof steps and every dependency used in those steps.

Hypothesis and clause correspondence:

- Field `k`: `(k : Type u) [Field k]`.
- Commutative finite type `k`-algebra `S`: `(S : Type v) [CommRing S] [Algebra k S]`
  and `[FiniteType k S]`. Finite type is the standard existence of finitely many algebra
  generators, equivalent to the displayed finite polynomial quotient in the node.
- Domain `S`: `[IsDomain S]`, including nontriviality; hence its zero ideal is prime.
- Fraction field `L`: `(L : Type w) [Field L] [Algebra S L] [IsFractionRing S L]`.
  The last instance says localization at all non-zero-divisors, precisely all nonzero
  elements in this domain; it identifies the specified field with the fraction field.
- The induced extension via `k → S → L`: `[Algebra k L] [IsScalarTower k S L]`.
  The tower is exactly the compatibility of the two structural ring maps, not an
  additional mathematical restriction on the induced extension.
- Separability in the node's general (possibly transcendental) sense:
  `(hsep : IsSeparableExtension k L)`, not algebraic `Algebra.IsSeparable k L`.
- Smoothness at `(0)`: `IsSmoothAtPrime k
  (⟨(⊥ : Ideal S), inferInstance⟩ : PrimeSpectrum S)`.
- The explanatory conclusion, existence of nonzero `g` with `S_g` smooth over `k`,
  is the full definition of that same predicate: `∃ g, g ∉ (⊥ : Ideal S) ∧
  Smooth k (Localization.Away g)`. Membership in the bottom ideal is equality to zero;
  `Localization.Away g` inverts the powers of `g`, with the canonical induced algebra.
  Thus there is no omitted second conclusion or additional conclusion.

Recorded dependency declarations read and used:

- `def-pc-field-extension`: `Mathlib.Algebra.Algebra.Defs`, `Algebra` (full class and
  docstring read, lines 91–100); specialized with both field instances.
- `def-weil-pbc-separable-field-extension`: `Sheaf.FieldTheory.SeparableExtension`,
  `Algebra.IsSeparableExtension` (lines 35–43), whose finitely generated intermediate
  fields must be `Algebra.IsSeparablyGenerated` (lines 24–31).
- `def-weil-pbc-singular-ideal`: `Sheaf.RingTheory.SingularIdeal`,
  `Algebra.IsSmoothAtPrime` (lines 20–26); this recorded subsidiary declaration is the
  notion required here, rather than the node's principal declaration `singularIdeal`.
- `def-weil-pbc-smooth-ring-map`: `Mathlib.RingTheory.Smooth.Basic`, `Algebra.Smooth`
  (lines 535–542), used through the imported `IsSmoothAtPrime` definition.

Also read `IsFractionRing` and its docstring in
`Mathlib.RingTheory.Localization.FractionRing` (lines 44–54), and the existing
`regularLocal_iff_smoothAtPrime` statement as a check of the source proof's criterion.

Edge cases checked: `S = k`, with fraction field `k`, gives the expected smooth zero
prime and allows `g = 1`. Arbitrary transcendence degree finite type domains and
singular domains with separable fraction field are allowed; the conclusion is only
smoothness on a suitable principal neighborhood, not smoothness everywhere. Positive
characteristic and imperfect base fields remain allowed, with general separability
required. The zero ring is excluded exactly by the node's domain hypothesis. The
three object universes `u v w` are bound independently and exclude no fraction field.

Searches actually run:

- `msearch.py leansearch`: `finite type domain separable fraction field smooth at zero
  prime`; service returned Internal Server Error, recorded as unavailable.
- `msearch.py leanfinder`: `domain of finite type over a field with separable fraction
  field is smooth at the generic point`; eight hits, including `Algebra.smoothLocus`,
  `Algebra.IsSmoothAt.exists_notMem_smooth`, and standard-smooth localization results.
  None states this implication from a separable fraction field.
- `msearch.py loogle`: `Algebra.Smooth, IsFractionRing`; zero hits.
- `msearch.py grep`: `generic|IsFractionRing|exists_notMem_smooth` in
  `RingTheory/Smooth`; three hits, notably `IsSmoothAt.exists_notMem_smooth` at
  `Smooth/Locus.lean:150`, an ingredient requiring already-known formal smoothness.
- `rg` of `WeilConjectures` and `lean/Sheaf` for
  `smooth.*generic|generic.*smooth|IsSeparableExtension|IsSmoothAtPrime`: existing
  definitions and related statements (including the regular-local criterion), no
  exact statement of this node.
- Node-id search in `WeilConjectures` and `dag/lean_names_upstream.json`: no match.
- Full proposed declaration-name search in Mathlib, `WeilConjectures`, and
  `lean/Sheaf`: no match.

Validation: `scompile.py E1 lem-weil-pbc-smooth-at-generic-point-over-field` compiled the
module on the server in 1.4 seconds with exit code 0 and no warnings.

## Second reading by E1

I independently opened the sandbox node and module, all four statement-dependency
nodes, and their recorded declarations. No statement mismatch was found; the Lean
module and node record are unchanged. Only this second-reading report was added.
There are no new definition nodes, dependency modules, or statement corrections in
this delivery, so H12/H13 and corrected-statement citer checks do not apply.

Source: the local repository contains only literature lists, not the Stacks checkout.
I read the official pages [07ND](https://stacks.math.columbia.edu/tag/07ND),
[00TV](https://stacks.math.columbia.edu/tag/00TV), and
[00TB](https://stacks.math.columbia.edu/tag/00TB), then downloaded the official
`stacks/stacks-project` algebra.tex to this item's scratchpad and read the actual
source around labels `lemma-smooth-at-generic-point` (38891),
`lemma-separable-smooth` (38740), and `definition-smooth-at-prime` (37511).
The source imposes no perfectness or characteristic restriction. Its injectivity
hypothesis in 07ND is automatic for a unital field map into the nonzero domain S;
its field-base specialization has K = k. No extra global hypothesis is needed.

Object, hypothesis, and conclusion checklist, written from the node and checked
against the Lean:

| Node item | Lean rendering | Verdict |
| --- | --- | --- |
| Field k | `(k : Type u) [Field k]` | Exact. |
| Commutative k-algebra S | `(S : Type v) [CommRing S] [Algebra k S]` | Exact structural map. |
| S is a domain | `[IsDomain S]` | Exact, including nontriviality. |
| S finite type over k, equivalently a finite polynomial quotient | `[FiniteType k S]` | Exact finite algebra generation; no finite-presentation hypothesis added. |
| Fraction field L of S | `(L : Type w) [Field L] [Algebra S L] [IsFractionRing S L]` | Exact localization at non-zero-divisors, which are the nonzero elements of this domain. |
| L/k induced by k → S → L | `[Algebra k L] [IsScalarTower k S L]` | Exact compatibility of maps, not an arbitrary second extension. |
| L/k separable, including transcendental extensions | `(hsep : IsSeparableExtension k L)` | Exact recorded definition, not merely algebraic separability. |
| Smoothness at the zero prime of S | `IsSmoothAtPrime k (⟨(⊥ : Ideal S), inferInstance⟩ : PrimeSpectrum S)` | Exact prime; primality follows from the domain instance. |
| There exists nonzero g with S_g smooth over k | Same conclusion unfolded: `∃ g : S, g ∉ (⊥ : Ideal S) ∧ Smooth k (Localization.Away g)` | Exact entire existential clause, including the induced k-algebra structure; g outside bottom means g ≠ 0. |

Dependency verification: `Algebra` in Mathlib.Algebra.Algebra.Defs is the unital
structural homomorphism with compatible scalar multiplication. In the recorded
SeparableExtension module, `IsSeparableExtension` quantifies over every
`IntermediateField k L` with `F.FG`; `IsSeparablyGenerated` uses a transcendence
basis and algebraic separability over its adjoined intermediate field. These are
exactly the two clauses of the dependency node. In SingularIdeal,
`IsSmoothAtPrime` is literally the existential above. Mathlib's `Algebra.Smooth`
is finite presentation plus formal smoothness, with its documented equivalence
to Stacks' cotangent definition (00T2/00TN). I also read `IsFractionRing` and its
localization definition, and the proof dependency's
`regularLocal_iff_smoothAtPrime` signature: finite type over a field, separable
residue extension, equivalence with regularity of the local ring. The proof
narrative follows that criterion at the zero prime, exactly the node's two steps.
No private copy of any dependency notion occurs.

Edge cases: zero generators (S = k) are allowed, with g = 1; finite algebraic
separable domain extensions and positive transcendence degree are both allowed.
The zero ring/empty spectrum is excluded by precisely the node's domain
hypothesis. Singular domains are allowed: the conclusion only concerns a
principal neighborhood of the generic point. All characteristics and imperfect
fields are allowed; a purely inseparable fraction extension is excluded only by
the stated separability hypothesis. The three universes u, v, w are explicitly
bound and independent, with no quantifier over smaller test objects. There is no
index set or extra dimension restriction in this statement.

Independent searches used different wording from the worker's searches:

- LeanFinder via msearch: `generically smooth finitely generated integral algebra
  separable function field`. Eight hits; I opened
  `Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable` in
  Mathlib/RingTheory/Smooth/Field.lean and
  `Algebra.IsSmoothAt.exists_notMem_smooth` in Smooth/Locus.lean. The former gives
  formal smoothness of a field from an algebraically independent family; the
  latter assumes formal smoothness at the prime already. Neither is this node.
- Loogle via msearch: `IsFractionRing, Algebra.Smooth`. Zero hits.
- LeanSearch via msearch: `A finitely generated domain over a field is smooth on a
  nonempty principal open if its field of fractions is separable`. Service returned
  Internal Server Error; recorded as unavailable, not as evidence of absence.
- msearch grep `fraction|generic|separable` returned broad unrelated hits. Direct
  rg narrowed the search to Mathlib/RingTheory, WeilConjectures, and lean/Sheaf
  using `generically.smooth|smooth.*fraction|fraction.*smooth` and the proposed
  declaration name. Only related proof-docstring references appeared in Sheaf;
  no duplicate statement. The node id also has no hit in WeilConjectures or
  dag/lean_names_upstream.json. I read the recorded related criterion directly.

H5/H6/H8/H9: there are no new definitions or hollow data; the one theorem has
exactly `by sorry`. Both module and declaration docstrings contain the source and
blueprint id; the declaration describes both proof steps and their dependencies.
The namespace, imports, and explicit binders follow the contract, and the node's
lean.statement is verbatim the file signature. No Lean or node repair was needed.

Validation: scompile.py with the absolute sandbox module path compiled on the
server in 1.4 s, exit code 0, with no warnings. An initial invocation using a
repository-relative module path failed to locate the sandbox file; the corrected
absolute-path invocation above succeeded without changing the module.
