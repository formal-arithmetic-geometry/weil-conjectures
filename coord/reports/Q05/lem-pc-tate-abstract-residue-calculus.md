## Worker report

The module `Sheaf.RingTheory.TateAbstractResidueCalculus` states
`TateResidue.abstract_residue_calculus`, with one named theorem and one `sorry`.
No definitions are added or replaced. The node changes only in `lean`.
The source read was the local Tate PDF, §1, pp. 149–151 (T1–T5 and Propositions 1–2),
and §2, pp. 151–153 (Theorem 1, formula (*), R1–R2).
There is no source error, statement correction, or disputed clause.

Hypothesis and clause correspondence:

- The field is `{k : Type u} [Field k]`. The commutative k-algebra is
  `{C : Type v} [CommRing C] [Algebra k C]`, with no domain, finiteness, or
  faithfulness assumption. The C-module is `{V : Type w} [AddCommGroup V]
  [Module k V] [Module C V] [IsScalarTower k C V]`; the scalar tower states
  the induced k-vector-space structure. The subspace is `A : Submodule k V`.
- Multiplication `m_f` is the existing `TateResidue.act k f`. Its full definition
  in `WeilConjectures.RingTheory.TateResidue.Residue` is
  `DistribSMul.toLinearMap k V f`, with value `f • v`.
- Admissibility is `hA : TateResidue.Admissible C A`. In `Residue.lean`, this is
  `∀ f : C, E A (act k f)`. In `TateIdeals.lean`, `E A T` means
  `(A.map T).AlmostLE A`, where `Submodule.AlmostLE X Y` is
  `∃ U, U.FG ∧ X ≤ Y ⊔ U`. Over a field FG is finite-dimensionality.
  This is exactly finite-dimensionality of `(m_f A + A)/A`: the image of U
  surjects onto that quotient in one direction, and representatives of a finite
  quotient basis give U in the other. No new admissibility predicate is introduced.
- Finite-potence uses the existing `Module.End.IsFinitePotent` from
  `WeilConjectures.RingTheory.TateResidue.FinitePotent`: `∃ n, (range (T^n)).FG`.
  Allowing n=0 gives the same notion as requiring N≥1: if the zero-th image is
  finite-dimensional, so is the first image. The existing `Module.End.tateTrace`
  takes ordinary trace on the least finite-dimensional power image. The full
  signature and docstring of `Module.End.tateTrace_eq_trace_restrict` were read:
  it identifies this value with trace on any finite-dimensional stable U containing
  a power image. This supplies exactly the trace and choice-independence in the setup.
- The actual residue is the existing `TateResidue.res C A`, a
  `KaehlerDifferential k C →ₗ[k] k`. This is constructed from the existing residue
  pairing and the Kähler universal property in `Residue.lean`, not from arbitrary
  choices of a purported residue map.
- A projection is represented by `π : Module.End k V`, `∀ x, π x ∈ A`, and
  `∀ a ∈ A, π a = a`. This is equivalent to the node's k-linear retraction
  `V →ₗ[k] A`: compose a retraction with `A.subtype` in one direction, or
  codomain-restrict π using its range condition in the other.
- The first conjunct quantifies over every k-linear functional r, every such π,
  and every f,g. The expression
  `π * act k f * act k g - act k g * π * act k f`
  is precisely `[π m_f, m_g]`, because multiplication of endomorphisms composes
  with the right factor applied first. It is asserted finite-potent, and r on
  `f • KaehlerDifferential.D k C g` equals its Tate trace.
- The equivalence of that universal projection property with `r = res C A`
  states both existence and uniqueness, and pins the functional to the actual
  upstream residue. Substituting r=`res C A` gives its formula and finite-potence;
  the forward implication identifies every functional satisfying the formula.
  Finite-potence is independent of r, so including it inside the property does
  not strengthen uniqueness. Since the formula holds for all π, projection
  independence is explicit. A projection always exists by the complement node,
  so this property has no vacuous-projection case.
- Pair isomorphism invariance quantifies over every independently sized
  `V' : Type w'`, its compatible C-module structure, `A' : Submodule k V'`, and
  `e : V ≃ₗ[C] V'`. The equation
  `A.map (e.restrictScalars k).toLinearMap = A'` means exactly e(A)=A'.
  Its conclusion is equality of `res C A` and `res C A'`. Admissibility of A'
  follows from this equation and hA, so it is not added as a hypothesis.
- Ambient invariance quantifies over `W : Submodule C V` containing A via
  `A ≤ W.restrictScalars k`. The subspace A inside W is precisely
  `A.comap (W.subtype.restrictScalars k)`. The two actual residue maps are equated.
  No additional admissibility assumption on this restriction is imposed.
- Vanishing for finite A or finite V/A is the disjunction
  `FiniteDimensional k A ∨ FiniteDimensional k (V ⧸ A)` implying `res C A = 0`.
- The local vanishing clause quantifies over all f,g and uses
  `∀ a ∈ A, f • a ∈ A` and `∀ a ∈ A, g • a ∈ A`, concluding
  `res C A (f • KaehlerDifferential.D k C g) = 0`.
- The final clause uses `∀ f : C, ∀ a ∈ A, f • a ∈ A`, the exact condition
  that the k-subspace is a C-submodule, and concludes equality with the zero map.

Recorded statement dependency used: `def-weil-pbc-kahler-differentials` points to
`Mathlib.RingTheory.Kaehler.Basic`, declarations `KaehlerDifferential`,
`KaehlerDifferential.D`, and `KaehlerDifferential.linearMapEquivDerivation`.
Their complete signatures and docstrings were read, including the universal
property. The module is publicly imported. The proof dependency
`lem-trf-vector-subspace-complement` is the Mathlib leaf `Submodule.exists_isCompl`
in `Mathlib.LinearAlgebra.Basis.VectorSpace`; its signature and surrounding
projection construction were read, and its module is imported for the proof.
The trace-calculus and endomorphism-ideal nodes have no recorded Lean bindings
in this checkout. Their actual existing notions and lemmas were read directly
in the upstream `FinitePotent` and `TateIdeals` modules, which are already publicly
imported through `Residue`; no dependency notion needs a replacement interface.
The stage-3 plan in the docstring follows every node proof step, using those
trace and ideal results with their restricted trace additivity hypotheses.

Edge cases checked mathematically: V=0; A=0 and A=V; finite-dimensional A;
finite-dimensional V/A including zero quotient; arbitrary dimensions; independent
universes for k, C, V, and the comparison V'; zero C (forcing V=0); nonfaithful
C-actions; zero f or g and constant g; arbitrary characteristic including 2.
There is no division by 2 or assumption of characteristic zero. For the sign,
V=k((t)), A=k[[t]], f=t⁻¹, g=t makes the indicated commutator the projection
onto the constants, with trace 1, as required for res(t⁻¹ dt).
For W=V the ambient comparison identifies the original pair; for A contained
in a smaller W, comap identifies exactly the same vectors, not their C-span.

Searches actually run:

- msearch.py leanfinder: `Abstract Tate residue on Kahler differentials for
  admissible subspace finite potent trace of projection commutator`: 8 hits,
  including `KaehlerDifferential.D_apply`, `KaehlerDifferential.derivationQuotKerTotal`,
  `Algebra.Extension.toKaehler`, and presentation/cotangent maps. None states
  this theorem.
- msearch.py loogle: `KaehlerDifferential, LinearMap.trace`: 0 hits.
- msearch.py grep: `finite.?potent|tateTrace|TateResidue`: 0 Mathlib hits.
- rg on `lean/WeilConjectures` found the upstream `RingTheory/TateResidue` modules.
  Direct reading of `Residue.lean`, `FinitePotent.lean`, `TateIdeals.lean`, and
  `ResidueProperties.lean` found the actual existing definitions and partial
  results. In particular `res_smul_D_proj` has TWO projected multiplications,
  whereas this item has only the first projected; `res_eq_add_of_exact` does not
  literally state pair isomorphism or ambient-W invariance. There is no exact
  existing declaration for the complete item. Its existing vanishing results
  remain available as ingredients of the single combined theorem.
- grep/rg for this node id in `lean/WeilConjectures` found no binding.
- rg on `lean/Sheaf/RingTheory` and `lean/Sheaf/LinearAlgebra` for
  `TateResidue.(res|Admissible)` and `Module.End.(IsFinitePotent|tateTrace)` found
  the sibling `TateResidue/DVRResidueCalculus.lean`, a specialization to a DVR,
  not this abstract theorem. A broader Sheaf search also found no exact match.
- `dag/lean_names_upstream.json` names the original trace and residue definitions
  under the shared blueprint unit; these definitions were reused, not copied.

Validation: scompile.py compiled the initial statement in both sandbox and library
module modes without diagnostics. The final version additionally binds V' inside
its universal isomorphism clause and explicitly disables auto-implicit variables;
that version is compiled again before delivery. Every compile uses the prescribed
server wrapper and the 60-second limit. No proof was attempted.

## Second reading by Q05

This is the author's second reading, not an independent-agent review: the dispatcher
explicitly forbids starting other agents and supplies the maintainer's independent
review after delivery. I reread the source, node statement, and final signature
side by side. The commutator has exactly one projected factor and the sign agrees
with the Laurent-series test. The universal-functional equivalence gives existence
as well as uniqueness and identifies the already constructed residue. Both
projection conditions are necessary and together express a retraction onto A.
The pair comparison uses a C-linear equivalence but restricts scalars only when
mapping the k-subspace; the ambient comparison uses the C-submodule's actual subtype.
Both vanishing alternatives, the two stable-multiplier clause, and its
C-submodule consequence are present. A review of the first draft moved V' into
the relevant universal clause so other conclusions do not require inference of
an unrelated space; no mathematical hypothesis or conclusion changed. There are
no new nodes or dependency modules to review.
