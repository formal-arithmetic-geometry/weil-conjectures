## Worker report

The new module `Sheaf.RingTheory.LocalTrivializationResidueRank` states
`Module.local_trivialization_residue_rank` with the whole proof `sorry`. It adds
no definitions. The item node changes only in `lean`; its statement, dependencies,
proof plan, source, and other fields are unchanged. No statement dispute or node
fault was found. No repair note exists for this item.

Source read: `literature/stacks-project/algebra.tex`, the proof of
`lemma-locally-free-semi-local-free` (Tag 02M9, lines 19291–19305). The lemma is
the explicit local calculation supporting its first hint about the dimension
of maximal residue modules. The node's proof expands this calculation using
Tags 07JZ and 00DK. The module docstring reproduces all five proof steps.

Hypotheses and objects, in node order:

- A commutative ring `E` is `{E : Type u} [CommRing E]`.
- An arbitrary `E`-module `P` is `(P : Type v) [AddCommGroup P] [Module E P]`.
  The universes `u` and `v` are independent and explicitly declared.
- A maximal ideal is `(q : Ideal E) [q.IsMaximal]`. Its prime complement
  `q.primeCompl` is precisely `S = E ∖ q`, and primality is inferred from maximality.
- The principal-open element and its avoidance hypothesis are `(f : E)` and
  `(hf : f ∉ q)`.
- A nonnegative integer rank is `(r : ℕ)`.
- The trivialization `P_f ≅ E_f^r` is
  `hfree : Nonempty (Module.Basis (Fin r) (Localization.Away f)
  (LocalizedModule.Away f P))`. A basis indexed by `Fin r` is equivalent to the
  stated finite-free isomorphism, including `r = 0`; no basis is required to be
  fixed as additional data. There is no finite-generation assumption on `P`.
- `E_q` and `P_q` are the dependency definitions `Localization.AtPrime q`
  and `LocalizedModule q.primeCompl P`. The residue field `k_q` is `E ⧸ q`.

Conclusions, in node order:

- `P_q ≅ E_q^r` is the first conjunct, the nonemptiness of a basis on `Fin r`
  over `Localization.AtPrime q`.
- The displayed ring identification is the second conjunct: an equivalence
  `(E ⧸ q) ≃+* (Localization.AtPrime q ⧸ Ideal.map
  (algebraMap E (Localization.AtPrime q)) q)`, required for every representative
  `a` to send `[a]` to `[a/1]`. Thus it is the canonical identification, rather
  than an unspecified ring isomorphism. This representative formula determines
  the equivalence uniquely.
- The third conjunct is an `E ⧸ q`-linear equivalence from `P/qP` to `P_q/qP_q`.
  Its representative formula is `∀ p : P, e (Submodule.Quotient.mk p) =
  Submodule.Quotient.mk (LocalizedModule.mkLinearMap q.primeCompl P p)`.
  This specifies exactly `[p] ↦ [p/1]`, and determines the map uniquely.
- The products `qP` and `qP_q` are `q • (⊤ : Submodule E P)` and
  `q • (⊤ : Submodule E (LocalizedModule q.primeCompl P))` respectively.
  The latter is formed after restricting the localized module to `E`; it is
  exactly the finite sums of `a • x`, `a ∈ q`, `x ∈ P_q` appearing in the node.
  It is stable under `E_q`, since multiplication by any localized scalar
  commutes with the `E` action. It therefore equals the usual extended-ideal
  submodule `(q E_q)P_q`; no scalar-localization data is being replaced.
- Both module quotients carry Mathlib's canonical `E/q` action from the
  torsion quotient construction. On representatives it is `[a] • [x] = [a • x]`.
  On the target this is exactly restriction of the `E_q/qE_q` action along
  the preceding ring equivalence, since that equivalence sends `[a]` to `[a/1]`.
  Thus the module equivalence is over the specified ring identification.
- The final two conjuncts are `Module.Finite (E ⧸ q) (P ⧸ q • ⊤)` and
  `Module.finrank (E ⧸ q) (P ⧸ q • ⊤) = r`. These express the node's assertion
  that this vector space has the finite dimension `r`. The finite clause is
  necessary to avoid Mathlib's convention assigning finrank zero to infinite
  dimension; it is part of “has dimension r”, not an additional hypothesis.
  Since `q` is maximal, `Ideal.Quotient.field q` supplies its field structure
  whenever needed in a proof. Neither clause depends on a chosen field instance.

Dependency declarations read and used:

- `Mathlib.Algebra.Module.LocalizedModule.Basic`: `LocalizedModule`,
  `LocalizedModule.Away`, `LocalizedModule.mkLinearMap`; `IsLocalizedModule.lift`
  was also inspected for the dependency's universal-property clause.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime` and
  `Ideal.primeCompl`; `Ideal.ResidueField` and `Ideal.Fiber` were inspected in
  the residue-field modules named by the dependency record, but the item uses
  the quotient by a maximal ideal directly, as its statement specifies.
- `Mathlib.LinearAlgebra.FreeModule.Basic`: `Module.Free` and the underlying
  `Module.Basis`, used with index `Fin r` to express the particular rank.
- `Mathlib.LinearAlgebra.Dimension.Finrank`: `Module.finrank`.
- `Mathlib.Algebra.Module.Torsion.Basic`: the canonical quotient module
  instance on `M ⧸ I • ⊤`, constructed from
  `Module.isTorsionBySet_quotient_ideal_smul` and
  `Module.IsTorsionBySet.module`; no replacement notion is introduced.
- The already-stated proof dependencies are imported privately through
  `Mathlib.LinearAlgebra.TensorProduct.Basis`: `TensorProduct` and
  `Module.Basis.baseChange`/`Module.Basis.baseChange_apply`.
  `Ideal.Quotient.field` (the quotient-field proof dependency) is already
  available from the statement imports. All dependencies are Mathlib leaves.

Edge cases checked before writing and again on rereading:

- `r = 0`: `Fin 0` is empty. The principal localization and the maximal
  localization are zero modules, and the residue module is zero. Explicit
  finite dimensionality excludes an accidental infinite-dimensional rank-zero
  assertion.
- `P = 0` is covered with rank zero. A maximal ideal precludes the zero ring,
  so there is no exceptional trivial-ring rank convention to exclude manually.
- For a field and `q = 0`, the localizations and residue quotients give the
  original rank statement. There is no nonzero characteristic restriction.
- `f = 1` is included; `f = 0` is automatically excluded by `hf`.
  Elements need not be non-zero-divisors, and `E` need not be local or Noetherian.
- `E = ℤ`, `q = (2)`, `P = ℤ ⊕ ℤ/3`, `f = 3`, `r = 1` confirms why global
  freeness and finite flatness must not be assumed: localization removes the
  torsion, and the residue quotient has dimension one. Infinite modules with
  an arbitrary summand killed after inverting `f` are also included.

Searches for an existing statement (all via the prescribed tools or read-only rg):

- `msearch.py ... leanfinder`: “A module free on a principal open containing a
  maximal ideal is free of the same rank at that ideal and its residue quotient
  has that dimension”. Eight hits: `IsLocalRing.finrank_quotient_map` concerns
  algebras; `Module.rankAtStalk_eq_finrank_of_free` assumes global freeness;
  other hits concern finite flat modules or unrelated Krull dimensions. None
  states these three comparisons for an arbitrary module.
- `msearch.py ... loogle`: `IsLocalizedModule, Module.Basis`. Five hits, including
  `Module.Basis.ofIsLocalizedModule` and the finite-presentation neighborhood
  basis theorem; these are tools for the proof, not this combined statement.
- `msearch.py ... grep`: `quotientEquiv|quotient.*[Ee]quiv|basisQuotient` in
  `RingTheory/LocalRing`. Eleven hits: algebra quotients and the tensor fibre
  ring, not the arbitrary-module canonical residue comparison with rank.
- `msearch.py ... leansearch`: “The quotient of a module by a maximal ideal
  times the module is unchanged by localizing at that maximal ideal”. Eight
  hits: ring residue equivalences and localized quotient maps supply partial
  tools; no complete statement including the rank transfer is present.
- `rg` on `lean/WeilConjectures` and `lean/Sheaf` for local trivialization,
  residue rank, basis quotient and quotient/localization patterns found
  related fibre-localization and semilocal basis modules. Read
  `Sheaf.RingTheory.FibreModuleLocalization` and
  `Sheaf.RingTheory.SemilocalSubmoduleBasis`: the former is a different tensor
  fibre and annihilator comparison; the latter is a consumer of this local
  calculation. Neither duplicates the item.
- Exact node-id search in `lean/WeilConjectures` returned no result. Exact
  proposed declaration-name searches in Mathlib and both project roots
  returned no result. All searches are also recorded by msearch in
  `searches.jsonl` in this sandbox.

Validation: `scompile.py NK lem-a1-local-trivialization-residue-rank` compiled
this file in sandbox and library module modes, cleanly (1.8 s and 2.3 s).
No global build or direct source-repository mutation was run.

## Second reading by NK

Separate rereading by the same dispatched worker; the dispatch explicitly
forbids starting other agents. The maintainer's independent review remains
separate from this delivery. I reopened the node and the completed module and
matched every binder and conjunct as above. The ring equivalence includes the
representative formula, so it cannot be an arbitrary residue-field automorphism.
The module equivalence also includes the specified map on every class `[p]`.
The `E/q` target action agrees with the action through the canonical ring
identification; forming `qP_q` after restriction of scalars does not shrink or
enlarge that submodule. No finite-generation, flatness, Noetherian, local-ring,
positive-rank, or domain assumption has slipped into the binders. Finite
-dimensionality is in the conclusion. There are no hidden local notations,
instances, auto-implicit variables, new definitions, dependency repairs or
statement changes. No mismatch was found on this rereading, and no changes
were required after the clean compile.
