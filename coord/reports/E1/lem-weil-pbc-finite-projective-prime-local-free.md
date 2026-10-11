## Worker report

The module `Sheaf.RingTheory.FiniteProjectivePrimeLocalFree` states
`Module.exists_localizationAway_equiv_finsupp_of_finite_projective`, with only a `sorry`
proof. No definition, additional node, dependency module, or statement correction is needed.
The original node is unchanged except for `lean`.

Hypothesis and conclusion correspondence:

- A commutative ring A: `{A : Type u} [CommRing A]`.
- An A-module M: `{M : Type v} [AddCommGroup M] [Module A M]`.
- Finite generation: `[Module.Finite A M]`, exactly the dependency's finite-generation class.
- Projectivity: `[Module.Projective A M]`, exactly the dependency's split-surjection class,
  equivalent to the lifting and direct-summand characterizations.
- Every prime ideal p: `(p : Ideal A) [p.IsPrime]`. Universal theorem parameters quantify
  over every ideal and every proof of primality; no maximality hypothesis is imposed.
- There exists f in A outside p: `∃ f : A, f ∉ p ∧ ...`.
- The ring A_f and module M_f: `Localization.Away f` and `LocalizedModule.Away f M`,
  using the canonical scalar structure already defined in Mathlib.
- Some integer r ≥ 0: `∃ r : ℕ`. Natural numbers parameterize precisely the nonnegative
  integers; r is not assumed positive and is allowed to depend on p and f.
- M_f is isomorphic to A_f^{⊕r} as A_f-modules:
  `Nonempty (LocalizedModule.Away f M ≃ₗ[Localization.Away f]
  (Fin r →₀ Localization.Away f))`. Finitely supported functions on `Fin r` are the
  finite direct sum of r copies of A_f. The equivalence is linear over A_f, not merely A.
  `Nonempty` asserts existence of the isomorphism without choosing extra data.

Dependency declarations read and used:

- `def-weil-finitely-generated-module`: `Module.Finite`,
  `Mathlib.RingTheory.Finiteness.Defs`, with its field `(⊤ : Submodule A M).FG`.
- `def-weil-pbc-projective-module`: `Module.Projective`,
  `Mathlib.Algebra.Module.Projective`, with its section of the canonical free-module
  surjection; the source docstring and lifting-property signature were read.
- `def-weil-pbc-module-localization-away`: `LocalizedModule.Away`,
  `Mathlib.Algebra.Module.LocalizedModule.Basic`, the abbreviation for localization
  at `Submonoid.powers f`; its full signature and docstring were read. Canonical maps
  from this dependency are not needed in this statement.

Edge cases checked before writing: the zero module has rank r = 0 and one may take f = 1;
`Fin 0 →₀ A_f` is the zero module. A zero ring has no prime ideals, so the statement is
vacuous without adding `[Nontrivial A]`. Arbitrary nonzero commutative rings, including
rings with nilpotents and any characteristic, are allowed. A nilpotent element cannot
serve as f outside p. There is no global rank or globally free hypothesis. The separate
universes u and v place no same-universe restriction on the ring and module.

Sources checked: the local Stacks checkout is absent on this machine. Read the source
online at https://stacks.math.columbia.edu/tag/00NX, Lemma 10.78.2, (2) ⇒ (3) ⇒ (1) ⇒ (7),
and https://stacks.math.columbia.edu/tag/0GWM, Lemma 10.79.3. They support precisely this
conclusion. The docstring carries all three DAG proof steps and their dependency ids.
No statement fault or STATEMENT-DISPUTED issue was found.

Searches performed with `msearch.py` (full machine records in `searches.jsonl`):

- Lean Finder: "finite projective module over a commutative ring is finite free on a
  principal open neighborhood of every prime ideal". Eight hits, including
  `Module.freeLocus_eq_univ_iff` and
  `Module.FinitePresentation.exists_free_localizedModule_powers`; none has this exact
  finite-projective hypothesis and explicit finite-free conclusion.
- Loogle: `Module.Projective, Module.Free`. Three hits: `Module.Projective.of_free`,
  `Module.Projective.iff_split`, and `Module.Projective.iff_split'`; none is the node.
- Mathlib grep: `exists_free_localizedModule_powers|freeLocus_eq_univ|finitePresentation_of_projective`.
  Nineteen hits supply separate finite-presentation, free-locus, and spreading ingredients.
- LeanSearch: "finite projective module is finite free after localization away from an
  element outside any specified prime ideal". Service unavailable (Internal Server Error).
- Source and project `rg`: `prime-local-free|exists.*free|finite_projective` in
  `WeilConjectures` and `lean/Sheaf`. Source contains
  `Module.exists_free_localizedModule_powers_of_flat` in
  `WeilConjectures.Mathlib.RingTheory.Spectrum.Prime.FreeLocus`: its full signature and
  docstring were read; it assumes finite presentation and flatness, not finite projectivity,
  and returns Free and Finite. The statement requires derived facts and is not identical
  hypothesis by hypothesis. Project `finite_projective_of_localizationAway_free` gives the
  converse cover criterion. No exact declaration was found.
- Source node-id grep: `lem-weil-pbc-finite-projective-prime-local-free`; no hits.
- Exact-name/pattern grep across Mathlib, source, and project:
  `exists_free_localizedModule_powers_of_projective|exists.*Away.*projective|exists.*powers.*projective`;
  no hits. The chosen declaration is new.

Validation: server compilation and delivery dry run are run with the prescribed tools.
The independent second reading is left to the next worker; this report does not claim it.

## Second reading by E1

I independently opened the delivered node and module, all three statement dependency
nodes, and their declarations in the pinned Mathlib. No new definition nodes,
dependency modules, or statement correction are present or needed.

Objects, hypotheses, and conclusion clauses, matched in the node's order:

1. A commutative ring A: `{A : Type u} [CommRing A]`. Exact; Stacks' Algebra
   conventions specify commutative rings with identity and allow the zero ring.
2. An A-module M: `{M : Type v} [AddCommGroup M] [Module A M]`. Exact; this
   is an ordinary unital module with no additional topology or scalar extension.
3. Finite generation: `[Module.Finite A M]`. Exact; the recorded dependency
   `def-weil-finitely-generated-module` is Mathlib's class whose field is
   `(⊤ : Submodule A M).FG`; `Submodule.FG` is the span of a finite set.
   This is finite generation, not finiteness of M's underlying set.
4. Projectivity: `[Module.Projective A M]`. Exact; dependency
   `def-weil-pbc-projective-module` has Mathlib match `Module.Projective`.
   I read its canonical free-module splitting field and
   `Module.Projective.iff_split` and `Module.projective_lifting_property`.
   They give the dependency's direct-summand and lifting notions. No auxiliary
   finite-presentation, flatness, or Noetherian binder has been added.
5. Every prime ideal p of A: `(p : Ideal A) [p.IsPrime]`. Exact; theorem
   parameters quantify universally over ideals with primality, not only maximals.
6. An element f outside p: `∃ f : A, f ∉ p ∧ ...`. Exact; f depends on p,
   without demanding that f be a unit in A or that M itself be free.
7. Localized ring A_f and module M_f: `Localization.Away f` and
   `LocalizedModule.Away f M`. Exact; the latter is the recorded declaration
   of `def-weil-pbc-module-localization-away`, an abbreviation of localization
   at `Submonoid.powers f`. I read the quotient construction, its fraction
   relation, and scalar action. The canonical localization scalar structure
   supplies the A_f-module, rather than a private replacement or just an A-module.
8. Some integer r ≥ 0: `∃ r : ℕ`. Exact; natural numbers parameterize all
   nonnegative integers, with no positivity requirement or common global rank.
9. M_f is isomorphic as an A_f-module to r copies of A_f:
   `Nonempty (LocalizedModule.Away f M ≃ₗ[Localization.Away f]
   (Fin r →₀ Localization.Away f))`. Exact; finitely supported functions
   on `Fin r` give the finite direct sum. The linear equivalence is over A_f,
   and `Nonempty` asserts existence of an isomorphism. Quantifier order is
   universal A, M, p, then existential f, r and the equivalence.

Source reading: the local Stacks checkout is absent. I read the actual
[algebra.tex](https://raw.githubusercontent.com/stacks/stacks-project/master/algebra.tex)
sections `section-conventions` and `section-finite-projective-modules`, definition
`definition-locally-free`, and lemmas `lemma-finite-projective` and
`lemma-finitely-presented-localization-free`. I also checked the rendered
[00NX](https://stacks.math.columbia.edu/tag/00NX) and
[0GWM](https://stacks.math.columbia.edu/tag/0GWM) statements and proofs.
00NX identifies finite projectivity with finite local freeness on standard opens;
there are no standing domain, nonzero, characteristic, or Noetherian assumptions.
0GWM spreads freeness at a prime for a finitely presented module. The node's
pointwise principal-open conclusion follows exactly from these sources.

Edge cases: for M = 0, r = 0 is permitted and `Fin 0 →₀ A_f` is the zero
module; f = 1 lies outside every prime. The zero ring has no prime ideals,
so its case is vacuous, as is the empty spectrum. There is no covering-index
binder to exclude an empty cover; schemes are not objects of this statement.
Nilpotents and every characteristic are allowed; no nilpotent can lie outside
a prime. Independent universes u and v impose no equality or ordering: the
actual projective class and its splitting characterization support these
universes despite an outdated explanatory sentence in its module header.
The finite direct sum lives in the ring universe and may be linearly equivalent
to a module in another universe. Every variable and universe is explicitly bound.

Independent searches (different wording from the worker; machine queries recorded
in searches.jsonl):

- Lean Finder: "a finitely generated projective module admits a basis after
  inverting some element not in a prime". Eight results; read the nearby
  `Module.FinitePresentation.exists_basis_localizedModule_powers` and
  `Module.FinitePresentation.exists_free_localizedModule_powers` signatures.
  Both need finite presentation and an already free localization; neither
  states the finite-projective assertion at every prime.
- Loogle: `LocalizedModule.Away, LinearEquiv`. One result,
  `Module.FinitePresentation.exists_lift_equiv_of_isLocalizedModule`:
  a spreading ingredient for two finitely presented modules, not this statement.
- LeanSearch: "projective finite module locally isomorphic to a finite direct
  sum of a localization ring". Service unavailable (Internal Server Error);
  no mathematical search verdict is inferred from this failure.
- `rg` across pinned Mathlib's Algebra/Module and RingTheory, the full source
  `WeilConjectures`, and the project's `lean/Sheaf`, using
  `exists.*(basis|equiv|free).*projective`, `projective.*(basis|equiv|free)`,
  and `exists.*(localizationAway|localizedModule_powers)`.
  I opened source `Module.exists_free_localizedModule_powers_of_flat`:
  it assumes finite presentation and flatness, so using it here requires
  deriving those hypotheses and converting Free/Finite to an explicit
  finite-rank equivalence. It is a useful ingredient, not an exact statement.
  The project's `Module.finite_projective_of_localizationAway_free` is the
  converse cover criterion. No duplicate of this theorem was found.
- Exact declaration-name lookup in `dag/lean_names_upstream.json` found no
  collision. All notions used already belong to Mathlib and the listed DAG nodes.

Mismatch and repair: there is no statement mismatch. The original proof docstring
said simply to lift the localized basis to M, omitting the denominator-clearing
step necessary for such a lift. I expanded only step 3: multiply the finitely
many basis vectors by a common denominator outside p, which is a unit in A_p;
the resulting basis comes from M and defines a map that is an isomorphism at p.
Then finite presentation spreads that isomorphism. The theorem signature and
node record remain unchanged. All three DAG proof steps and their named
references remain in the docstring. No theorem is proved, no definition is
introduced, and the only proof is the named theorem's `sorry`.

Conventions checked: module/header and declaration source/blueprint docstrings,
namespace `Module` without a Sheaf prefix, imports naming the Mathlib notions
used, and line lengths at most 100. The node's `lean.statement` is verbatim
equal to the signature in the file. Server single-file compilation completed
with exit code 0 and no warnings other than the permitted `sorry` warning.

Delivery dry run: `deliver2.py E1 lem-weil-pbc-finite-projective-prime-local-free --no-push`
printed OK: preflight passed and the module compiled; nothing pushed by the dry run.
