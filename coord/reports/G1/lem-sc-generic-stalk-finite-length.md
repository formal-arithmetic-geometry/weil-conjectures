## Worker report

The module `Sheaf.RingTheory.LengthOfSupportAtMaximalIdeal` states
`Module.length_eq_nat_of_support_subset_maximalIdeal`, with a single `sorry` proof.
It introduces no definitions and proves nothing. The module and declaration docstrings
name Stacks Tag 00L5 and carry the three-step DAG proof, including every proof-dependency
node used in that proof.

Hypotheses and conclusion, clause by clause:

- A commutative ring R: `(R : Type u) [CommRing R]`.
- R is Noetherian: `[IsNoetherianRing R]`.
- R is local with maximal ideal m: `[IsLocalRing R]`; m is
  `IsLocalRing.maximalIdeal R`, the canonical unique maximal ideal. There is no
  additional choice or assumption on m.
- M is an R-module: `(M : Type v) [AddCommGroup M] [Module R M]`.
- M is finite in the module sense: `[Module.Finite R M]`, not finiteness of its
  underlying set. The old sheaf-finite-type citation is corrected below.
- M is nonzero: `[Nontrivial M]`; for an additive group this is exactly not the zero
  module, since any nonzero element witnesses distinct elements and conversely.
- Support is contained in the singleton maximal ideal:
  `h_support : ∀ p ∈ Module.support R M, p.asIdeal = IsLocalRing.maximalIdeal R`.
  `Module.support` consists of prime-spectrum points at which the canonical
  `LocalizedModule p.asIdeal.primeCompl M` is nontrivial. Equality of prime ideals
  is equality of the corresponding prime-spectrum points, so this universal
  formulation is exactly singleton containment, with no equality-of-support
  hypothesis silently added.
- Finite length and its equivalent positive-natural-number formulation:
  `∃ n : ℕ, 0 < n ∧ Module.length R M = (n : ℕ∞)`. The existential natural
  number expresses finiteness; `0 < n` expresses positivity. By the recorded
  length definition this also asserts that M has finite length; the two textual
  formulations are equivalent, rather than independent extra conclusions.

Dependency declarations read and used:

- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing` in
  `Mathlib.RingTheory.Noetherian.Defs`, read with its docstring and
  `isNoetherianRing_iff_ideal_fg`. It says all ideals are finitely generated.
- Corrected finite-module dependency `def-weil-finitely-generated-module`:
  `Module.Finite` in `Mathlib.RingTheory.Finiteness.Defs`, whose field is
  `(⊤ : Submodule R M).FG`, exactly finitely many module generators.
- `def-weil-pbc-module-localization`: `LocalizedModule` in
  `Mathlib.Algebra.Module.LocalizedModule.Basic`, read with `mk` and `mk_eq`.
  This recorded definition is used through Mathlib's existing `Module.support`
  (`Mathlib.RingTheory.Support`), not copied privately.
- `def-weil-pbc-module-length`: `Module.length` in `Mathlib.RingTheory.Length`,
  read with its docstring, `length_pos_iff` and `length_ne_top_iff`.
- `IsLocalRing` in `Mathlib.RingTheory.LocalRing.Defs` and its canonical
  `maximalIdeal` / `maximalIdeal.isMaximal` in
  `Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic` supply the local-ring objects.
- The original finite-type dependency's full signatures/docstrings were read:
  `SheafOfModules.IsFiniteType` in `Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators`
  and `SheafOfModules.IsFinitePresentation` in the sibling `Quasicoherent` module.
  They take sheaves on ringed sites, and do not typecheck as predicates on the
  ring-module M in this lemma. No duplicate or replacement sheaf notion is written.

Edge cases checked: the zero module is expressly excluded, as required for positivity;
nonzero finite-dimensional vector spaces over a field are included (the maximal ideal
is zero and length is their positive dimension); the residue field over any Noetherian
local ring has length one; any characteristic is allowed. Modules of finite length
may be infinite as sets, and `Module.Finite` does not exclude them. A nonzero finite
module cannot have empty support, so containment has no unintended zero-support case.
A zero ring admits no nonzero unital module and is not local in the stated standard
sense. Independent universes u and v permit arbitrary ring and module sizes.

Searches (all remote searches logged in `searches.jsonl`):

- LeanFinder: `finite module over a Noetherian local ring supported only at the maximal
  ideal has positive finite length`: eight hits including `Module.length_ne_top_iff`,
  `Module.length_ne_top`, support-dimension inequalities and a principal-quotient
  finite-length theorem; none is the support-point theorem.
- LeanSearch: `finite module supported at maximal ideal has finite length`: service
  returned Internal Server Error, recorded unavailable.
- Loogle: `Module.length, Module.support`: zero hits.
- Mathlib grep via msearch: `support.*maximal|length_ne_top|def support|class Finite`
  in RingTheory: length finiteness and support-dimension lemmas, no exact theorem.
- Direct rg of Mathlib, WeilConjectures and lean/Sheaf for
  `support.*(finite|length)|length.*support|isFiniteLength.*support|00L5`: only
  supporting definitions, dimension results and unrelated sheaf/compact-support results;
  no matching theorem. Direct project search for the item id also found no declaration.
- DAG searches found the already-existing `def-weil-finitely-generated-module` Mathlib
  leaf; no new node is needed. The proposed full declaration name was searched in
  Mathlib, WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json, with no hits.

The local Stacks checkout is absent on this machine. The source was opened directly at
[Stacks Tag 00L5](https://stacks.math.columbia.edu/tag/00L5): the lemma assumes a
Noetherian local ring and a nonzero finite ring-module, and characterizes finite length
by support being the singleton maximal ideal. Our node takes its forward implication;
for a nonzero finite module singleton containment implies equality. No mathematical
statement is disputed.

## Statement corrected

The old statement is:

Let $(R,\mathfrak m)$ be a Noetherian local ring [def-weil-pbc-noetherian-ring] and let $M$ be a finite nonzero $R$-module [def-weil-pbc-module-finite-type-presentation] whose support [def-weil-pbc-module-localization] is contained in $\{\mathfrak m\}$. Then $M$ has finite length over $R$; equivalently, $\mathrm{length}_R(M)$ [def-weil-pbc-module-length] is a positive natural number.

The finite-module citation pointed to `def-weil-pbc-module-finite-type-presentation`,
which defines sheaves of finite type/presentation on ringed spaces. Its predicate takes
a `SheafOfModules`, whereas Tag 00L5 and this lemma have an ordinary R-module M; the
recorded predicate cannot be applied to M. Replace only that citation and its matching
stmt_deps entry by `def-weil-finitely-generated-module`, whose Mathlib declaration is
`Module.Finite`. The ring, module, hypotheses and conclusion remain exactly the same.
The source is Stacks Project, Algebra, Lemma 10.62.3, Tag 00L5. No proof or proof_deps
change is forced, and neither is changed.

All citers were found by searching the item id through dag/nodes and checking the
stmt_deps/proof_deps lists. There is exactly one:

- `lem-sc-numerical-polynomial-leading-term`: holds true. Its first proof step applies
  this lemma to a finite nonzero generic stalk, and still obtains the same positive
  finite length. The correction merely points finiteness to its proper definition.

No citer is edited. No new definition node or dependency module is needed.

## Second reading by G1

I reread the corrected node, its Stacks source (Algebra Lemma 10.62.3, Tag 00L5),
and the Lean declaration. The source assumes a Noetherian local commutative ring with
maximal ideal `m` and a nonzero finite module, and states that support equal to
`{m}` implies finite length (indeed, it gives an iff). The node deliberately records
the forward implication using singleton containment; for a nonzero finite module this
is equivalent to the source condition.

The node objects and hypotheses render as follows, in order: `R : Type u` with
`[CommRing R] [IsNoetherianRing R] [IsLocalRing R]`; `M : Type v` with
`[AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]`; and
`h_support : ∀ p ∈ Module.support R M, p.asIdeal = IsLocalRing.maximalIdeal R`.
The last hypothesis is exactly support containment in the singleton maximal ideal,
with the canonical maximal ideal supplied by the local-ring instance. The conclusion
is `∃ n : ℕ, 0 < n ∧ Module.length R M = (n : ℕ∞)`, which says finite and positive
length in the recorded Mathlib length convention. Every binder is explicit and the
independent universes `u` and `v` preserve the source's generality.

Dependency declarations were checked: `IsNoetherianRing`, `Module.Finite`,
`LocalizedModule`/Mathlib `Module.support`, and `Module.length` are the recorded
notions. The former mistaken dependency on the sheaf predicate
`def-weil-pbc-module-finite-type-presentation` has been replaced by the existing
`def-weil-finitely-generated-module` (`Module.Finite`); no private copy or extra
finiteness assumption remains. The module imports only support, length, and the
local maximal-ideal API, and its theorem docstring carries the Tag 00L5 source and
all proof steps with their proof-dependency nodes. It contains only the required
`sorry` proof.

Edge cases checked: `Nontrivial M` excludes the zero module and ensures positivity;
nonzero finite-dimensional vector spaces over a field (maximal ideal zero) satisfy
the statement; the residue field has length one; arbitrary characteristic and
independent ring/module universes are allowed; and finite length does not imply that
the underlying module set is finite. Empty support cannot occur for the nonzero
finite module under these hypotheses.

Searches for an existing exact theorem or declaration in Mathlib, WeilConjectures,
lean/Sheaf, and the upstream name index found no match; LeanFinder and Loogle found
only general length/support lemmas, and LeanSearch was unavailable. Thus this module
is needed. The only mismatch found was the finite-module dependency citation; I
changed the node statement citation and `stmt_deps` to
`def-weil-finitely-generated-module`, recorded the correction in `statement_change`,
and left the mathematical statement, proof steps, and citer
`lem-sc-numerical-polynomial-leading-term` unchanged (its use still holds).
