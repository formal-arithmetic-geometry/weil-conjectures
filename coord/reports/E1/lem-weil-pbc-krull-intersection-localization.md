## Worker report

The module `Sheaf.Algebra.KrullIntersectionLocalization` states the localization
part of Stacks Tag 00IQ (1). It binds a commutative ring `R`, assumes
`[IsNoetherianRing R]`, an ideal `I`, an additive commutative `R`-module `M`
with `[Module.Finite R M]`, and a prime ideal `p` with `I ≤ p`. The local
intersection is rendered as `N : Submodule R M := ⨅ n : ℕ, I ^ n • ⊤`, exactly
`N = ⋂ n≥0 I^n M`. The conclusion gives `f : R` with `f ∉ p` and, for every
`x : N`, a natural number `n` such that `f ^ n • (x : M) = 0`. This is the
annihilator characterization of `N_f = 0` stated in the node.

The dependency notions use their recorded declarations: `IsNoetherianRing`
from `Mathlib.RingTheory.Noetherian.Defs`, `Module.Finite` from
`Mathlib.RingTheory.Finiteness.Defs`, and `LocalizedModule.Away` from
`Mathlib.Algebra.Module.LocalizedModule.Basic`. The latter supplies the
meaning of localization away from `f`; the conclusion uses the node's explicit
equivalent annihilator criterion and no private localization definition.

Edge cases checked: `n = 0` gives the full submodule (`I ^ 0 • ⊤ = ⊤`), the
zero intersection element is handled by exponent `0`, and no nonzero or
properness hypothesis on `M` or `I` is introduced. The universe parameters
`u` and `v` are explicit. A prime ideal is represented by `(p : Ideal R)
[p.IsPrime]`, and containment is exactly `I ≤ p`.

Searches made before writing:

* `msearch.py E1 lem-weil-pbc-krull-intersection-localization leanfinder` for
  “Noetherian ring, finite module, intersection of I^n M vanishes after
  localizing at an element outside a prime containing I”: no exact statement;
  candidates were filtration lemmas.
* `msearch.py ... loogle` for `⨅ i, _ ^ i • (⊤ : Submodule _ _), LocalizedModule`:
  no match.
* `msearch.py ... grep` over Mathlib filtration files: found
  `Ideal.mem_iInf_smul_pow_eq_bot_iff` and Jacobson-radical variants, but no
  localized-away statement.
* `rg` over `WeilConjectures/` and project `lean/Sheaf/`, and grep for the node
  id: no existing project declaration of this statement.

No new nodes, dependency modules, or statement correction were needed.

## Earlier second reading (a previous round; superseded)

The theorem signature was checked against the node clause by clause. The
intersection is the submodule infimum of `I ^ n • ⊤`; the prime containment is
`I ≤ p`; and the output is one element outside `p` together with a power
annihilating each intersection element. No hypothesis or conclusion is added.

## Second reading by E1

Read the sandbox node and module independently, all three statement-dependency
nodes and their Mathlib declarations, and Stacks algebra.tex lines 12230–12315
on the server (local literature sources are not installed). Read the chapter's
Conventions too: rings are commutative with one and include the zero ring.
Tag 00IQ (1) has exactly the node's hypotheses; part (2) is intentionally absent.

Object/hypothesis/conclusion checklist (node order):

- Ring R: `(R : Type u) [CommRing R]`, exactly the source's commutative ring
  with one. `[IsNoetherianRing R]` is the node's Noetherian hypothesis.
  Opened Noetherian/Defs.lean: `IsNoetherianRing R := IsNoetherian R R`,
  whose field says every submodule/ideal is FG. Verdict: exact.
- Ideal I: `(I : Ideal R)`; no finiteness or properness added. Verdict: exact.
- Finite R-module M: `(M : Type v) [AddCommGroup M] [Module R M]
  [Module.Finite R M]`. Finiteness/Defs.lean uses FG of the top submodule,
  precisely finite generation, not finiteness of the underlying set.
  Verdict: exact; no field, torsion-free or faithful-module assumption.
- N = intersection over n >= 0 of I^n M: the local binding
  `let N : Submodule R M := ⨅ n : ℕ, I ^ n • ⊤` uses the ideal action on
  submodules, not elementwise products. `N` is determined by R, I and M.
  Verdict: exact.
- Every prime p containing I: `(p : Ideal R) [p.IsPrime] (hIp : I ≤ p)`.
  Typeclass binders universally quantify the prime proof and add exactly
  primality. Moving this universal binder before the definitional let does
  not change N or the quantifier order relative to f. Verdict: exact.
- There exists one f outside p: `∃ f : R, f ∉ p ∧ ...`, after the binder p.
  This f is shared by all elements of N. Verdict: exact.
- N_f = 0: `∀ x : N, ∃ n : ℕ, f ^ n • (x : M) = 0`, the explicit equivalent
  criterion already written in the node. Opened LocalizedModule/Basic.lean:
  `LocalizedModule.Away f N` is localization at `Submonoid.powers f`,
  `mkLinearMap` sends x to x/1, and `IsLocalizedModule.eq_iff_exists`
  gives exactly the power-annihilator kernel criterion. Every fraction is
  an inverse power times x/1; hence this criterion is equivalent to the
  entire localized module being zero. No new localization notion is defined.
  Verdict: exact; exponents may depend on x, whereas f cannot.
- No clause about the Jacobson-radical case is introduced. Verdict: exact.

Edge cases: n = 0 is included and contributes the top submodule. M = 0 or
N = 0 is allowed (choose f = 1); the zero element is killed with exponent 0.
For I = 0, the n = 1 term gives N = 0. For I = top or the zero ring there
is no prime containing I, so the universal prime statement is vacuous,
exactly as in Stacks. No nontrivial-ring assumption is added. The finite
set of generators may be empty; its product is 1. The intersection's index
set is fixed to all natural numbers, not an arbitrary potentially empty
family. Schemes are not objects of this node; empty schemes are inapplicable.
There is no characteristic restriction. Independent explicit universes u
and v allow arbitrary ring and module sizes; no test-object universe is used.

Independent searches, using other phrasing than the first reader:

- LeanSearch via msearch: “A finite module over a Noetherian ring has I-adic
  intersection zero on a principal neighborhood of any prime containing I”.
  Service returned Internal Server Error; unavailability is recorded in
  searches.jsonl, and no mathematical verdict is drawn from it.
- Loogle via msearch: `"iInf", "smul", "pow"`. Five hits: local-ring,
  torsion-free and Jacobson-radical Krull intersection statements, the
  elementwise membership criterion, and IsHausdorff.iInf_pow_smul.
  Opened Filtration.lean signatures: none gives the shared f outside p.
- LeanFinder via msearch: “The intersection of ideal powers times a finitely
  generated module becomes zero after inverting a scalar outside a prescribed
  prime ideal”. Eight hits, the same Krull intersection variants plus
  Artin–Rees and Hausdorff statements; none states this localization conclusion.
- msearch grep for `intersection|iInf.*pow|exists.*annihil` in
  RingTheory/Filtration.lean, followed by direct rg of that file: the nearby
  `Ideal.mem_iInf_smul_pow_eq_bot_iff` characterizes individual elements;
  `Ideal.iInf_pow_smul_eq_bot_of_le_jacobson` needs I in the Jacobson radical.
  Neither is the node's statement.
- Direct rg on WeilConjectures/, project lean/Sheaf/, and
  dag/lean_names_upstream.json for `krull_intersection_localization`,
  `iInf.*pow.*smul`, `intersection.*powers`, `intersection.*localiz`:
  no existing declaration of this statement. Opened the upstream
  Mathlib/RingTheory/Filtration.lean declaration list: local flatness criteria
  use Krull intersection internally but do not state this lemma. Cartier's
  Hopf-algebra intersection statements concern different objects.

Mismatches repaired: H8, the original proof docstring only summarized the
argument; expanded it to all five node steps with named dependencies and
localization kernel/fraction arguments. H9, added the standard copyright
header and moved the module from Algebra/ to RingTheory/, matching Mathlib
and the source's topic directories; updated lean.module and lean.file.
No mathematical mismatch found and no signature changed. The node's
lean.statement remains verbatim equal to the signature; explicit binders
were checked by eye. No new nodes or dependency modules, no corrected
statement, no hollow definitions, and the only proof is `by sorry`.

Validation: scompile.py on the repaired module compiled cleanly on the
server (1.3 seconds, exit 0, no warnings). All lines are at most 100 characters.
