## Worker report

The module `Sheaf.AlgebraicGeometry.AffineFiniteModuleFreeLocus` states
`Module.finite_free_at_primes_localized_cover`. It formalizes the affine criterion
from Stacks Tag 0GWM: for a Noetherian commutative ring `A` and finite `A`-module
`M`, if every prime localization `LocalizedModule p.primeCompl M` is free over
`Localization.AtPrime p`, then finitely many elements generate the unit ideal and
all corresponding localizations are finite free. The sheaf formulation in the
node is the associated principal-open module-sheaf interpretation, documented in
the theorem docstring via Mathlib's tilde construction.

Hypotheses and clauses are rendered as follows. `A : Type u` with
`[CommRing A] [IsNoetherianRing A]` gives the Noetherian ring. `M : Type v` with
`[AddCommGroup M] [Module A M] [Module.Finite A M]` gives a finite module. The
pointwise hypothesis is `∀ (p : Ideal A) (_hp : p.IsPrime), Module.Free
(Localization.AtPrime p) (LocalizedModule p.primeCompl M)`. The conclusion uses
`∃ (n : ℕ) (f : Fin n → A)` for finitely many elements,
`Ideal.span (Set.range f) = ⊤` for generation of the unit ideal, and for every
`i : Fin n` the conjunction of `Module.Free (Localization.Away (f i))
(LocalizedModule.Away (f i) M)` and the corresponding `Module.Finite` proposition.
`LocalizedModule.Away` is Mathlib's localization at powers of the element.

Dependencies used are Mathlib's `Module.Free`, `Module.Finite`,
`IsNoetherianRing`, `LocalizedModule`, and `Localization.AtPrime`/`Away`.
The DAG leaves `def-pc-scheme`, `def-weil-finitely-generated-module`,
`def-weil-pbc-free-module`, `def-weil-pbc-noetherian-ring`, and
`lem-weil-pbc-spec-module-tilde-sections` are represented by those Mathlib notions
and the module-sheaf interpretation; no private duplicate definition is introduced.

Edge cases checked: `n = 0` is permitted (in the zero ring the empty range spans
`⊤`); `M = 0` and free finite powers are admitted; arbitrary universes are allowed;
no characteristic, nonemptiness, reducedness, or separatedness is assumed. A
nonfree ideal such as `(x,y)` over `k[x,y]` fails the pointwise hypothesis at its
maximal prime, as expected.

Searches made: `msearch.py ... leanfinder "finite module free at every prime locally
free on affine cover"` found `Module.mem_freeLocus`,
`Module.FinitePresentation.exists_free_localizedModule_powers`, and related free-locus
lemmas, but no exact finite-cover theorem. `msearch.py ... loogle "Module.Free,
LocalizedModule, Ideal.span"` returned no exact hit. `msearch.py ... grep
"freeLocus_eq_univ|exists_free_localizedModule_powers" RingTheory` found only the
localization/free-locus ingredients in Mathlib. `rg` over Mathlib, `WeilConjectures`,
and `lean/Sheaf` found no declaration with this node's statement.

The module compiled cleanly with `scompile.py`; its only proof placeholder is the
required `sorry`. No statement correction or disputed-statement marker is needed.

## Earlier second reading (a previous round; superseded)

I reread the node and module. Every node hypothesis and conclusion clause is
present with the same quantifier order and the same localized modules. The finite
cover is represented by `Fin n`, and unit-ideal generation by `Ideal.span` of its
range. The zero module, empty finite index, and arbitrary universe cases remain
allowed. The associated sheaf equivalence is explained in the docstring and uses
Mathlib's existing tilde/localization dictionary. No mismatch was found.

## Second reading by C1

I opened the item's node and module, all five original statement-dependency nodes,
and their actual Mathlib declarations. I read algebra.tex at
`lemma-finitely-presented-localization-free` (Tag 0GWM), coherent.tex at
`lemma-coherent-Noetherian` (Tag 01XZ), and schemes.tex at the affine module-sheaf
construction and restriction lemmas in the local Stacks source at
`/home/ubuntu/c1-stacks-review/`. The additional definition was read against
modules.tex, `definition-locally-free`, part (2), downloaded to scratchpad, and
against the existing source declaration and the local-generators predicates it uses.
The preceding worker report and earlier reading omit the now-explicit sheaf theorem;
this reading supersedes their assertion that a comment alone covers that clause.

Object, hypothesis, and conclusion inventory and verdicts:

1. A commutative Noetherian ring A: `{A : Type u} [CommRing A]
   [IsNoetherianRing A]`. Exact. The dependency defines Noetherian by finite
   generation of ideals; Mathlib's `IsNoetherianRing A := IsNoetherian A A`
   has exactly this meaning. Stacks' ring convention is commutative with identity.
2. An A-module M: `{M : Type v} [AddCommGroup M] [Module A M]` in the affine
   theorem. Exact; an additive group is part of being a module over a ring.
3. M finite: `[Module.Finite A M]`. Exact; the dependency's recorded declaration
   says that the top submodule is finitely generated, not that the underlying set
   is finite. I read Finiteness/Defs.lean:117-119.
4. Every prime p, with no chosen-prime or maximal-prime restriction:
   `∀ (p : Ideal A) (_hp : p.IsPrime), ...`. Exact. The proof binder supplies
   the prime instance needed by `Localization.AtPrime p`.
5. M_p finite free over A_p: `Module.Free (Localization.AtPrime p)
   (LocalizedModule p.primeCompl M)`. Equivalent in the stated context: finiteness
   of every such localization follows from `[Module.Finite A M]` by the existing
   localization instance (Localization/Finiteness.lean:177). Thus omitting a
   redundant conjunct here adds no cases. `Module.Free` means existence of a
   basis, as the free-module dependency requires (FreeModule/Basic.lean:43-44).
6. Finitely many ring elements, possibly none: `∃ (n : ℕ) (f : Fin n → A)`.
   Exact; no positive-rank or nonempty-cover assumption.
7. These elements generate the unit ideal: `Ideal.span (Set.range f) = ⊤`.
   Exact, equivalent to their basic opens covering Spec A.
8. Every M_f finite free over A_f: `∀ i : Fin n, Module.Free
   (Localization.Away (f i)) (LocalizedModule.Away (f i) M) ∧
   Module.Finite (Localization.Away (f i)) (LocalizedModule.Away (f i) M)`.
   Exact. The chosen elements need not be units or nonzero; their localizations
   are precisely localization at their powers.
9. The equivalent sheaf conclusion: the added declaration
   `AlgebraicGeometry.isFiniteLocallyFree_tilde_of_free_at_primes` has the same
   ring, finite-module, and prime-freeness hypotheses and concludes
   `SheafOfModules.IsFiniteLocallyFree.{u, u, u}
   (tilde (R := CommRingCat.of A) (ModuleCat.of A M))`.
   Exact. `tilde` is precisely the dependency's existing associated sheaf, not
   an unrelated sheaf with isomorphic sections. I read Tilde.lean:150-180,
   its quasi-coherence instance at :465, and the existing predicate at
   WeilConjectures/Mathlib/Algebra/Category/ModuleCat/Sheaf/LocallyFree.lean:156-158.
   Its generator maps are isomorphisms and each generator index is finite;
   no constant rank is required. This explicitly states the node's alternative
   conclusion instead of leaving it in prose. The pair of declarations renders
   the two formulations of the node; the node does not assert an additional
   unrelated biconditional.

Universes and edge cases: the affine theorem retains independent arbitrary `u v`.
The sheaf theorem uses an arbitrary common ambient universe `u`, as required by
Mathlib's `tilde : ModuleCat.{u} R → (Spec R).Modules`; every ring and module can be
placed in a common ambient universe, and the independent-universe affine result
is retained. All universes and variables are explicitly bound. The zero ring is
allowed; it has empty spectrum and can use `n = 0` because its bottom ideal is top.
For a nonzero ring, `n = 0` cannot satisfy unit-ideal generation. The zero module
has the empty basis, and local rank zero is allowed by the sheaf predicate.
An empty scheme presents no covering obstruction. No condition on characteristic,
reducedness, connectedness, field structures, or a globally constant rank is added.
A product of two rings with a module of different ranks on the two components is
covered by the varying-rank predicate. The nonfree ideal (x,y) over k[x,y] fails
the prime-local freeness hypothesis at (x,y), as expected.

Independent searches: LeanFinder query `finite principal open cover free
localizations finitely generated module Noetherian ring` found localization
finiteness criteria, not this free-cover theorem. Loogle query `Module.Free,
Localization.Away` found `Module.Invertible.exists_finset_free_localization` (rank
one hypothesis) and `Module.Free.away_of_finite_of_flat_of_rankAtStalk_constant`
(a local result with different hypotheses); neither is the node's statement.
LeanSearch query `finite locally free sheaf of modules rank allowed to vary`
returned HTTP 500, recorded as unavailable, without a mathematical verdict.
LeanFinder query `sheaf modules finite locally free local generators finite varying
rank` returned the Mathlib local-generator ingredients. The grep service query
`IsFiniteLocallyFree` in `Algebra/Category/ModuleCat/Sheaf` found no Mathlib predicate.
Direct rg of Mathlib, WeilConjectures, and lean/Sheaf found the existing source
predicate at LocallyFree.lean:156, and no exact free-at-every-prime tilde theorem.
I also searched all DAG definition nodes by title and declaration: the morphism
notion and the constant-rank module notion are different; none carries the
varying-rank predicate. No Lean definition was duplicated.

Mismatches repaired: (a) the sheaf conclusion was only a docstring comment, now
an explicit sorry theorem using the dependency's actual tilde construction;
(b) the proof docstring summarized the argument without naming the DAG steps,
now both declarations carry all four steps and their node identifiers;
(c) the varying-rank sheaf predicate lacked a DAG definition reference, now
`def-sc-finite-locally-free-sheaf` references the already existing source class.
Removed the now-unused FreeLocus import. The original affine theorem's signature
and the item's mathematical statement remain unchanged; its lean.statement is
verbatim the signature in the module. No definitions or proofs were introduced.
Both theorem bodies consist solely of `sorry`. Server scompile passed with no
errors or warnings. There are no dependency modules to review.

## New nodes

`def-sc-finite-locally-free-sheaf` records finite local freeness with the finite
rank permitted to vary on an open cover of a scheme. This is Stacks modules.tex,
Definition 17.14.1 (Tag 01C6), part (2), specialized to schemes. It references
`SheafOfModules.IsFiniteLocallyFree` from the existing source module
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`, with
`existing: true` and no Lean file. I checked its signature and body: local
isomorphisms to free sheaves, with finite generator index on each covering member,
are exactly the source notion; sheafification instances are supplied on schemes,
not extra geometric hypotheses. Part (3) of that source instead imposes a fixed
rank and corresponds to `def-amb-finite-locally-free-module`, so that existing DAG
node cannot serve this conclusion. The searches above and the node's three-kind
search record explain why this is a new DAG reference but no new Lean definition.
Its fields follow brief-stage2 section 5, it has no proof, uses the item's chapter
and unit, and its blueprint ancestry is the item's ancestry with the item prepended.
