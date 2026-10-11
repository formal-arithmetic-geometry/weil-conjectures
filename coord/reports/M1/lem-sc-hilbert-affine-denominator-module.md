## Worker report

The module `Sheaf.RingTheory.HilbertAffineDenominatorModule` states
`Module.hilbert_affine_denominator_module`, with proof `sorry` and no new definitions.
It formalizes the entire affine calculation of Stacks Project Tag 02P2,
Lemma 31.25.5, proof paragraphs after the affine reduction. The local Stacks
checkout is absent on this machine; the source was read at
https://stacks.math.columbia.edu/tag/02P2 .

Hypothesis and clause correspondence:

- A Noetherian commutative ring: `(A : Type u) [CommRing A] [IsNoetherianRing A]`.
- A finite A-module: `(M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M]`.
  Independent universes allow arbitrary ring and module sizes.
- Full support: `hSupport : Module.support A M = Set.univ`, a statement about all
  points of `PrimeSpectrum A`, with support defined through nonzero localized modules.
- Every associated prime is minimal in A: `hAssoc : associatedPrimes A M ⊆ minimalPrimes A`.
  This is containment, not an extra equality assumption.
- Non-zero-divisors a and b: `ha : a ∈ nonZeroDivisors A` and
  `hb : b ∈ nonZeroDivisors A`. No domain or reducedness hypothesis is imposed.
- Total quotient ring q: `Q := Localization (nonZeroDivisors A)`.
- Fraction a/b: `s := IsLocalization.mk' Q a ⟨b, hb⟩`.
- I is exactly the denominator set and is an ideal: the existential `I : Ideal A`
  together with `∀ x, x ∈ I ↔ ∃ c, algebraMap A Q c = s * algebraMap A Q x`.
  Thus the carrier is precisely the prescribed set, not an arbitrary smaller ideal.
  For commutative A the product order agrees with x(a/b).
- Finite generation of I: `I.FG`.
- The submodule (a/b)I of A: existential `J : Ideal A` and
  `∀ c, c ∈ J ↔ ∃ x ∈ I, algebraMap A Q c = s * algebraMap A Q x`.
  This set is an A-submodule of A, equivalently an ideal; the witness records it
  without defining a duplicate notion. Injectivity of A → Q ensures this is
  literally the subset of A representing sI inside q.
- b is a non-zero-divisor on M: `IsSMulRegular M b`.
- M embeds in M_b: `Function.Injective (LocalizedModule.mkLinearMap (Submonoid.powers b) M)`.
- IM: `N := I • (⊤ : Submodule A M)`, the submodule of finite sums of products,
  rather than I tensor M.
- First multiplication map: the canonical inclusion `N.subtype`, and
  `Function.Injective N.subtype`. It maps the actual product submodule into M.
- Second A-linear map: `∃ f : N →ₗ[A] M`, with `∀ z, b • f z = a • (z : M)`.
  Because b is regular on M, this relation uniquely determines f. In M_b it is
  exactly `f(z)/1 = az/b`: equality after localization clears to some power of b,
  and regularity cancels that power. Conversely the displayed relation gives
  the localized equality. Thus f is the source's canonical map, not an arbitrary
  injection. It also enforces the rule on sums, not merely pure generators.
- Injectivity of second map: `Function.Injective f`.
- First cokernel annihilated by I:
  `I ≤ Module.annihilator A (M ⧸ LinearMap.range N.subtype)`.
  The range of inclusion is IM; this is the concrete module cokernel M/IM.
- Second cokernel annihilated by (a/b)I:
  `J ≤ Module.annihilator A (M ⧸ LinearMap.range f)`.
  This is the concrete cokernel M/s(IM). Ideal containment in the annihilator
  expresses annihilation of every quotient element, not just some generators.

Dependency declarations used:

- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing`,
  `Mathlib.RingTheory.Noetherian.Defs`, abbreviation for `IsNoetherian A A`.
- Corrected finite-module citation `def-weil-finitely-generated-module`:
  `Module.Finite`, `Mathlib.RingTheory.Finiteness.Defs`, class asserting that the
  top submodule is finitely generated. Both modules are imported transitively
  by the displayed Mathlib imports.
- Original `def-weil-pbc-module-finite-type-presentation` was read in full,
  including `SheafOfModules.IsFiniteType` (Generators) and
  `SheafOfModules.IsFinitePresentation` (Quasicoherent). Its record defines
  sheaves on ringed spaces, not the module M in this affine statement; this is
  a wrong citation in the item, not a fault of that definition node.
- Other existing Mathlib notions used: `Module.support` (RingTheory.Support),
  `associatedPrimes` (Ideal.AssociatedPrime.Basic), `minimalPrimes`
  (Ideal.MinimalPrime.Basic), `IsSMulRegular` (Regular.IsSMulRegular),
  `IsLocalization.mk'` (Localization.Defs), `LocalizedModule.mkLinearMap`
  (Algebra.Module.LocalizedModule.Basic), ideal scalar multiplication on
  submodules, `Submodule.subtype`, `LinearMap.range`, and `Module.annihilator`.

Edge cases checked before writing: zero ring is allowed (empty spectrum, zero
module, and localization at a submonoid containing zero all remain well typed);
zero module over a nonzero ring fails full support, as it should. Units a and b
are allowed: both I and J are the whole ring, both maps are isomorphisms and the
cokernels vanish. For a=b, the second map is the inclusion and both annihilation
clauses agree. Zero-divisors and nilpotents in A are allowed; only a and b must
be regular. For A=Z, a=2, b=3, I=(3), J=(2), so the two different annihilator
clauses have the intended order. No Nontrivial, domain, characteristic or
faithfulness hypothesis was added. No disputed mathematical claim was found.

Searches (2026-10-11):

- `msearch.py ... leanfinder "finite module full support minimal associated primes affine denominator ideal two injective maps cokernels annihilated"`:
  eight hits including `Module.mem_support_iff_of_finite`,
  `associatedPrimes.finite`, `Module.support_quotient`, and
  `isAssociatedPrime_iff_exists_injective_linearMap`; no packaged denominator lemma.
- `msearch.py ... loogle "IsSMulRegular, Module.Finite"`: five hits concerning
  dimension and regularity, including `IsSMulRegular.subsingleton_linearMap_iff`;
  none give the denominator maps or the two cokernel assertions.
- `msearch.py ... grep "denominator.*ideal|ideal.*denominator|total.*quotient" RingTheory`:
  hits in Algebraic/Denominator define a denominator generator over a principal
  ideal ring for an integral-closure colon ideal; not this theorem.
- `msearch.py ... leansearch "ideal of denominators regular fraction injective maps finite module"`:
  service unavailable, Internal Server Error, recorded as unavailable.
- `rg` of the item ID, denominator and 02P2 in the source `WeilConjectures` and
  project `lean/Sheaf`: hits only unrelated clearing-denominator statements,
  total-quotient constructions, and commentary; no declaration of this lemma.
- `rg` of the proposed full-name suffix in Mathlib, source, project's modules
  and `dag/lean_names_upstream.json`: no collision.
- DAG searches for `Module.Finite` and finite module titles located the existing
  `def-weil-finitely-generated-module`; its complete node and Mathlib signature
  were read. No new definition node or dependency replacement module is needed.

Validation: server single-file compilation via `scompile.py` succeeded in 1.7 s
without errors or warnings. All universes and variables are bound explicitly.

## Statement corrected

Only the definition citation for the finite A-module hypothesis is corrected:
`[def-weil-pbc-module-finite-type-presentation]` is replaced by
`[def-weil-finitely-generated-module]`. The full old statement is preserved
verbatim in the node's `statement_change.old_statement`; every other word of
its statement is unchanged. The former citation defines sheaves on a ringed
space and cannot be applied to M. The latter is exactly the algebraic finite
module notion required by the affine coherent-sheaf reduction in Tag 02P2.
The item's stmt_deps changes accordingly; proof and proof_deps stay unchanged.

All citers were found by searching the item ID in dag/nodes and checking
stmt_deps and proof_deps (the item's own file is excluded):

- `lem-sc-hilbert-difference`: holds true. Its affine step takes the finite
  A-module of sections of a coherent sheaf and applies this exact lemma.
  The mathematical hypothesis is unchanged, so the citation correction
  preserves its use. No citer is edited.

## Second reading by M1

Independent reading of the sandbox node and Lean file, the two corrected
statement dependencies, the original sheaf dependency, and the sole citer.
I first checked the corrected node against the actual Stacks TeX at
https://raw.githubusercontent.com/stacks/stacks-project/master/divisors.tex,
label `lemma-make-maps-regular-section` (Tag 02P2), including the hypotheses
before its proof; I also read https://stacks.math.columbia.edu/tag/02P2.
The local Stacks checkout is absent. The affine reduction trivializes the
invertible sheaf and writes the regular meromorphic section as a/b with both
numerator and denominator regular. Coherence over the affine Noetherian ring
means a finite module; full support and no embedded associated points give
exactly the node's support and associated-prime hypotheses. No global
properness, field, reducedness or nonemptiness belongs in this affine lemma.

Objects, hypotheses and conclusions, independently listed and matched:

| Node item | Lean rendering | Verdict |
| --- | --- | --- |
| Arbitrary Noetherian commutative ring A | `(A : Type u) [CommRing A] [IsNoetherianRing A]` | Exact. |
| Finite A-module M | `(M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M]` | Exact; finite generation, not finiteness of the underlying set. |
| Support equal to Spec(A) | `hSupport : Module.support A M = Set.univ` | Exact; all prime localizations are nonzero. |
| Each associated prime is a minimal prime of A | `hAssoc : associatedPrimes A M ⊆ minimalPrimes A` | Exact containment; no added equality hypothesis. |
| Regular elements a and b | `(a b : A)` and `ha`, `hb` in `nonZeroDivisors A` | Exact, including rings with zero divisors. |
| q is the total quotient ring | `let Q := Localization (nonZeroDivisors A)` | Exact canonical localization; no fraction-field assumption. |
| Fraction a/b | `let s : Q := IsLocalization.mk' Q a ⟨b, hb⟩` | Exact with the given denominator. |
| I consists of precisely those x with sx in A | First membership biconditional for `I : Ideal A` | Exact; algebraMap into Q is injective, so existence of c expresses membership in the embedded A. Commutativity permits the product order used. |
| I is an ideal and finitely generated | Ideal witness and `I.FG` | Exact; not merely a generating subset. |
| The submodule sI inside A | `J : Ideal A` with its membership biconditional | Exact; this submodule is automatically an ideal since s is a scalar in Q. No extra closure assertion beyond the source's submodule. |
| Actual product IM and its multiplication map to M | `N := I • (⊤ : Submodule A M)` and `N.subtype` | Exact product submodule of finite sums, not a tensor product; multiplication map is inclusion. |
| First map injective | `Function.Injective N.subtype` | Exact. |
| b regular on M, allowing M inside M_b | `IsSMulRegular M b` and injectivity of `LocalizedModule.mkLinearMap (Submonoid.powers b) M` | Exact explicit facts in the source's map construction, not extra hypotheses. |
| Canonical A-linear fraction map IM to M | `∃ f : N →ₗ[A] M`, `∀ z, b • f z = a • (z : M)` | Exact: in M_b this is f(z)/1=az/b. Conversely localization equality clears by a power of b, which cancels by regularity. Regularity also makes f unique, so the existential does not permit arbitrary maps. |
| Second map injective | `Function.Injective f` | Exact. |
| First cokernel killed by I | `I ≤ Module.annihilator A (M ⧸ LinearMap.range N.subtype)` | Exact quotient M/IM and annihilation of every element. |
| Second cokernel killed by sI | `J ≤ Module.annihilator A (M ⧸ LinearMap.range f)` | Exact quotient M/s(IM), with the correct second ideal. |

The hypotheses precede both ideal witnesses and the map witness. Membership
biconditionals determine I and J completely; hence their existential packaging
does not change the quantifier meaning. The inclusion is already A-linear;
the type of f states A-linearity explicitly. There is no conclusion missing
and no strengthening of the mathematical statement.

Dependency signatures were checked in Mathlib itself. `IsNoetherianRing R`
is `IsNoetherian R R` and `isNoetherianRing_iff_ideal_fg` gives precisely the
node definition. `Module.Finite` has field `(⊤ : Submodule R M).FG`, precisely
the corrected dependency. The discarded dependency's
`SheafOfModules.IsFiniteType` and `SheafOfModules.IsFinitePresentation` take
sheaves, confirming that the recorded citation correction is necessary and
changes no mathematics. `Module.support` uses `Nontrivial` prime-localized
modules. I checked the subtle radical in Mathlib's `associatedPrimes`:
`Submodule.isAssociatedPrime_iff [IsNoetherianRing R]` identifies this with
the usual prime annihilator of an element, so it is the source's associated
prime notion here. `minimalPrimes` means primes minimal above the zero ideal.
`IsSMulRegular` is injectivity of scalar multiplication, and
`LocalizedModule.mkLinearMap` is m mapped to m/1. Ideal scalar multiplication
on submodules is the standard product (`Submodule.smul_eq_map₂`). All are
existing notions; this delivery has no new nodes, dependency modules or
private definitions to audit.

Correction/citers: the old statement in `statement_change` is byte-for-byte
the repository statement. The new statement replaces only the finite-module
citation. An independent search of every DAG node found exactly one citer,
`lem-sc-hilbert-difference`, not two. I read its statement and both proof
steps citing this item: the first needs the two canonical affine injections
and annihilation facts; the second needs finite generation of I. They remain
valid under the corrected citation, so its recorded `holds: true` is correct.
No citer is missing and none is edited.

Edge cases: the zero ring is allowed, with empty prime spectrum and necessarily
zero modules; localization and all quotients remain valid. The zero module
over a nonzero ring fails full support, just as in the source. No finite
index set or positive number of generators is selected: zero generators and
zero submodules are covered. There is no n in the statement, so n=0 imposes
no boundary condition. Units a,b, and a=b give the expected whole denominator
ideal; a=b yields the identity scalar and inclusion. For A=Z, a=2, b=3 one
gets I=(3), J=(2), verifying the order of the cokernel annihilators. Nilpotent
and nonreduced rings are admitted, and no characteristic is restricted.
Independent universes u,v are explicitly declared and all variables bound;
no Nontrivial, faithful-module or equal-universe instance was added.

Independent searches, using different words from the worker (2026-10-11):

- LeanFinder via `msearch.py`: `fraction multiplication denominator submodule
  cokernel annihilator`. Eight hits, including
  `FractionalIdeal.den_mul_self_eq_num` and localization multiplication and
  common-denominator lemmas. These concern fractional-ideal presentations or
  localization operations, not the two maps of this statement; no exact match.
- Loogle via `msearch.py`: `IsLocalization.mk', LinearMap`. One hit,
  `IsLocalizedModule.mk'_smul_mk'`, a scalar-action identity in localization,
  not this module lemma. An earlier incorrectly escaped query was rejected
  as an unknown constant and was rerun correctly; it is not negative evidence.
- LeanSearch via `msearch.py`: `An ideal of a commutative ring acts on a finite
  module by a regular fraction with two injective maps whose quotients have
  specified annihilators`. Service unavailable (Internal Server Error), not
  counted as a successful search or a negative match.
- `rg` over Mathlib/RingTheory, source WeilConjectures, project lean/Sheaf and
  the upstream name index for `denominators`, fraction/injective,
  annihilator/cokernel, Tag 02P2, and the declaration suffix. Results concern
  fractional ideals, clearing denominators and unrelated quotient/localization
  facts. I opened the nearby upstream
  `Scheme.Modules.exists_tensorPowSection_eq_restrict`: it is extension of
  a section after multiplying by a power on a quasi-compact separated scheme,
  not this affine denominator lemma. No matching statement or name collision.

Mismatch/changes: no mathematical or Lean mismatch was found. I retained the
worker's correct module and node verbatim and appended this independent
reading to the report. The module header, source docstrings, blueprint ID,
all five natural-language proof steps, topic/namespace and 100-character
line convention were checked. The only theorem proof is `sorry`; there are
no definitions with postponed data and no proved additions. Exact string
comparison confirms `lean.statement` equals the file's full signature.
Server compilation with `scompile.py` succeeded in 1.6 seconds, exit code 0,
with no warnings or errors.
