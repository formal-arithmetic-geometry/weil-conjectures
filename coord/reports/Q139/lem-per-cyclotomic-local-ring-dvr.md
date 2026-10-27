## Worker report

Stage 2, Q139, lem-per-cyclotomic-local-ring-dvr, 2026-10-24.

The module `Sheaf.RingTheory.CyclotomicPrimeLocalizations` states
`IsPrimitiveRoot.cyclotomic_prime_localization_isField_or_isDiscreteValuationRing`.
Its only theorem has proof `sorry`. There are no new definitions, new DAG nodes,
dependency repairs, or statement corrections. The accepted NX stage-1 split is
preserved verbatim; only the item's `lean` record changes. The previous worker's
unchanged-item rejection concerned stage 1 and is superseded by this stage-2
assignment (the live queue has stage 2 and the node had no Lean record).

Hypothesis and clause correspondence:

- The integer `N ≥ 1` is `(N : ℕ) (hN : 1 ≤ N)`. Positive integers and positive
  natural numbers describe the same indices; no positive index is omitted.
- The given complex root is `(ζ : ℂ) (hζ : IsPrimitiveRoot ζ N)`.
  Mathlib's structure says `ζ ^ N = 1` and that `ζ ^ j = 1` implies `N ∣ j`.
  For positive N this is equivalent to the node's absence of a smaller positive
  exponent with value one: apply division with remainder to any such exponent.
  Thus the full primitive-root hypothesis is retained even though the proof
  route only needs its power-equals-one clause.
- The actual subring `A = ℤ[1/N, ζ] ⊆ ℂ` is
  `Subring.closure ({(N : ℂ)⁻¹, ζ} : Set ℂ)`. Mathlib defines closure as the
  infimum of subrings containing the given set. Every unital subring contains
  all integers, so no separate integer-image generator is needed. The inverse
  here is the inverse in ℂ, hence precisely 1/N; this is not an abstract
  cyclotomic quotient or an arbitrary algebra with an evaluation map.
- Every prime ideal of that very ring is bound by
  `(p : Ideal (Subring.closure ({(N : ℂ)⁻¹, ζ} : Set ℂ))) [p.IsPrime]`.
  No maximality or nonzero-prime assumption is imposed.
- The localization is exactly `Localization.AtPrime p`.
- The field-or-DVR conclusion is
  `IsField (Localization.AtPrime p) ∨ IsDiscreteValuationRing (Localization.AtPrime p)`.
  `IsField` asserts that the existing ring is a nontrivial commutative field;
  the DVR class asserts a local principal ideal domain with nonzero maximal
  ideal. The automatically inferred domain instance comes from the actual
  subring of ℂ and its prime localization, not from an extra hypothesis.

Statement dependencies read and used:

- `def-weil-pbc-localization-at-prime` records
  `Mathlib.RingTheory.Localization.AtPrime.Basic`, `Localization.AtPrime`.
  Its source docstring identifies this as the quotient localization at the
  prime complement; this exact construction occurs in the conclusion.
  The residue-field and fibre-ring clauses of that dependency are not needed
  for this statement.
- `def-sc-discrete-valuation-ring` is a Mathlib leaf whose `mathlib_match` is
  `IsDiscreteValuationRing` in `Mathlib.RingTheory.DiscreteValuationRing.Basic`.
  I read its class declaration, which extends `IsPrincipalIdealRing` and
  `IsLocalRing` on a domain and requires `maximalIdeal R ≠ ⊥`.

The full eight-step node proof appears in the theorem's docstring: localize ℤ;
use the finite etale binomial algebra; ascend normality; decompose its normal
sections; select the evaluation component using idempotents; kill the kernel
by integral incomparability; apply Dedekind localization at nonzero primes;
handle zero by fraction inversion. All currently recorded project proof modules
and Mathlib proof-dependency modules are imported with plain `import`.
The genuine unstated node `lem-sfb-smooth-normal-ascent` is only a proof
prerequisite, not a notion needed to state this item, and has no recorded module
to import. Its role is named in the proof docstring. No import is omitted to
avoid a cycle.

Searches made with the prescribed msearch.py wrapper (logs in searches.jsonl):

- LeanFinder: “For a primitive Nth root of unity in C, prime localizations of
  Z[1/N,zeta] are fields or discrete valuation rings”. Eight hits, including
  prime/prime-power cyclotomic integral-closure theorems and prime-ideal
  theorems; none treats this actual subring for arbitrary N.
- Loogle: `IsPrimitiveRoot, IsDiscreteValuationRing`. Zero hits.
- Mathlib grep: `cyclotomic.*(Dvr|dvr|localization)|IsPrimitiveRoot.*IsDiscreteValuationRing`.
  Zero hits.
- LeanSearch: “Prime localizations of the subring of complex numbers generated
  by a primitive root of unity and the inverse of its order are fields or
  discrete valuation rings”. Eight hits, including
  `IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain`,
  `IsDedekindDomainDvr.is_dvr_at_nonzero_prime`, and generic local-subring
  constructions. The first requires the Dedekind hypothesis established by
  the item; it is not an exact match. I opened its full signature/docstring.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for `IsPrimitiveRoot`,
  cyclotomic/localization/DVR combinations, and the proposed declaration name;
  `rg` over `lean/WeilConjectures` for the node id. Roots-of-unity, Kummer,
  tame-character, and Tate-module declarations appear, but no exact theorem.
  The proposed full declaration name has no existing match. The expected
  NumberTheory subdirectory does not exist under Sheaf; the subsequent
  searches covered the whole Sheaf tree.
- I read Mathlib's `Subring.closure` definition and `IsPrimitiveRoot` structure
  directly, as well as the recorded localization and DVR declarations.

Source checked: literature/stacks-project/more-algebra.tex,
lemma-Dedekind-etale-extension (Tag 0AP2), with its full proof. Its normal-product
argument is the source of the existing eight-step split. The module preserves
the node's actual coefficient ring and its Expose X provenance.

Edge cases checked mathematically before writing: N=1 forces ζ=1 and gives
A=ℤ; the zero prime gives ℚ and nonzero primes give the usual integer DVRs.
N=2 gives ℤ[1/2]. N=6 is allowed, with no prime-power hypothesis. For arbitrary
N the zero prime is included and is a field, while a nonzero prime has the DVR
alternative. A is always a nonzero domain as a unital subring of ℂ. No root,
prime, or integer-index choice excludes an intended case.

No STATEMENT-DISPUTED finding and no node fault. All binders are explicit,
`autoImplicit` is disabled, and there are no implicit universe parameters
because the node fixes the ambient field ℂ.

Validation: scompile.py compiled this delivered file separately in sandbox
mode and library mode against the published server build (7.5 s and 8.2 s),
with no errors or unexpected warnings.

## Second reading by Q139

I reopened the node and the completed file for a separate self-check; this is
not a claim of an independent second agent's review. The maintainer supplies
the independent review, as this dispatcher's brief specifies.

The binders retain N≥1, a complex primitive Nth root, the specific generated
subring, and an arbitrary prime of that ring. The subring closure includes ℤ
because it is unital; it includes exactly the two further generators 1/N and
ζ, not all complex scalars. Its prime ideal type is not the prime ideal type
of ℂ. The conclusion uses the recorded quotient localization and the recorded
DVR predicate, with the field alternative explicit and the zero prime
unrestricted. No stronger Dedekind, etale, nonzero-prime, or maximal-prime
hypothesis has slipped into the signature. Every proof is still `sorry`.
I checked the N=1 and zero-prime cases again and found no mismatch; no
statement correction was necessary. There are no dependency modules or new
nodes to review, and no preserved sandbox statement existed to repair.
