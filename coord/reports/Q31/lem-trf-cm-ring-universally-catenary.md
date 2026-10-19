## Worker report

The module `Sheaf.RingTheory.CohenMacaulayRingUniversallyCatenary` states
`IsUniversallyCatenary.of_local_depth_eq_dimension`. It assumes a commutative
ring `R` with `[IsNoetherianRing R]` and, for every prime ideal `p` (with its
prime instance), identifies the cast of the depth of the local ring
`Localization.AtPrime p` with its `ringKrullDim`. The conclusion is exactly the
existing `IsUniversallyCatenary R` predicate, whose definition includes
Noetherianity and catenarity of every finite-type algebra. The proof is `sorry`
as required at stage 2.

The Lean rendering of each clause is as follows. The commutative ring is
`{R : Type u} [CommRing R]`; Noetherianity is `[IsNoetherianRing R]`.
The universal prime quantifier is `(hCM : ∀ (p : Ideal R) [p.IsPrime], ...)`.
The local ring is `Localization.AtPrime p`, using Mathlib's canonical
localization and local-ring instance. Its depth is
`IsLocalRing.depth (R := Localization.AtPrime p) (Localization.AtPrime p)`;
this is cast from `ℕ∞` to `WithBot ℕ∞` so it can equal the recorded
`ringKrullDim (Localization.AtPrime p)`. The conclusion
`IsUniversallyCatenary R` unfolds to the node's finite-type algebra catenarity
clause, including finite bounds for prime-chain lengths and equality of all
saturated-chain lengths.

Dependency declarations read and used:

- `Sheaf.RingTheory.ExcellentRing`, `IsUniversallyCatenary`.
- `Sheaf.RingTheory.Depth`, `IsLocalRing.depth` and `Ideal.depth`.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`, `Localization.AtPrime`.
- `Mathlib.RingTheory.KrullDimension.Basic`, `ringKrullDim`.
- `Mathlib.RingTheory.Noetherian.Defs`, `IsNoetherianRing`.
- The proof plan also cites the recorded generic nodes
  `Sheaf.RingTheory.MaximalChainLengthOfDepth`/
  `IsLocalRing.maximal_chain_length_eq_of_depth`, the Mathlib prime
  correspondence `IsLocalization.AtPrime.orderIsoOfPrime`, the Mathlib finite
  local Krull-dimension instance `instFiniteRingKrullDimOfIsLocalRing`, and
  `PrimeSpectrum.isClosedEmbedding_comap_of_surjective`; these are imported or
  available through the proof plan where stated. The polynomial
  Cohen–Macaulay input is the separate stage-1 node
  `lem-trf-polynomial-algebra-cm` and has no Lean declaration yet.

Edge cases checked before writing: `p = q` gives the zero-length interval;
`n = 0` in the polynomial reduction is the original ring; fields and DVRs
satisfy the intended local interpretation; an Artinian Cohen–Macaulay ring
with nilpotents is allowed; and the zero ring has no prime ideals, so the
universal prime hypothesis and chain conclusions are vacuous. No reducedness,
domain, finite global dimension, or nonzero-ring hypothesis was added.

Searches made: `msearch.py` leanfinder for “Noetherian Cohen Macaulay ring has
equal lengths of saturated prime chains in finite type algebras” and for the
polynomial/local-depth variants returned only generic dimension,
Noetherianity, and finite-type declarations; no exact theorem. `msearch.py`
loogle for `CohenMacaulay, universally catenary, catenary` and for
`"depth", "Polynomial"` returned no matching declaration (CohenMacaulay was
unknown). `msearch.py` grep for `catenary|Cohen.?Macaulay` and
`CohenMacaulay|IsCohenMacaulay|CM-polynomial|catenary` returned zero Mathlib
hits. `rg` over the project source found no declaration of this theorem; the
only relevant project definitions are `Ideal.depth` and
`IsUniversallyCatenary`. The existing declaration therefore does not exist and
a new statement module is required.

No statement correction or `STATEMENT-DISPUTED` issue was found.

## Second reading by Q31

Independent reading by the maintainer's reviewer (the group's 2026-10-17 stub
"no second reading by a worker" is replaced by this reading). The Worker report
above is unchanged.

Node statement against Stacks algebra.tex Tag 00NM (lemma-CM-ring-catenary,
line 25607; first assertion only) with definition-ring-CM (line 25383: a
Noetherian ring all of whose local rings are Cohen–Macaulay) and 00N7 (local CM:
depth = dim). Clause by clause:

1. Commutative ring R: `{R : Type u} [CommRing R]`. Correct.
2. R Noetherian [def-weil-pbc-noetherian-ring]: `[IsNoetherianRing R]` (the
   recorded Mathlib leaf). Correct.
3. For every prime p: `∀ (p : Ideal R) [p.IsPrime], ...`. Correct quantifier.
4. R_p [def-weil-pbc-localization-at-prime]: `Localization.AtPrime p`, the
   recorded declaration, with Mathlib's local-ring instance. Correct.
5. depth(R_p) [def-weil-pbc-depth]: `IsLocalRing.depth (R := Localization.AtPrime p)
   (Localization.AtPrime p)`, the recorded `Sheaf.RingTheory.Depth` declaration
   (`(maximalIdeal R_p).depth R_p`; `Module.Finite` is `Module.Finite.self`). R_p is
   nonzero, so m·R_p ≠ R_p and the value is the supremum of the lengths of regular
   sequences in m, as in 00LI. Correct.
6. dim(R_p) [def-weil-pbc-krull-dimension-ring]: `ringKrullDim (Localization.AtPrime p)`
   in `WithBot ℕ∞`; the depth is cast `ℕ∞ → WithBot ℕ∞`. The equation is the
   node's depth = dim, with nothing weaker or stronger. Correct.
7. Conclusion, universally catenary [def-exc-excellent-ring]: `IsUniversallyCatenary R`,
   the recorded declaration in `Sheaf.RingTheory.ExcellentRing`. It is Noetherian ∧
   every `Algebra.FiniteType` R-algebra A is `IsCatenaryRing`: for primes p ≤ q, a
   finite bound N on `IsPrimeChain` lengths and equal lengths of all
   `IsSaturatedPrimeChain`s. These are exactly the node's clauses. The
   finite-type algebras are quantified in the same universe u as R. That comes
   from the recorded definition, and it is harmless: every finite-type algebra is
   isomorphic to a quotient of `MvPolynomial (Fin n) R : Type u`.

No extra hypotheses: no domain, reduced, finite-dimension, nonzero or excellence
assumption. Edge cases: R = 0 has no primes, so hCM is vacuous; the conclusion
is also vacuous for chains, and Noetherianity is given. p = q gives the length-0
interval. Artinian rings with nilpotents (depth = dim = 0) are allowed. Fields
and DVRs satisfy hCM.

One definition per notion: there is no Cohen–Macaulay predicate in Mathlib or in
the project's Sheaf/WeilConjectures trees (rg for `Cohen`/`CM` definitions finds
only `IsCohenRing`). The spelled-out depth = ringKrullDim form is the one already
used in `Sheaf/AlgebraicGeometry/PolynomialChartFibreFlatCriterion.lean:109`.
There is no existing declaration of this theorem.

Maintainer gates: the module and theorem docstrings give the source place and
`(blueprint: lem-trf-cm-ring-universally-catenary)`. The theorem docstring follows
node Steps 1–6. The proof is only `sorry`. There are no definitions, so there is
no hollow data. `lean.statement` is verbatim the signature in the file.

Compile: `nt_compile.py --json` (local side overlay), 5.5 s, rc 0, no
diagnostics. An injected-error probe confirmed that the tool reports
diagnostics.

Changes: none to the Lean or the node; only this section was replaced.
