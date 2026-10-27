## Worker report

Module: `Sheaf.RingTheory.ParameterRootBoundaryDvrs`. Main declaration:
`Algebra.parameter_root_boundary_dvrs`; companion clause declaration:
`Algebra.parameter_root_boundary_quotients`. Both proofs are `sorry`.
The five data constructions have explicit definitions, with no postponed proof.
No mathematical statement correction is needed. The item cites the already landed definition node
`def-sfb-parameter-root-algebra` for the existing quotient construction.
This packet delivers no new or dependency definition node.

Hypothesis and clause correspondence:

- `R : Type u`, `[CommRing R]`, `[IsRegularLocalRing R]`, and
  `[HenselianLocalRing R]` render the henselian Noetherian regular local base.
  Regular-local includes Noetherianity and locality. No domain hypothesis is added:
  the published `IsRegularLocalRing.isDomain` instance supplies it.
- `t : Fin r → R`, `tail : List R` and
  `ht : IsLocalRing.IsRegularSystemOfParameters (List.ofFn t ++ tail)` render the
  full ordered system of d parameters and its first r entries. Here d is the length
  of this full list, so the definition enforces dimension d and r ≤ d without
  a redundant dimension binder. Conversely every full list and r ≤ d admits this split.
- `n : ℕ` and `hn : 0 < n` render the arbitrary positive root order. There is no
  characteristic, unit, primitive-root or strict-henselian hypothesis.
- `Algebra.pthRootAlgebra n r R t` is exactly the existing quotient
  `MvPolynomial (Fin r) R ⧸ span {X_i^n - C(t_i)}`. Its definition has no primality
  restriction on n. The landed definition node `def-sfb-parameter-root-algebra` is added to stmt_deps.
  The characteristic-p locality theorem is not a statement dependency.
- `parameterRootBoundaryCoordinate` is the class of `X_i`;
  `parameterBaseBoundaryIdeal` and `parameterRootBoundaryIdeal` are `(t_i)` and `(x_i)`.
  All three are explicit constructions using the standard quotient and ideal span.
- The first four conjuncts of `parameter_root_boundary_quotients` state that
  R/(t_i) and B/(x_i) are regular local domains, independently of any inferred
  instances. The two `IsSMulRegular` clauses state that t_i and x_i are nonzerodivisors.
- The containment witness `hc` makes the canonical `Ideal.quotientMap` coefficient
  map well typed. Its injectivity and `RingHom.Finite` state injective finite
  scalar extension. The `Module.Basis` has index `{j : Fin r // j ≠ i} → Fin n`
  and value exactly the product of surviving root classes to their indicated powers.
  Thus it is the finite free monomial basis with all exponents below n; the zero
  exponent vector exists because n > 0 and maps to 1. For r = 1 the index consists
  of the empty function and the displayed product is 1.
- `parameterRootBoundaryPresentation` is literally the surviving-variable quotient
  over R/(t_i). The equivalence `e` is pinned down on every base-ring coefficient
  and every surviving variable, so it is the canonical presentation over R/(t_i),
  expressed as a ring equivalence with its scalar-compatibility equations. This
  avoids silently assuming an arbitrary algebra structure on B/(x_i).
- In `parameter_root_boundary_dvrs` the existential domain proof for B allows
  its fraction field and localized-domain instances to be formed; `hRB` is
  injectivity of the actual original coefficient map.
- For each i the two `.IsPrime` witnesses and equality `hc` state primality and
  q_i contraction = p_i. They are conclusions, not extra assumptions.
- The two `IsDiscreteValuationRing` conclusions refer to the actual
  `Localization.AtPrime` rings. Their maximal ideals equal the principal ideals
  of the displayed localized parameter and root, which is exactly the requested
  uniformizer condition (Mathlib's `irreducible_iff_uniformizer`).
- The tensor/localization equivalence is a ring equivalence fixed on both tensor
  factors: `b ⊗ 1` maps to the localized b, and `1 ⊗ v` maps by the canonical
  `Localization.localRingHom` using contraction `hc`. These equations express
  exactly the canonical V_i-algebra isomorphism without choosing an unrelated map
  or adding an algebra instance as a hypothesis.
- `hj` and `.Finite` give injectivity and finiteness of that same `localRingHom`.
  The fraction-ring equivalences `ev`, `ea` are normalized on R and B.
  `ea.comp (IsFractionRing.map hj) = (IsFractionRing.map hRB).comp ev` states
  precisely that the localized map induces the original canonical K → E.
- The final three equalities give the chain m_V A = (t_i) = (x_i^n) = m_A^n.
  Each scalar and ideal extension uses the canonical localization map.
- Each q_i has `height = 1`; the opening biconditional, quantified over all prime
  ideals Q of B, says exactly that the height-one primes containing the image of
  f = `∏ j, t j` are the q_i. In a domain height one is equivalently nonzero with
  no prime strictly between zero and Q, as in the node.
- If r = 0 there is no i, the product is 1, and no prime contains it. The theorem
  still states the domain and coefficient injection for the no-variable quotient.
  The full parameter list can be empty, so dimension zero is not excluded.

Dependency declarations read and used:

- `WeilConjectures.Mathlib.RingTheory.Henselian`: `HenselianLocalRing`, whose
  definition is in Mathlib.RingTheory.Henselian; no strict-henselian assumption.
- `Mathlib.RingTheory.RegularLocalRing.Defs`: `IsRegularLocalRing`, the ring clause
  retained in def-weil-regular-scheme.mathlib_match. Its recorded scheme wrapper
  `Sheaf.AlgebraicGeometry.IsRegularScheme` was read; this ring-only statement
  does not need the scheme predicate or an additional scheme import.
- `WeilConjectures.RingTheory.IsRegularSystemOfParameters`:
  `IsLocalRing.IsRegularSystemOfParameters` (span = maximal ideal, length = dimension).
- `Mathlib.Algebra.MvPolynomial.Basic` and quotient operations: `MvPolynomial`,
  `MvPolynomial.X`, `MvPolynomial.C`, `Ideal.Quotient.mk`, `Ideal.quotientMap`.
- `WeilConjectures.RingTheory.PthRootAlgebraLocal`: `Algebra.pthRootAlgebra`;
  this is existing data, now carried by `def-sfb-parameter-root-algebra`. The
  characteristic-p locality theorem in that module is not used to state the item.
- `Mathlib.Algebra.Algebra.Defs`: `Algebra`, `algebraMap`, `RingHom.toAlgebra`;
  `Mathlib.RingTheory.Localization.FractionRing`: `FractionRing`, `IsFractionRing.map`.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`,
  `Localization.localRingHom`. `Mathlib.RingTheory.DiscreteValuationRing.Basic`:
  `IsDiscreteValuationRing`, `IsDiscreteValuationRing.irreducible_iff_uniformizer`.

The stated proof dependencies are imported non-publicly: regular-local generators
and quotients, principal-prime localization DVRs, monic quotient freeness,
localization base change, finite-dimensional domain is field, finite algebra
integrality, maximal-ideal contraction, DVR dimension one and primes of localization.
The local-ring unit criterion is already available from the public localization
imports. The domain instance is public because it is needed to type the statement.
`lem-sfb-henselian-parameter-root-regularity` currently has no recorded module in the
read DAG, so there is no module to import for that proof-only prerequisite; its full
use is retained in the proof docstrings, and no copy or extra assumption is introduced.

Edge cases checked before writing: n = 1 gives B = R and ramification exponent 1;
r = 1 gives a no-variable boundary presentation and basis {1}; r = 0 makes the
height-one boundary list empty and f = 1; d = 0 forces r = 0; residue characteristic
dividing n is allowed (e.g. k[[x]] over k[[t]], t = x^p). Distinct coefficients
and variables in the quotient equivalence have their actual canonical images.
No fault or STATEMENT-DISPUTED flag remains.

Searches (wrapper results are also in sandbox searches.jsonl):

- leanfinder: “Boundary primes and discrete valuation localizations of the simultaneous
  parameter root algebra R[x_i]/(x_i^n-t_i)”: 8 hits, on perfectoid tilts, valuations,
  power series and height-one spectra; no theorem giving these quotient/localization clauses.
- loogle: `"IsDiscreteValuationRing", "MvPolynomial"`: 0 hits.
- grep Mathlib through msearch: `(parameterRoot|ParameterRoot|rootAlgebra|RootAlgebra)`:
  0 hits.
- rg project `lean/WeilConjectures` and `lean/Sheaf` for parameterRoot, ParameterRoot,
  parameter.root, rootAlgebra and RootAlgebra found the existing unrestricted
  `Algebra.pthRootAlgebra` quotient, also the definitionally identical
  `strictLocalParameterRootRing` and `sncRootLevel`, and unrelated prime-to-p root towers.
  The upstream small ring-theory module is used to avoid importing geometric consumers.
- rg for `lem-sfb-parameter-root-boundary-dvrs` in `lean/WeilConjectures`: no match.
- Source read directly from the local PDF, printed pp.133--134 (PDF pages 139--140),
  confirms the simultaneous polynomial quotient in ILO IX 2.1(i). Stacks and Mathlib
  signatures were read for the regular local, DVR, quotient and localization notions.

## Second reading by Q68

This is a second self-review; no other agent was started, as required by the dispatcher.
The maintainer supplies the independent review after delivery. Reading the node and
module together, I checked every clause against the correspondence above. The explicit
surviving-generator and coefficient equations are necessary to make the presentation
canonical. The two tensor-factor equations are necessary to make the localization
comparison the V_i-algebra comparison. The fraction-field square uses this same map.
I checked the existential typeclass binders introduce conclusions rather than extra
hypotheses, and the list split includes every r ≤ d and d = 0. Compilation revealed
only a missing tensor-notation scope and a long line; both were repaired.

## Existing root-algebra dependency

The shared branch now contains `def-sfb-parameter-root-algebra`, independently
landed from Q65. Its existing declaration is `Algebra.pthRootAlgebra` in
`WeilConjectures.RingTheory.PthRootAlgebraLocal`. I reopened its complete signature
and quotient body: it takes arbitrary natural exponent `p`, variable count `n`,
a commutative coefficient ring `A : Type u` and `a : Fin n → A`, and is exactly
`MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range (fun i ↦ X i ^ p - C (a i)))`.
Its coefficient algebra structure is inherited from this quotient. Thus the
landed definition supplies the same root algebra used throughout this module,
including zero variables, exponent one and arbitrary residue characteristic.
Its unrestricted exponent also permits zero; this theorem separately requires
positive exponent. No definition or record repair is needed, and the delivered
packet contains no copy of this landed node.

## Previous repair of returned head 33bd1f90f3fc (historical)

H2 / theorem-stmt_dep: removed `lem-weil-pbc-pth-root-algebra-local` from the
item's statement dependencies and replaced it with the new definition node
`def-sfb-parameter-root-algebra`, as requested. The item differs from the current
base only in `lean` and this added definition dependency. Its natural-language
statement, proof, proof dependencies, Lean module and all declaration signatures
are unchanged. No SNC chart package is cited or imported. The signature in the new
node is copied verbatim from the abbrev, up to its `:=`.

In the second reading I checked that the new definition provides exactly the
quotient used by both existing theorem statements and all five explicit data
constructions; no theorem result is required to form it. All previously reviewed
hypothesis and clause correspondences above still apply, including the canonical
presentation, tensor comparison, fraction-field square and height-one biconditional.
The saved packet's initial dry run passed; the repaired packet is compiled and
checked again before delivery.

Validation after repair: scompile.py compiled the delivered module in both its
sandbox and library positions cleanly (7.2 s and 5.3 s). The explicit self-check
confirmed that the item changes only `lean` and the added definition dependency,
and that both `lean.statement` signatures are verbatim from their source files.

The repaired dry run required the upstream branch label `slopmaster2` for the
existing `WeilConjectures` declaration; the definition record now uses that label.

## Repair of returned head 8ac97f85d605

L returned this packet because `def-sfb-parameter-root-algebra` had independently
landed. The saved packet's required initial dry run confirmed that its stale copy
would change that landed dependency's `lean` record and require a dependency repair
report. The interface is already usable: I removed the stale definition-node file
from this delivery instead of changing its landed record. The item retains its
statement dependency on that existing node. I compared the item with the current
shared branch: the only changes are its `lean` attachment and the added landed
definition dependency; the natural-language statement, proof and proof dependencies
are unchanged. The Lean module and every signature are unchanged from the returned
head. This is a packet repair, not an unchanged re-push.

Second self-reading: I reopened the module, item statement, all statement-dependency
records, and the landed root-algebra declaration. The quotient, root coordinates,
boundary ideals, monomial basis, canonical tensor comparison, fraction-field square
and height-one-prime biconditional still use exactly the objects reviewed above.
The explicit hypotheses and edge cases in the worker report are unaffected. There
are no new nodes, no dependency module, and no statement correction in this repair.

Validation for this repair: `scompile.py` compiled the unchanged delivered module
cleanly in both positions (sandbox 7.2 s, library 5.3 s). The self-check confirmed
that the sole delivered node differs from current main only in `lean` and the
added landed definition dependency, that its signature is verbatim from the module,
that `autoImplicit` is disabled and all lines meet the 100-character limit.
