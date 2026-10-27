## Worker report

The delivery states `RingEquiv.normalization_pair_ring_invariance` in
`Sheaf.RingTheory.NormalizationPairRingInvariance`. Its only theorem proof is `sorry`.
`RingEquiv.normalizationPairDefect` is a transparent abbreviation for the quotient
already named in this item's statement: the integral closure in total fractions,
modulo the range of `Algebra.linearMap`. It supplies real quotient data, not a
chosen model or an independently assumed quotient map. It is an owning-node helper
under the launcher's missing-helper authorization, rather than a new mathematical
notion. There are no new nodes, dependency repairs, or statement corrections.

Hypotheses, matched individually:

- The field is `(k : Type u) [Field k]`.
- Each base ring has its own type universe, `CommRing`, `IsLocalRing`,
  `IsNoetherianRing`, `IsReduced`, and `Algebra k` instances. `IsLocalRing` already
  includes `Nontrivial`, so the nonzero condition is present without a duplicate
  instance. `IsReduced` means that every nilpotent element is zero.
- The structural identifications of the two residue fields with k are precisely
  `hres` and `hres'`: bijectivity of the composite of the structural ring map and
  `IsLocalRing.residue`, rather than existence of an unrelated field isomorphism.
- `FractionRing H` is Mathlib's localization at `nonZeroDivisors H`, even for a
  reduced ring that is not a domain. The normalization is literally
  `integralClosure H (FractionRing H)`; similarly for H'.
- The normalization finiteness assumptions are the two `Module.Finite` instances
  over H and H'. The defect dimension assumptions are the two `FiniteDimensional`
  instances over k on the actual quotient helper.
- The two finite nonempty families are `I`, `I'` with `Finite` and `Nonempty`.
  `S`, `S'` are dependent families with commutative ring, local ring and domain
  instances. Locality and domain each imply their required nonzeroness. The ring
  decompositions are `decomp` and `decomp'`. Their universes are independent of
  those of the field, base rings and index types.
- `phi : H ≃+* H'` is an arbitrary ring isomorphism. There is no scalar-compatibility
  hypothesis in the main theorem.

Conclusions, in their order in the signature:

1. The existential `F` is a ring equivalence of total fraction rings. Its first
   conjunct specifies the extension on every base-ring element; the second says
   every ring equivalence with this extension property equals F. Uniqueness is
   therefore not restricted to maps satisfying the later conclusions.
2. `E` is a ring equivalence of the actual integral closures. The equality of its
   ambient values with F restricts F to the closure; surjectivity of E says the
   closure is carried onto the entire other closure.
3. `T` is an additive quotient equivalence. Its equation on `Submodule.Quotient.mk`
   pins it to `[z] ↦ [E(z)]`. The next conjunct states exactly
   `T (h • m) = phi h • T m`.
4. `L` is an order equivalence of quotient submodule lattices, and `LC` is one of
   normalization submodule lattices, matching proof step 4. Their membership
   biconditionals pin both to the images under T and E. Thus these are the
   indicated lattice identifications, including meets and joins, rather than
   unrelated existence assertions.
5. Both quotient lengths are explicitly `< ⊤`. The later three length/dimension
   equations give the full displayed four-term equality, with the natural-valued
   dimensions coerced to `ℕ∞`, the codomain of `Module.length`.
6. The idempotent conjunct is an iff under E between the literal primitive nonzero
   idempotent predicates: idempotent, nonzero, and every decomposition as the sum
   of orthogonal idempotents has a zero summand. Since E is bijective this
   identifies their sets. No condition on non-idempotent decompositions is added.
7. `Nat.card I = Nat.card I'` is b=b' for the finite families. No enumerations or
   choices of primitive idempotents are assumed.
8. Only the final implication assumes scalar compatibility, written as
   `∀ a : k, phi (algebraMap k H a) = algebraMap k H' a`. Its conclusion gives
   the scalar identities for F, E and T. Each is already additive; these identities
   express k-linearity. The inverse identities follow from their bijectivity.

Dependency declarations read and used:

- `Field`, `Mathlib.Algebra.Field.Defs` (available through fraction-ring imports).
- `IsNoetherianRing`, `Mathlib.RingTheory.Noetherian.Defs`.
- `integralClosure`, `IsIntegral`,
  `Mathlib.RingTheory.IntegralClosure.Algebra.Basic` and its imported definitions;
  also read `IsIntegrallyClosedIn` in IntegralClosure/IntegrallyClosed.lean.
- `Module.Finite`, `Mathlib.RingTheory.Finiteness.Defs`.
- `Module.length`, `Mathlib.RingTheory.Length`.
- Proof dependency imports: `IsLocalization.lift` and `IsLocalization.ringHom_ext`
  through FractionRing; `Module.length_eq_add_of_exact` through Length;
  `IsSimpleModule` through Length/FiniteLength; and
  `Module.exists_simple_filtration_of_length_lt_top` by the plain proof import
  `WeilConjectures.RingTheory.SimpleFiltration`. No statement depends on that
  proof-only import.

Read the local Stacks sources at curves.tex, equation-multicross (Tag 0C1U), and
algebra.tex, definition-integral-closure, lemma-length-independent,
lemma-characterize-length-1 and lemma-simple-pieces. The theorem docstring carries
all nine proof steps, with the named DAG dependencies. The latest blueprint
lem-trf-local-term-locality follows the contracting-correspondence argument, as
already explained by the accepted split; this delivery preserves the assigned
surviving ring-invariance node without changing that unit or its route.

Searches actually run on 2026-10-24:

- `msearch.py ... leanfinder`, query: "A ring isomorphism of reduced local rings
  extends to total fraction rings and integral closures and preserves normalization
  quotient module length and branch count". Eight hits, principally integral norms,
  ramification and inertia. None states this comparison.
- `msearch.py ... loogle`, query: `"integralClosure", "equiv"`. Eight hits, including
  `AlgEquiv.mapIntegralClosure` and `IsIntegralClosure.equiv`. Read the former's
  full signature and the fraction-ring equivalence signature: fixed-base algebra
  equivalences alone do not state the varying-base quotient/lattice/numerical result.
- `msearch.py ... leansearch`, query: "A ring isomorphism preserves integral closure
  in total fractions, normalization quotient length, and branch count". Eight hits,
  including `RingEquiv.isIntegral_iff`, `integralClosure_map_algEquiv`, and
  `IsIntegrallyClosed.of_equiv`; no complete match.
- `msearch.py ... grep`, query:
  `ringEquivOfRingEquiv|length.*finrank|IsPrimitive.*[Ii]dempotent`, subdirectory
  `RingTheory`. Twenty-five displayed hits include fraction-ring extension and
  field-module length=dimension. Read FractionRing.lean:423-438 and
  LocalRing/Length.lean:49-70; neither supplies the whole item.
- `rg` over Mathlib's Algebra and RingTheory, and then all Mathlib, for primitive
  idempotent names/descriptions found no primitive-idempotent definition.
  `IsIdempotentElem` itself is reused from `Mathlib.Algebra.Group.Idempotent`.
- `rg` over both `lean/WeilConjectures` and `lean/Sheaf` for normalization quotients,
  defects, pairs and primitive idempotents found scheme-stalk quotient helpers,
  specialized series computations, and unrelated results; none gives this general
  ring theorem. `grep -rn` of the item id in `lean/WeilConjectures` found nothing.
  The final exact-name search, including `dag/lean_names_upstream.json`, found no
  `normalization_pair_ring_invariance`, `normalizationPairDefect`, or
  `normalizationPair` declaration. DAG search found the assigned comparison and
  specialized nodal/normalization applications, not an existing general interface.

Edge cases checked mathematically before and after writing:

- H=H'=k has zero defect, length and dimension zero, one domain factor, and a
  perfectly valid quotient additive equivalence on the zero module.
- The two-branch formal node has a reduced non-domain base and one-dimensional
  defect. No domain constraint on H or H' was introduced by FractionRing.
- Twisting coefficients by a nontrivial automorphism of k on a multicross ring
  gives a ring isomorphism which need not be k-linear. Its dimensions and branch
  count still agree; only the final linearity implication has an extra antecedent.
- Characteristic two causes no change: the orthogonal-idempotent predicate uses
  multiplication and addition, with no division by two.
- Empty families are explicitly excluded by the source, and `Nonempty` renders
  that condition. Singleton families remain allowed. Finite index types in any
  universe are accepted, with cardinality recorded by `Nat.card`.

Validation: the initial misspelled plural idempotent import was repaired to the
actual Mathlib module. The resulting module compiled cleanly through the prescribed
`scompile.py` wrapper. The final import list also imports the recorded finiteness
module explicitly and removes the unnecessary Localization.Algebra import. The
normal dry run recompiles that final file. No unresolved statement dispute or node
fault was found.

## Second reading by Q68

I reread the full node and final signature after the first successful compile.
The dispatcher explicitly prohibits starting another agent, so this is the worker's
second pass; the maintainer supplies the independent review.

Checked separately that `hres` uses the structural map, `IsLocalRing` includes
nonzeroness, `FractionRing` does not require a domain, and the quotient's k-action
is the canonical action through its base ring. Checked that uniqueness of F only
requires its extension equation, E is tied to F, T is tied to E on every
representative, and each lattice map is tied to that same E or T. Rechecked the
four-term numerical equality, finite lengths, both primitive predicates and the
finite nonempty factor cardinalities. The only scalar-compatibility assumption
occurs inside the final implication. The zero-defect and coefficient-twist cases
therefore retain precisely their intended meanings. All universes and variables
are explicitly bound; the helper has real quotient data; the only postponed proof
is the named theorem matching the item. No mathematical mismatch or statement
change was needed.
