## Worker report

The module Sheaf.RingTheory.LocalDomainBirationalDimensionOne states
IsLocalRing.exists_birational_dimension_one_subalgebra, with proof sorry.
Source read: literature/stacks-project/algebra.tex, lemma-dominate-by-dimension-1
(Tag 00P8), lines 28892 onward, statement and whole proof. The node asks for
clauses (1) and (2) and the same-fraction-field consequence of its inclusions;
it does not ask for the essentially-finite-type clause (3).

Hypothesis and clause correspondence:

- A commutative ring B: `(B : Type u) [CommRing B]`.
- Noetherian: `[IsNoetherianRing B]` (every ideal is finitely generated).
- Nonzero local integral domain: `[IsDomain B] [IsLocalRing B]`;
  IsDomain includes nontriviality, and IsLocalRing gives the unique maximal ideal.
- The maximal ideal is nonzero: `(hB : IsLocalRing.maximalIdeal B ≠ ⊥)`.
- K is a field: `(K : Type v) [Field K]`, with an independent universe.
- The specified containment of B in K, and every element being b/c with c nonzero:
  `[Algebra B K] [IsFractionRing B K]`. For a domain and a field,
  localization at nonzero divisors is exactly the injective inclusion and the
  stated fraction representation. No stronger condition is introduced.
- A subring R of K containing B: `R : Subalgebra B K`. Its elements are actual
  elements of K; its scalar map contains the image of B. A subalgebra is the
  canonical packaging of a subring containing that image, not extra structure
  restricting which subrings qualify.
- R is Noetherian and local: existential proof binders
  `(_ : IsNoetherianRing R) (_ : IsLocalRing R)`.
- R is a nonzero integral domain: the canonical subalgebra instances inherit
  this from the field K; no additional conclusion is omitted.
- Dimension one: `ringKrullDim R = 1`.
- The unique maximal ideal contracts to that of B:
  `(IsLocalRing.maximalIdeal R).comap (algebraMap B R) = IsLocalRing.maximalIdeal B`.
- Its fraction field, with the given embedding, is K: `IsFractionRing R K`.
  The R-algebra on K is its canonical subalgebra inclusion.

Statement dependencies read and used:

- def-weil-pbc-noetherian-ring: Mathlib.RingTheory.Noetherian.Defs,
  IsNoetherianRing and isNoetherianRing_iff. Read the definition and docstring,
  and isNoetherianRing_iff_ideal_fg, identifying it with the node's condition.
- def-weil-field: mathlib_match Field, Mathlib.Algebra.Field.Defs, lines 116-125
  and 180. Field extends CommRing and DivisionRing; DivisionRing supplies
  Nontrivial and the inverse law, exactly the node's definition.
- def-weil-pbc-krull-dimension-ring: Mathlib.RingTheory.KrullDimension.Basic,
  ringKrullDim, lines 26-31: order Krull dimension of PrimeSpectrum in WithBot ℕ∞.

Proof-dependency imports (all existing Mathlib declarations, no local copies):
Mathlib.RingTheory.Valuation.LocalSubring (LocalSubring.exists_le_valuationSubring);
Mathlib.RingTheory.Valuation.ValuationRing (ValuationRing, ValuationRing.TFAE);
Mathlib.RingTheory.FiniteType (Algebra.FiniteType.isNoetherianRing);
Mathlib.RingTheory.Ideal.MinimalPrime.Basic (Ideal.nonempty_minimalPrimes);
Mathlib.RingTheory.Ideal.KrullsHeightTheorem
(Ideal.height_le_height_add_encard_of_subset);
Mathlib.RingTheory.Localization.AtPrime.Basic (Localization.AtPrime);
Mathlib.RingTheory.Localization.Submodule (IsLocalization.isNoetherianRing);
Mathlib.RingTheory.Ideal.Height (IsLocalization.AtPrime.ringKrullDim_eq_height).
The docstring carries all eight steps of the recorded proof, including the
finite induction choosing a, the height-zero quotient argument, and the actual
localization subring inside K.

Searches actually run on 2026-10-22:

- msearch.py leanfinder: “A nonfield Noetherian local domain has a birational
  Noetherian local overring of dimension one”: eight hits, including
  IsDiscreteValuationRing.TFAE, the local-domain TFAE, Dedekind equivalences,
  and the finite-dimension instance. None constructs the overring required here.
- msearch.py loogle: “IsLocalRing, ringKrullDim”: twelve hits, including
  maximalIdeal_height_eq_ringKrullDim and
  ringKrullDim_eq_one_iff_of_isLocalRing_isDomain. They characterize an existing
  ring or bound its dimension and do not assert this existence theorem.
- msearch.py grep: “exists_ringKrullDim_eq_one|dominat.*[Nn]oetherian”,
  subdirectory RingTheory: zero hits.
- rg in lean/WeilConjectures and lean/Sheaf for the item id, birational/dimension,
  and exists_ringKrullDim_eq_one; grep -rn for the item id in WeilConjectures:
  found upstream IsLocalRing.exists_ringKrullDim_eq_one in
  WeilConjectures.RingTheory.DiscreteValuationRing.Dominating, lines 178 onward.
  Its complete signature gives an abstract local domain and an injective local
  map only; it does not give an embedding into the prescribed fraction field
  or equality of fraction fields. It is therefore not an exact existing match.
  The landed LocalDomainSameFieldDvr module is the stronger downstream consumer,
  whose proof explicitly uses this node; using it here would reverse that route.

Edge cases checked before writing: a field B is excluded by hB, since its
maximal ideal is zero; the zero ring is excluded by IsDomain. For a DVR B the
subalgebra image of B itself is a valid result. A two-dimensional regular local
ring such as k[x,y]_(x,y) is permitted, so the statement does not identify R with B
or impose dimension one on B. Singular domains such as k[t²,t³]_(t²,t³) are
permitted: no normality or regularity is imposed. The statement allows every
characteristic, independent universes u and v, and the identity fraction-field
embedding. No finite-type assertion has been added.

No new nodes, dependency repairs, or statement correction are needed. No
STATEMENT-DISPUTED finding. The sandbox node is changed only in lean, with
its statement taken verbatim from the theorem signature. autoImplicit is false.
The prescribed scompile.py compiled both sandbox and library-name probes cleanly
(1.3 seconds each). All proof dependencies are plain imports; statement imports
are public in module mode.

## Second reading by Q65

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
