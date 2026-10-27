## Worker report

The module `Sheaf.RingTheory.CompleteDVRFiniteNormalization` states
`IsDiscreteValuationRing.complete_finite_normalization`, with its entire proof `sorry`.
The original node statement and dependency lists are unchanged. No new definitions,
helper theorems, dependency repairs, or statement corrections are needed.

Hypothesis and conclusion correspondence:

- The ring A is `(A : Type u) [CommRing A] [IsDomain A]
  [IsDiscreteValuationRing A]`. Mathlib's DVR class includes locality, the principal
  ideal property and the nonzero maximal ideal, so fields are excluded exactly as
  in def-sc-discrete-valuation-ring.
- Completeness of A for its maximal ideal is
  `[IsAdicComplete (IsLocalRing.maximalIdeal A) A]`; this includes separatedness.
- Its fraction field K is `(K : Type v) [Field K] [Algebra A K]
  [IsFractionRing A K]`.
- The finite extension L/K is `(L : Type w) [Field L] [Algebra K L]
  [Module.Finite K L]`. Module finiteness over a field is finite dimensionality.
  `[Algebra A L] [IsScalarTower A K L]` records the composite inclusion A → K → L;
  these are compatible structures on the original objects, not extra mathematical
  restrictions. The map A → L is automatically injective.
- The integral closure C is the existing `integralClosure A L : Subalgebra A L`.
  It consists precisely of the elements satisfying monic polynomial equations over A.
  The theorem uses this actual subalgebra throughout; it does not choose a new ring.
- C is a DVR: `∃ hC : IsDiscreteValuationRing (integralClosure A L), ...`.
  Its domain structure is inferred from its embedding in the field L.
- Its fraction field is L: `IsFractionRing (integralClosure A L) L`, for the canonical
  subtype algebra structure.
- It is finite over A: `Module.Finite A (integralClosure A L)`.
- It is complete for its own maximal ideal: `IsAdicComplete
  (@IsLocalRing.maximalIdeal (integralClosure A L) _ hC.toIsLocalRing)
  (integralClosure A L)`. The explicit local-ring proof argument avoids a hidden
  let/local instance; hC is the DVR proof just asserted.
- The inclusion A → C is local: its canonical maximal ideal has comap along
  `algebraMap A (integralClosure A L)` equal to `IsLocalRing.maximalIdeal A`.
- Uniqueness quantifies over every `(V : Subalgebra A L)
  [IsDiscreteValuationRing V]`, assumes `IsFractionRing V L` and the stated equality
  of maximal-ideal comaps along `algebraMap A V`, and concludes
  `V = integralClosure A L`. A subalgebra of L is exactly a subring containing the
  image of A with the induced A-algebra structure, so this covers every V ⊆ L in
  the node, without assuming V finite or complete. Subalgebra equality is equality
  of those actual subrings inside L, not only an abstract ring isomorphism.
- There is no separability, perfect residue field, characteristic restriction, or
  hypothesis that V is complete or finite.

Statement dependency declarations read in full and used:

- def-sc-discrete-valuation-ring: `Mathlib.RingTheory.DiscreteValuationRing.Basic`,
  `IsDiscreteValuationRing` (lines 55–60).
- def-weil-pbc-adically-complete-ring: `Mathlib.RingTheory.AdicCompletion.Basic`,
  `IsAdicComplete` (lines 42–56, including Hausdorff/precomplete definitions).
- def-pc-field-extension: `Mathlib.Algebra.Algebra.Defs`, `Algebra` (lines 91–100).
- def-weil-finitely-generated-module: `Mathlib.RingTheory.Finiteness.Defs`,
  `Module.Finite` (lines 116–119).
- def-weil-pbc-integral-closure: `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`,
  `integralClosure` (lines 215–222).

Proof dependencies are imported non-publicly: the PID/normality results in
`Mathlib.RingTheory.DedekindDomain.Basic`; the normality and fraction-field results
in `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed` and
`Mathlib.RingTheory.Localization.Integral`; DVR dimension and power decomposition
in `Mathlib.RingTheory.DiscreteValuationRing.TFAE` and the public Basic import;
`Mathlib.RingTheory.Ideal.GoingUp`; and the recorded upstream modules
`WeilConjectures.RingTheory.NagataOfCompleteLocal` (`isNagataRing_of_complete_local`),
`WeilConjectures.RingTheory.NagataRing` (`IsNagataRing`),
`WeilConjectures.RingTheory.JapaneseDomain` (`IsN2`),
`WeilConjectures.RingTheory.FiniteOverCompleteLocalProduct`
(`Algebra.finite_over_complete_local_product`),
`WeilConjectures.Mathlib.RingTheory.Ideal.HasGoingUp`
(`ringKrullDim_eq_of_isIntegral`), and
`WeilConjectures.AlgebraicGeometry.Regular`
(the recorded `AlgebraicGeometry.IsRegular.of_isIntegrallyClosed_stalk` module,
which also imports the ring-theoretic regular/DVR criterion).
The declaration docstring gives all six proof steps and their DAG inputs.

Source check: read local Stacks More on Algebra, remark-construction (09EM),
assertions (1), (4), (8), and lemma-special-case (09F8), first proof paragraph;
Algebra lemma-Noetherian-complete-local-Nagata (032W). They explicitly allow an
arbitrary finite extension, using Nagata finiteness and domination maximality.

Edge cases checked before writing: extension degree one recovers A inside K;
nonseparable extensions in positive characteristic and imperfect residue fields
remain allowed; a competing V need not be finite or complete; field/zero-ring
base cases are excluded by the original DVR assumption; C cannot be a field
because an injective integral extension preserves dimension one. Independent
universes u, v, w are retained for A, K, L. Every competing subring is a subtype
of L and therefore is represented in L's universe without a restriction.

Searches actually run:

- msearch.py leansearch, query: "integral closure of a complete discrete valuation
  ring in a finite extension of its fraction field is a finite complete discrete
  valuation ring". Eight hits, including
  `integralClosure.isIntegrallyClosedOfFiniteExtension`,
  `integralClosure.isIntegralClosure` and valuation-subring integral closedness;
  no result supplies the full conclusion.

- msearch.py leanfinder, query: "integral closure of a complete discrete valuation
  ring in a finite field extension is a finite complete discrete valuation ring
  unique dominating valuation ring". Eight hits: valuation integrality, Dedekind
  integral closedness, adic completion integers, and locally compact valued-field
  characterizations; none states this full result.
- msearch.py loogle, query: `IsDiscreteValuationRing, integralClosure`: zero hits.
- msearch.py grep, query: `IsDiscreteValuationRing|IsAdicComplete|Module.Finite`,
  subdirectory `RingTheory/DedekindDomain`: 23 hits. Read IntegralClosure.lean
  lines 147–176: its finiteness theorem requires `Algebra.IsSeparable K L`, so
  cannot replace this theorem for arbitrary finite extensions.
- rg in both `lean/WeilConjectures` and `lean/Sheaf`, patterns
  `complete.*dvr|dvr.*complete|finite_normalization|lem-per-complete-dvr-finite-normalization`
  and `integralClosure.*(complete|Complete)|[Cc]omplete.*integralClosure|normalization.*DVR|DVR.*normalization`.
  Nearby results concern tame inertia, codimension-one purity, normalized
  composita, and coefficient rings; no exact statement. Also ran the requested
  grep for this node id in `lean/WeilConjectures`: no hits. Read the normalized
  compositum and local Abhyankar modules to check those nearby hits.

No statement dispute or node fault was found. Compilation is through scompile.py
only; the final dry run and delivery perform the server checks again.

## Second reading by O3

The dispatcher explicitly prohibits starting other agents; this is a second pass
by the same worker, not an independent review. The maintainer supplies independent
review after delivery. Reread the node and signature clause by clause: the
existential DVR proof supplies the canonical maximal ideal in both completeness
and locality; neither conclusion has become an assumption. The universally
quantified V is a subalgebra containing A, with the canonical inclusion into L.
Its fraction-field and local-inclusion conditions are the two original conditions,
and equality is inside L. No additional clause or missing hypothesis was found.
