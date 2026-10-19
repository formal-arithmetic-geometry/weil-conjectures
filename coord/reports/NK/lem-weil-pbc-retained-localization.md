## Worker report

The module Sheaf.RingTheory.RetainedLocalizationProperties states
PrincipalWLocalization.Retained.properties, with a single postponed theorem proof.
The helper structuralMap constructs the actual composite R → R^w → R_[T], using the
already recorded algebras; its data is not postponed. No node statement was corrected.
The source read is the blueprint's lemma at order 1225 and both paragraphs of its proof.

Hypothesis and clause correspondence:

- Commutative ring R: `{R : Type u} [CommRing R]`; no nontriviality assumption.
- Zariski closed T: `(T : Set (PrimeSpectrum R)) (hT : IsClosed T)`.
- R_[T]: precisely `PrincipalWLocalization.Retained.algebra T hT` from the dependency.
- The structural map is ind-Zariski: the first conjunct is
  `@Algebra.IsIndPrincipalZariski R (algebra T hT) _ _ (structuralMap T hT).toAlgebra`.
  Using the composite map's induced algebra explicitly avoids choosing an incompatible
  implicit R-algebra structure on the R^w-algebra.
- Its points are exactly pairs (x,y) with x in T and y contained in x: the equivalence
  `e` has target `{p : PrimeSpectrum R × PrimeSpectrum R //
  p.1 ∈ T ∧ p.2.asIdeal ≤ p.1.asIdeal}`.
- The canonical map from R_y to the local ring at the corresponding point is an
  isomorphism: for each q, `hq` identifies y with the contraction of q, and
  `Function.Bijective (Localization.localRingHom ... (structuralMap T hT) hq)`
  asserts precisely that canonical map is an isomorphism. The contraction identification
  specifies the meaning of the canonical local map, rather than assuming another map.
- Every point of T is closed: `∀ x ∈ T, IsClosed ({x} : Set (PrimeSpectrum R))`.
  This hypothesis guards both the w-local/closed-point clause and the quotient clause.
- W-locality: `IsWLocalRing (algebra T hT)`, the recorded existing notion.
- Closed-point set identified with patch T: the Homeomorph from subtype T with
  `TopologicalSpace.induced Subtype.val (constructibleTopology (PrimeSpectrum R))`
  to `closedPoints (PrimeSpectrum (algebra T hT))`, and its compatibility
  `(e (h x).val).val = (x.val, x.val)`. The target uses its Zariski subspace topology.
- T=V(J): `∀ J : Ideal R, T = PrimeSpectrum.zeroLocus (J : Set R) → ...`.
- Canonical quotient isomorphism: bijectivity of `Ideal.quotientMap
  (J.map (structuralMap T hT)) (structuralMap T hT) Ideal.le_comap_map`.
  The codomain is exactly R_[T]/JR_[T], and the domain is R/J. No arbitrary ring
  equivalence substitutes for the canonical map.

Dependency declarations read and used:

- Sheaf.RingTheory.RetainedLocalization: PrincipalWLocalization.Retained.algebra;
  its selectors and reverse-inclusion filtered diagram supply the actual retained object.
- Sheaf.RingTheory.IndPrincipalZariski: Algebra.IsIndPrincipalZariski (publicly imported
  through PrincipalWLocalization and RetainedLocalization).
- WeilConjectures.RingTheory.ProEtale.WLocal: IsWLocalRing; the associated
  WLocalSpace definition and its closed-points field were also read. This and
  constructibleTopology are exposed by the same dependency import chain.
- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Spec and Spec.map;
  spectra are represented on their underlying PrimeSpectrum spaces here.
- Mathlib.RingTheory.Localization.AtPrime.Basic: Localization.AtPrime and
  Localization.localRingHom; its docstring and full signature identify the canonical map.
  The recorded residue-field and fibre-ring clauses are not needed by this statement.
- Mathlib.RingTheory.Ideal.Quotient.Operations: Ideal.quotientMap;
  Mathlib.RingTheory.Ideal.Maps: Ideal.le_comap_map, for the canonical quotient map.

Proof imports retain the recorded modules PrincipalWLocalizationPoints and
IndEtaleStability (also exposing PrincipalWLocalization), and the exact Mathlib
sources for the recorded compact-Hausdorff and affine local-ring criteria.
The proof dependency lem-weil-pbc-zero-dimensional-spectrum-profinite has no
recorded module or Mathlib match; there is therefore no import to add for it yet.
It is a proof prerequisite only, not a missing object needed to state this item.
The theorem docstring carries all seven DAG proof steps (the final two combined
as step 6), including the fraction calculation and the generic proof prerequisites.

Edge cases checked: the zero ring and empty T yield empty prime-pair types and
empty closed-point spaces; no Nonempty or Nontrivial assumption excludes them.
For T empty and J the unit ideal, both quotient rings are zero rings. The case
T equal to the whole spectrum is included without any closed-point assumption
in the ind-Zariski and local-ring clauses. The closed-point hypothesis is not
silently imposed on those clauses. Neither an enumeration of constructible
neighbourhoods nor a countability assumption is used. All objects remain in
one arbitrary ring universe u; no larger spectrum is excluded.

Searches for an existing statement:

- msearch.py leanfinder, query "Retained localization of a closed subset of a prime
  spectrum is ind-Zariski with prime pairs and unchanged local rings": eight hits,
  only generic localization and local-property results; no retained theorem.
- msearch.py loogle, query "Ideal.quotientMap, Localization.localRingHom": zero hits.
- msearch.py grep, query "retained|Retained" under RingTheory: zero Mathlib hits.
- msearch.py leansearch, query "retained localization closed subset prime spectrum":
  unavailable, Internal Server Error (recorded by the search tool).
- rg on all upstream WeilConjectures and project lean/Sheaf for retained-localization
  names and this node id: only the existing definition module, no properties theorem.
- Direct Mathlib source searches located localRingHom and quotientMap, whose full
  signatures and docstrings were read, as well as Ideal.le_comap_map.

Server scompile.py compiled every delivered file cleanly (1.6 s for the new module),
with nice 19, two threads and the 60 s per-file limit. No local compiler was used.
No disputed statement, dependency repair or new definition node was needed.

## Second reading by NK

Read the node statement and all seven proof steps independently against the exact
source named by the node: blueprint order 1225, both proof paragraphs, and the
preceding retained-localization definition at order 1224. This node cites the
blueprint rather than a Stacks tag; its source introduces no additional standing
Noetherian, characteristic, or finiteness assumptions.

Object/hypothesis/conclusion checklist, in source order:

1. Arbitrary commutative ring R: `{R : Type u} [CommRing R]` above the declaration.
   Verdict: exact, including the zero ring.
2. Zariski closed subset T: `(T : Set (PrimeSpectrum R)) (hT : IsClosed T)`.
   Verdict: exact; the topology here is the existing Zariski topology.
3. Retained ring: `algebra T hT` is the dependency's colimit in
   `CommAlgCat (PrincipalWLocalization.algebra R)`. I opened its concrete
   selector, reverse-inclusion neighborhood diagram, transition maps and colimit,
   as well as the dependency node. `structuralMap` is the composite of the two
   algebra maps, with actual data. Verdict: the required ring and canonical map.
4. Ind-Zariski structural map: the first conjunct explicitly supplies
   `(structuralMap T hT).toAlgebra` to `Algebra.IsIndPrincipalZariski`.
   I read that dependency definition: filtered colimits of finite products of
   principal localizations, including the empty product. Verdict: exact; upstream
   general local-isomorphism `IndZariski` is appropriately not substituted.
5. Exactly the pairs (x,y) with x in T and y contained in x: the equivalence `e`
   targets `{p : PrimeSpectrum R × PrimeSpectrum R //
   p.1 ∈ T ∧ p.2.asIdeal ≤ p.1.asIdeal}`. Verdict: both directions and the
   non-strict inclusion (including the diagonal) are present.
6. Canonical local-ring isomorphism at every pair: `∀ q, ∃ hq, ...` identifies
   `(e q).val.2.asIdeal` with contraction of q along `structuralMap`; bijectivity
   is asserted for `Localization.localRingHom` using that equality. I read its
   full definition and fraction formula in Mathlib. Verdict: exact canonical map,
   with source `R_y` and target the prime localization of the retained ring;
   `hq` is a conclusion witnessing contraction, not an extra hypothesis.
7. Conditional clause: `(∀ x ∈ T, IsClosed ({x} : Set (PrimeSpectrum R))) → ...`.
   Verdict: precisely the source's closed-point assumption, imposed only on the
   w-local/closed-point and quotient assertions.
8. W-local spectrum: `IsWLocalRing (algebra T hT)`. I read the recorded upstream
   class and its imported `WLocalSpace`: closed closed-point set and unique closed
   specializations. On spectra this is the recorded component formulation.
   Verdict: the dependency's notion, with no additional assumption.
9. Closed points identified with patch T: `Homeomorph T (closedPoints ...)`
   supplies the induced `constructibleTopology (PrimeSpectrum R)` on T and the
   ordinary subspace topology on the target. The equation
   `(e (h x).val).val = (x.val, x.val)` ties this to the same pair description.
   Verdict: full topological identification and diagonal correspondence, not just
   cardinality. Mathlib's constructible topology is generated by compact opens
   and their complements, giving the required D(f),V(f) topology on spectra.
10. For every ideal J with T=V(J): `∀ J : Ideal R,
    T = PrimeSpectrum.zeroLocus (J : Set R) → ...`. Verdict: correct quantifier
    order and no radical or finite-generation restriction.
11. Canonical quotient isomorphism: bijectivity of `Ideal.quotientMap
    (J.map (structuralMap T hT)) (structuralMap T hT) Ideal.le_comap_map`.
    I opened `quotientMap` and `le_comap_map`: the implicit domain ideal is J,
    and the codomain ideal is its extension. Verdict: exactly the canonical
    R/J to R_[T]/JR_[T] map, not an arbitrary equivalence.

I also opened the recorded `PrincipalWLocalization.points` signature and docstring:
its pairs, contraction, local rings, patch topology and closed diagonal agree with
this proof's use. The affine-spectrum dependency's `Spec` and `Spec.map` use the
same PrimeSpectrum underlying spaces. There are no new nodes or dependency modules
in this packet and no statement_change needing a citer audit.

Edge cases: empty T gives an empty pair space and includes the selector of the
empty constructible neighborhood; the zero ring has empty spectrum and its empty
stage product. Neither case is excluded by Nonempty or Nontrivial. For T=V(1),
the quotient assertion compares zero rings. T=Spec R is allowed in the first
three conclusions without assuming all primes closed. The diagonal y=x is included.
There is no degree n, characteristic restriction, sequence/countability restriction,
or independently chosen index universe. Arbitrary `u` covers all ring sizes; all
spectra, subsets, and retained colimit are in the corresponding ring universe.

Independent searches used different descriptions from the first worker:

- LeanFinder: "Idempotent localization retaining closed primes is ind Zariski and
  induces an isomorphism on quotient rings": eight generic results, including
  `IsLocalization.localizationLocalizationAtPrimeIsoLocalization` (ordinary
  localization only) and `PrimeSpectrum.toPiLocalization_bijective` (discrete
  spectrum only). Neither states the retained construction's properties.
- Loogle: `Localization.localRingHom`: twelve hits identifying the canonical map
  and its formulas and functoriality; no retained-localization theorem.
- grep service: `idempotent.*localization|localization.*idempotent`: eight generic
  uses of idempotent localizations, no complete statement match.
- LeanSearch: "A filtered colimit of idempotent localizations retaining a closed
  subset of the prime spectrum": unavailable (Internal Server Error), not a
  negative search result.
- Direct rg in Mathlib RingTheory, all upstream WeilConjectures, and project
  lean/Sheaf using retained/Retained, selector, and IsIndPrincipalZariski found
  the existing definition module and unrelated uses of the English word;
  no competing retained properties declaration. Read the relevant Mathlib
  localRingHom and quotientMap declarations rather than relying on names.

No mathematical mismatch found, and no Lean or node change was needed. The module
has one theorem with proof `sorry`, and the helper map has real data. Both declarations
have source/blueprint docstrings; the theorem docstring covers all seven proof steps
(the last two combined). Explicit `universe u` and the bound R/ring instance leave no
unbound variable. The node's lean.statement was checked verbatim against the signature.

Second-reader validation: scompile.py compiled the delivered module cleanly in
1.6 seconds, with nice 19, two threads, 60-second per-file limit; dependency overlay
files also compiled cleanly. No local compiler was used. Verbatim signature check passed.
