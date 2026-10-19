## Worker report

The module `Sheaf.RingTheory.StrictWCoverProperties` states
`PrincipalWLocalization.StrictWCover.properties`, with its sole proof `sorry`.
The source is blueprint order 1229 and Stacks Tag 097X, first proof paragraph,
properties (1), (3), (7), (9). The full five-step DAG proof is included in its docstring.
No definition, dependency record, or natural-language statement was changed.

Hypothesis and clause correspondence:

- An arbitrary commutative ring A: `(A : Type u) [CommRing A]`, with u explicitly bound.
- The specified strict cover C_A: `PrincipalWLocalization.StrictWCover.algebra A`,
  using its bundled composite A-algebra structure, rather than an arbitrary cover.
- A -> C_A faithfully flat: `Module.FaithfullyFlat A (algebra A)`.
- That same map ind-etale: `Algebra.IndEtale A (algebra A)`.
- Its spectrum w-local: `IsWLocalRing (algebra A)`.
- All its maximal local rings strictly henselian:
  `∀ (m : Ideal (algebra A)) [m.IsMaximal],
  IsStrictlyHenselianLocalRing (Localization.AtPrime m)`.
- Its closed points surject onto Spec A: `Function.Surjective` of the function
  from `closedPoints (PrimeSpectrum (algebra A))` to `PrimeSpectrum A` given by
  `PrimeSpectrum.comap (algebraMap A (algebra A)) q.val`.

Dependency declarations read and used:

- `Sheaf.RingTheory.StrictWCover`: `PrincipalWLocalization.StrictWCover.algebra`;
  its concrete underlying retained localization and specified composite structural map.
- `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`: `Module.FaithfullyFlat`,
  flatness plus the properness criterion for all maximal ideals, matching the
  node's exactness-reflection definition as explained in its recorded Mathlib match.
- `Sheaf.RingTheory.IndPrincipalZariski`, exposing
  `WeilConjectures.RingTheory.ProEtale.IndEtale`: `Algebra.IndEtale`, the filtered
  colimit of etale algebras (which are finitely presented).
- `WeilConjectures.RingTheory.ProEtale.WLocal`: `IsWLocalRing`, whose spectrum
  is `WLocalSpace`; the dependency record identifies its unique closed
  specializations with the connected-component formulation.
- `WeilConjectures.Mathlib.RingTheory.Henselian`: `IsStrictlyHenselianLocalRing`,
  extending `HenselianLocalRing` by separably closed residue field.

All recorded proof-dependency modules are imported, without public re-export:
`PrincipalWLocalizationPoints`, `EtaleContractionProperties`, `IndEtaleStability`,
`WeaklyEtaleField`, `RetainedLocalizationProperties`, `PrincipalWLocalization`
under `Sheaf.RingTheory`, and `Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra`.
Statement dependencies already public-imported are not repeated.

Edge cases checked: the zero ring is admitted (no nontriviality hypothesis);
its empty base spectrum makes closed-point surjectivity vacuous, and a zero
cover has no maximal ideals. For nonzero rings the final clause requires a
closed point above EVERY prime, not merely every maximal prime of A. Arbitrary
characteristics, infinite spectra, and every ring universe u remain admitted.
No uniqueness of the closed point over a given base prime is asserted.

Searches for an existing statement:

- msearch LeanFinder: `faithfully flat ind etale strict w local cover closed points
  surjective`; eight hits including `flat_and_surjective_SpecMap_iff` and the
  faithful-flatness spectrum criterion; none states the cover's full properties.
- msearch Loogle: `Algebra.IndEtale, IsWLocalRing`; zero hits, unknown identifier
  `Algebra.IndEtale` (the service indexes Mathlib rather than upstream).
- msearch LeanSearch: `strict w local cover faithfully flat closed points surjective`;
  unavailable, Internal Server Error.
- msearch Mathlib grep: `StrictWCover|strictW|strict.*[Cc]over`; hits concern unrelated
  modular-form widths and restriction/cover text, no strict w-local cover theorem.
- Direct rg of upstream `WeilConjectures` and project `lean/Sheaf` for
  `strictW|StrictWCover|strictWCover`: only the recorded strict-cover definition
  module occurs, with no properties theorem. A separate upstream search for
  `lem-weil-pbc-strict-w-cover` has no hits.

No node faults or disputed statements were found. Server compilation and the
required delivery dry run are used for validation; no local compiler is run.

## Second reading by NE

Read the item node, its exact blueprint source at order 1229, Stacks proetale.tex
lines 1505–1561 (Tag 097X), all five statement-dependency records and the actual
Lean declarations. Independent object/hypothesis/conclusion inventory:

1. Any commutative ring A: `theorem properties (A : Type u) [CommRing A]`.
   Verdict: exact, with no nonzero, Noetherian, field, or finiteness hypothesis.
2. The specified algebra C_A and specified map A → C_A:
   `PrincipalWLocalization.StrictWCover.algebra A`, with `algebraMap A (algebra A)`.
   Opened StrictWCover.lean: `closedIdeal` is the vanishing ideal of all closed
   points of the principal w-localization; `contraction` and `contractionMap`
   use the representative-based etale contraction and its stage-zero map;
   `extendedIdeal` is ideal extension along that map; `retainedAlgebra` uses
   precisely its zero locus. `structuralMap` composes A → W → E → E^w → C_A,
   and `algebra` bundles that map via `toAlgebra`. Verdict: same object and map,
   with real construction data, not an arbitrary algebra or chosen witness.
3. Faithfully flat map: `Module.FaithfullyFlat A (algebra A)`.
   Read Mathlib's class (flat plus proper maximal-ideal extension), and the
   dependency's recorded exactness-equivalence interface. Verdict: exact.
4. Ind-etale map: `Algebra.IndEtale A (algebra A)`.
   Read IndPrincipalZariski's public imports and upstream IndEtale.lean:
   the class gives a small filtered colimit presentation by etale A-algebras;
   their finite presentation is explicit in `etale_le_finitePresentation`.
   Verdict: exact; no principal-Zariski condition substituted for ind-etale.
5. W-local spectrum: `IsWLocalRing (algebra A)`.
   Read WLocal.lean, WLocal/Basic.lean and WLocal/ConnectedComponents.lean:
   the class supplies the w-local prime spectrum; closed points are closed,
   and the closed-point-to-component map is a homeomorphism. Verdict: exact
   Zariski connected-component condition, not a patch-topology condition.
6. Every maximal local ring is strictly henselian:
   `∀ (m : Ideal (algebra A)) [m.IsMaximal],
   IsStrictlyHenselianLocalRing (Localization.AtPrime m)`.
   Read the upstream class: it extends `HenselianLocalRing` with separably
   closed residue field. The maximal-ideal binder supplies primality for
   AtPrime; there is no extra local-ring assumption on C_A. Verdict: exact.
7. Its closed points surject onto all of Spec A: `Function.Surjective`
   of `fun q : closedPoints (PrimeSpectrum (algebra A)) ↦
   PrimeSpectrum.comap (algebraMap A (algebra A)) q.val`.
   Verdict: exact restriction of the specified spectrum map; the codomain is
   every prime of A, not just closed points, and no injectivity is asserted.

Source context: Tag 097X introduces a map A → B inducing algebraic residue
extensions to construct a square. Its first proof paragraph constructs C
solely from A and proves exactly properties (1), (3), (7), (9). The B-related
hypothesis is used for D in the next paragraph, so it is correctly absent
here. No scheme or coefficient datum is part of this lemma.

Edge cases: zero rings and empty spectra are allowed. A zero A forces any
A-algebra, including this one, to be zero; the maximal-ideal quantifier and
surjectivity to the empty spectrum are vacuous. No index or natural-number
parameter is exposed, so empty-index/n = 0 cases impose no new hypotheses.
Every characteristic, finite or infinite spectrum, and arbitrary universe u
are covered. The constructed algebra lives in u by the dependency's
CommAlgCat.{u} result; this introduces no independent size restriction.

Independent searches (different terms from the worker):

- msearch LeanFinder, `canonical ring extension w strictly local maximal stalks
  closed points cover spectrum`: eight results about local stalk maps,
  `OfLocalizationMaximal`, and affine closed points, none about this cover.
- msearch Loogle, `"IsWLocalRing"`: zero results.
- Direct rg in upstream RingTheory/ProEtale, project lean/Sheaf/RingTheory,
  and Mathlib/RingTheory, using `WStrictLocalization|StrictWCover|strictly.*local|
  strict.*[Cc]over`. This does find the important upstream candidate
  WStrictLocalization. Opened its definition, indEtale/faithfullyFlat/isWLocalRing
  instances and WeaklyEtaleIndEtale's
  `WStrictLocalization.exists_mem_zeroLocus_comap_eq` signature. They concern
  `(WStrictLocalization.contractionIdeal R).WLocalization`, formed from
  upstream WLocalization and IndEtaleContraction, not the recorded
  PrincipalWLocalization.StrictWCover.algebra. No identification with the
  node's particular construction is given. Thus these cannot replace this
  theorem by an existing record. No exact duplicate was found in Mathlib or
  the project's statements.

No new nodes, dependency modules, or statement correction were needed.
The sole postponed theorem is named, carries its source/blueprint docstring,
and reproduces all five DAG proof steps: closed points of W; maximality of
T via algebraic domains; retained localization and transport of strict
henselianity; closed-point surjectivity; ind-etaleness and faithful flatness.
All declaration binders and u are explicit. The node lean.statement was
checked byte-for-byte against the theorem signature, and every source line
is at most 100 characters. No mathematical mismatch was found. Changes:
appended this independent reading and its additional duplicate-candidate audit;
left the correct Lean module and node record unchanged.
