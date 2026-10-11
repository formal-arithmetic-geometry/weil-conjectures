## Worker report

The module `Sheaf.RingTheory.DVRCompletionRegular` states
`AdicCompletion.isRegular_of_dim_one_principal_charZero`, with a single `sorry` proof.
There are no new definitions, dependency modules, or statement corrections.

Hypothesis and conclusion correspondence:

- Commutative ring A: `(A : Type u) [CommRing A]`.
- Noetherian: `[IsNoetherianRing A]`, the recorded declaration of
  `def-weil-pbc-noetherian-ring` in `Mathlib.RingTheory.Noetherian.Defs`.
- Local: `[IsLocalRing A]`; its maximal ideal m is `IsLocalRing.maximalIdeal A`.
- Domain: `[IsDomain A]`.
- Krull dimension one: `(hdim : ringKrullDim A = 1)`.
- Principal maximal ideal: `(hprincipal : (IsLocalRing.maximalIdeal A).IsPrincipal)`.
  These explicit hypotheses render the node's stated characterization of a DVR; no
  additional valuation, PID, or normality hypothesis is imposed.
- Fraction field K: `(K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]`.
  `IsFractionRing` is Mathlib's localization at the non-zero-divisors, which for this
  domain is its fraction field. The algebra instance specifies its canonical inclusion.
- Characteristic zero of K: `[CharZero K]`.
- Completion: `AdicCompletion (IsLocalRing.maximalIdeal A) A`, using the recorded
  `AdicCompletion` of `def-weil-pbc-adic-completion` in
  `Mathlib.RingTheory.AdicCompletion.Basic`. Its ring and algebra structures are in
  `Mathlib.RingTheory.AdicCompletion.Algebra`, imported through GRing.
- Canonical ring map: `algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)`.
  Reading the algebra instance and `AdicCompletion.algebraMap_apply` confirms that this
  sends each a to its compatible system of residue classes modulo m^n.
- Regularity: `RingHom.IsRegular` of that map, the companion declaration recorded for
  `def-weil-pbc-g-ring` in `Sheaf.RingTheory.GRing`. Reading this definition confirms
  flatness and Noetherian geometrically regular fibres at every prime. Its definition
  uses `Algebra.IsGeometricallyRegular`, including the Noetherian condition, so neither
  flatness nor any fibre clause is omitted.

All universes and variables are explicit. The docstring carries all seven proof steps
and the supporting node identifiers. No supporting theorem is proved in this stage.

Edge cases checked: dimension one excludes fields and the zero maximal ideal; the
zero ring is excluded by `IsDomain`, as in the node. Mixed-characteristic DVRs are
included: only K is required to have characteristic zero, and the residue field may
have positive characteristic. No completeness assumption is made on A. Both complete
and noncomplete DVRs are allowed, and there is no restriction on the size or characteristic
of the residue field. Independent universes u and v allow arbitrary fraction-field models;
the conclusion concerns only A and its completion.

Sources read: the repository has no local `literature/stacks-project/more-algebra.tex`,
so the Stacks pages were opened online:
https://stacks.math.columbia.edu/tag/07PX and
https://stacks.math.columbia.edu/tag/00PD.
07PX's proof treats the characteristic-zero Dedekind/DVR case via completion being a DVR;
00PD gives the Noetherian local-domain/nonzero-principal-maximal-ideal characterization.
The node's dimension-one condition rules out the zero generator. No statement fault found.

Searches (msearch.py H1 lem-weil-pbc-dvr-completion-regular):

- leanfinder: `A discrete valuation ring with characteristic zero fraction field has regular
  canonical map to its maximal ideal adic completion`: eight hits, concerning valuation
  subrings of Dedekind fraction-field completions and locality of adically complete rings;
  none states regularity of this ring map.
- loogle: `AdicCompletion, RingHom.IsRegular`: zero hits; unknown identifier
  `RingHom.IsRegular` (this predicate is defined by the project's GRing module).
- grep: `IsRegular|regular.*completion|completion.*regular` in
  `RingTheory/AdicCompletion`: zero hits.
- leansearch: `The completion homomorphism of a characteristic zero discrete valuation ring
  is a regular ring map`: service unavailable, Internal Server Error; no result available.
- rg over `WeilConjectures` and `lean/Sheaf`:
  `regular.*(completion|Completion)|completion.*regular|lem-weil-pbc-dvr-completion-regular`:
  no source-repository match; project hits concern regular local rings, completion of DVRs,
  and G-rings, rather than this regular-map theorem. Each relevant GRing and CompletionOfDVR
  declaration was read; neither already states this item.
- grep -rn of the exact item id in `WeilConjectures`: no hits.
- rg of `IsRegular|GRing|completion.*regular` in `dag/lean_names_upstream.json`:
  only unrelated regular-immersion/regular-local declarations, no matching theorem.
- The chosen full name was checked against Mathlib, WeilConjectures and lean/Sheaf: absent.

Validation: server single-file compilation and `deliver2.py --no-push` are run for this
sandbox. The independent second reading is left to the second worker, as requested.

## Second reading by H1

Independent review of the node copy, its original repository node, the theorem module,
and the three statement-dependency nodes and their declaration sources. No mismatch
found; the Lean module and node signature were left unchanged.

Object/hypothesis/conclusion checklist (each verdict: exact):

- A commutative ring: `(A : Type u) [CommRing A]`.
- A Noetherian ring: `[IsNoetherianRing A]`. Opened the dependency
  `def-weil-pbc-noetherian-ring` and Mathlib `Noetherian/Defs.lean`: the abbreviation
  is `IsNoetherian A A`, equivalently every ideal is finitely generated.
- A local ring and its maximal ideal m: `[IsLocalRing A]` and
  `IsLocalRing.maximalIdeal A`; no separate choice of ideal is introduced.
- A domain: `[IsDomain A]`; this includes nontriviality as the source requires.
- Dimension one: `hdim : ringKrullDim A = 1`. Opened `KrullDimension/Basic.lean`:
  this is the order Krull dimension of `PrimeSpectrum A`, not a dimension bound.
- Principal maximal ideal: `hprincipal : (IsLocalRing.maximalIdeal A).IsPrincipal`.
  Together with the preceding conditions this is precisely the node's DVR
  characterization; no valuation structure or normality assumption was added.
- Fraction field K: `(K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]`.
  Opened `Localization/FractionRing.lean`: `IsFractionRing` is localization at
  `nonZeroDivisors A`, hence the fraction field for this domain. The algebra structure
  is constrained by this localization, not an arbitrary extra field extension.
- Characteristic zero of K: `[CharZero K]`, without a condition on the residue field.
- Completion A-hat: `AdicCompletion (IsLocalRing.maximalIdeal A) A`.
  Opened `def-weil-pbc-adic-completion` and `AdicCompletion/Basic.lean` and
  `Algebra.lean`: the compatible sequences modulo `m ^ n • ⊤` are the inverse
  limit modulo `m ^ n` for the ring regarded as its own module.
- Canonical ring map: `algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)`.
  The algebra instance and `AdicCompletion.algebraMap_apply` identify this with
  `AdicCompletion.of`, the residue-class sequence of each a.
- Conclusion: `RingHom.IsRegular` of precisely that map. Opened
  `def-weil-pbc-g-ring` and `Sheaf.RingTheory.GRing`: its companion predicate uses
  the map's own algebra structure, requires flatness, and quantifies over every
  prime ideal with `Algebra.IsGeometricallyRegular p.ResidueField (p.Fiber S)`.
  The latter includes Noetherianity and regularity after every finite purely
  inseparable field extension. Opened Mathlib `ResidueField/Fiber.lean`:
  `p.Fiber S` is `p.ResidueField ⊗[A] S`; swapping tensor factors gives the node's
  written order, with the same residue-field algebra structure. Thus all clauses
  and quantifiers agree, including fibre Noetherianity.

Source check: local Stacks .tex files are absent. Read the actual upstream .tex
at https://raw.githubusercontent.com/stacks/stacks-project/master/more-algebra.tex
(label `proposition-ubiquity-G-ring`) and `algebra.tex` (label
`lemma-characterize-dvr`), as well as Stacks tags
https://stacks.math.columbia.edu/tag/07PX,
https://stacks.math.columbia.edu/tag/00PD, and
https://stacks.math.columbia.edu/tag/07BZ.
07PX treats Dedekind domains with characteristic-zero fraction field and uses
completion of DVRs. 00PD identifies Noetherian local domains with nonzero principal
maximal ideal as DVRs, equivalently regular local rings of dimension one. The node's
explicit dimension-one condition supplies nonzeroness; no source-wide extra
hypothesis is missing. 07BZ agrees with the recorded regular-map predicate.

Edge cases: zero rings are excluded by `IsDomain`; fields and zero maximal ideals
are excluded by dimension one. No completeness of A is assumed. Mixed characteristic
and arbitrary residue fields are included. The inverse limit includes n = 0; its
zero quotient component imposes no extra restriction. There is no free index set,
scheme, or module whose emptiness needs an additional check. Explicit universes u
and v allow arbitrary ring and fraction-field models. The dependency's extensions
in universe `max u v` cover finite extensions by transport to a small isomorphic
model; this is not a finiteness or cardinality restriction on the rings.

Independent searches (different wording from the first worker):

- `msearch.py ... leanfinder "Formal fibres of a discrete valuation ring with
  fraction field of characteristic zero are geometrically regular"`: eight hits.
  DVR TFAE and cotangent-space criteria, Dedekind localizations, and formally
  unramified algebra statements; none states regularity of the completion map.
- `msearch.py ... loogle "AdicCompletion, IsDiscreteValuationRing"`: zero hits.
- `msearch.py ... leansearch "The formal fibres of a discrete valuation ring in
  characteristic zero are geometrically regular"`: unavailable, Internal Server
  Error; no negative mathematical verdict inferred from the failed service.
- `rg -n -i` over Mathlib RingTheory, WeilConjectures, repository lean/Sheaf,
  and dag/lean_names_upstream.json for `geometrically.?regular`,
  `formal.?fi[bv]res`, the exact full theorem name, and regularity within thirty
  characters of adic/completion: no exact theorem. Opened project
  `CompletionOfDVR.lean`, `CompletionRegularLocal.lean`, `CompleteLocalGRing.lean`
  and `GRing.lean`: they state completion is a DVR, regular local equivalence,
  complete local G-rings, and the predicates, respectively, not this item.

H4/H5/H6/H8/H9 review: existing dependency notions are used without private copies;
there are no new definition nodes or dependency modules to audit. No hollow data
or proved theorem occurs: the single named theorem has `by sorry`. Its docstring
contains the source, blueprint id and all seven node proof steps with their
supporting nodes. Imports supply the predicate, dimension, and fraction-field
notions; namespaces, header and line lengths follow project conventions. All
variables and universes are bound. The node's `lean.statement` is verbatim the
signature in the module. There is no statement correction or citer change.

Changes: appended this independent review only; no mathematical or Lean repairs
were needed. Validation: server single-file compile, delivery dry run, and delivery
are recorded by their tool outputs.

## Reviewer fix (R-dcr0949, stage 2)

The DVR hypothesis is restated in the project's form for discrete valuation rings,
`[IsDomain A] [IsDiscreteValuationRing A]` (STATE; as in the landed sibling
`AdicCompletion.isDiscreteValuationRing` of lem-weil-pbc-completion-of-dvr-is-dvr, whose
inline 00PD characterization was fixed the same way), replacing the inline
`[IsNoetherianRing A] [IsLocalRing A] [IsDomain A] (hdim : ringKrullDim A = 1)
(hprincipal : (maximalIdeal A).IsPrincipal)`. Mathematically the same class (Stacks 00PD:
a Noetherian local domain of dimension one with principal maximal ideal is exactly a DVR;
Mathlib's DVR is a local PID that is not a field). The theorem is renamed
`AdicCompletion.isRegular_algebraMap_of_isDiscreteValuationRing_of_charZero`. Fraction field,
characteristic zero, completion and `RingHom.IsRegular` conclusion are unchanged.
