## Worker report

The module `Sheaf.RingTheory.FibreRegularQuotientNeighbourhood` states
`RingTheory.flat_quotient_neighbourhood_of_closedFiber_regular`, with `sorry` as
its entire proof. It introduces no definitions. Only the item's `lean` field
changes; the mathematical statement and all dependency lists remain unchanged.

Source checked: Stacks Project, more-morphisms.tex, Tag 056Y,
`lemma-slice-given-element`, final paragraph. The node isolates its flat-quotient
argument; it does not request the later spreading of the nonzerodivisor itself.
The source uses finite type over Noetherian rings; the node's finite-presentation
form is equivalent in this setting. The seven proof steps are transcribed in the
theorem docstring with the existing DAG dependency names.

Hypotheses and objects, clause by clause:

- The commutative rings A₀ and B₀ are `{A : Type u} {B : Type v}` with
  `[CommRing A] [CommRing B]`. Both universes are explicit and independent.
- The map A₀ → B₀ is represented by `[Algebra A B]` and its `algebraMap A B`.
  This represents every unital map of commutative rings, without imposing
  injectivity or any other condition on that map.
- Flatness is `(hflat : (algebraMap A B).Flat)`, exactly `RingHom.Flat`.
- Finite presentation is `[Algebra.FinitePresentation A B]`.
- Both rings are Noetherian: `[IsNoetherianRing A] [IsNoetherianRing B]`.
- The specified prime is `(q : Ideal B) [q.IsPrime]`.
- Its contraction p₀ is `q.under A`, Mathlib's abbreviation for
  `q.comap (algebraMap A B)`. Its primality is inferred from the primality of q;
  it is not an extra assumption or an independently chosen prime.
- The specified element and its membership are `(a : B) (ha : a ∈ q)`.
- The ring C₀ is precisely
  `Localization.AtPrime q ⧸ (q.under A).map (algebraMap A (Localization.AtPrime q))`.
  The mapped ideal is p₀Bq, with the canonical composite base action.
- The hypothesis `hreg` is `RingTheory.Sequence.IsRegular C₀ [abar]`, where
  `abar` is `Ideal.Quotient.mk` applied to `algebraMap B (Localization.AtPrime q) a`.
  Thus it is regularity of the actual singleton image, including the nonzero
  final quotient condition; it is not merely weak regularity or regularity of a.

Conclusions, clause by clause:

- The first conjunct is `RingHom.Flat` of the composite of
  `Localization.localRingHom (q.under A) q (algebraMap A B) rfl` with
  `Ideal.Quotient.mk (Ideal.span {algebraMap B (Localization.AtPrime q) a})`.
  Its source is exactly Aₚ and its target is exactly Bq/(a/1). The `rfl`
  certifies the definitional identity of the contraction; the scalar map is
  canonical, not an arbitrary structure supplied as a new hypothesis.
- The second conjunct is `Module.Flat A` of this same quotient, with its
  canonical A-action through B and Bq. This is the separate flatness over A₀.
- The third conjunct is `∃ g : B, g ∉ q ∧ Module.Flat A (...)`, with target
  `Localization.Away g ⧸ Ideal.span {algebraMap B (Localization.Away g) a}`.
  This is the requested g₀ outside q₀ and H₀ = (B₀)g₀/(a₀), with the original
  base action. H₀ is written directly instead of quantified with an equality.

Statement dependencies used (all recorded interfaces are usable unchanged):

- `def-weil-pbc-flat-ring-map`: `Mathlib.RingTheory.RingHom.Flat`,
  `RingHom.Flat`; module flatness is `Module.Flat` from `Mathlib.RingTheory.Flat.Basic`.
  Read both definitions and their docstrings.
- `def-weil-pbc-finitely-presented-algebra`: `Mathlib.RingTheory.FinitePresentation`,
  `Algebra.FinitePresentation` (finite polynomial presentation with FG kernel).
- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing` (Noetherian as a module over itself).
- `def-weil-pbc-regular-sequence`: `Mathlib.RingTheory.Regular.RegularSequence`,
  `RingTheory.Sequence.IsRegular`, extending `IsWeaklyRegular` with properness
  of the final generated submodule.
- `def-weil-pbc-localization-at-prime`: `Mathlib.RingTheory.Localization.AtPrime.Basic`,
  `Localization.AtPrime`. The same module supplies `Localization.localRingHom`.
- `def-weil-ring-localization-away`: `Localization.Away`, defined in
  `Mathlib.GroupTheory.MonoidLocalization.Away` and supplied as a ring with its
  canonical algebra by `Mathlib.RingTheory.Localization.Away.Basic`.

Proof dependencies are available through the imports:
`WeilConjectures.RingTheory.RegularSequenceFlatClosedFiber`
(`RingTheory.Sequence.isRegular_and_flat_quotient_of_closedFiber`),
`WeilConjectures.RingTheory.OpenFlatLocus`
(`Module.isOpen_setOf_flat_localizedModule`), and Mathlib's ring-hom flatness,
localization, localization-of-quotient, ideal maps and prime-spectrum topology
APIs. The two upstream theorem signatures and their docstrings were read.
No dependency module or new definition node was needed.

Edge cases checked mathematically before drafting:

- A zero ring B has no prime q; a zero ring A admits no unital map to a nonzero
  B. These cases are handled by the existing prime hypothesis, without adding
  nontriviality assumptions.
- The closed fibre at the contracted prime is nonzero: pBq lies in the maximal
  ideal of Bq. Thus a = 0 fails singleton regularity, as expected. A unit a is
  excluded by a ∈ q; no unit/nonzero assumptions have been added silently.
- For A = ℤ, B = ℤ[t], q = (p,t), both a = t and a = t+p have regular image
  in the closed fibre and give the expected flat quotient. For A = B = k[s,t],
  q = (s,t), a = st fails the fibre regularity hypothesis, so the nonflat
  quotient cannot be inferred. The zero prime over a field has no element
  satisfying the regular singleton hypothesis after localization; the theorem
  is correctly conditional there.
- The ideal notation always generates the ideal of the mapped element in the
  stated localized ring; it never takes a quotient of the base ring instead.
- The element g is quantified in B with g ∉ q, so the neighbourhood contains q;
  neither an empty basic open nor g = 0 can satisfy this condition.

Searches for an existing exact statement:

- `msearch.py` LeanFinder: "A flat finitely presented map of Noetherian rings
  and an element regular in the closed fibre at a prime has flat principal
  quotient on a basic open neighbourhood". Eight hits: localization flatness,
  smoothness neighbourhoods and local criteria; no exact statement.
- `msearch.py` Loogle: `"Flat", "IsRegular"`. Five hits: faithful-flat regular
  sequence base change, regular scalars on flat modules and unrelated category
  declarations; no exact statement.
- `msearch.py` grep in `RingTheory`:
  `flat.*quotient|quotient.*flat|isOpen.*flat`. Zero hits for that expression.
- `msearch.py` LeanSearch: "If a flat finitely presented algebra of Noetherian
  rings has an element regular on a closed fibre at a prime then its principal
  quotient is flat on a neighbourhood of that prime". Eight hits, including
  `RingHom.Flat.localRingHom` and smooth-localization results; none includes
  the principal quotient and the three required conclusions.
- `rg` over both `lean/WeilConjectures/RingTheory` and `lean/Sheaf/RingTheory`:
  `fibreRegular|fiberRegular|flat.*quotient|quotient.*flat|regular.*[Nn]eighbourhood|regular.*[Nn]eighborhood`.
  The closest results were the closed-fibre regular-sequence theorem used for
  the local part and the regular-sequence neighbourhood theorems, which have
  different hypotheses and conclusions. None is this statement.
- Exact item-id search over `lean/WeilConjectures` found no recorded declaration.
  Exact proposed-name search over `dag/lean_names_upstream.json`, Mathlib,
  `lean/WeilConjectures` and `lean/Sheaf` found no declaration-name collision.

Validation: `scompile.py Q65 lem-trf-noetherian-fibre-regular-quotient-neighbourhood`
compiled this delivered module successfully in both the sandbox and library
contexts (3.0 s and 2.8 s); no errors or non-sorry warnings. Every declaration
variable and universe is explicitly bound. No node fault or disputed statement
was found. The prescribed `deliver2.py --no-push` completed successfully: commit
`2c9991b7b66` passed the server preflight and per-file compilation; nothing
was pushed by that dry run.

## Second reading by Q65

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
