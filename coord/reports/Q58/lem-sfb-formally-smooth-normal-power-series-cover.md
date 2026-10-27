## Worker report

The module `Sheaf.RingTheory.FormallySmoothNormalPowerSeriesCover` states
`Algebra.exists_normal_powerSeries_cover_of_formallySmoothAdic`, with `sorry` as its entire
proof. It defines no new notion and constructs no data using a postponed proof. The node is
unchanged except for its `lean` record.

The source is the first paragraph of the proof of EGA IV4 Theorem 21.14.1, read in the online
English translation at https://jcreinhold.github.io/ega/iv/34-ch4-21-divisors.html.
The node already supplies a repaired proof using a completed tensor square in place of the
source's finite coefficient extension. The module docstring follows all seven current DAG
proof steps, including this repair; this delivery does not alter that accepted proof plan.

Every hypothesis and conclusion clause has the following rendering.

| Node clause | Lean rendering |
| --- | --- |
| Commutative Noetherian local rings A and B | `(A : Type u) (B : Type v)`, `[CommRing A] [CommRing B]`, `[IsNoetherianRing A] [IsNoetherianRing B]`, `[IsLocalRing A] [IsLocalRing B]` |
| Specified local homomorphism A to B | `[Algebra A B] [IsLocalHom (algebraMap A B)]`; the algebra structure includes precisely the ring map and its induced scalar action |
| Maximal ideals | `IsLocalRing.maximalIdeal A` and `IsLocalRing.maximalIdeal B` |
| Completed A is a normal domain | `[IsDomain (AdicCompletion (IsLocalRing.maximalIdeal A) A)]` and `[IsIntegrallyClosed (AdicCompletion (IsLocalRing.maximalIdeal A) A)]` |
| Adic formal smoothness for the maximal ideal of B | `hfs : FormallySmoothAdic A B (IsLocalRing.maximalIdeal B)` |
| Strict dimension inequality | `hdim : ringKrullDim A < ringKrullDim B` |
| Induced residue extension is finite | `[Module.Finite (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]`; the algebra on these residue fields is Mathlib's canonical one induced by the given local algebra map |
| p = m_A B is prime | `hp : ((IsLocalRing.maximalIdeal A).map (algebraMap A B)).IsPrime`; p is substituted by its defining ideal throughout |
| Existence of a complete Noetherian normal local coefficient domain C | `∃ (C : Type (max u v)) (_ : CommRing C) (_ : IsLocalRing C), IsNoetherianRing C ∧ IsDomain C ∧ IsIntegrallyClosed C ∧ IsAdicComplete (IsLocalRing.maximalIdeal C) C ∧ ...` |
| Nonnegative integer d and D = C[[T1,...,Td]] | `∃ (d : ℕ) ...`; every occurrence of D is `MvPowerSeries (Fin d) C` |
| Faithfully flat local map iota : B to D | `∃ (_ : Algebra B (MvPowerSeries (Fin d) C)), Module.FaithfullyFlat B (MvPowerSeries (Fin d) C) ∧ IsLocalHom (algebraMap B (MvPowerSeries (Fin d) C)) ∧ ...` |
| D is a Noetherian normal local domain | Explicit conjuncts `IsNoetherianRing`, `IsDomain`, `IsIntegrallyClosed` on `MvPowerSeries (Fin d) C`; its local-ring structure is Mathlib's canonical instance from the existential local-ring structure on C |
| iota inverse image of nD is p | `((IsLocalRing.maximalIdeal C).map (MvPowerSeries.C (σ := Fin d))).comap (algebraMap B (MvPowerSeries (Fin d) C)) = (IsLocalRing.maximalIdeal A).map (algebraMap A B)` |
| Local means contraction of the maximal ideal is the maximal ideal | `IsLocalHom` expresses exactly this between local rings, by `IsLocalRing.local_hom_TFAE` and `IsLocalRing.maximalIdeal_comap`; no extra continuity or residue separability assumption is imposed |

Statement dependency interfaces read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, the module-theoretic condition
  that all ideals are finitely generated.
- `Mathlib.RingTheory.AdicCompletion.Basic`, with ring operations provided by
  `Mathlib.RingTheory.AdicCompletion.Algebra`: `AdicCompletion`, `IsAdicComplete`.
  These serve both def-weil-pbc-adic-completion and def-weil-pbc-adically-complete-ring.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`, paired
  with `IsDomain` as prescribed by def-weil-pbc-normal-ring for normal domains.
- `WeilConjectures.RingTheory.FormallySmoothAdic`: `Algebra.FormallySmoothAdic`, with its
  full lifting predicate over `Type (max u v)` test algebras, not ordinary formal smoothness.
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim` in `WithBot ℕ∞`.
- `Mathlib.RingTheory.MvPowerSeries.Basic`, publicly available through `.Inverse`:
  `MvPowerSeries`, `MvPowerSeries.C`; `.Inverse` supplies the local-ring instance.
- `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`: `Module.FaithfullyFlat` for the exact
  algebra structure existentially specifying iota, as required by the project convention.
- `Mathlib.RingTheory.LocalRing.ResidueField.Basic`: `IsLocalRing.ResidueField` and its
  canonical algebra instance; `algebraMap_residue` identifies this extension map with the
  residue map of A to B. `IsLocalHom` and `IsLocalRing.maximalIdeal_comap` provide locality.

All already-stated proof dependencies are imported with plain `import`: the completion
local-ring and completeness theorems from Mathlib, faithful flatness and ideal contraction
from `Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra`, and the recorded upstream modules
`AdicCompletionNoetherian`, `FormallySmoothAdicCompleteSourceTarget`,
`FormallySmoothCompleteLocalRegular`, `GRing`, `RegularRingNormal`, and
`NormalOfFlatNormalFibers` under `WeilConjectures.RingTheory`.
The two proof-only nodes `lem-sfb-formally-smooth-completed-local-tensor-square` and
`lem-sfb-split-local-power-series-section-criterion` currently have no Lean declaration,
so there is no module to import for either. Neither notion is needed in this statement's
signature; they remain named in the complete proof docstring for stage 3. All eight
statement dependencies have usable interfaces; no dependency module or new node is needed.

Edge cases checked before writing:

- `d = 0` is included by `d : ℕ` and `Fin d`; the empty-variable power-series ring is the
  coefficient ring, as the node requires. No positivity assumption on d was added.
- Local rings here are nontrivial, matching rings with a maximal ideal. Zero rings are
  excluded by locality, not by an accidental extra domain assumption on A or B.
- The dimension comparison is the exact strict comparison of Krull dimensions, not a
  truncated natural-number comparison. No separate finite-dimension restriction is added.
- Finite inseparable residue extensions and mixed characteristic are allowed. No chosen
  coefficient field, separability, equicharacteristic, or characteristic-zero hypothesis occurs.
- A and B have independent universes u and v. The coefficient witness has universe max u v,
  which contains the completed B construction used in the node's proof (up to universe lift).
  Countable sequences and the finite-variable power-series ring remain in this universe.
  There is no quantification over an accidentally too-small test-ring universe.
- The contraction uses the coefficient maximal ideal extended through the canonical constants
  map. It is not the maximal ideal of D (which also contains the variables), nor the extension
  of the maximal ideal of B. The map contracted along is the very same map used for faithful
  flatness and locality.
- The strict dimension and primality hypotheses remain, even though the proof plan says its
  construction works without using them separately. No conclusion stronger than the node
  (such as completeness of D or a specified dimension d) has been added.

Searches performed with `msearch.py Q58 lem-sfb-formally-smooth-normal-power-series-cover`:

- LeanFinder: "A formally smooth Noetherian local algebra over an analytically normal local
  ring has a faithfully flat local cover by power series over a complete normal local domain".
  Eight hits: ordinary smooth/formally-smooth flatness, local flat maps being faithfully flat,
  completion flatness, smoothness definitions, and smooth loci. None gives the asserted
  coefficient domain, power-series cover, or specified ideal contraction.
- LeanSearch: "A formally smooth Noetherian local algebra admits a faithfully flat cover by
  power series over a complete normal local domain". Eight hits, namely ordinary formal
  smoothness, smoothness implying flatness or formal smoothness, the split-surjection
  criterion, smooth loci, and lifting to an adic completion of a kernel. No exact match.
- Loogle: `"FormallySmooth", "IsLocalRing"`. No hits.
- Mathlib grep in RingTheory: `formallySmooth.*(normal|powerSeries)|normal.*formallySmooth|normal.*powerSeries`.
  Two irrelevant hits concerning normalization monoids for ordinary power series, no cover.
- Project `rg` in `lean/WeilConjectures` and `lean/Sheaf` with the same semantic patterns,
  `normalPowerSeries|normal_powerSeries`, and the node id: no matching declaration.
  A broader FormallySmoothAdic search identified the recorded formal-smoothness interface
  and existing related regularity results, none states this cover theorem.

The online EGA source and every recorded statement-dependency signature/docstring were read.
No node fault or statement correction was needed. The sole postponed declaration is
`Algebra.exists_normal_powerSeries_cover_of_formallySmoothAdic`.

Validation: `scompile.py` compiled the module against the current published project both as
its sandbox module and as `Sheaf.RingTheory.FormallySmoothNormalPowerSeriesCover`, with no
errors or non-sorry warnings. The delivery dry run passed preflight and per-file compilation.

## Second reading by Q58

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
