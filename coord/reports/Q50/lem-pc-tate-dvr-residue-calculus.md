## Worker report

The delivery states `TateResidue.dvr_residue_calculus` in
`Sheaf.RingTheory.TateResidue.DVRResidueCalculus`. Its only postponed proof is the whole
named theorem, with all eleven DAG proof steps in its docstring. The node's statement,
proof and proof dependencies are unchanged. One definition node supplies the precise
meaning of a compatible completed Laurent coordinate. No dependency module or private
copy of a notion is introduced.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

* The fields k ⊂ K are `(k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]`.
  The field algebra map is injective. Independent universes u and v remain independent.
* The subring containing k is `(O : Subalgebra k K)`. The instances
  `[IsDiscreteValuationRing O] [IsFractionRing O K]` express exactly the DVR and
  fraction-field conditions. Its domain instance follows from the subalgebra of K.
* κ is `IsLocalRing.ResidueField O`, literally O modulo its maximal ideal, with its
  canonical k-algebra structure. `[FiniteDimensional k (IsLocalRing.ResidueField O)]`
  is precisely finiteness of this residue extension.
* The quotient (fO+O)/O is represented by the image
  `(O.toSubmodule.map (act k f)).map O.toSubmodule.mkQ` in K/O. This is the actual
  principal-parts subspace, canonically isomorphic to that quotient. The first
  conjunct states its finite dimensionality for EVERY f, including zero.
* A projection is `π : K →ₗ[k] O` with `∀ x : O, π (x : K) = x`. The inclusion
  `O.val.toLinearMap.comp π` converts this retraction into an endomorphism of K.
  `act k f` is the existing multiplication endomorphism. Multiplication of these
  endomorphisms is composition, giving exactly [π m_f,m_g] with AB-BA sign.
* `Module.End.IsFinitePotent` and `Module.End.tateTrace` are reused from upstream
  `WeilConjectures.RingTheory.TateResidue.FinitePotent`, not copied. The definition
  of finite-potency permits n=0; this is equivalent to the node's N≥1, since the
  range of T is finite-dimensional whenever the whole space is. On a finite-potent
  map, tateTrace is an actual construction using the least power with finite range.
  `Module.End.tateTrace_eq_trace_restrict` gives exactly the node's characterization
  for EVERY finite-dimensional stable U containing the range of ANY power; hence
  independence of power and finite-dimensional subspace is already provided by this
  imported theorem. Its signature was read in full, as were the definition and
  other finite-potent trace properties. No new trace scalar is chosen.
* The second conjunct says the displayed commutator is finite-potent and that its
  tateTrace is `localRes O (f • KaehlerDifferential.D k K g)`, for every projection
  π and every f,g. The existing `localRes O : Ω[K/k] →ₗ[k] k` is the required extension.
  It is defined through the universal property of differentials. Because the same
  map appears for every π, the formula explicitly establishes projection independence.
* The third conjunct is `∀ ω : KaehlerDifferential k O, localRes O
  (KaehlerDifferential.map k k O K ω) = 0`, exactly annihilation of regular differentials.
* A uniformizer is written `t : O` with `maximalIdeal O = Ideal.span {t}`. For each
  `a : O`, the fourth conjunct is res((a/t) dt) = `Algebra.trace k κ (residue O a)`.
  There is NO separability restriction on this normalization.
* Only the last conjunct assumes `Algebra.IsSeparable k κ`. For EVERY uniformizer
  it asserts `Nonempty (DVRLaurentCoordinates O t)`. This includes the completion
  isomorphism, normalization on t, residue compatibility, and its extension to K.
* For EVERY such coordinate c, it supplies a k-linear differential coefficient map d
  with `d (f • D g) = c.fieldMap f * LaurentSeries.derivative κ (c.fieldMap g)`
  for ALL f,g. This pins down d uniquely, since the f dg generate Ω[K/k] over k.
  It is therefore the image in the continuous Laurent differential module κ((T)) dT,
  where dT is represented by 1; no arbitrary differential comparison is substituted.
  The final quantified equality for EVERY ξ is
  `localRes O ξ = Algebra.trace k κ ((d ξ).coeff (-1))`.
  Existence of d is a conclusion, not a new hypothesis. It prevents vacuous use of
  an unspecified continuous differential map. Universality also makes the result
  independent of any representative or presentation of ξ.

Dependency declarations and source reading:

* `Mathlib.RingTheory.Kaehler.Basic`: `KaehlerDifferential`, `KaehlerDifferential.D`,
  `KaehlerDifferential.linearMapEquivDerivation`, and `KaehlerDifferential.map`; read
  their full definitions, docstrings, and map_D. These give the recorded differentials
  dependency and its canonical map from O to K.
* `Mathlib.RingTheory.DiscreteValuationRing.Basic`: `IsDiscreteValuationRing` and
  `IsDiscreteValuationRing.irreducible_iff_uniformizer`. The class includes local PID
  and nonzero maximal ideal, in addition to the domain instance, as the node requires.
* `Mathlib.LinearAlgebra.FiniteDimensional.Defs`: `FiniteDimensional`, the abbreviation
  for `Module.Finite`; `Mathlib.LinearAlgebra.Trace`: `LinearMap.trace` (basis-independent).
* `Mathlib.RingTheory.AdicCompletion.Basic` and `.Algebra`: `AdicCompletion`,
  its compatible-sequence definition, canonical algebra map and `AdicCompletion.evalOneₐ`.
* `Mathlib.RingTheory.LaurentSeries`: `LaurentSeries`, its `derivative`, and coefficient
  formula for derivatives. `Mathlib.RingTheory.HahnSeries.PowerSeries`:
  `HahnSeries.ofPowerSeries`. These are the recorded Laurent-series dependency.
* `Mathlib.FieldTheory.Separable`: `Algebra.IsSeparable`, with the built-in algebraicity
  explained by `Algebra.IsSeparable.isAlgebraic`.
* The upstream modules `FinitePotent`, `TateIdeals`, `Residue`, `ResidueProperties`,
  and `LocalResidue` were opened. `Module.End.tateTrace_eq_trace_restrict`,
  `TateResidue.E`, E₁, E₂, `TateResidue.Admissible`, `TateResidue.act`,
  `TateResidue.res`, `TateResidue.localRes`, `TateResidue.localRes_map_eq_zero`, and
  `TateResidue.localRes_mul_inv_smul_D` are reused, transitively imported publicly by
  LocalResidue. In particular the unrecorded proof nodes about trace and ideals do
  NOT require inventing these notions: upstream already supplies them. The existing
  local normalization uses O/(t), while this statement has the canonically identical
  residue-field quotient. Upstream lacks the full separable Laurent comparison, so
  there is no exact existing declaration for the complete item.
* Proof imports include `Mathlib.RingTheory.AdicCompletion.LocalRing`
  (`AdicCompletion.isAdicComplete_self`), `.Completeness`
  (`pow_smul_top_eq_ker_eval`, `ker_evalOneₐ_eq_map`), `Mathlib.RingTheory.Henselian`
  (`IsAdicComplete.henselianRing`), and
  `Sheaf.RingTheory.HenselianSeparablyGeneratedResidueSection`
  (`Algebra.exists_section_of_separating_family`). The recorded signatures were read.
  The latter has a one-universe signature; the statement here DOES NOT impose that
  restriction: its proof can lift the fields/rings to a common maximum universe.
* The node's other proof dependency, unit-times-uniformizer-power, is
  `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible`, in the public DVR import.

Sources were read in the local Tate PDF using pdftotext, pp.149–155, including §1's
trace characterization, Propositions 1–2, Theorem 1, formula (*), R2, R4 and Theorem 2;
the current blueprint unit sk-thm-picard-duality was read for the finite separable
coefficient-field comparison. The item supplies the detailed completion argument and
finite-strip coefficient calculation for that extension of Tate's rational-point case.

Edge cases checked before and during writing: f=0 and g=0 give zero commutators;
f,g∈O give regular differentials; a=0 normalizes to zero; t=0 cannot generate the
nonzero DVR maximal ideal; both positive and zero characteristic are admitted; finite
inseparable κ/k is retained in all clauses preceding the last; κ=k gives the ordinary
coefficient -1 formula with positive sign res(t⁻¹dt)=1. The derivative uses the integer
coefficient in κ, so characteristic-p cancellation is respected. No finite-type or
perfectness condition on k or K was added. Arbitrary-dimensional trace uses the
existing definition and characterization without assuming the ambient space finite.

Searches actually executed through msearch.py (all successful):

* leanfinder: “Tate residue of Kahler differentials of a discrete valuation field via
  finite potent commutator trace”: eight hits on cotangent dimensions, residue maps,
  valuations and generators; no full residue calculus match.
* loogle: `LinearMap.trace, KaehlerDifferential, LaurentSeries`: zero hits.
* grep: `finite.?[Pp]otent|[Tt]ate[Rr]esidue|[Cc]ontinuous[Dd]ifferential`: zero Mathlib hits.
* leansearch: “A discrete valuation ring completion with separable residue field has
  compatible Laurent series coordinates and continuous differential map”: eight hits,
  principally LaurentSeriesPkg and completion of RatFunc; no general DVR coordinate.
* loogle: `"LaurentSeries.derivative"`: five hits, including the existing derivative
  and its coefficient/iterate/map lemmas. The derivative is reused directly.
* grep in Mathlib RingTheory:
  `DVRLaurent|LaurentCoordinates|coefficient.?field|continuous.*[Dd]ifferential`: zero hits.
* rg and the node-id grep in upstream found the actual TateResidue modules; these
  were opened and reused. rg in Sheaf found continuous ADIC differentials and formal
  presentations, neither the Laurent coordinate structure needed here. DAG grep and
  blueprint_refs.py search Laurent found no existing coordinate notion. The formal
  presentation structure permits several variables, relations and a surjection,
  rather than the specified normalized DVR isomorphism with fraction-field extension.

Validation: both modules compiled through scompile.py against the published library,
with no errors or warnings. The final delivery dry run also compiles each delivered
module separately. No global build or direct edits/Git commands in the shared clone.
No statement correction or STATEMENT-DISPUTED issue was necessary.

## New nodes

`def-pc-dvr-laurent-coordinates` introduces `TateResidue.DVRLaurentCoordinates`: the
actual completion algebra equivalence normalized at the uniformizer, reduction as
constant coefficient, and the compatible fraction-field algebra map. Source: Tate §3,
Theorems 2 and 4, and the completion construction in item proof steps 7–11. The source
of the coefficient-field identification is the power-series constants under the inverse
equivalence; its section property follows from residue_eq. All fields are actual data
or their compatibility propositions; there is no sorry, choice, extra axiom or abstract
existence substituted for a construction. Its existence is the item's theorem conclusion.
The searches above found none of this bundled coordinate data in Mathlib, upstream,
Sheaf, the DAG or blueprint. It reuses all basic notions, in particular the canonical
AdicCompletion and LaurentSeries inclusion, and is cited in the item's stmt_deps.

## Second reading by Q50

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
