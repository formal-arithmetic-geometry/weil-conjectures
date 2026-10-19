## Worker report

Group N9, stage 2, item `lem-per-mixed-reduced-special-fibre-cover`.

The module `Sheaf.RingTheory.MixedReducedSpecialFibreCover` states
`IsLocalRing.exists_mixed_reduced_special_fibre_cover`, with its sole proof `sorry`.
It defines no additional notion. The node copy changes only `lean`.

The preceding worker's stale-queue report concerned the reviewed stage-1 split.
I read the current item and Q83 report: Q83 supplied a proof plan, not a Lean
statement; the item is `split` and has no `lean` record. This delivery formalizes
that existing split and does not resplit it.

I read the source PDF, via a sandbox text extraction, Exposé IV 4.1.7–4.1.9 and
4.2.1–4.2.5, especially the normalized Epp base change of 4.2.3, reducedness lemma
4.2.4, and component and dimension assertions in 4.2.5. The node matches the
reduced-fibre preparation. No statement correction or dispute is needed.

The clause-by-clause correspondence is:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Commutative local ring `(A,m)` | `(A : Type u) [CommRing A] [IsLocalRing A]`; `m = maximalIdeal A` |
| Noetherian | `[IsNoetherianRing A]` |
| Complete | `[IsAdicComplete (maximalIdeal A) A]` |
| Normal domain | `[IsDomain A] [IsIntegrallyClosed A]` |
| Mixed characteristic `(0,p)` | `[CharZero A]`, `(p : ℕ) (hp : p.Prime)`, `hres : ringChar (ResidueField A) = p` |
| Dimension `d ≥ 2` | `(d : ℕ) (hd : 2 ≤ d) (hdim : ringKrullDim A = (d : WithBot ℕ∞))` |
| Existence of a complete DVR `W` | `∃ (W : Type u) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : IsAdicComplete (maximalIdeal W) W), ...` |
| `W` has mixed characteristic `(0,p)` | Existential `CharZero W` witness and `ringChar (ResidueField W) = p` |
| Perfect residue field `k₀` | `k₀` is the actual quotient `ResidueField W`; `PerfectField (ResidueField W)` |
| Uniformizer `π ∈ W` | `∃ π : W, maximalIdeal W = Ideal.span {π} ∧ ...` |
| Complete Noetherian normal local domain `(C,n)` | Existential `C : Type u`, `CommRing C`, `IsNoetherianRing C`, `IsLocalRing C`, `IsDomain C`, `IsIntegrallyClosed C`, `IsAdicComplete (maximalIdeal C) C` witnesses |
| Injective local map `A ↪ C` | `(ι : A →+* C) (_ : IsLocalHom ι)` and `Function.Injective ι` |
| `C` finite as an `A`-module along that map | `ι.Finite`, definitionally `Module.Finite A C` for `ι.toAlgebra` |
| Injective local map `W ↪ C` | `(γ : W →+* C) (_ : IsLocalHom γ)` and `Function.Injective γ` |
| Special fibre `C/πC` | The actual ring `C ⧸ Ideal.span {γ π}` |
| Reduced special fibre | `IsReduced (C ⧸ Ideal.span {γ π})` |
| Dimension `d-1` of the special fibre | `ringKrullDim (C ⧸ Ideal.span {γ π}) = ((d - 1 : ℕ) : WithBot ℕ∞)` |
| Equidimensional of that dimension | For each `Q : Ideal (C ⧸ Ideal.span {γ π})` in `minimalPrimes` of this ring, `ringKrullDim ((C ⧸ Ideal.span {γ π}) ⧸ Q) = ((d - 1 : ℕ) : WithBot ℕ∞)` |
| Residue field `k' = C/n` finite over `A/m` | `k'` is the actual `ResidueField C`; `(ResidueField.map ι).Finite` |
| Its specified inclusion of `k₀` | The canonical ring homomorphism `ResidueField.map γ : ResidueField W →+* ResidueField C`, determined by the returned local map `γ`; not an unrelated field map |
| `dim C = d` | `ringKrullDim C = (d : WithBot ℕ∞)` |

The residue-field maps have the exact compatibility
`(ResidueField.map f).comp (residue _) = (residue _).comp f`
by Mathlib's `IsLocalRing.ResidueField.map_comp_residue`. Thus no arbitrary
residue algebra structure or residue-field identification is substituted. A
ring homomorphism from a field into a field is injective, so the canonical map
from `k₀` is precisely the specified inclusion, without an extra redundant
injectivity conjunct.

### Dependency declarations used

I opened the recorded source signatures and docstrings for all six statement
dependencies and reused them directly:

- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing`, the abbreviation `IsNoetherian A A`.
- `def-weil-pbc-adically-complete-ring`:
  `Mathlib.RingTheory.AdicCompletion.Basic`, `IsAdicComplete`; the equivalence
  `AdicCompletion.of_bijective_iff` confirms that it includes separatedness and
  bijectivity of the canonical completion map.
- `def-weil-pbc-normal-ring`:
  `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`, `IsIntegrallyClosed`,
  used together with `IsDomain` as explicitly required for a normal domain.
- `def-weil-pbc-krull-dimension-ring`:
  `Mathlib.RingTheory.KrullDimension.Basic`, `ringKrullDim : WithBot ℕ∞`.
- `def-sc-discrete-valuation-ring`: its Mathlib match
  `Mathlib.RingTheory.DiscreteValuationRing.Basic`, `IsDiscreteValuationRing`,
  extends local PID and excludes fields. Its `irreducible_iff_uniformizer`
  confirms the exact maximal-ideal-generator formulation used here.
- `def-weil-finitely-generated-module`:
  `Mathlib.RingTheory.Finiteness.Defs`, `Module.Finite`; the same module's
  `RingHom.Finite` installs exactly the module structure induced by the named
  map. This applies both to `ι` and its canonical residue-field map.

Additional Mathlib notions are reused without copies:
`IsLocalRing.ResidueField` and `.map` in
`Mathlib.RingTheory.LocalRing.ResidueField.Basic`, `PerfectField` in
`Mathlib.FieldTheory.Perfect`, `minimalPrimes` in
`Mathlib.RingTheory.Ideal.MinimalPrime.Basic`, and `IsReduced` from Mathlib.
The six dependency modules are public imports. Every already stated proof
dependency is imported through its recorded source module or Mathlib match;
proof-only imports are nonpublic. The two Epp inputs
`lem-per-epp-perfect-core-complete-local` and `lem-per-epp-finite-family-traits`
currently have no declaration and no Mathlib match. Their future modules cannot
yet be imported; their full intended uses are retained in the theorem's ten-step
proof docstring. They are proof dependencies, not missing notions in this statement.

### Edge cases

- At `d = 2`, the dimension of each component and of the special fibre is one.
  The subtraction is explicitly natural subtraction inside the dimension cast;
  `hd` excludes the truncation cases `d = 0,1` exactly as the node does.
- `hp` excludes `p = 0,1` and includes `p = 2`. Characteristic zero of `A`
  and characteristic `p` of its residue field express genuinely mixed
  characteristic. No perfectness of `ResidueField A` is assumed.
- A DVR has nonzero maximal ideal, so its specified generator is nonzero and a
  nonunit. The returned injective local map `γ` makes `γ π` nonzero and a
  nonunit in `C`. Thus the special fibre is a nonzero quotient, not the zero
  ring arising from an inverted or zero uniformizer.
- `C` is required to be a domain; it is a component of the normalization, not
  the generally disconnected whole finite normalization.
- The finite extension of the original residue field may be inseparable.
  `k'/k₀` need not be finite, and `k/k₀` may be imperfect or transcendental.
  Neither a separability assumption nor finiteness over `k₀` is inserted.
- Equidimensionality quantifies over all minimal primes of the actual quotient;
  it does not require that the special fibre be a domain.
- All universes and variables are explicit, with `autoImplicit false`.
  Existential `W,C : Type u` loses no case: `C` is finite as an `A`-module
  and `W` embeds in it, so both admit carriers in `A`'s universe. There is
  no quantification over test rings in a possibly smaller independent universe.

### Searches

All service searches were actually run with
`python3 /home/ubuntu/weil-launcher-nt/msearch.py N9 lem-per-mixed-reduced-special-fibre-cover`:

- `leanfinder`: `A complete noetherian normal local domain of mixed characteristic admits a finite injective local extension with reduced equidimensional special fibre over a complete discrete valuation ring with perfect residue field`.
  Eight hits: DVR characterization, Henselianity, polynomial étale lifting,
  and ordinary unramified/quasi-finite residue-field results. None constructs
  the Epp cover, coefficient DVR, and reduced equidimensional special fibre.
- `loogle`: `IsDiscreteValuationRing, IsReduced`. Zero hits.
- `grep`: `Epp|mixed.*[Cc]haracteristic|reduced.*[Ss]pecial`, restricted to
  `RingTheory`. Four irrelevant hits, three for the variable `ePp` in
  `Flat.Equalizer` and one in `Smooth.Fiber`.
- `leansearch`: `Epp elimination of ramification finite extension complete local ring reduced special fiber`.
  Eight hits about formal unramifiedness, residue fields and ramification
  indices; none is this simultaneous finite-cover theorem.

Direct `rg` searches of `WeilConjectures` and side `lean/Sheaf` used
`Epp|epp_|mixed.*[Rr]educed|mixed.*[Ff]ibre` and the exact blueprint id.
No exact declaration was found. The parent
`Sheaf.RingTheory.CohenGabberFinitePresentations` mentions this input in its
proof plan but states the later power-series presentation, which is a different
conclusion. The coefficient-DVR module likewise starts from an already given
coefficient trait and does not construct this cover.
`dag/lean_names_upstream.json` has no `mixed_reduced_special_fibre_cover` or
`MixedReducedSpecialFibreCover` declaration. Mathlib and project source
inspection supplied every notion needed, so no new definition node is necessary.

### Validation

The prescribed `scompile.py` compiled both its sandbox and library-name checks
cleanly, in 2.6 and 2.5 seconds. No compiler warning was emitted. The module has
one theorem, one expected `sorry`, and no definition or proof needing a helper.
The JSON signature was extracted verbatim from the theorem keyword through the
signature preceding `:=`; JSON uses indent 1, Unicode, and a final newline.
The official delivery dry run is the next gate.

## Second reading by N9

I made a separate second pass with the natural-language node, ILO source, and
final Lean file open. This is a second pass by the same worker; the dispatcher
forbids starting other agents, and the maintainer supplies independent review.

The six input conditions correspond exactly to the binders above: completeness
uses the maximal ideal, normality is normal-domain normality, mixed
characteristic includes the prime residue characteristic, and finite dimension
and the lower bound are both hypotheses. On the output, I checked that
`IsDiscreteValuationRing W` supplies the local structure before completeness and
residue fields are elaborated; `CharZero W`, residue characteristic `p` and
perfect residue field are all present. The chosen `π` generates the actual
maximal ideal. Every local map's `IsLocalHom` witness is bound before its
canonical residue map is used. The same `ι` supplies injectivity, module
finiteness, and the finite residue extension; the same `γ` supplies the image
of `π` in the quotient and the specified residue inclusion. `C` retains
Noetherianity, completeness, normality, locality and dimension `d`. Reducedness,
quotient dimension, and all component dimensions are asserted for the same
special-fibre ring. No mismatch or silently added hypothesis was found, and no
statement correction was made. The proof docstring retains all ten DAG steps;
only the proof is postponed.
