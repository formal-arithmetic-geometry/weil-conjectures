## Worker report

The module `Sheaf.RingTheory.RegularMapReducedTarget` states
`RingHom.isReduced_of_isRegular`, with `sorry` as its whole proof. No definition is
introduced and nothing is proved. The item is unchanged outside its new `lean` record.

The previous worker's unchanged-node failure arose from treating Q19's stage-1 split as a
stage-2 completion. The shared node has no `lean` record; Q19's report contains a proof split,
not a Lean statement. This delivery supplies the missing stage-2 declaration.

Statement correspondence, checked against the full node and
[Stacks Tag 07QK](https://stacks.math.columbia.edu/tag/07QK):

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Arbitrary commutative rings A and B | `{A : Type u} {B : Type v} [CommRing A] [CommRing B]` |
| Both rings Noetherian | `[IsNoetherianRing A] [IsNoetherianRing B]` |
| A is reduced, every nilpotent is zero | `[IsReduced A]` |
| A ring homomorphism φ : A → B | `(φ : A →+* B)` |
| φ is regular | `(hφ : φ.IsRegular)` |
| B is reduced, every nilpotent is zero | `IsReduced B` |

All universes and variables are explicitly bound. The source and target universes are
independent. There is no Nontrivial, domain, local, finite-type, smoothness, or injectivity
assumption. `IsReduced` in Mathlib's `Algebra.GroupWithZero.Basic` means precisely that every
nilpotent element is zero; it is reused rather than copied.

Statement dependencies used:

- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing`. Read its signature and docstring: Noetherian as a module over itself,
  equivalently every ideal finitely generated.
- `def-weil-pbc-g-ring`: `Sheaf.RingTheory.GRing`, `RingHom.IsRegular`, one of the dependency's
  explicitly recorded declarations. Read the complete local module and confirmed the current
  source through `scompile.py --source Sheaf.RingTheory.GRing`. Its argument is the arbitrary
  ring homomorphism; its body uses precisely that homomorphism's algebra structure. It asserts
  flatness and geometric regularity of every residue-field fibre. The geometric-regularity
  predicate includes fibre Noetherianity and tests all finite purely inseparable extensions.
  The larger G-ring predicate in that module is not used as a substitute for regularity.

Proof dependencies are imported as ordinary imports, preserving the DAG's five-step proof
plan for stage 3. `Mathlib.RingTheory.RegularLocalRing.Defs` supplies the ring clauses of
`def-weil-regular-scheme` (`IsRegularRing`, `IsRegularLocalRing`).
`WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs` supplies
`IsRegularLocalRing.isDomain` for `lem-sc-regular-local-domain`.
`Mathlib.RingTheory.Spectrum.Maximal.Localization` supplies
`PrimeSpectrum.toPiLocalization_injective` for
`lem-weil-pbc-prime-localizations-jointly-injective`, whose reducedness clause is its stated
elementary consequence. The remaining recorded modules and declarations are
`Sheaf.RingTheory.SerreCriterionReduced` /
`Ring.isReduced_iff_serreR_zero_and_serreS_one`,
`Sheaf.RingTheory.RegularityRkGoesUp` / `RingHom.regularity_rk_goes_up`, and
`Sheaf.RingTheory.SerreSkGoesUp` / `RingHom.isSerreS_of_flat`.
Their declarations and proof docstrings were opened. The item docstring reproduces the
full five-step natural-language proof: regular fibres give prime-local domains and hence
reduced fibres; Serre's criterion supplies R_0 and S_1 for source and fibres; the two ascent
lemmas supply both conditions on the target; the converse criterion gives reducedness.
No missing dependency interface or helper is needed.

Edge cases checked before writing:

- A = B = 0 is permitted. No nontriviality or nonempty spectrum is required.
- A nonzero reduced ring can map regularly to B = 0; the conclusion is still true and the
  zero fibres have empty spectra. No domain assertion is made about a zero fibre.
- A = 0 forces B = 0 for a unital ring homomorphism, again permitted by the binders.
- The identity on the reduced singular ring k[x,y]/(xy) meets the hypotheses; regularity of
  A or B is not added. Regularity concerns the map and its fibres.
- A field mapping to its polynomial ring gives the expected regular-map example.
- The flat map k → k[ε]/(ε²) fails the regularity hypothesis, so no false flat-ascent
  assertion has replaced the actual statement.
- Identity purely inseparable extensions are allowed, including in characteristic zero.
  Arbitrary source and target type universes remain available.

Searches for an existing declaration (all queries run before writing):

- `msearch.py ... leanfinder "regular ring homomorphism between Noetherian rings with reduced
  source has reduced target"`: eight hits for reduced localizations, geometrically reduced
  algebras, injective descent, and affine schemes. None states this regular-map ascent.
- `msearch.py ... loogle "IsReduced, RingHom.IsRegular"`: no hits; the Mathlib index does not
  know the project predicate `RingHom.IsRegular`.
- `msearch.py ... grep
  "IsReduced.*[Ff]lat|[Rr]educed.*[Rr]egular|[Rr]egular.*[Rr]educed" RingTheory`:
  two hits concerning `IsReduced.tensorProduct_of_flat_of_forall_fg`. Read its complete
  signature and docstring at `Mathlib/RingTheory/Flat/Basic.lean:638–661`: it assumes
  reducedness of tensor products with every finitely generated subalgebra, not regular
  residue-field fibres, so it is not an exact match.
- `rg` in the source project's `WeilConjectures`, this project's `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for the item id, `regular_map_reduced`, and
  `isReduced_of_isRegular`: no existing declaration. Broader regular/reduced searches find
  the already imported Serre criterion and unrelated Hopf-algebra text, not the item.
- The full source and target dependency nodes and their recorded signatures were read.
  No new definition node or dependency repair is necessary.

No statement correction or STATEMENT-DISPUTED flag applies. The natural statement agrees
with Stacks 07QK, which assumes exactly a regular map, a Noetherian target, and a Noetherian
reduced source. Compilation and dry-run results are recorded below after validation.

Validation (2026-10-16 UTC): `scompile.py N7 lem-exc-regular-map-reduced-target` compiled
both the sandbox check and the named module cleanly, with no errors or warnings. The node
copy differs from the shared node only in `lean`, and every Lean line has at most 100
characters. Required `deliver2.py N7 lem-exc-regular-map-reduced-target --no-push` printed
`OK (dry run)` for commit `96e301f5e2`: compilation and preflight pass except for the
independent second reading, which the second reader supplies. Nothing was pushed. This
worker has not written a second-reading section.

Supplementary search: LeanSearch query `reducedness ascends along a regular ring map of
Noetherian rings` returned `UNAVAILABLE`, with `Internal Server Error`; no mathematical
verdict is inferred from the unavailable service. The successful LeanFinder, Loogle and
grep searches above cover the existing-declaration check.

## Second reading by N7

I independently opened the node, Stacks Tag 07QK, and
`Sheaf/RingTheory/RegularMapReducedTarget.lean`. The source says: given a ring map
`φ : R → S`, (1) `φ` is regular, (2) `S` is Noetherian, and (3) `R` is Noetherian
and reduced, conclude that `S` is reduced. The Lean renders each item as follows:

| Node item | Lean declaration | Verdict |
| --- | --- | --- |
| commutative source ring `A` | `{A : Type u} [CommRing A]` | exact |
| commutative target ring `B` | `{B : Type v} [CommRing B]` | exact |
| source Noetherian | `[IsNoetherianRing A]` | exact Mathlib notion |
| target Noetherian | `[IsNoetherianRing B]` | exact Mathlib notion |
| source reduced | `[IsReduced A]` | exact Mathlib notion (all nilpotents vanish) |
| ring map `φ : A → B` | `(φ : A →+* B)` | exact unital commutative ring map |
| regularity of `φ` | `(hφ : φ.IsRegular)` | exact `RingHom.IsRegular` from `def-weil-pbc-g-ring` |
| target reduced | `: IsReduced B` | exact conclusion |

There are no additional hypotheses (no domain, finite type, injectivity, locality,
characteristic, or smoothness condition), and the quantifier order is the source
objects, their structures, the map, regularity proof, then the reducedness conclusion.
The independent universes `u` and `v` preserve all source and target cases. The
regular-map predicate supplies its own fibre and geometric-regularity clauses; no
private replacement is introduced. The theorem's docstring records all five proof
steps from the node and cites each proof dependency, with the source place and
`(blueprint: lem-exc-regular-map-reduced-target)`.

I checked edge cases before accepting the statement: the zero ring is admitted; a
map to the zero ring is admitted when its regularity proof exists; the empty prime
spectrum of a zero fibre is covered; identity maps on reduced singular rings are
allowed; and no characteristic or nonempty-spectrum assumption is hidden. The
`n = 0` issue does not occur in this statement.

For the one-definition check I searched the source project and Mathlib with `rg` for
`isReduced_of_isRegular`, regular/reduced combinations, and `RingHom.IsRegular`; the
hits were element-regularity and regular-sequence declarations only. The recorded
LeanFinder, Loogle, grep, and unavailable LeanSearch queries in the worker report
likewise found no exact theorem. The dependency declarations were opened: Mathlib's
`IsNoetherianRing`, `Sheaf.RingTheory.GRing`'s `RingHom.IsRegular`, and the imported
Serre/ascent modules all match the node's interfaces. No mismatch was found, so no
source, node, statement, dependency, or Lean-file change was needed in this second
reading.
