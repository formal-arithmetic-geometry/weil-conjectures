## Worker report

The module `Sheaf.RingTheory.ParameterCutExpectedCodimensionTuple` states
`IsRegularLocalRing.parameterCut_expectedCodimension_tuple`, with proof `sorry`.
No definition or auxiliary theorem is introduced. The node is unchanged outside `lean`.

Hypotheses, in node order:

- The commutative regular local ring is `R : Type u`, `[CommRing R]`,
  `[IsRegularLocalRing R]`. Mathlib's class includes locality and Noetherianity.
- Dimension `d ≥ 1` is `d : ℕ`, `hdpos : 1 ≤ d`,
  `hd : ringKrullDim R = (d : WithBot ℕ∞)`.
- The ordered parameters `t₁,...,t_d` are represented by `x :: ts`.
  `htlen` gives length `d`; `htmem` puts every element in the maximal ideal;
  `htspan` says their generated ideal is that maximal ideal. There is no
  distinctness assumption or added regularity hypothesis on this tuple.
- `b : ℕ`, `hbpos : 1 ≤ b`, and `hbd : b ≤ d` give precisely the stated range.
  The ordered list `zs` represents `z₂,...,z_b`, with `hzlen : zs.length = b - 1`;
  `hzmem` puts its entries in the maximal ideal.
- `I : Ideal R` and `hI : I = Ideal.ofList (x :: zs)` name the specified generated ideal.
  `hcodim` is exactly `dim(R/I) = d - b`. Natural subtraction is correct here
  because `b ≤ d` is assumed.

Conclusions, in node order:

- The parameter quotient is always the concrete ring `R ⧸ Ideal.span {x}`.
  The map `q` is always the concrete canonical projection
  `Ideal.Quotient.mk (Ideal.span {x})`. The image ideal `I'` is always
  `I.map (Ideal.Quotient.mk (Ideal.span {x}))`; no arbitrary quotient/map is assumed.
- The existential proof `hQ : IsRegularLocalRing (R ⧸ Ideal.span {x})` gives regular
  locality. The first conjunct is its dimension `d - 1`. The second identifies its
  maximal ideal with the image of the original maximal ideal; `hQ.toIsLocalRing`
  explicitly supplies the local-ring instance to this maximal ideal.
- `RingTheory.Sequence.IsRegular` on the image list asserts regularity of this very
  ordered tuple over the quotient ring. The next conjunct places every image entry
  in its maximal ideal, and the next equates the tuple's generated ideal to `I'`.
- The ring equivalence `e : R'/I' ≃+* R/I`, with its displayed formula on every `r : R`,
  is the canonical quotient isomorphism `[q(r)] ↦ [r]`. Since both quotient maps are
  surjective, that formula uniquely determines `e`; this is not an unconstrained
  isomorphism or a replacement of a canonical map by an arbitrary one.
- The next conjunct states `dim(R'/I') = (d - 1) - (b - 1)`. The range conditions ensure
  both subtractions give the ordinary nonnegative dimensions.
- The final general clause quantifies over every `S : Type v` with commutative and
  local-ring structures, and every ring homomorphism `f : R →+* S`. Its three premises
  are surjectivity, locality `IsLocalHom f`, and `x ∈ RingHom.ker f`. It produces `f'`
  whose composite with the canonical projection is `f`, uniquely specifying the
  induced map. Its surjectivity and locality are asserted. `IsLocalHom` is equivalent
  to maximal ideals mapping into maximal ideals for local rings, by Mathlib's
  `IsLocalRing.local_hom_TFAE`.
- The witness `s : ℕ` with `ringKrullDim S = (s : WithBot ℕ∞)` states finite Krull
  dimension of the local target, rather than assuming it. The integer equality
  `((d - 1 : ℕ) : ℤ) - (s : ℤ) = ((d : ℤ) - (s : ℤ)) - 1` is exactly
  `dim R' - dim S = (dim R - dim S) - 1`, using the stated dimension equalities.
  Subtraction in this difference formula is in `ℤ`, not truncated subtraction.
- The `b = 1` implication explicitly states that the list is empty and `I' = ⊥`.
  The equivalence `e₀ : R'/I' ≃+* R'`, characterized by `e₀([a]) = a`, renders the
  stated identification `R'/I' = R'` as its canonical zero-ideal quotient identification.

Dependency declarations read and used:

- `def-weil-regular-scheme`: the ring clause is exactly the recorded Mathlib match
  `IsRegularLocalRing` in `Mathlib.RingTheory.RegularLocalRing.Defs`. Its full class
  signature extends `IsLocalRing` and `IsNoetherianRing` and equates the maximal ideal's
  `spanFinrank` to `ringKrullDim`. The recorded scheme declaration
  `AlgebraicGeometry.IsRegularScheme` in `Sheaf.AlgebraicGeometry.IsRegularScheme`
  was also read; its scheme-only conjunction is irrelevant to this ring statement.
  No private copy or scheme restriction is introduced.
- `def-weil-pbc-regular-sequence`: `RingTheory.Sequence.IsRegular` in
  `Mathlib.RingTheory.Regular.RegularSequence`. Its `IsWeaklyRegular` parent gives
  injectivity on every prefix quotient, and `top_ne_smul` gives a nonzero final quotient.
- The dimension expression uses `ringKrullDim`, the recorded declaration for
  `def-weil-pbc-krull-dimension-ring`, in `Mathlib.RingTheory.KrullDimension.Basic`.
  This is exposed by the public regular-local-ring import.

The stated proof dependencies are imported privately:
`WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence`
(`IsRegularLocalRing.isRegular_and_quotients_of_generators`),
`Mathlib.RingTheory.LocalRing.Quotient` (the quotient-local-structure Mathlib matches),
and `Sheaf.RingTheory.IsRegularIffDimensionDrop`
(`RingTheory.Sequence.isRegular_iff_dimension_drop`). Regular sequences and dimension
are already public statement imports. The proof-only node
`lem-trf-regular-local-regular-sequence-depth` has no Lean record or Mathlib match on
this base, so no module can yet be imported for it; its use is explained in the proof
plan in the theorem docstring. It is not a missing notion needed to state this item.

Source and edge checks:

Read `literature/stacks-project/algebra.tex`, the complete proof of
`lemma-ci-well-defined` (Tag 00SE), especially the last paragraph replacing `A` by
`A/xA` and `I` by `I/xA`; also read `lemma-regular-ring-CM` (00NQ) and
`lemma-reformulate-CM` (02JN). These justify the fixed-tuple formulation.
For `d = b = 1`, the parameter quotient is a field of dimension zero, the list `zs`
is empty and regular, and `I'` is zero. For general `b = 1`, the empty regular sequence
has nonzero quotient `R'`. For `b = d`, the final quotient has dimension zero and the
remaining list has length `d - 1`. Zero rings are excluded precisely by the original
local-ring hypotheses, not by an extra premise. The target ring is quantified in an
independent universe `v`: no size restriction on local surjections is introduced.
Repeated or zero entries are not excluded artificially; the expected-dimension
hypothesis rules out precisely the impossible positive-length cases. No statement
fault or correction was required.

Searches before writing (2026-10-24):

- `msearch.py ... leanfinder`: query “In a regular local ring of dimension d generated
  by t1 through td, quotient by t1 is regular local of dimension d minus one and the
  remaining generators of an ideal of expected codimension form a regular sequence”.
  Eight hits, including `ringKrullDim_add_length_eq_ringKrullDim_of_isRegular`,
  `RingTheory.Sequence.isRegular_cons_iff'`, and
  `IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal`. None states this
  result with the fixed expected-codimension tuple and quotient/local-map bookkeeping.
- `msearch.py ... loogle 'IsRegularLocalRing, RingTheory.Sequence.IsRegular'`: zero hits.
- `msearch.py ... grep '(regular|parameter).*(quotient|dimension)|IsRegularLocalRing'
  RingTheory/RegularLocalRing`: ten hits in `Defs.lean` and `Polynomial.lean`, giving
  definitions and localization results rather than this statement.
- `msearch.py ... leansearch`: query “Parameter cut in a regular local ring preserves
  regularity and makes the expected codimension tuple into a regular sequence”. Eight
  hits, regular-sequence permutation/flat-base-change facts and the one-equation
  dimension theorem; no exact match.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for
  `parameter.*[Cc]ut|parameter_cut|expected_codimension` found only unrelated cutoff,
  Kummer, and formal-power-series text. The item-id search in `lean/WeilConjectures`
  found no declaration. A name search for the new declaration in Mathlib, both project
  trees and `dag/lean_names_upstream.json` found no existing declaration.

Validation: the prescribed `scompile.py Q46 lem-trf-parameter-cut-expected-codimension-tuple`
compiled the delivered module in sandbox and library modes with no errors or warnings.
The only theorem proof is `sorry`; definitions and additional axioms are absent.

## Second reading by Q46

This is the author's second pass, not a claim of independent review. I reopened the
node and the Lean file and checked the correspondence above in order. In particular,
`x :: ts` has exactly `d` entries, `zs` has exactly `b - 1`, regularity applies to the
specified image list, both maps are characterized on all representatives, and the
universal local-surjection clause concludes finite dimension rather than assuming it.
The endpoint `b = 1` is explicit, and integer subtraction occurs only after finite
natural dimension witnesses are supplied. No mismatch was found and no statement was
changed. The maintainer supplies the independent delivery review.
