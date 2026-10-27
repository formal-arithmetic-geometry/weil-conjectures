## Worker report

Stage 2, Q16, repaired 2026-10-24 (UTC). The module `Sheaf.RingTheory.PermissibleBlowupStandardDegrees`
states `Hironaka.permissibleBlowupStandardDegrees`, with proof exactly `sorry`.
The accepted stage-1 split remains unchanged. Q50's 12:22 delivery was that split,
not a stage-2 Lean statement: the current item has lean=null. The stage-handoff rule
at brief-stage2 §0 explicitly permits this delivery. No repair note is present.

Read the entire item, its four proof steps, all fourteen original statement dependencies,
and each recorded signature/docstring or Mathlib match. Also read the chart and numerical
modules used below, the reduced trace-formula twin, the one-step standard-basis theorem,
and the current blueprint/latest Artin--Gabber proof. The current blueprint uses perverse
generators; the present item is the already accepted historical lower algebraic branch.
No target, unit, route, statement, proof, or proof-dependency field is changed.

Source read: Hironaka, Certain numerical characters of singularities (1970), pp.154--156,
including initial ideals, the degree sequence, assumptions (2.1)--(2.2), and Theorem III;
also its concluding proof on p.187. The PDF was read at
https://scispace.com/pdf/certain-numerical-characters-of-singularities-18d51ii5bz.pdf .
The hypotheses concern an arbitrary closed subscheme, not just a reduced one.
The declaration's docstring records the node's full four-step proof, including the
normal-flat polynomial factor, the fibre chart, the two inequalities and cancellation,
and both standard-degree equality clauses.

Hypothesis and clause correspondence:

- Nonzero commutative regular local T: `{T : Type u} [CommRing T]
  [IsRegularLocalRing T]`. The latter extends local and Noetherian ring classes;
  local rings are nontrivial. The residue field k is literally
  `IsLocalRing.ResidueField T`, the quotient by `IsLocalRing.maximalIdeal T`.
- Integers r,s >= 0 and parameters x0,...,xr,y1,...,ys: `r s : ℕ`,
  `x : Fin (r+1) → T`, `y : Fin s → T`, and `hparams` applied to
  `List.ofFn x ++ List.ofFn y`. This uses the recorded upstream regular-parameter predicate.
- P=(x_i), a contained in P, R=T/a, I=P/a: `Ideal.span (Set.range x)`,
  `b`, `hb`, `T ⧸ b`, and `(Ideal.span (Set.range x)).map (Ideal.Quotient.mk b)`.
  The original maximal ideal is `IsLocalRing.maximalIdeal T`; its image is the
  maximal ideal used by `quotientHilbertFunction`.
- A=T/P=R/I and G flat over A: `hflat : Module.Flat ((T ⧸ b) ⧸ I)
  (Ideal.associatedGraded I)`, with I expanded in the file. This is the recorded
  associated graded algebra's canonical degree-zero scalar action. The quotient
  R/I is the displayed A via the canonical quotient-by-quotient identification.
- S=G tensor_A k and B=k[X0,...,Xr] are auxiliary rings used only in the node's
  proof, not extra quantified hypotheses or an additional conclusion. They are
  constructed from the already fixed inputs; their names are not gratuitous theorem
  binders. The existing tensor product and polynomial/graded-algebra declarations
  give these constructions. The docstring follows their exact role in the split.
- No minimal prime of R contains I: `hmin : ∀ q ∈ minimalPrimes (T ⧸ b), ¬ I ≤ q`.
  Mathlib's `minimalPrimes` are minimal elements among prime ideals over zero.
- z is in the x0 chart of Bl_I(Spec R): `z : PrimeSpectrum (chartRing I xbar0)`.
  This represents exactly a point of the specified chart, with local ring
  `Localization.AtPrime z.asIdeal`. The upstream chart algebra is canonically
  isomorphic to the degree-zero homogeneous localization chart of the Rees Proj,
  by `AffineBlowup.homogeneousAwayEquivChart`; thus no additional point is chosen
  and no closed/rational-point condition is imposed.
- z lies over m: `hz` says its contraction along T → R → chartRing equals
  `IsLocalRing.maximalIdeal T`, equivalently its contraction in R equals M/a.
- D_T and its surjection to the quotient chart: `ParameterChart x` reuses
  `PermissibleCoordinateChart.Chart x Finset.univ 0`, the polynomial quotient
  with relations x_i-x0*t_i (the negative of the written relations, hence the
  same ideal). `ρ` with `hρ : IsQuotientChartMap x b ρ` specifies the quotient
  on every coefficient and every ratio. These identities determine the map
  uniquely by the polynomial quotient universal property. Supplying its pinned
  realization adds no mathematical assumption or choice of arbitrary map.
- p' is the inverse image of z, T' its localization: `LocalChart ρ z` unfolds to
  `Localization.AtPrime (PrimeSpectrum.comap ρ z).asIdeal`.
- T' regular local: `[IsRegularLocalRing (LocalChart ρ z)]`, exactly as assumed.
- R_z and a'=ker(T' → R_z): the local ring is the chart prime localization;
  `transformIdeal ρ z` is the kernel of the actual
  `Localization.localRingHom` induced by ρ. This is the owning definition,
  not an arbitrary ideal or an unspecified quotient comparison.
- E and the multiplicities defining ν*: `nuStar` is the recorded
  `generatorDegreeSequence` of `gradedGeneratorMultiplicity` for
  `adicInitialIdeal` in `Ideal.associatedGraded (maximalIdeal _)`.
  Its homogeneous pieces are computed over the literal residue field. The
  degree-d denominator is the sum of positive-degree multiples prescribed in
  the node. The constructed initial ideal equals the stated graded-map kernel
  for a proper ideal. The enumeration uses the least degree whose cumulative
  multiplicity exceeds the index and pads the empty tail by infinity.
- h_R and h_z: `quotientHilbertFunction (IsLocalRing.maximalIdeal T) b` and
  the explicit `Module.length (Localization.AtPrime z.asIdeal)
  ((Localization.AtPrime z.asIdeal) ⧸ maximalIdeal _ ^ (n+1))`, respectively.
  The former computes exactly length over R with M/a; the latter exactly over R_z.
  The natural-number conversions lose nothing: both rings are Noetherian local
  rings and their maximal-adic truncations have finite length.
- δ=trdeg_k κ(z): `Cardinal.toNat (Algebra.trdeg (IsLocalRing.ResidueField T)
  z.asIdeal.ResidueField)`. The `κ` map is pinned by `hκ` on the surjective residue
  map of T, so its `toAlgebra` is exactly the induced extension. Existence follows
  from hz by descent to T/M; uniqueness follows from residue surjectivity. No
  coefficient field, separability, rationality, or arbitrary lift is assumed.
  This transcendence degree is finite since the chart is of finite type over R
  and z is over its closed point. The universe u is arbitrary.
- Λ is `AlgebraicGeometry.HilbertSamuel.summation`, inclusive from 0 to n;
  its δ-fold iterate and equality with h_R are exactly `hnear`.
- Conclusion: `nuStar (transformIdeal ρ z) = nuStar b`, equality as functions
  ℕ → ℕ∞, including all multiplicities and the infinitely padded tail.
  No converse, reducedness, or weaker pointwise comparison is asserted.

Dependency declarations reused (module, name):

- `Mathlib.RingTheory.RegularLocalRing.Defs`: `IsRegularLocalRing`, the ring
  clause retained in def-weil-regular-scheme's mathlib_match. The scheme-only
  `Sheaf.AlgebraicGeometry.IsRegularScheme` is unnecessary for this ring statement.
- `WeilConjectures.RingTheory.IsRegularSystemOfParameters`:
  `IsLocalRing.IsRegularSystemOfParameters`.
- `WeilConjectures.RingTheory.AssociatedGradedRing`: `Ideal.associatedGraded`,
  its pieces and canonical quotient-base algebra instance.
- `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat`, `Module.Flat`.
- `Mathlib.RingTheory.LocalRing.ResidueField.Basic` and `.Ideal`:
  `IsLocalRing.ResidueField`, `IsLocalRing.residue`, `Ideal.ResidueField`.
  `Mathlib.AlgebraicGeometry.ResidueField` records the scheme formulation;
  here its underlying local-ring quotient is used directly.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`;
  `Localization.localRingHom` constructs the canonical localized map.
- `WeilConjectures.Blowup.Affine.ChartAlgebra`: `AffineBlowup.chartRing`,
  `chartFraction`, `homogeneousAwayEquivChart`; `.Defs`: `AffineBlowup` as Rees Proj.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Spec.map`.
- `Mathlib.LinearAlgebra.TensorProduct.Defs`: `TensorProduct`;
  `Mathlib.Algebra.MvPolynomial.Basic`: `MvPolynomial`, `MvPolynomial.algHom_ext`;
  `.Eval`: `MvPolynomial.aeval`; these give the auxiliary rings/universal properties.
- `WeilConjectures.RingTheory.GradedAlgebra.Standard`: `GradedAlgebra.IsStandard`.
- `Mathlib.RingTheory.Length`: `Module.length`;
  `Mathlib.RingTheory.AlgebraicIndependent.Basic`: `Algebra.trdeg`.
- `Sheaf.RingTheory.PermissibleBasisChartData`: `Hironaka.ParameterChart`,
  `IsQuotientChartMap`, `LocalChart`, `transformIdeal`.
- `Sheaf.RingTheory.ProjectiveConeHilbertStandardDegrees`: `Hironaka.nuStar`
  and its concrete numerical helpers, owned by the definition node
  `def-trf-adic-initial-ideal-generator-degrees`; `Hironaka.quotientHilbertFunction`,
  owned by `def-trf-local-quotient-hilbert-function`. Both owning nodes have
  existing:true records on these unchanged definitions. Neither construction is
  a choice from the projective-cone theorem.
- `Sheaf.AlgebraicGeometry.HilbertSamuelInvariant`:
  `AlgebraicGeometry.HilbertSamuel.summation`, owned by
  `def-trf-hilbert-samuel-invariant`, now explicitly cited in stmt_deps
  (already exposed through the preceding module).
- Proof-only import `WeilConjectures.AlgebraicGeometry.RelativeProj.BaseChange`:
  `Scheme.GradedAlgebraData.PullbackData.relProjIsoPullback`. The projective-cone
  and coordinate-chart proof modules are already public via statement dependencies.
  The other three algebraic proof dependencies have no current Lean record and
  are not imported; their mathematical steps remain in the docstring, with no
  replacement assumptions or conclusions invented for them.

Edge cases checked before writing:

- r=0: no ratio variables, the ambient chart is T; the signature still accepts it.
- s=0: no transverse parameters; nothing requires a positive-length y-list.
- b=0: both initial ideals are zero and both degree sequences consist entirely of infinity.
- n=0: inclusive summation uses the single value at zero; lengths of residue fields are one.
- Zero ring is excluded by local-ring nontriviality exactly as in the node; T of
  dimension zero cannot have the required nonempty x-parameter list, as intended.
- Arbitrary characteristic and nonclosed/nonrational/inseparable residue points
  are admitted. No coefficient field of T is selected.
- Nonreduced test: T=k[[u,v]], b=(v²), P=(u,v), and the u-chart point (u,t)
  gives R_z=k[u,t]_(u,t)/(t²) in the corresponding local/complete model.
  Both raw functions are 2n+1 and both sequences are (2,∞,...); the flatness
  over the centre's field and minimal-prime exclusion hold. No IsReduced binder occurs.

Searches (actual msearch output is retained in sandbox/searches.jsonl):

- LeanFinder: “Equality of Hilbert Samuel functions at a point of a permissible
  blowup implies equality of minimal initial ideal generator degree sequences
  without assuming the quotient ring reduced”: 8 hits on filtrations, local
  cohomology, power-series ideals, ramification, adic completions and Weierstrass
  division; read returned signatures, none is this comparison.
- Loogle: `"Ideal", "associatedGraded", "Flat"`: 0 hits.
- Mathlib grep: `Hilbert.?Samuel|standard.?basis|Hironaka` in RingTheory:
  4 hits, ordinary presentation basis vectors and Witt-polynomial bases, no match.
- LeanSearch: “A normally flat permissible blowup preserves the sequence of minimal
  homogeneous tangent ideal generator degrees if the shifted Hilbert Samuel
  functions agree”: 8 hits on flat maps and regular sequences, no degree comparison.
- rg over `lean/WeilConjectures` and `lean/Sheaf` for `nuStar`, permissible blowups,
  standard degrees and Hironaka, plus exact item/declaration names: no existing
  theorem. The reusable Hironaka chart/numerical definitions above were found.
  Exact item-tag grep of WeilConjectures returned no match. The reduced trf twin
  has no Lean statement and cannot replace this nonreduced statement.

Added the already landed statement dependencies permitted by brief §5: the owning
chart-data node, `def-trf-adic-initial-ideal-generator-degrees`,
`def-trf-local-quotient-hilbert-function`, and `def-trf-hilbert-samuel-invariant`.
The projective-cone theorem is retained in proof_deps only; its module remains a
public import because it houses the plain definitions owned by the two definition nodes. No new definition nodes, dependency repairs, or statement
corrections are needed. No STATEMENT-DISPUTED issue found.

Validation: scompile.py compiled this file in sandbox mode and at its actual module
path successfully, with no errors or warnings. The only proof body is sorry.


## Repair of return H2

The return on immutable head 624025335318 accepted the mathematical statement and
Lean file, and requested a definition-ownership correction in the DAG. Removed
`lem-trf-projective-cone-hilbert-standard-degrees` from stmt_deps and replaced it
with `def-trf-adic-initial-ideal-generator-degrees` and
`def-trf-local-quotient-hilbert-function`; also added
`def-trf-hilbert-samuel-invariant`. Read all three current definition-node records
and the underlying definition signatures and docstrings. The theorem stays in
proof_deps, which is unchanged. Updated the dependency paragraphs above.
The retained Lean source and signature are unchanged from the returned delivery.
Compared the sandbox node with current main: every field other than lean and
stmt_deps agrees, so no accepted split or mathematical statement needs rebasing.
Recompiled through scompile.py and validated through deliver2.py --no-push before
redelivery.

## Second reading by Q16

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
