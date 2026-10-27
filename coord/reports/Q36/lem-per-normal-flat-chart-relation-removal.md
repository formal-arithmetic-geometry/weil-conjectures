## Worker report

The new module `Sheaf.RingTheory.NormalFlatChartRelationRemovalWithoutReducedness`
states `Hironaka.normalFlatChartRelationRemovalWithoutReducedness` with one `sorry`.
It constructs no new notion. It reuses the recorded chart, order, initial-form,
and minimal-generator definitions. The existing reduced-case theorem
`Hironaka.normalFlatChartRelationRemoval` is strictly more restrictive, so it is
not an existing match. The new signature follows its coordinate interface but
has no `IsReduced (T ⧸ b)` hypothesis. No statement correction is needed.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Nonzero commutative regular local T: `{T : Type u} [CommRing T]
  [IsRegularLocalRing T]`. The latter class extends the Noetherian and local
  predicates; `IsLocalRing` extends `Nontrivial`. Its maximal ideal is always
  `IsLocalRing.maximalIdeal T` and its residue field is `IsLocalRing.ResidueField T`.
- Nonnegative r,s and ordered parameters: `(r s : ℕ)`, `x : Fin (r+1) → T`,
  `y : Fin s → T`, and `hparams` on `List.ofFn x ++ List.ofFn y`.
  Indices of y start at zero in Lean, merely relabelling y_1,...,y_s.
- P is `Ideal.span (Set.range x)`; the original ideal a is named `b` in Lean.
  `hb` says a ≤ P. R is `T ⧸ b`, I is `P.map (Ideal.Quotient.mk b)`.
  The quotient maximal ideal m is implicit in the quotient ring construction.
- Normal flatness: `hflat : Module.Flat (R ⧸ I) (Ideal.associatedGraded I)`.
  The coefficient algebra is the recorded degree-zero quotient algebra. Under
  a ≤ P, the canonical identification R/I = T/P identifies this with the node's A.
- G and its homogeneous pieces are the recorded `Ideal.associatedGraded` and
  `Ideal.associatedGradedPiece`. S = G tensor_A k is an auxiliary notation in
  the node, unused in any hypothesis or conclusion: it is determined by these
  rings and canonical quotient maps, so it introduces no independent binder.
  B is `MvPolynomial (Fin (r+1)) (IsLocalRing.ResidueField T)`; polynomial
  homogeneity in the statement is the standard total grading, all variables
  of degree one.
- No minimal prime contains I: `hmin`, quantified over `minimalPrimes (T ⧸ b)`.
  These are genuinely minimal primes, without a minimal-associated-prime substitute.
- D_T is the recorded `ParameterChart x`, namely
  `PermissibleCoordinateChart.Chart x Finset.univ 0`. Its relations have the
  opposite sign from the displayed relations, generating the same ideal.
- The actual map to the quotient chart is `ρ`, fixed on coefficients and
  every ratio variable by `hρ : IsQuotientChartMap x b ρ`.
  The ambient map `ι` is fixed similarly by `hι : IsAmbientChartMap x ι`.
  These are coordinate characterizations of the canonical maps, not arbitrary maps
  or extra algebraic assumptions. In a regular parameter chart they exist and
  are unique. The ambient map is injective and the quotient map is surjective;
  those facts follow from this presentation and the parameter hypotheses.
- z is `PrimeSpectrum (chartRing I (Ideal.Quotient.mk b (x 0)))`: working in
  the affine chart encodes membership in that open of the blowup.
  `hz` says the composite T → R → chart has inverse-image prime M, exactly
  that z lies over m. No rationality or residue-field equality is required.
- The pulled-back prime is `PrimeSpectrum.comap ρ z`; T' is `LocalChart ρ z`,
  its actual localization. `[IsRegularLocalRing (LocalChart ρ z)]` is precisely
  the additional regular-local assumption. R_z is the chart's localization at z,
  and a' is `transformIdeal ρ z`, the kernel of the canonical localized ρ.
  This is the stalk on the affine open, canonically the blowup stalk at z.
- M' is `IsLocalRing.maximalIdeal (LocalChart ρ z)`.
  H is `exceptionalIdeal x y (PrimeSpectrum.comap ρ z)`, the image of `(x_0,y)`.
- p is the prime of the residue polynomial ring with labels `{i // i ≠ 0}`.
  `hp` says its inverse image under the actual coefficient reduction map is
  the preimage of the ambient chart prime under the quotient presentation.
  This specifies reduction modulo M D_T without an arbitrary residue prime.
  L and N occur inside `InOrderSpace` as `Localization.AtPrime p.asIdeal` and
  its maximal ideal. The presentation gives T'/H = L; no extra isomorphism
  hypothesis is imposed.
- `m : ℕ`, `hm : 1 ≤ m`, and `f : Fin m → T` encode the nonempty family.
  `d : Fin m → ℕ`, `hd : Monotone d`, and `hdpos` encode the increasing
  positive finite orders. `hf` gives membership in a and P^d_i and equality
  of the recorded `adicOrder` with the finite natural number d_i.
- `χ` is the tangent coordinate map from k[X,Y], fixed on constants and every
  X,Y parameter by `hχ : IsParameterGradedMap x y χ`.
  The regular-system-of-parameters assumption ensures this is the canonical
  graded identification. `hφ` says φ_i is homogeneous in X alone of degree d_i
  and maps, after `MvPolynomial.rename Sum.inl`, to the actual initial form
  `initialForm T (d i) ⟨f i, hi⟩` in gr_M T.
- `hbasis : IsMinimalGeneratingFamily ...` says these initial forms generate
  the actual initial ideal `adicInitialIdeal M b`, and no member lies in the
  ideal of the others. That ideal equals the kernel of gr_M T → gr_m R.
- g is a family in T'; `hg` uses `IsDividedElement`, requiring a representative
  in D_T whose ambient image is f_i/x_0^d_i and whose local image is g_i.
  Thus division takes place before quotienting by a, as the node specifies.
- The prefix length called b in the node is `a : Fin m`. Thus 0 ≤ b < m,
  including b=0. j < a labels exactly the first b entries, corresponding to
  the source's one-based j ≤ b. The integer threshold d is `e : ℕ` with `he`.
  `hdegree` gives d_j ≤ e on the prefix and e ≤ d_i on the complement.
- `q w : Fin m → T'` have conditions only on the prefix. Extra values outside
  the prefix are unused and can always be filled with zero.
  `hearlier` encodes all four earlier-generator conditions: `InOrderSpace`
  is φ_j(1,t)/1 ∈ N^d_j (and repeats its already-assumed homogeneity),
  q_j = g_j-w_j, w_j ∈ H * prefixIdeal g j, and exact M'-order d_j.
- J is `prefixIdeal q a`. `hjet` is a' ≤ J ⊔ M'^e.
  The conclusion is literally J ⊓ (H ⊔ M'^e) ≤ H*J ⊔ M'^e;
  lattice sup is ideal sum and inf is ideal intersection.
- There is no reducedness hypothesis anywhere in the new theorem or its
  defining predicates. All universes and variables are explicit; autoImplicit is false.

Dependency declarations read and reused (including the constituent ring clauses
of nodes with broader scheme statements):

- Mathlib.RingTheory.RegularLocalRing.Defs: `IsRegularLocalRing`;
  Sheaf.AlgebraicGeometry.IsRegularScheme: its docstring explicitly retains the
  Mathlib ring predicates for the ring clauses of def-weil-regular-scheme.
- Mathlib.AlgebraicGeometry.ResidueField: `Scheme.residueField`, whose underlying
  ring construction is `IsLocalRing.ResidueField` in LocalRing.ResidueField.Defs.
- WeilConjectures.RingTheory.IsRegularSystemOfParameters:
  `IsLocalRing.IsRegularSystemOfParameters`.
- WeilConjectures.RingTheory.AssociatedGradedRing: `Ideal.associatedGraded`,
  `Ideal.associatedGradedPiece`, and `Ideal.associatedGradedAlgebra`.
- Mathlib.RingTheory.RingHom.Flat: `RingHom.Flat` and `Module.Flat`; flatness
  uses the equivalent module formulation over the canonical coefficient algebra.
- Mathlib.LinearAlgebra.TensorProduct.Defs: `TensorProduct` (auxiliary S only).
- Mathlib.Algebra.MvPolynomial.Basic: `MvPolynomial`; and
  WeilConjectures.RingTheory.GradedAlgebra.Standard: `GradedAlgebra.IsStandard`.
- Mathlib.AlgebraicGeometry.Scheme: `Spec` (its affine point encoding is
  `PrimeSpectrum`); WeilConjectures.Blowup.Affine.Defs: `AffineBlowup`;
  WeilConjectures.Blowup.Affine.ChartAlgebra: `AffineBlowup.chartRing`, `chartFraction`.
- Mathlib.RingTheory.Localization.AtPrime.Basic: `Localization.AtPrime` and
  `Localization.localRingHom`.
- Sheaf.RingTheory.LocalStandardBasisInvariants: `adicOrder`,
  `IsMinimalGeneratingFamily`; Sheaf.RingTheory.ProjectiveConeHilbertStandardDegrees:
  `adicInitialIdeal`; Sheaf.AlgebraicGeometry.NodalLocalTangentData: `initialForm`.
- Sheaf.AlgebraicGeometry.PermissibleCoordinateChart:
  `PermissibleCoordinateChart.Chart`, `relations`, and `ratio`.
- Sheaf.RingTheory.PermissibleBasisChartData: `ParameterChart`, `IsAmbientChartMap`,
  `IsQuotientChartMap`, `residuePolynomialMap`, `IsParameterGradedMap`,
  `IsDividedElement`, `LocalChart`, `transformIdeal`, `exceptionalIdeal`,
  `prefixIdeal`, and `InOrderSpace`. The already-landed owner node
  def-trf-permissible-basis-chart-data is added to stmt_deps, as permitted for
  landed definition owners. No private copy or dependency repair is needed.

The two theorem proof dependencies (normal-flat-initial-coefficient-lifting and
projective-order-leading-syzygies) currently have no Lean records; consequently
there are no modules for them to import. Both are named in the five-step proof
in the declaration docstring, preserving the mathematical proof plan.

Edge cases checked: r=0 has no ratio variables, but still has the pivot x_0;
s=0 has no y parameters; a=0 gives the zero prefix ideal; e=1 needs no
order-raising steps; m=1 necessarily has an empty prefix; repeated d_i are
allowed by Monotone; zero initial forms cannot be minimal generators; finite
orders exclude f_i=0 in this separated Noetherian setting. Arbitrary residue
primes, characteristics, imperfect fields, and nonreduced R remain covered.
For a concrete nonreduced compatibility check use
T=k[x_0,x_1,x_2]_(x_0,x_1,x_2), P=M, a=(x_1,x_2^3): I=m meets no
minimal prime, normal flatness over k is automatic, and the x_0-chart retains
the nilpotent ratio t_2 with relation t_2^3=0 after inverting x_0. The empty prefix is
always immediate; with prefix (x_1), its divided generator is t_1 of order one.
The finite-jet hypothesis is stated explicitly rather than silently inferred.

Searches made with the prescribed msearch.py wrapper:

- leanfinder: "In a normally flat regular local blowup chart remove residue
  relations among a corrected standard basis modulo a finite maximal ideal
  power without reducedness". Eight hits: Weierstrass division and local
  quotient bases, no matching theorem.
- loogle: `"Ideal", "pow", "inf"`. Twelve hits: Krull intersection,
  Artin--Rees, ideal valuations, and divided-power ideal lattices. No match.
- grep: `normal.?flat|Hironaka|permissible` in RingTheory: zero Mathlib hits.
- Direct rg in lean/Sheaf, lean/WeilConjectures and dag/lean_names_upstream.json:
  only the reduced twin normalFlatChartRelationRemoval was found; no declaration
  of the reducedness-free assertion. Direct grep for this item's blueprint id
  in lean/WeilConjectures found nothing. Existing chart definitions were found
  and read in full before use.

Source read online: Hironaka (1970), pp.176--181, (19.1)--(20.12), at
https://scispace.com/pdf/certain-numerical-characters-of-singularities-18d51ii5bz.pdf .
This confirms the divided coordinates, quotient by (x_0,y), and the finite
coefficient-order-raising mechanism. The node's five-step finite-jet assembly
and its reducedness-free inputs are copied into the proof docstring. No
STATEMENT-DISPUTED flag or source-based correction is required.

## Second reading by Q36

A separate pass by this same dispatcher-started worker compared the node and
final signature after writing; no independent second worker was started,
as the dispatch brief explicitly forbids other agents. Independent review is
performed by the maintainer on delivery.

The pass checked each correspondence listed above, especially the two different
uses of b (ideal `b` versus prefix `a`), strict versus one-based prefix indexing,
the actual localized-map kernel, ambient rather than quotient division, the
residue-prime comap equality, and finite rather than infinite orders. It also
compared the whole signature with the reduced twin: the only mathematical
hypothesis removed is its IsReduced assumption, exactly as this node requires.
No additional assumptions or weakened conclusions were introduced. The owner
node for the reused chart predicates was added to stmt_deps; no new node or
module implementing a second definition was introduced.
