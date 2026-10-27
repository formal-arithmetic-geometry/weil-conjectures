## Worker report

The module `Sheaf.RingTheory.NodalPolynomialModelCompletion` states
`NodalPolynomialModel.nodal_polynomial_model_completion`. Its single theorem has
`sorry` as its proof. All concrete helper definitions have complete data and no
postponed proof. The original DAG statement, dependencies and proof are unchanged.

Source read: Stacks `literature/stacks-project/curves.tex`, Tag 0CBY,
`lemma-etale-local-structure-nodal-family`, first proof, third paragraph: the
completed local ring of the polynomial model `Y_sigma`. The newest blueprint has
no occurrence of this historical nodal argument; the node's accepted stage-1
report explicitly records this, and the algebraic statement is retained. The
source's `Z[u,v,t]/(uv-a)` has the known stray `t`; the assigned two-variable
polynomial model is the stated intent of that paragraph.

Hypotheses and objects, matched against the node:

- A commutative Noetherian local ring: `(A : Type u) [CommRing A]
  [IsLocalRing A]` and `[IsNoetherianRing A]`. The type and universe are explicitly
  bound in the section; `autoImplicit` is false.
- Completeness at its maximal ideal:
  `[IsAdicComplete (IsLocalRing.maximalIdeal A) A]`. This includes separatedness.
- `h` in the maximal ideal: `(h : A) (hh : h ∈ IsLocalRing.maximalIdeal A)`.
- `k=A/m`: Mathlib's `IsLocalRing.ResidueField A`, definitionally the quotient by
  `IsLocalRing.maximalIdeal A`.
- `P=A[x,y]`: `MvPolynomial (Fin 2) A`; the variables are `X 0` and `X 1`.
- `q=mP+(x,y)`: `originIdeal A` is the preimage of `m` under constant-term
  evaluation, and the first conjunct explicitly identifies it with the required
  mapped coefficient ideal joined with the span of the two variables. This
  computational description supplies a prime-ideal instance without an extra
  axiom or a separate postponed theorem. It does not replace the specified ideal.
- `D=P_q`: `localPolynomialRing A := Localization.AtPrime (originIdeal A)`.
- `qD`: `localOriginIdeal A`, the ideal image under the localization map.
- `R=A[[x,y]]`: `MvPowerSeries (Fin 2) A`.
- `a=mR+(x,y)`: `seriesOriginIdeal A`, the coefficient ideal image joined with
  the span of the two series variables.
- `xy-h`: `equation A h := X 0 * X 1 - C h` in P; its series coercion is the
  same equation in R. `modelRing`, `localModelRing` and `seriesModelRing` name
  precisely the three specified principal-ideal quotients.

Conclusions, clause by clause:

- `q` is maximal: `(originIdeal A).IsMaximal`. The next conjunct explicitly
  identifies `localOriginIdeal A` with `maximalIdeal (localPolynomialRing A)`;
  consequently the completion below is exactly the specified maximal completion.
- The polynomial-to-series map on localization: the witness `j : D →ₐ[A] R`
  satisfies `j (algebraMap P D p) = (p : R)` for every polynomial p. This equation
  uniquely determines the localization extension; j is not an arbitrary map.
- For every `r ≥ 1`, the witnesses `v r hr` and `w r hr` have types
  `P/q^r ≃ₐ[A] D/(qD)^r` and `D/(qD)^r ≃ₐ[A] R/a^r`.
- The formulas for v on polynomial classes and w on every localized class
  identify these as the induced maps, and identify their composite with the
  polynomial inclusion. Their A-algebra types preserve constants; taking p equal
  to either variable gives exactly the required variable normalization.
- Compatibility with transitions: there are two separate universally quantified
  equations for all positive `s ≤ r`, using `Ideal.Quotient.factorPow` on the
  polynomial/localized quotients and on the localized/series quotients. Their
  composition also gives the transition equation for P to R.
- The induced completed-local-polynomial comparison:
  `e : AdicCompletion (localOriginIdeal A) D ≃ₐ[A] R`.
  The first equation says `e (of d) = j d` for every d. The second specifies its
  reduction at every positive level as `w r hr (AdicCompletion.evalₐ _ r z)`;
  thus e is induced by this same compatible system, rather than a bare equivalence.
- The scheme is `Spec (CommRingCat.of (modelRing A h))`. Its actual stalk is
  `modelStalk A h o`, and `polynomialGerm A h o` is the composition of the quotient
  map with `StructureSheaf.toStalk`. The coefficient algebra on the stalk is the
  composition of this canonical stalk map with the coefficient structure map.
- The point o is an existential point of `PrimeSpectrum (modelRing A h)`, which
  is the underlying point type of that Spec. Its ideal is explicitly the image
  of q under the quotient map, i.e. `q/(xy-h)`. This characterizes a unique point;
  the existential introduces no extra hypothesis about the origin.
- `O_(M_h,o) ≃ D/(xy-h)D`: the witness
  `b : modelStalk A h o ≃ₐ[A] localModelRing A h`. Its equation for every p sends
  the polynomial germ to its localized polynomial class. In particular it
  preserves coefficients and both named variables.
- `κ(o) ≃ k` through coefficients: the witness ρ has source the actual
  `Scheme.residueField o` and target `IsLocalRing.ResidueField A`. Its displayed
  equation for every a identifies the residue of the coefficient germ with the
  residue of a in A/m. This states the canonical coefficient comparison.
- `completed O_(M_h,o) ≃ R/(xy-h)`: E is an A-algebra equivalence from
  `AdicCompletion (maximalIdeal (modelStalk A h o)) (modelStalk A h o)` to
  `seriesModelRing A h`. The final equation applies to every polynomial germ;
  specializing to `C a`, `X 0` and `X 1` gives the three required normalizations.
  This completion also explicitly uses the actual maximal ideal.

Dependency interfaces read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.RingTheory.AdicCompletion.Basic` (public through `.Algebra`):
  `IsAdicComplete`, `AdicCompletion`, `AdicCompletion.of`.
- `Mathlib.Algebra.MvPolynomial.Basic` (public through the power-series import):
  `MvPolynomial`, `constantCoeff`, `X`, `C`; the recorded evaluation and uniqueness
  interfaces are `MvPolynomial.aeval`, `MvPolynomial.algHom_ext`.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime` and
  its local-ring/algebra instances.
- `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries`, its coefficient/variable
  constructors, and the canonical `MvPolynomial.toMvPowerSeries` coercion.
- `Mathlib.AlgebraicGeometry.Scheme` (public through `.ResidueField`): `Spec`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`. Stalks and the
  actual germ map use `StructureSheaf.toStalk` from `.StructureSheaf`.

All already-stated proof dependencies are plain imports, as the proof plan requires:

- `WeilConjectures.RingTheory.PowerSeriesCombinedIdealCoefficients`:
  `power_series_mem_combined_ideal_pow_iff`.
- `WeilConjectures.RingTheory.PowerSeriesCompleteOverCompleteBase`:
  `power_series_complete_over_complete_base`.
- `Sheaf.NumberTheory.Padics.AdicInverseLimitIso`:
  `adicCompletionRingEquivOfCompatible`.
- `Mathlib.AlgebraicGeometry.AffineScheme`:
  `IsAffineOpen.fromSpec_app_self`, `IsAffineOpen.isLocalization_stalk` and
  the recorded affine-open stalk interfaces.
- `Mathlib.RingTheory.Localization.Ideal`, together with the already exposed
  `Ideal.Maps` and `Localization.Basic`: quotient-localization instance,
  `Ideal.map_primeCompl_comap_of_surjective`, `IsLocalization.algEquiv`.
- `Mathlib.RingTheory.FiniteType`: `Algebra.FiniteType.isNoetherianRing`.
- `Mathlib.RingTheory.Localization.Submodule`: `IsLocalization.isNoetherianRing`.
- `WeilConjectures.RingTheory.LocalCompletionQuotient`:
  `AdicCompletion.exists_local_completion_quotient`.

The full nine-step natural-language proof, naming these DAG inputs, is in the
main theorem's docstring. The helpers introduce only the concrete objects and
maps in this statement; no independent missing notion or dependency repair is
needed and no new node is introduced.

Edge cases checked mathematically:

- `r=1`: all three finite quotients are A/m; variable classes vanish.
- `s=r`: the transition conditions reduce to the identity square.
- Field base (`m=0`, hence `h=0`): D is the polynomial ring localized at (x,y),
  with completion A[[x,y]]; the final equation is the split node xy=0.
- `A=k[[t]], h=t`: the equation has a nonzero linear coefficient-ideal term;
  no assumption that xy-h belongs to q squared is used.
- A nonreduced complete base, e.g. `k[ε]/ε²` and `h=ε`: no domain, regularity or
  reducedness assumption was introduced.
- Arbitrary characteristic, including characteristic two: no division by two
  or separability assumption is present.
- The zero ring is already excluded by the original local-ring hypothesis in
  Mathlib's convention; no extra nontriviality hypothesis is added. Level r=0
  is not claimed, exactly as the node requires positive levels.

Searches for an existing statement:

1. `msearch.py ... leanfinder` with “The completed local ring of Spec
   A[x,y]/(xy-h) at (m,x,y) over a complete Noetherian local ring is
   A[[x,y]]/(xy-h)”: eight hits, chiefly one-variable Weierstrass quotient
   equivalences and general stalk/localization lemmas; no exact match.
2. `msearch.py ... loogle MvPowerSeries.toAdicCompletionAlgEquiv`: three hits
   for that equivalence and its apply lemmas. Its ideal is only `idealOfVars`,
   whereas this item needs the combined maximal-coefficient and variable ideal.
3. `msearch.py ... grep 'nodal|polynomial.*completion|completion.*polynomial'
   RingTheory`: twelve hits for Laurent-series completions and the variables-ideal
   power-series equivalence; no exact match.
4. `rg` in `lean/WeilConjectures` and `lean/Sheaf` for nodal completion,
   polynomial models, and the item ID: existing geometric nodal hypotheses,
   field-base completion transports and universal nodal chart definitions do
   not state this complete-local-base polynomial-model computation. The universal
   integral nodal chart is a different object and is not copied here.
5. `rg` of `dag/lean_names_upstream.json`, Mathlib, upstream and project modules
   for `NodalPolynomialModel|nodal_polynomial_model_completion`: no name collision.
6. Search of `literature/blueprint/latest/blueprint` for the Stacks label and
   item name confirms the historical-source status described in the accepted split.

Validation: `scompile.py Q18 lem-trf-nodal-polynomial-model-completion` compiled
both its sandbox pass and the actual module cleanly (37.2 s and 6.3 s). A prior
scratch synthesis check confirmed the localization and completion A-algebras;
its unnecessary arbitrary-point probe lacked a Nonempty instance and was removed.
The delivered file contains no diagnostic commands, file-local notation, private
helpers, local instances or auto-bound variables. There are no lines over 100
characters. No statement dispute or correction.

## Second reading by Q18

The assigned worker reread the node and complete module after compilation; no
other agent was started, in accordance with the dispatcher's explicit instruction.
The maintainer's independent delivery review remains the independent reading.

This rereading checked the commutative/local/Noetherian/complete hypotheses and
h in m against the binders; the exact combined ideals against the first equality
and `seriesOriginIdeal`; both positive finite quotient types and both transition
squares; the normalization and quotient projections of e; the actual Spec stalk
and coefficient algebra; the unique point's quotient ideal; b's polynomial-germ
formula; ρ's coefficient-residue equation; and E's maximal-ideal source and final
polynomial-germ normalization. The coefficient-map formula for ρ is necessary:
a bare field isomorphism would omit the node's specified map. No remaining
mismatch was found. The main statement's existential j, o, and equivalences are
all characterized by canonical maps, rather than extra choices or hypotheses.
