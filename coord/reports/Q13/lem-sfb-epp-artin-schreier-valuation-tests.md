## Worker report

The module `Sheaf.RingTheory.ArtinSchreierValuationTests` states
`IsDiscreteValuationRing.artinSchreier_valuation_tests`, with one `sorry` and no other
new declarations. It states the three pole tests as a conjunction. The node is unchanged
except for `lean`. No new notions, dependency repairs, or statement corrections are needed.

Source read: `literature/stacks-project/more-algebra.tex`,
`lemma-pre-characteristic-p-case`, Tag 09F0, statement and proofs of Cases (A), (B), (C)
(lines 34765–34823). The node specializes to complete DVRs and makes explicit the
integral order and residue presentation established by Case (C). Its six proof steps
are in the declaration docstring, grouped by case, with their named dependencies.

Hypotheses and objects, individually:

- `R : Type u`, `[CommRing R]`, `[IsDomain R]`, and `[IsDiscreteValuationRing R]`
  give exactly a DVR. `[IsAdicComplete (maximalIdeal R) R]` is completeness,
  including separatedness. No topology or perfectness assumption is added.
- `p : ℕ`, `[Fact p.Prime]`, and `[CharP R p]` say p is prime and R has
  characteristic p. The fraction field consequently has characteristic p.
- `E : Type v`, `[Field E]`, `[Algebra R E]`, and `[IsFractionRing R E]`
  are the specified fraction field; `a : E` is arbitrary.
- `H` is a commutative E-algebra with `eH : AdjoinRoot (X ^ p - X - C a) ≃ₐ[E] H`.
  This explicitly presents H as the quotient in the node, allowing any isomorphic
  representation. Its R-algebra and `IsScalarTower R E H` require the coefficient
  map from R to be the composite through E. These are presentation data, not an
  additional mathematical condition: the literal quotient and identity equivalence
  supply them. Abstracting the quotient avoids repeatedly unfolding the quotient
  type during instance synthesis; no field structure on H is assumed.
- D is always Mathlib's actual `integralClosure R H`; k is `ResidueField R`.
  Neither is replaced by an arbitrary ring or a choice.
- The uniformizer `π` occurs where used, in B and C. `Irreducible π` is equivalent
  to `maximalIdeal R = Ideal.span {π}` by the recorded DVR declaration's
  `IsDiscreteValuationRing.irreducible_iff_uniformizer`. This excludes zero and units.
- In B and C, `n : ℕ`, `0 < n`, and `u₀ : Rˣ` give the positive pole order and
  unit. `a = (algebraMap R E π)⁻¹ ^ n * algebraMap R E (u₀ : R)` is exactly
  `a = π^(-n)u`. The extra conditions are respectively `¬ p ∣ n` and `p ∣ n`.
- C's `∀ c : ResidueField R, c ^ p ≠ residue R (u₀ : R)` is exactly
  nonmembership of the leading residue in the set of pth powers.

Conclusions, individually:

- A is guarded by `a ∈ Set.range (algebraMap R E)`, exactly `a ∈ R`. It quantifies
  every ideal `q : Ideal (integralClosure R H)` with `[q.IsMaximal]`. It states
  `(maximalIdeal R).map (algebraMap R (Localization.AtPrime q)) =
  q.map (algebraMap (integralClosure R H) (Localization.AtPrime q))`.
  These are exactly the two extended ideals in D_q. An existential local-map
  witness registers the natural residue-field algebra; `Module.Finite` and
  `Algebra.IsSeparable` for the resulting `ResidueField R` algebra
  `ResidueField (Localization.AtPrime q)` give finite separability of the
  corresponding extension. The witness describes the same coefficient map; it
  does not assume a new map or impose a field hypothesis on H.
- B says `IsField H` and `Module.finrank E H = p`. Since p is positive, this is
  precisely a field extension of degree p, with finiteness implicit in positive
  finite dimension over the field E. The existential `IsDomain H` witness merely
  exposes the domain structure implied by `IsField H` so the DVR class can be typed.
- B's existential `IsDiscreteValuationRing (integralClosure R H)` and
  `IsAdicComplete (maximalIdeal (integralClosure R H)) (integralClosure R H)`
  say D is a complete DVR. The local-map witness enables its canonical induced
  residue algebra, not an arbitrary coefficient structure.
- B's `Function.Bijective (algebraMap (ResidueField R)
  (ResidueField (integralClosure R H)))` expresses D/m_D = k via the induced
  map, rather than an unrelated ring isomorphism. Its final ideal equality is
  `m_R D = (maximalIdeal D) ^ p`, exactly the stated ramification clause.
- C has the same field, degree, DVR, and completeness conclusions, and additionally
  equality of subalgebras `integralClosure R H = Algebra.adjoin R {s}`, where
  `s = algebraMap E H ((algebraMap R E π) ^ (n / p)) *
  eH (AdjoinRoot.root (X ^ p - X - C a))`. Thus D is exactly R[π^(n/p)T],
  not merely isomorphic to an unspecified order.
- C states `(maximalIdeal R).map (algebraMap R D) = maximalIdeal D`.
  It gives `Module.finrank (ResidueField R) (ResidueField D) = p` for the
  natural induced algebra. As p is positive, this also gives module finiteness.
- C states, for every `x : ResidueField D`, existence of `c : ResidueField R`
  with `x ^ p = algebraMap (ResidueField R) (ResidueField D) c`, exactly the
  node's specified meaning of purely inseparable.
- Finally C provides `y : D` whose image in H is exactly s, and an R-algebra
  equivalence from `AdjoinRoot (X ^ p - C (residue R (u₀ : R)))` to `ResidueField D`
  taking its polynomial generator to `residue D y`. Since R surjects onto k,
  R-algebra compatibility is also compatibility with the induced k map. This is
  the precise presentation k[ubar^(1/p)] and identifies its distinguished root.

Statement dependencies read and used:

- `def-sc-discrete-valuation-ring`: `IsDiscreteValuationRing` and
  `IsDiscreteValuationRing.irreducible_iff_uniformizer`,
  `Mathlib.RingTheory.DiscreteValuationRing.Basic` (class lines 58–60,
  uniformizer equivalence lines 91–96).
- `def-weil-pbc-adically-complete-ring`: `IsAdicComplete`,
  `Mathlib.RingTheory.AdicCompletion.Basic` (definition and Hausdorff/precomplete
  signatures read at lines 39–56).
- `def-pc-field-extension`: `Algebra` and `algebraMap`,
  `Mathlib.Algebra.Algebra.Defs` (class signature and docstring lines 90–103).
- `def-weil-pbc-integral-closure`: `integralClosure`,
  `Mathlib.RingTheory.IntegralClosure.Algebra.Basic` (full subalgebra construction
  and docstring lines 216–224).
- `def-weil-pbc-localization-at-prime`: `Localization.AtPrime`,
  `Mathlib.RingTheory.Localization.AtPrime.Basic` (definition lines 50–58),
  and `Ideal.ResidueField`, `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`
  (signature/docstring lines 27–34). The latter is definitionally
  `IsLocalRing.ResidueField (Localization.AtPrime q)`, the form used here.
  `IsLocalRing.ResidueField` and its canonical induced algebra and map are in
  `Mathlib.RingTheory.LocalRing.ResidueField.Basic` (map lines 92–103 and
  residue algebra lines 177–211).

Proof-dependency imports include the recorded modules for
`AlgebraicGeometry.exists_finite_etale_normal_generic_components`,
`AlgebraicGeometry.unramified_neighbourhood_iff_maximalIdeal_residue`,
`IsDiscreteValuationRing.complete_finite_normalization`, and
`NumberTheory.dvr_galois_degree_data`; their source signatures and docstrings were read.
The stated Mathlib proof dependencies are imported through AdjoinRoot, StandardEtale,
PrincipalIdealDomain/RationalRoot, GoingUp, Etale, and KummerPolynomial.
The proof-only nodes `lem-sfb-epp-artin-schreier-presentation` and
`lem-sfb-finite-free-field-fibre-dvr` had neither Lean record nor Mathlib match when
read, so there is no module to import yet. They are not needed to type this statement.

Edge cases checked before writing:

- A permits a=0 and the fully split H=E^p; no domain or field is assumed there.
  Every maximal ideal of the product normalization is covered separately.
- B with p=2 and n=1 has the expected totally ramified degree-two extension;
  n=0 and p-divisible n are excluded only in B as the source requires.
- C with n=p and k=F_p(t), unit residue t, gives the explicit order generated
  by πT and residue field F_p(t^(1/p)), degree p. For perfect k the C hypothesis
  is false; that case is correctly vacuous, without a perfectness assumption.
- Positive n and p|n ensure n/p>=1 in C, including the smallest case p=2,n=2.
- The zero ring and fields are excluded by the existing DVR class, exactly as
  the node's DVR definition requires. Universes u and v are explicitly bound;
  the canonical quotient has universe v and satisfies the chosen H representation.
- The conclusion uses the induced residue map throughout; an abstract isomorphism
  that could lose the coefficient embedding is insufficient and was not used.

Searches actually run through `msearch.py Q13 <item>`:

- LeanFinder: `Artin Schreier pole valuation complete discrete valuation ring ramification
  index residue inseparable` returned eight general ramification/inertia results, including
  `Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing`; none states these pole tests.
- Loogle: `IsDiscreteValuationRing, AdjoinRoot` returned zero hits.
- Mathlib grep: `artinSchreier|artin_schreier|Artin.Schreier` returned one comment in
  `Mathlib/FieldTheory/KummerExtension.lean:53`; no matching statement.
- LeanSearch: `Artin Schreier extension complete discrete valuation ring pole totally
  ramified inseparable residue` returned eight general local unramifiedness,
  residue, valuation and pure inseparability results; none matches the tests.
- `rg` on `lean/WeilConjectures` and `lean/Sheaf` for Artin–Schreier names found
  geometric coverings and sheaves and `WeilConjectures.FieldTheory.ArtinSchreierExtension`.
  Its full source was read: it constructs a field from an irreducible reciprocal
  polynomial over a field containing a finite field, and gives translations. It does
  not give a complete-DVR valuation criterion. Narrow searches in the RingTheory and
  FieldTheory directories found only that module, ValueGroupDivisible and ArtinSchreierKernel.
  The exact item-id search in `lean/WeilConjectures` had no hit. The intended theorem-name
  search in Mathlib/project/upstream-name records had no existing declaration.

Validation: `scompile.py Q13 lem-sfb-epp-artin-schreier-valuation-tests <module>`
compiled the final single theorem cleanly, in both the sandbox and its library path
(7.7 s and 2.3 s respectively). No limit was raised. The earlier concrete quotient
expressions exceeded elaboration heartbeats at the residue interfaces; using the
explicit equivalent quotient presentation resolved this without changing the objects.
No `STATEMENT-DISPUTED` issue or node fault was found.

## Second reading by Q13

No second reading by a worker: the dispatcher brief requires direct delivery and
prohibits starting other agents. The maintainer's independent review is the only
independent reading. A final self-check matched each of A, B, and C to the source
and the unchanged node, including the split case, coefficient compatibility,
completeness, both ideal equalities and the distinguished residue generator.
