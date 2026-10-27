## Worker report

The module `Sheaf.RingTheory.AffinoidCanonicalReductionFiniteType` states
`RestrictedSeries.affinoid_canonical_reduction_finite_type`, with its sole theorem
proof `sorry`. Its helper `RestrictedSeries.affinoidCharacterSup` is the actual
supremum function explicitly introduced in this node; it has real data (`sSup` of
the character-value set), not a selected seminorm or a postponed construction.
Both declarations are recorded in `lean.declarations` and have source/blueprint
docstrings. No independent notion, definition node, dependency repair, or statement
correction is required.

Hypotheses and conclusion, clause by clause:

- The field `K` is `[NormedField K]`; its inherited `Field` is the Mathlib match
  of `def-weil-field`. `[IsAlgClosed K]` states algebraic closedness,
  `[CompleteSpace K]` states completeness, and `[IsUltrametricDist K]` states
  nonarchimedeanness. `hK : ∃ a : K, a ≠ 0 ∧ ‖a‖ ≠ 1` is exactly nontriviality
  of this real-valued absolute value. No characteristic restriction is imposed.
- `C` has `[NormedCommRing C] [CompleteSpace C] [Nontrivial C] [IsReduced C]`
  and `[Algebra K C]`: a nonzero reduced commutative unital Banach algebra.
  No isometry condition on the chosen Banach norm is added.
- The existential `r` and surjective ring map `q` in `haff` give the quotient
  presentation from Mathlib's `MvPowerSeries.IsRestricted.subring` at polyradius
  one. `q.comp (constants K r) = algebraMap K C` gives scalar compatibility,
  using the dependency's existing `RestrictedSeries.constants`.
- The open-set equivalence in `haff` states exactly the quotient topology of
  the Gauss metric: for each series over a point of an open set, a positive
  Gauss-radius ball lies in its inverse image. The expression is the dependency's
  Mathlib `MvPowerSeries.gaussNorm`, applied to the difference of the actual
  restricted series. This avoids using the coefficientwise topology of formal
  series, which would be wrong, and avoids imposing equality of the arbitrary
  Banach norm on `C` with one particular presentation's quotient norm.
- `affinoidCharacterSup K C c` is `sSup {r | ∃ χ : C →ₐ[K] K,
  Continuous χ ∧ r = ‖χ c‖}`. Thus the supremum ranges over exactly continuous
  unital `K`-algebra homomorphisms to `K`, rather than all ring maps, all
  characters without continuity, or only a specified family of evaluations.
- `∃ (t : ℕ) (b : Fin t → C)` supplies the finite family. The first conjunct
  puts every `b i` in `C_{≤1}` by `affinoidCharacterSup K C (b i) ≤ 1`.
- Every `c : C` with spectral value at most one has a polynomial
  `p : MvPolynomial (Fin t) K` whose every coefficient has norm at most one.
  Thus the coefficients are precisely in `V = {a : K | ‖a‖ ≤ 1}`.
  The concluding strict inequality is
  `affinoidCharacterSup K C (c - MvPolynomial.eval₂ (algebraMap K C) b p) < 1`.
  It says equality in the quotient by exactly `C_{<1}`.

Why this conclusion is exactly the node's residue-algebra statement: reducing the
coefficients of `p` gives a polynomial over `κ = V/m`; the strict inequality says
that its value is the class of `c`. Conversely, a polynomial over `κ` has only
finitely many coefficients, all of which lift to `V`; evaluating the lifted
polynomial gives precisely the displayed strict inequality. Consequently the
same `t` and the same elements `b` satisfy either formulation. Neither the
coefficient lift nor the polynomial has a degree bound. This is an expansion of
the node's explicit sentence defining generation, with no extra approximation
parameter: the bound is strictly less than one, not arbitrarily small. There is
no replacement of the canonical residue action by an arbitrary algebra structure.
The quotient's ring operations are encoded by their actual polynomial operations
and the actual spectral congruence. The spectral Banach norm lemma listed in the
proof plan supplies the usual subring/ideal properties; these are not extra
hypotheses of this statement.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`, `Field` (the `mathlib_match` of
  `def-weil-field`); its full declaration extends `CommRing` and `DivisionRing`.
- `Sheaf.RingTheory.RestrictedSeriesPresentation`,
  `RestrictedSeries.constants`,
  `RestrictedSeries.IsTopologicallyFinitelyPresented`, and
  `RestrictedSeries.IsAffinoidQuotient`: their definitions/docstrings were read.
  The first is used for the canonical constants in the presentation. The
  restricted-series ring and Gauss norm are the exact Mathlib objects imported
  by this dependency. The latter predicate is not imposed on the current norm:
  it requires norm equality, whereas the node only fixes the Banach topology.
  The quotient-topology condition is also the established encoding in the
  landed `RestrictedSeries.grauert_remmert_powerbounded` module.
- Proof dependency `Sheaf.RingTheory.TateNormalizationLift`,
  `RestrictedSeries.tate_normalization_lift`, is imported with plain `import`;
  its full signature and proof docstring were read. The three other proof
  dependencies have no Lean record or Mathlib match in the supplied DAG:
  `lem-trf-affinoid-spectral-banach-norm`,
  `lem-trf-affinoid-supremum-seminorm-calculus`, and
  `lem-trf-finite-affinoid-canonical-reduction`. No unavailable module import
  is invented. The theorem docstring carries all four proof steps, including
  these node ids and the coefficient-reduction and final generator arguments.

Edge cases checked before writing:

- `r = 0` is allowed; its restricted series are constants. The theorem allows
  `t = 0`; polynomials in `Fin 0` are constants. For `C = K`, this is the expected
  empty generating family of `κ` over itself.
- The zero quotient is excluded by precisely `[Nontrivial C]`, as the node
  requires; a product of nonzero reduced affinoids is not excluded by a domain
  assumption. No domain or connectedness hypothesis is present.
- Coefficients of norm exactly one are allowed. Error of spectral value exactly
  one is excluded, so the congruence is modulo `C_{<1}`, not modulo `C_{≤1}`.
- The zero polynomial and its zero coefficients meet the coefficient bound.
  The zero class has representative zero and permits that polynomial.
- Neither a discrete valuation, positive residue characteristic, spherical
  completeness, nor a bound on the number of variables/generators is imposed.
- `K : Type u` and `C : Type v` have independent explicitly bound universes;
  all variables are explicitly bound with both auto-implicit options disabled.
- For these nonzero strict affinoids, the character set is nonempty and its
  values are bounded: the affinoid maximal-residue theorem over the algebraically
  closed field gives characters, and the quotient-Gauss bound bounds their
  values. Thus this is the actual finite supremum, not an empty-set or unbounded
  supremum artifact.

Source check: opened the current blueprint ancestor
`literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.md`;
this item is a supporting analytic node, not that unit's statement. Opened the
source URL https://webusers.imj-prg.fr/~laurent.fargues/Groupesanalytiques.pdf,
Section 1.7.1, printed p. 18. The paragraph defining `A-tilde = A^0/A^00`
explicitly states finite type over the residue field and cites BGR 6.4.3/3.
This p-adic exposition corroborates the node; the arbitrary-characteristic input
remains BGR, as the node already explains. No statement correction or dispute.
The obsolete CompactObject example is withdrawn; its node points upstream, and
the actual `WeilConjectures.CategoryTheory.CompactObject` header was read.

Searches made on 2026-10-24:

- `msearch.py ... leanfinder "The canonical reduction of a reduced strict affinoid
  algebra is finitely generated over the residue field"`: 8 hits, ordinary
  quasi-finite/residue-field/module finiteness declarations, no canonical
  affinoid reduction statement.
- `msearch.py ... loogle '"FiniteType", "spectralNorm"'`: 0 hits.
- `msearch.py ... grep 'affinoid|canonical.?reduction|spectralNorm'`: 16 returned
  hits concerning algebraic field-extension spectral norms; no matching theorem.
- `msearch.py ... leansearch "Canonical reduction of a reduced strict affinoid
  algebra is finite type over the residue field"`: 8 hits (quasi-finiteness,
  geometric reducedness, and ordinary residue-field finiteness), no match.
- `rg` for `canonicalReduction|canonical_reduction|spectral.*[Bb]all|StrictAffinoid|
  Affinoid|affinoid` in project Analysis/RingTheory and `WeilConjectures` found
  the presentation and related affinoid modules, not this statement. A focused
  follow-up search for canonical reduction, character supremum, spectral balls,
  and the proposed declaration name in `Sheaf/RingTheory` and all
  `WeilConjectures` found no duplicate. `grep -rn` of this node id in
  `lean/WeilConjectures` returned no match.
- Mathlib normed-ring, normed-field, and valuation searches found ordinary unit
  balls and algebraic-extension `spectralNorm`; that function is not the
  continuous-character supremum in this node. DAG searches showed the same
  supremum explicitly described inside neighboring analytic statements, but
  none with a usable recorded declaration defining it.

Validation: the required `scompile.py` and `deliver2.py --no-push` results are
recorded by the delivery tools. Only the expected theorem-uses-`sorry` warning
is permitted. No proof, axiom, hidden data choice, new node, or live-repository
edit is included in this delivery.

## Second reading by Q11

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
