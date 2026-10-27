## Worker report

The module `Sheaf.RingTheory.SeparableRegularAffinoidResidualConormal` states
`RestrictedSeries.separable_regular_affinoid_residual_conormal`, with proof `sorry`.
The only helper is the real instance `RestrictedSeries.quotientConstantsAlgebra`,
whose data is `(Ideal.Quotient.mk n).comp (RestrictedSeries.constants F r)`.
It fixes the coefficient-field action on the actual quotient; there is no arbitrary
algebra map or choice of an unknown object.

Hypothesis and clause correspondence, after reading the item and both statement
dependencies in full:

- The real-valued absolute value is the norm of `[NormedField F]`. Its nonarchimedean
  inequality is `[IsUltrametricDist F]`, completeness is `[CompleteSpace F]`, and
  nontriviality is `hF : ∃ a : F, a ≠ 0 ∧ ‖a‖ ≠ 1`.
- `r s : ℕ` includes both zero cases. The Tate algebra is exactly Mathlib's
  `MvPowerSeries.IsRestricted.subring (R := F) (fun _ : Fin r ↦ (1 : ℝ))`.
  `IsRestricted` at polyradius one says coefficient norms tend to zero along the
  cofinite filter, equivalently the node's finite epsilon-level sets. The subring
  inherits coefficientwise addition and Cauchy multiplication from `MvPowerSeries`.
  `Fin r →₀ ℕ` is the usual finite multiindex set `ℕ^r`.
- `f : Fin s → T`, `I : Ideal T`, and `hf : Ideal.span (Set.range f) = I` introduce
  exactly the finite family and its generated ideal. Naming I with this defining
  equality does not add a hypothesis on the family.
- `n : Ideal T`, `[n.IsMaximal]`, and `hIn : I ≤ n` give the maximal ideal containing I.
  The quotient `B` is the actual `T ⧸ I`; `m` is
  `n.map (Ideal.Quotient.mk I)`. No independent quotient ring or ideal is assumed.
- The residue field is the actual quotient `T ⧸ n`. Its algebra over F is the
  quotientConstantsAlgebra instance, induced by the existing constants map.
  `[Module.Finite F (T ⧸ n)]` is finite dimensionality and
  `[Algebra.IsSeparable F (T ⧸ n)]` says that every minimal polynomial is separable.
  Over fields this is exactly having distinct roots in a splitting field. These
  classes do not require introducing another residue field model.
- `hregular : IsRegularLocalRing (@Localization.AtPrime ...
  (n.map (Ideal.Quotient.mk I)) (Ideal.isPrime_map_quotientMk_of_isPrime hIn))`
  is regularity of precisely `B_m`. The explicitly supplied prime proof is an
  existing Mathlib theorem derived from hIn, not another assumption. Regularity
  after any coefficient extension is absent.
- The source of d is `I ⧸ n • (⊤ : Submodule T I)`, literally I/nI. Mathlib's
  canonical quotient-module instance gives its `T ⧸ n` vector-space structure;
  `Module.Quotient.mk_smul_mk` identifies scalar multiplication with multiplication
  by a representative. The target `Fin r → (T ⧸ n)` is the finite direct sum.
- `∃ d : ... →ₗ[T ⧸ n] ...` states existence, descent, and residue-field linearity;
  `Function.Injective d` states injectivity. For every g in I and every coordinate i,
  the witness `dg : T` has underlying series exactly
  `MvPowerSeries.pderiv F i g.val.val`, and
  `d (Submodule.Quotient.mk g) i = Ideal.Quotient.mk n dg`.
  This simultaneously states restrictedness of each derivative used and the exact
  required reduction formula. The witness is not an unspecified derivative: its
  value is uniquely fixed by equality of its underlying series. Every quotient
  class has a representative, so the formula uniquely determines d. No map is
  defined by choosing it from this existential theorem.

Dependency declarations read and reused:

- `Mathlib.RingTheory.Localization.AtPrime.Basic`, `Localization.AtPrime`
  (the recorded localization dependency; actual localization at the displayed prime).
- `Mathlib.RingTheory.RegularLocalRing.Defs`, `IsRegularLocalRing`
  (the exact ring clause of the regular-scheme dependency's mathlib_match).
  The scheme-only declaration `AlgebraicGeometry.IsRegularScheme` is irrelevant
  to this ring statement; the node explicitly retains this Mathlib ring match.
- `Sheaf.RingTheory.RestrictedSeriesPresentation`, `RestrictedSeries.constants`;
  this existing map codRestricts `MvPowerSeries.C` to the actual restricted subring.
- `Mathlib.RingTheory.MvPowerSeries.Restricted`, `MvPowerSeries.IsRestricted.subring`;
  `Mathlib.RingTheory.MvPowerSeries.Derivative`, `MvPowerSeries.pderiv` and its
  coefficient formula `coeff_pderiv` (Derivative.lean:118--130).
- `Mathlib.Algebra.Module.Torsion.Basic`, the quotient module instance at line 648
  and `Module.Quotient.mk_smul_mk` at line 651.
- `Mathlib.FieldTheory.Separable`, `Algebra.IsSeparable` (line 549) and
  `Mathlib.RingTheory.Finiteness.Defs`, `Module.Finite` (line 117).
- Plain proof imports: `Mathlib.RingTheory.Localization.Ideal` for the recorded
  localization/quotient Mathlib leaf, and
  `WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs` for
  `IsRegularLocalRing.exists_span_eq_of_isRegularLocalRing_quotient` (full source
  signature and docstring read). The cotangent-coordinate proof dependency
  `lem-per-tate-separable-local-cotangent-coordinates` has no Lean record yet;
  it is mentioned in the complete proof docstring and needs no new statement
  dependency to state this item. No unavailable proof theorem is used as data.

Sources read: Conrad, Irreducible components of rigid spaces,
https://www.numdam.org/article/AIF_1999__49_2_473_0.pdf, proof of Lemma 3.3.1,
printed p. 510 (regular point with finite separable residue field is smooth), and
Conrad's AWS notes https://math.stanford.edu/~conrad/papers/aws.pdf, Theorem 1.1.5(1),
PDF p. 4 (regularity of Tate algebras and dimension at maximal ideals). The exact
six-step algebraic conormal argument in the item is carried in the theorem docstring.
I also read the current blueprint ancestor's proof in
`literature/blueprint/latest/blueprint/sec-deligne-laumon-a1/sk-p-dl-a1-perverse/lem-per-artin-gabber-affine-curve.proof.md`.
No source correction or mathematical dispute was found.

Edge cases checked before drafting: r=0 gives T=F, so maximal n=0 and hIn forces
I=0, and both vector spaces are zero. s=0 forces I=0 by hf. An explicitly zero
family also gives I=0. The unit ideal is automatically impossible because n is
proper. Positive characteristic is allowed; only the residue extension is assumed
separable. Without separability, over F_p((t)) the ideal (x^p-t) gives a regular
field quotient but zero derivative, explaining the indispensable hypothesis.
A rational point and a nonrational finite separable point both use the same quotient
and scalar action. No perfectness, characteristic-zero, rational-point or global
regularity assumption was introduced. The scalar field is in universe u because
it is a quotient of the actual series ring; this imposes no restriction on F.

Searches run (through the prescribed msearch wrapper):

- leanfinder: `The termwise derivative of restricted multivariate power series induces
  an injective conormal map at a regular quotient point with finite separable residue
  field`. Eight hits, including `Algebra.SubmersivePresentation.cotangentComplex_injective`
  and `Algebra.FormallySmooth.iff_injective_lTensor_residueField`. These are algebraic
  smoothness statements with additional hypotheses, not the continuous Tate statement.
- loogle: `"MvPowerSeries.pderiv", "IsRestricted"`. Zero hits.
- leansearch: `Derivative map from a restricted power series relation ideal modulo
  maximal ideal times the relation ideal to a residue vector space is injective for a
  regular local quotient`. Eight hits, none an exact statement (residue-map and general
  quotient/derivation API results).
- grep: `IsRestricted.*pderiv|pderiv.*IsRestricted|conormal.*injective` in RingTheory:
  zero hits. A second grep `pderiv|IsRestricted` in RingTheory/MvPowerSeries found the
  exact existing formal derivative and restricted-series notions, read in full.
- Direct rg of `lean/WeilConjectures` and `lean/Sheaf` for restricted-series derivatives,
  residual_conormal and separable_regular_affinoid found no duplicate. The required
  grep for the item ID in `lean/WeilConjectures` found none, and the same ID is absent
  from `dag/lean_names_upstream.json`. Searches of DAG Tate/restricted-series nodes
  located the existing restricted-presentation node and the distinct ambient-coordinate
  theorem, not an existing declaration for this item's assertion.

Validation: scompile.py compiled both the sandbox and final library module cleanly
(15.3 s and 9.6 s). An initial extra closing parenthesis in the written quotient type
was corrected before the clean run. No diagnostic commands remain in the file.

## Second reading by Q10

I reread the complete node and delivered file directly after the successful compile;
this is a worker self-check, with the maintainer's independent review still required.
The field assumptions, r and s including zero, actual Tate subring, family and span,
maximal n containing I, actual quotient residue extension, finite separability and
regularity of the particular quotient localization all occur verbatim in the signature.
The residual source is n times the top submodule of I, not I squared or the cotangent
space of n. The scalars are T/n, not F. The quotientConstantsAlgebra uses constants
followed by the quotient, and the source quotient action is Mathlib's existing action.
The linear map is existential with an exact representative formula, and is explicitly
injective. The witnesses for each derivative carry equality to the actual pderiv;
no derivative property is assumed as a hypothesis. The only defect found during
compilation was the extra parenthesis reported above; its repair did not change the
statement. The final declaration has no extra geometric regularity or characteristic
hypothesis. There are no new nodes, dependency replacements, or statement changes.
