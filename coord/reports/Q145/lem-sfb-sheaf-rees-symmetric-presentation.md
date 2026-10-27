## Worker report

The module states `AlgebraicGeometry.Scheme.IdealSheafData.sheaf_rees_symmetric_presentation`,
with one `sorry` and no new definitions. Source read: `divisors.tex`,
`lemma-blowing-up-projective` (Tag 02NS), especially its displayed graded
symmetric-to-Rees surjection. The finite-type hypothesis in that lemma is needed
for projectivity, not for this algebra surjection. No statement correction is needed.

Hypotheses and every clause, matched to the Lean:

- A scheme is `{X : Scheme.{u}}`; the quasi-coherent ideal is
  `I : X.IdealSheafData`. This interface already includes quasi-coherence via
  localization compatibility. `I.toModules` is its actual ideal module, with
  inclusion `I.toModulesι`; the result supplies `hqc`, rather than assuming a
  finite-type condition or an unavailable instance.
- The sheaf Rees algebra is precisely the recorded upstream `I.reesData`, not a
  private sheaf construction. Read its full definition and the documentation of
  `Scheme.GradedAlgebraData`: quasi-coherent graded algebra sheaves are encoded
  by affine rings, graded restrictions and coefficientwise base change. In this
  model `Gamma(U, Rees(I))` is definitionally `reesAlgebra (I.ideal U)`. Thus
  theta_U is the identity algebra equivalence. It has the existing grading
  `reesGrading`, and its unit is `algebraMap`, so its degree-zero map is the
  identity of the base ring under `reesGradingZero`.
- The `forall U n, exists e` conjunct identifies actual sections of `(I^n).toModules`
  with Rees degree n by a linear equivalence; its displayed formula is exactly
  x mapping to x t^n using `(I^n).toModulesι`. `ideal_pow` identifies the
  coefficients with `(I.ideal U)^n`. This includes n=0 and the structure sheaf.
- The `DirectSum.decomposeAlgEquiv` conjunct identifies each coefficient in the
  direct sum with the polynomial's coefficient, through `reesGradingEquivPow`.
  This is an algebra equivalence, not merely a collection of module bijections:
  its inverse sums the homogeneous monomials. Its direct-sum codomain includes
  finite support. Together with the preceding equivalences this gives the
  requested direct-sum sheaf presentation in the polynomial model.
- The `forall U V h F` conjunct says Rees restriction is `Polynomial.map` along
  structure-sheaf restriction, hence acts coefficientwise on every affine
  inclusion. On U=D(s), that restriction is the canonical localization map
  a mapping to a/1, so a t^n maps to (a/1)t^n. The statement uses the actual
  structure-sheaf restriction, rather than inventing a localization isomorphism.
- The source is exactly `SymmetricAlgebraSheaf.gradedAlgebraData I.toModules`
  from the recorded canonical-symmetric-grading dependency. `q` is a morphism
  to `I.reesData`. `GradedAlgebraData.Hom.app` is a graded ring homomorphism,
  `app_algebraMap` fixes scalars, and `naturality` commutes with restrictions.
  This is the dependency's affine-basis encoding of the sheaf algebra morphism.
- `Function.Surjective ((q.app U).gradedAddHom n)` asserts surjectivity in
  EACH degree on EVERY affine, including degree zero.
- The `Fin n` product conjunct is the exact symmetric monomial formula. For
  n=1 it is the required degree-one inclusion. The next scalar conjunct
  explicitly identifies degree zero with `Polynomial.C r`.
- `Function.Bijective (SymmetricAlgebraSheaf.sectionMap I.toModules (op U.1))`
  identifies this source with the affine sections of the actual symmetric
  algebra sheaf. `sectionMap` is a ring homomorphism and its construction sends
  scalars by the sheaf's structure morphism and generators by its inclusion;
  hence its bijectivity is exactly the canonical algebra identification.
- The second restriction conjunct writes the commutative square for q explicitly
  in the polynomial representation. It covers arbitrary sections and therefore
  also all symmetric monomials and scalars on every affine inclusion.
- The final conjunct proves uniqueness among ALL compatible affine algebra maps
  `f U`, without assuming grading on f. The hypotheses are precisely affine
  restriction compatibility and the specified degree-one inclusion. On an affine
  basis these are exactly morphisms of the sheaves of algebras. The conclusion
  `forall U a, f U a = q.app U a` is their equality.
- There are no finite-type, Noetherian, nonempty-scheme or nonzero-ideal binders.
  The universe `u` is explicit, and auto-implicit binding is disabled.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`: exposes
  `SheafOfModules.IsQuasicoherent` (the conjunction is not substituted for it).
- `WeilConjectures.AlgebraicGeometry.RelativeProj.Rees`:
  `Scheme.IdealSheafData.reesData`, its actual graded restriction definition,
  `powMulMap`, and `reesMonomial_mul_reesMonomial`. The node has no lean record,
  but its closed upstream audit records this exact source, as the brief allows.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Basic`: `IdealSheafData`, `ideal_pow`,
  `ideal_mul`, powers; upstream `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module`
  gives the actual `toModules`, `toModulesι`, section range and injectivity.
- `Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebra`:
  `exists_quasiCoherentSymmetricAlgebra`, using its concrete
  `SymmetricAlgebraSheaf.algebra`, `inclusion`, and `sectionMap` construction.
- `Sheaf.AlgebraicGeometry.CanonicalSymmetricGradedAlgebra`:
  `SymmetricAlgebraSheaf.gradedAlgebraData`, `gradedRestriction` and
  `sectionGradedAlgebra`, with degrees the powers of the inclusion range.
- `Mathlib.RingTheory.ReesAlgebra`: `reesAlgebra`, whose carrier is the
  coefficient-in-ideal-power condition.
- `WeilConjectures.Blowup.Affine.ReesPieceLocalization`: `reesGradingEquivPow`.
  Proof imports include `Mathlib.AlgebraicGeometry.Modules.Tilde` for all three
  tilde/restriction proof dependencies and
  `WeilConjectures.LinearAlgebra.SymmetricAlgebra.Graded` for the spanning proof.

Edge cases checked mathematically before writing: n=0 has empty products equal
one and I^0=R; the separate scalar formula covers every element of degree zero.
I=0 has zero positive Rees degrees, so degreewise surjectivity is still correct.
I=O has Rees algebra R[t]. On the empty affine the section rings are zero rings;
none of the equivalences or products require nontriviality. Nilpotent and
infinitely generated ideals are allowed. No intersection of arbitrary affine
opens is asserted affine. Uniqueness quantifies over ungraded competitors,
so it retains the full algebra universal-property meaning.

Searches actually run (2026-10-24):

- msearch LeanFinder: "A quasi coherent ideal sheaf symmetric algebra maps
  surjectively onto its Rees algebra with affine presentations and restriction
  compatibility". Eight hits, mostly ideal-sheaf quotient maps and Proj maps;
  none states this theorem.
- msearch Loogle: "reesAlgebra, SymmetricAlgebra". Zero hits.
- msearch LeanSearch: "For any quasi coherent ideal sheaf the symmetric algebra
  surjects degreewise onto the Rees algebra and commutes with restriction".
  Eight hits including `reesAlgebra`, `adjoin_monomial_eq_reesAlgebra`,
  `SymmetricAlgebra.lift`; no sheaf-level presentation theorem.
- msearch grep: "reesAlgebra|reesGrading" in RingTheory. Ten hits, defining the
  ring Rees algebra and its generation, not this affine sheaf presentation.
- rg in `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`:
  searched Rees/symmetric combinations, the item id, and the proposed name.
  Found upstream Rees data and the canonical symmetric data, and the different
  downstream `blowup_rees_symmetric_presentation` theorem. That theorem adds
  blowup comparison conclusions and lacks degreewise surjectivity and the
  present uniqueness assertion; it is not an exact existing match. The proposed
  declaration name is absent. No new notion or dependency repair was needed.

## Second reading by Q145

Author's second reading, as a dispatcher-started worker with no second worker;
the maintainer provides the independent review. Reopened the node and Lean file
and checked the clauses above against the actual `GradedAlgebraData.Hom`
signature. In particular, using only overall ring surjectivity would lose the
degreewise clause, so the statement uses `gradedAddHom n`. Uniqueness just
among graded maps would be insufficient, so the final clause quantifies over
ungraded algebra maps and their restriction compatibility. The source's affine
symmetric comparison is the canonical `sectionMap`, not an arbitrary equivalence.
The Rees theta does not need another chosen isomorphism: its source and target
are the same ring by the recorded definition. Actual ideal-power sections are
nevertheless linked by linear equivalences with explicit monomial formulas,
and the direct-sum coefficient formula makes the presentation explicit.
The scalar clause, n=0, zero ideal and empty affine all survive this encoding.
No mathematical statement was changed; compiler repairs disambiguated structure
ring notation and used the explicit polynomial subtype map. All declarations
are statements with `sorry`; there is no constructed data based on mere existence.
