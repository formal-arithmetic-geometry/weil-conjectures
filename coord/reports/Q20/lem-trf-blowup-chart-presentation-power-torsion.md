## Worker report

The module `Sheaf.AlgebraicGeometry.BlowupChartPresentationPowerTorsion` states
`AlgebraicGeometry.blowupChartPresentationPowerTorsion`. Its single proof is `sorry`.
There are no new definitions, helper axioms, dependency repairs or statement corrections.
Only the item's `lean` record is changed. I read the accepted four-step split and
Stacks `algebra.tex`, lemma-affine-blowup-quotient-description (Tag 0G8S), together
with its preceding polynomial example. They assert exactly this arbitrary-ring result.

Hypothesis and clause correspondence:

- A commutative ring R: `{R : Type u} [CommRing R]`, with arbitrary explicit universe u.
- A nonempty list of generators a,a_2,...,a_s: `(s : ℕ) (a : Fin (s + 1) → R)`.
  Lean's s counts the additional generators; thus its s=0 is the node's s=1.
  The distinguished generator is `a 0`; `a i.succ` runs through all the others.
  No regularity, Noetherian, nonzero or nontriviality hypothesis is present.
- I=(a,a_2,...,a_s): `Ideal.span (Set.range a)`.
- S=R[y_2,...,y_s]: `MvPolynomial (Fin s) R`.
- J=(a*y_i-a_i): the displayed `Ideal.span (Set.range (fun i : Fin s ↦
  MvPolynomial.C (a 0) * MvPolynomial.X i - MvPolynomial.C (a i.succ)))`.
- Q=S/J: the displayed quotient `MvPolynomial (Fin s) R ⧸ Ideal.span ...`.
- B=R[I/a] as the prescribed subalgebra of R_a: the existing
  `AffineBlowup.chartRing (Ideal.span (Set.range a)) (a 0)`, whose defining
  `Algebra.adjoin` uses the fractions of every x in I.
- The assignments induce an R-algebra homomorphism: `∃ φ : Q →ₐ[R] B`, followed
  by the first conjunct `∀ i : Fin s, ...`. That equation sends the quotient
  class `Ideal.Quotient.mk _ (MvPolynomial.X i)` to
  `AffineBlowup.chartFraction (a 0) 1 (a i.succ)` in `Localization.Away (a 0)`.
  Because B is a subalgebra, this equality in R_a specifies precisely the
  element of B. The algebra-hom type also fixes the images of all constants.
  Quotient surjectivity and polynomial algebra-hom extensionality make these
  images characterize the induced evaluation uniquely; no arbitrary map replaces it.
- Surjectivity is the second conjunct `Function.Surjective φ`.
- The exact kernel equality is rendered elementwise by the last conjunct:
  `∀ z, φ z = 0 ↔ ∃ N : ℕ, (algebraMap R _ (a 0)) ^ N * z = 0`.
  Here z and the algebraMap codomain are inferred to be Q. Naturals include N=0;
  the power and multiplication are taken in Q, not in R or B. This is precisely
  equality of the kernel's elements with the stated power-torsion set.

Dependency declarations read and used:

- `def-weil-pbc-mv-polynomial-ring`: `MvPolynomial` in
  `Mathlib.Algebra.MvPolynomial.Basic`, with `MvPolynomial.aeval` from
  `Mathlib.Algebra.MvPolynomial.Eval` and `MvPolynomial.algHom_ext` from Basic.
  Eval is publicly imported and exposes the polynomial structure and evaluation API.
- `def-nagata-blowup-chart-ring`: `AlgebraicGeometry.AffineBlowup.chartRing` in
  `WeilConjectures.Blowup.Affine.ChartAlgebra`, publicly imported. I read its full
  definition and `chartFraction`: the latter is the actual localization fraction
  `Localization.mk x ⟨a^n,n,rfl⟩`. No substitute chart algebra is introduced.
- `def-weil-ring-localization-away`: `Localization.Away` from
  `Mathlib.GroupTheory.MonoidLocalization.Away`, exposed through ChartAlgebra's
  public import of `Mathlib.RingTheory.Localization.Away.Basic`. Its abbreviation
  is localization at `Submonoid.powers a` and supplies the ring R_a used here.
- `def-weil-pbc-algebra-hom-quotient`: this mathlib node has no lean record; its
  mathlib_match supplies `AlgHom`, `Ideal.Quotient.algebra` and
  `Ideal.Quotient.mkₐ`. I read their definitions in Algebra/Algebra/Hom.lean and
  RingTheory/Ideal/Quotient/Operations.lean. The latter is publicly imported;
  the statement uses their algebra-hom type and quotient algebra instance, with
  `Ideal.Quotient.mk` for the generator classes. These are all four proof
  dependencies as well, so all their defining modules are available to stage 3.

Edge cases checked before writing:

- One generator: Lean s=0 gives no variables or relations. Q is canonically R;
  B=R[(a)/a] is the image of R in R_a, and its kernel is exactly a-power torsion.
- a=0 or a nilpotent: R_a and B are zero rings; a power kills every class of Q,
  so the entire kernel and surjectivity have exactly the stated meaning.
- R the zero ring: no nontriviality assumption excludes it; both rings are zero.
- a a unit: the relations eliminate every variable and the power-torsion is zero.
- Nonregular example R=Z, a=2, a_2=0: Q=Z[y]/(2y), and y is nonzero but maps
  to zero in B=Z. It is killed by 2, as the theorem says. Thus the statement
  does not accidentally assert injectivity.
- N=0 contributes only z=0, since a^0=1. Duplicate and zero additional
  generators are admitted by the arbitrary family a.

Searches for an existing exact statement (2026-10-23):

- msearch.py leanfinder query: "Evaluation from R[Y_i]/(a Y_i-b_i) to the blowup
  chart R[I/a] is surjective with kernel the elements killed by a power of a".
  Eight hits: AdicCompletion.evalOneₐ_surjective, AdicCompletion.surjective_evalₐ,
  Algebra.SubmersivePresentation.cotangentComplexAux_surjective,
  Algebra.Generators.aeval_val_surjective,
  AlgebraicGeometry.Proj.lift_awayMapₐ_awayMapₐ_surjective,
  MvPolynomial.counit_surjective,
  Algebra.Presentation.differentials.surjective_hom₁ and
  AlgebraicGeometry.ProjIsoSpecTopComponent.toSpec_surjective. None gives the
  prescribed quotient-to-chart map with its power-torsion kernel.
- msearch.py loogle query `"blowup", "ker"`: zero hits.
- msearch.py grep query `blowup|blowUp|blow_up|ReesAlgebra|reesAlgebra`, subdirectory
  RingTheory: ten hits in Filtration.lean and ReesAlgebra.lean. I read
  ReesAlgebra.lean's construction: it is a graded subalgebra of R[X], not this theorem.
- msearch.py leansearch query: "The kernel of the surjection from R[Y_i]/(a Y_i-b_i)
  to the subalgebra generated by b_i/a in R[1/a] is the a power torsion".
  Eight hits concerned finite-presentation kernels, AlgebraicIndependent.repr_ker,
  quotientKerAlgEquivOfSurjective (and its congr_simp), Submodule.torsionBy,
  IsLocalization.Away.of_surjective and Ideal.Quotient.torsionBy_eq_span_singleton.
  They do not state this arbitrary-ring quotient-to-chart calculation.
- rg in both project roots for the item id, proposed declaration name,
  chartRing, chart presentation, quotient/chart and power-torsion patterns:
  no exact existing statement. The regular-sequence sibling
  `AlgebraicGeometry.blowupChartRegularSequencePresentation` has a genuine
  regularity hypothesis and an isomorphism conclusion, so cannot serve here.
  `AffineBlowup.strictChartMap` and its kernel calculation concern
  a tensor-product base-change source, rather than this polynomial quotient.
  I read the regular-sequence sibling and ChartAlgebra in full.
- I also read `Algebra.Generators.ker_localizationAway` in
  Mathlib/RingTheory/Extension/Presentation/Basic.lean: it presents the full
  localization by rX-1 and is not an exact match.
- The dependency nodes' existing records were read individually; none requires repair.

The inherited BLOCKED ending concerned an unchanged stage-1 split. The current
queue lists this item at stage 2 and its current node has no lean record. The
stage-handoff rule in brief-stage2.md §0 expressly authorizes stating it now.
There is no released repair note for this item and no STATEMENT-DISPUTED issue.

Validation: scompile.py compiled the module both in its sandbox and under its
library name, in 1.6 and 1.7 seconds respectively, without errors or unaccepted
warnings. `autoImplicit false` enforces bound identifiers; all source lines are
at most 100 characters. The recorded signature is extracted verbatim up to `:=`, excluding that delimiter, as the
server preflight requires. The first dry run identified only this delimiter
formatting mismatch in the lean record; it has been repaired.

## Second reading by Q20

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
