## Worker report

Item: lem-per-scheme-near-point-order-generators. The module
Sheaf.AlgebraicGeometry.SchemeNearPointOrderGenerators states
AlgebraicGeometry.HilbertSamuel.scheme_near_point_order_generators, with its
entire proof `sorry`. No construction, theorem proof, or existing source is changed.
The node statement, proof and proof dependencies are retained verbatim. Only lean
and the authorized addition of two already landed definition dependencies change.

Clause-by-clause correspondence:

- Any field F: `{F : Type v} [Field F]`; arbitrary characteristic and an independent
  coefficient universe. The ring is `{R : Type u} [CommRing R] [IsLocalRing R]
  [IsNoetherianRing R] [Algebra F R] [Algebra.EssFiniteType F R]`. Mathlib's
  IsLocalRing extends Nontrivial, so the nonzero hypothesis is included.
- The prime centre contained in the maximal ideal is `(I : Ideal R) [I.IsPrime]
  (hI : I ≤ IsLocalRing.maximalIdeal R)`. The regular local quotient A=R/I is
  `[IsRegularLocalRing (R ⧸ I)]`, using the dependency's unchanged Mathlib ring clause.
- The non-component hypothesis is `hcomponents : ∀ p ∈ minimalPrimes R, ¬ I ≤ p`.
  These are all minimal primes, with no reducedness requirement.
- k=R/m is IsLocalRing.ResidueField R. G=gr_I R is Ideal.associatedGraded I,
  with its canonical R/I-algebra instance. Flatness is exactly
  `[Module.Flat (R ⧸ I) (Ideal.associatedGraded I)]`.
- S=G tensor_A k is the existing Ideal.normalConeFibre I hI, whose actual
  construction is k tensor_A G with the quotient-factor A action on k. The tensor
  commutation is canonical; this is the same graded commutative k-algebra.
- `𝒮` is the homogeneous-piece family, with `[GradedAlgebra 𝒮]` and `h𝒮`
  fixing every piece as the k-span of all canonical degree-n initial classes.
  This spells out the tensor-product grading and leaves no freedom to regrade S.
  It is not a second definition of the fibre or its homogeneous pieces.
- `φ : reesGrading I →+*ᵍ 𝒮` is fixed by `hφ` on EVERY Rees monomial a*t^n:
  its image is 1 tensor the degree-n class of a. These monomials additively
  generate the Rees algebra, so this specifies the canonical fibre quotient,
  rather than an arbitrary map or projective isomorphism. `hirr` is the irrelevant
  ideal certificate needed by Proj.map. This certificate follows for the canonical
  surjection. Together these binders explicitly encode the fibre identification
  already required by the node, with no additional geometric assumption.
- `y : AffineBlowup I` is the point of the node's actual blowup, and
  `hy : AffineBlowup.toSpec I y = IsLocalRing.closedPoint R` states precisely
  that it lies over the closed point. `t : Proj 𝒮` and `ht : Proj.map φ hirr t = y`
  select its representative under that canonical fibre identification.
- R_y and n_y are the scheme stalk and its maximal ideal in the existing
  HilbertSamuel.localFunction (AffineBlowup I) y. Its value is exactly
  `(Module.length R_y (R_y ⧸ n_y^(n+1))).toNat`.
- δ is a natural-number binder with hδ equating its cardinal to Algebra.trdeg
  k ((Proj 𝒮).residueField t), using EXACTLY the scalar action induced by
  Proj.toSpecOfAlgebra through residueFieldAlgebraMap. The canonical closed-fibre
  immersion identifies this residue extension with k → κ(y). Thus δ is the
  node's transcendence degree, not a free exponent. This degree is finite here:
  the blowup closed fibre is finite type over k. No rationality, separability or
  closedness assumption is placed on t or y.
- Λ is the existing inclusive HilbertSamuel.summation, and `hnear` is its δ-fold
  iteration applied to h_y, equal as a function to the R-lengths of R/m^(n+1).
  Both sides use toNat only on finite lengths: R is Noetherian local and the
  blowup is finite type over Spec R, so its local rings are Noetherian. This
  loses no information. The exponent is δ, with no extra summation.
- Q is MvPolynomial (Fin e) k with `(e : ℕ)` arbitrary. The k-algebra map α and
  `hα : Function.Surjective α` express Q onto S. `hgraded` says each homogeneous
  degree-n form maps to 𝒮 n. `hdegreeOne` is bijectivity of the restricted map
  `{f | f.IsHomogeneous 1} → (𝒮 1 : Set _)`, so exactly Q_1 onto S_1.
  Standardness of S follows from this finite graded presentation; no independent
  standardness or generation assumption is added.
- J is literally RingHom.ker α.toRingHom. It is homogeneous because α is graded.
  `q : Ideal Q` with `[q.IsPrime]` and `hq` fix q as the inverse image of
  t.asHomogeneousIdeal.toIdeal. No unrelated prime or arbitrary localization
  is used. Primality is a redundant structural certificate for the comap prime.
- The conclusion is J = Ideal.span of all H in J with some `d : ℕ`, `0 < d`,
  H.IsHomogeneous d, and algebraMap Q (Localization.AtPrime q) H belonging to
  `(q.map (algebraMap Q (Localization.AtPrime q))) ^ d`. This is precisely
  H/1 in (q Q_q)^d in the ORDINARY localization. It is an ideal-generation
  equality, not just a local generation assertion or a single suitable element.
- There is no IsReduced binder, no characteristic restriction, and no nonempty
  generating-family requirement. If J=0 the displayed set contains only zero;
  its span is zero, also generated by the empty family as the node permits.

Dependency declarations read and used:

- Mathlib.RingTheory.EssentialFiniteness: Algebra.EssFiniteType, the localization
  of a finite-type algebra; Mathlib.RingTheory.Noetherian.Defs: IsNoetherianRing.
- Mathlib.RingTheory.RegularLocalRing.Defs: IsRegularLocalRing, the ring clause
  retained by def-weil-regular-scheme. Also imported its recorded scheme module
  Sheaf.AlgebraicGeometry.IsRegularScheme; its scheme predicate is not substituted
  for regularity of the quotient ring.
- WeilConjectures.RingTheory.AssociatedGradedRing: Ideal.associatedGradedPiece,
  Ideal.associatedGraded, its CommRing and R/I-algebra structures.
- Mathlib.LinearAlgebra.TensorProduct.Defs and Mathlib.RingTheory.TensorProduct.Basic:
  TensorProduct and its tensor-product ring/algebra structures.
- Mathlib.RingTheory.RingHom.Flat: Module.Flat and RingHom.Flat (module form used).
- Mathlib.AlgebraicGeometry.Scheme: Spec;
  WeilConjectures.Blowup.Affine.Defs: AffineBlowup and AffineBlowup.toSpec;
  Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic/Scheme: Proj;
  WeilConjectures.AlgebraicGeometry.RelativeProj.Affine: Proj.toSpecOfAlgebra
  and the canonical graded Proj morphism API.
- Mathlib.RingTheory.Length: Module.length;
  Mathlib.RingTheory.AlgebraicIndependent.Basic: Algebra.trdeg;
  Mathlib.AlgebraicGeometry.ResidueField: Scheme.residueField, Hom.residueFieldMap;
  WeilConjectures.ZetaSeries: Scheme.Hom.residueFieldAlgebraMap.
- Mathlib.Algebra.MvPolynomial.Basic: MvPolynomial;
  Mathlib.RingTheory.MvPolynomial.Homogeneous: IsHomogeneous, homogeneousSubmodule;
  WeilConjectures.RingTheory.GradedAlgebra.Standard: GradedAlgebra.IsStandard
  (its existing homogeneous/Proj interfaces are reused, not copied).
- Mathlib.RingTheory.Localization.AtPrime.Basic: Localization.AtPrime.
- Added existing definition dependency def-trf-normal-cone-residue-fibre:
  Sheaf.RingTheory.NormalConeDirectrixMinimalPrimes, Ideal.normalConeFibre,
  Ideal.normalConeFibreClass and their canonical quotient/tensor instances.
- Added existing definition dependency def-trf-hilbert-samuel-invariant:
  Sheaf.AlgebraicGeometry.HilbertSamuelInvariant, HilbertSamuel.summation and
  HilbertSamuel.localFunction. These prevent duplicating the numerical functions.

Proof-only imports of already stated dependencies: the regular polynomial-ring
Mathlib result, WeilConjectures.RingTheory.RegularLocalQuotientKernelParameters,
WeilConjectures.Blowup.FiniteDegree.Algebra, and
WeilConjectures.Blowup.Affine.ChartAlgebra. The normal-flat double-initial-ideal,
parameter-blowup-regularity, and two nonreduced permissible-standard-basis nodes
have no recorded Lean declaration; they are referenced by ID in the complete
nine-step proof docstring and are not replaced by stronger hypotheses. They are
proof prerequisites only and are not needed to state this item.

Edge cases checked before writing: I=0 makes the blowup empty, so no y exists;
I=m is allowed when the non-component condition holds; e=0 is not artificially
excluded (a projective point will force a positive-degree fibre); J=0 has the
zero ideal span; δ=0 gives the raw equality without summation; nonrational and
inseparable residue points use the same canonical field embedding. For a
nonreduced test, R=k[u,v]_(u,v)/(v^2), I=m, the near chart over [1:0] has
R_y=k[u,t]_(u,t)/(t^2); both raw Hilbert functions are 2n+1. The minimal fibre
presentation has J=(V^2), q=(V), and V^2 belongs to (q Q_q)^2 as required.
No statement dispute or correction was found.

Searches actually run with the prescribed msearch.py Q63/item wrapper:

- leanfinder: "Homogeneous equations of normal cone fibre at a Hilbert Samuel near
  point are generated by forms of maximal order in the localization at the
  projective point". Eight hits, projective chart carriers and homogeneous
  localization, no near-point ideal-generation theorem.
- loogle: "MvPolynomial.IsHomogeneous, Ideal.span, Localization.AtPrime".
  Zero hits.
- leansearch: "homogeneous ideal generators normal cone blowup Hilbert Samuel
  equality". Eight hits, homogeneous ideals, homogeneous_span and irrelevant
  ideals; no numerical near-point statement.
- grep: "near.point|normal.flat|order.generators" in Mathlib. Ten unrelated
  collinear-point results, no match.
- rg in lean/WeilConjectures and lean/Sheaf for order.generators, OrderGenerators,
  near.point and nearPoint; node-ID grep in WeilConjectures: no existing theorem.
  The related HilbertSamuelNearNormalCone theorem assumes reducedness and
  characteristic zero and has a different conclusion, so is not an attachment.
- DAG rg found the reduced twin lem-trf-near-blowup-order-generators, which has no
  Lean binding and adds reducedness, so cannot state this item. Searches for the
  normal-cone construction found the existing def-trf-normal-cone-residue-fibre
  record and the already used canonical constructions. No new definition needed.

Sources opened: the latest blueprint ancestor's statement and its historical-branch
metadata, Hironaka's original PDF at
https://scispace.com/pdf/certain-numerical-characters-of-singularities-18d51ii5bz.pdf
(basic assumptions and Theorem III, pp.155--156, Proposition 21, p.181), and
Dietel's dissertation https://d-nb.info/1068056037/34 (chapter 9 context).
The theorem's docstring preserves all nine accepted DAG proof steps and their
cited inputs, including the ambient-to-minimal polynomial retraction.

Validation: prescribed scompile.py server compilation; no errors or unexpected
warnings. Final delivery preflight and compilation are recorded by deliver2.py.

## Second reading by Q63

Final worker rereading with the node and module open; the separate maintainer
review will be independent, as the dispatcher brief specifies. I checked the
nonzero local F-algebra hypotheses, all five centre/flatness clauses, the raw
inclusive-summation exponent, the actual blowup stalk, minimal degree-one
presentation, comap prime, ordinary localization and full ideal span. I made the
source and target of the degree-one restricted map explicit after the first
clean compile, so its signature reads without metavariable inference. The fibre
grade and Rees map are pinned by h𝒮 and hφ, and ht ties t to y. Using κ(t) in hδ
is valid precisely because this is the canonical closed-fibre inclusion; an
arbitrary projective identification would not suffice. The two existing
construction nodes were added to stmt_deps instead of privately redefining the
fibre or Hilbert functions. No additional hypothesis, omitted clause, or new
node is required, and no node statement was corrected.
