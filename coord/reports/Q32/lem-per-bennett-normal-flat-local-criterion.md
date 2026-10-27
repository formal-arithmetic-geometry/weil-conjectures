## Worker report

The module `Sheaf.RingTheory.BennettNormalFlatLocalCriterion` states
`Ideal.flat_associatedGraded_iff_hilbertSamuel_eq_iterate_summation` with one
`sorry` and no new definition or proved theorem. Its docstring carries all eleven
steps of the accepted node proof, including the finite nilpotent-filtration input.
The node statement and proof are unchanged. Its statement dependencies gain the
already landed `def-trf-hilbert-samuel-invariant`, solely to reuse its inclusive
summation rather than introduce a duplicate notion.

Hypothesis and clause correspondence:

- A field F: `(F : Type u) [Field F]`. A commutative F-algebra R:
  `(R : Type v) [CommRing R] [Algebra F R]`. The independent universes impose
  no size equality between field and algebra.
- Nonzero Noetherian local R: `[IsNoetherianRing R] [IsLocalRing R]`.
  `IsLocalRing R` extends `Nontrivial R`, so it already renders nonzero.
  The redundant explicit `Nontrivial` binder was removed after the compiler's
  overlapping-instance warning. No reducedness or domain hypothesis on R occurs.
- Essentially finite type: `[Algebra.EssFiniteType F R]`, Mathlib's localization
  of a finite type algebra, exactly the node's definition.
- Prime I contained in m: `(I : Ideal R) [I.IsPrime]`
  and `(hI : I ≤ IsLocalRing.maximalIdeal R)`.
- A is literally `R ⧸ I`; regular local A is
  `[IsRegularLocalRing (R ⧸ I)]`.
- d = dim A: `(d : ℕ)` and
  `(hd : ringKrullDim (R ⧸ I) = (d : WithBot ℕ∞))`.
  A regular Noetherian local ring has finite nonnegative dimension, so naming
  this natural number does not restrict the statement. In particular d = 0 is allowed.
- R_I is `Localization.AtPrime I`. The local maximal ideal used in its quotient
  is exactly IR_I by `Localization.AtPrime.map_eq_maximalIdeal`.
- h_R(n) is `(Module.length R (R ⧸ maximalIdeal R ^ (n + 1))).toNat`;
  h_RI(n) is the identical expression with R replaced by `Localization.AtPrime I`.
  The complete terms in the signature qualify `IsLocalRing.maximalIdeal` explicitly.
  Powers with exponent n+1 and all n : ℕ give precisely the length convention,
  including n = 0. These quotients have finite length: for any Noetherian local
  T, the finite maximal-ideal filtration has finite-dimensional residue-field
  subquotients. Localization preserves Noetherianity, so this applies to both
  rings. Thus no infinity is silently turned into zero by `toNat`.
- Lambda is the existing `AlgebraicGeometry.HilbertSamuel.summation`, defined by
  the sum on `Finset.range (n + 1)`. `summation^[d]` is its d-fold iterate.
- The graded ring is exactly the recorded `Ideal.associatedGraded I`, with its
  canonical `Ideal.associatedGradedAlgebra I` over `R ⧸ I`, through degree zero.
  Flatness is `Module.Flat (R ⧸ I) (associatedGraded I)`. Mathlib's
  `Module.Flat.iff_lTensor_preserves_injective_linearMap` identifies it with
  the node's tensor-injection criterion for arbitrary modules.
- `↔` is both directions of the criterion, and equality of functions means
  equality for every degree, not merely an eventual polynomial identity.

Dependency interfaces read and used:

- `Mathlib.RingTheory.EssentialFiniteness`: `Algebra.EssFiniteType`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: recorded dependency module;
  its ring clause is the unchanged Mathlib `IsRegularLocalRing`, imported here.
  `IsRegularScheme` itself is not imposed on this local-ring statement.
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`,
  its local-ring structure and `Localization.AtPrime.map_eq_maximalIdeal`.
- `Mathlib.RingTheory.Length`: `Module.length`.
- `WeilConjectures.RingTheory.AssociatedGradedRing`: `Ideal.associatedGraded`,
  `associatedGradedPiece`, and `associatedGradedAlgebra`; read the direct-sum
  construction, multiplication and quotient-algebra instance.
- `Mathlib.RingTheory.RingHom.Flat`: `Module.Flat` and `RingHom.Flat` interface.
- `Sheaf.AlgebraicGeometry.HilbertSamuelInvariant`:
  `AlgebraicGeometry.HilbertSamuel.summation`. Its `localFunction` takes a scheme
  stalk rather than an abstract local ring, so the two lengths are inline applications
  of the already recorded `Module.length`, not a second Hilbert-function definition.

Every proof dependency that has a module or Mathlib match is imported privately
under the recorded module (or the module containing its Mathlib match).
`lem-per-split-nilpotent-filtration-graded-piece` currently has no recorded
Lean declaration, so it has no import; the proof docstring names its future use.
It is not needed to type this statement. No recorded statement interface required repair.

Edge cases checked mathematically:

- I = m: A is the residue field, d = 0, localization at m is R up to its
  canonical equivalence, and the Hilbert equality is the identity. The graded ring
  is a vector space over A and flat. The empty iterate is allowed.
- I = 0 when prime: A = R is regular local. The associated graded is A in degree
  zero; R_I is the fraction field, with constant length function 1. The regular
  local Hilbert function is its d-fold inclusive summation. No nonzero-centre binder.
- Nonreduced normally flat example: localize F[t,x]/(x²) at (t,x), take I = (x).
  A is F[t]_(t), d = 1, and the first two graded pieces are free of rank one.
  h_R(n) = 2n+1 while h_RI is 1,2,2,..., whose partial sums are 2n+1.
- Failure example: localize F[t,x]/(x²,tx) at (t,x), I = (x).
  The degree-one piece is A/(t), not flat. Here h_R(n) = n+2 for n ≥ 1,
  while R_I kills x and has constant length function 1; its partial sums are n+1.
  Thus neither side holds. The zero ring is excluded by the local-ring structure.

Source check: opened the Cossart--Jannsen--Saito March 12 2009 PDF at
https://epub.uni-regensburg.de/13766/1/MP32.pdf, section 2, printed pages 28–29.
Theorem 2.3 identifies normal flatness and equality of degree-wise Hilbert
functions with codimension-many summations. One further summation gives the
length convention in this node. The ambient X is excellent, not assumed reduced;
D is reduced and regular. Definition 2.1 puts a proper-centre convention on the
geometric terminology, whereas the node deliberately includes zero/nilpotent
prime centres; its explicit local algebra proof and the examples above cover
these cases without changing the meaning of flatness. No statement correction
or STATEMENT-DISPUTED flag is needed.

Searches (2026-10-24):

- msearch leanfinder: "flat associated graded ring over regular local quotient iff
  Hilbert Samuel function is iterated summation of function at prime localization".
  Eight unrelated flatness/localization results; none is Bennett's criterion.
- msearch loogle: "Ideal.associatedGraded, Module.length, Algebra.EssFiniteType".
  Zero hits, unknown identifier Ideal.associatedGraded in the Mathlib service;
  inspected and reused the project's published declaration instead.
- msearch grep: "Bennett|normal.?flat|[Hh]ilbert.?[Ss]amuel", RingTheory.
  Zero hits in Mathlib.
- msearch leansearch: "Bennett normal flatness criterion associated graded Hilbert
  Samuel function regular quotient". Eight flatness results (equational criterion,
  localization and smoothness); none states the numerical criterion.
- `rg` on `lean/WeilConjectures` and `lean/Sheaf` for Bennett, bennett,
  hilbertSamuel, HilbertSamuel and normalFlat: found the reusable HilbertSamuel
  summation and related geometric statements, but no theorem with this signature.
- `grep -rn` for the exact item id in `lean/WeilConjectures`: no match.
- Read `lem-trf-bennett-normal-flat-numerical-criterion`: its statement adds
  reducedness and it has no Lean declaration, so it is not an existing match.
- Searched the proposed full theorem name in Mathlib and both project trees:
  no existing declaration.

## Second reading by Q32

The dispatcher explicitly prohibits starting another agent; this is the author's
second pass, not a claim of independent review. Reopened the node and the final
signature and compared every binder and both sides as listed above. Checked that
no reducedness was introduced; I = 0, I = m, d = 0 and n = 0 are all admitted;
all universes and variables are explicitly bound. Corrected the redundant
nontriviality binder after compilation. The summation is the shared declaration,
the scalar action is the canonical quotient action, and the lengths use the same
base rings as the node. The maintainer supplies the independent review.
