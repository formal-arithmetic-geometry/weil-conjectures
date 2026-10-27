## Worker report

Stage 2 states `AlgebraicGeometry.exists_projectiveClosedSubscheme_homogeneousIdeal` in
`lean/Sheaf/AlgebraicGeometry/ProjectiveClosedSubschemeHomogeneousIdeal.lean`, with `sorry`.
The three supporting definitions have actual data; there are no other postponed theorems.
No statement correction, new DAG node, or dependency repair is required.

The previous worker's stale-assignment diagnosis concerned Q03's stage-1 split. The live
node has status `split`, a seven-step proof, and no Lean record or reviewed Lean delivery.
Its Q03 report explicitly says that no Lean was written. Reusing that split as the source
for this stage-2 statement respects live precedence; it does not split the node again.

Source read: Stacks `literature/stacks-project/constructions.tex`,
`lemma-closed-in-projective-space`, Tag 03GL, lines 2988–3055, including the full proof.
Both statement-dependency nodes were read, including their records and the source
declarations' signatures and docstrings. The recorded proof-dependency interfaces were
also inspected. The withdrawn CompactObject example and its current upstream replacement
were read for module and node-record conventions.

Every hypothesis and clause is represented as follows:

- Arbitrary commutative base ring: `(R : Type u) [CommRing R]`. There is no field,
  Noetherian, nonzero-ring, finite-presentation, or reducedness hypothesis.
- `n ≥ 0`: `(n : ℕ)`; the coordinates are exactly `Fin (n + 1)`, including `n = 0`.
- `B = R[z₀,…,zₙ]`, each coordinate of degree one:
  `MvPolynomial (Fin (n + 1)) R` and its existing
  `MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R` total-degree grading. The existing
  `MvPolynomial.gradedAlgebra` abbreviation is registered with a public global instance
  attribute, so downstream signatures elaborate without any file-local instance.
- The closed subscheme is a scheme `Z : Scheme.{u}` with the specified morphism
  `i : Z ⟶ Proj (homogeneousSubmodule (Fin (n + 1)) R)` and `[IsClosedImmersion i]`.
- For every `d ≥ 0`, `F : homogeneousSubmodule (Fin (n + 1)) R d` is a form in `B_d`.
  `projectiveClosedSubschemeChartFraction R n d F a` constructs the degree-zero fraction
  with numerator `F` and denominator `X a ^ d`, using `HomogeneousLocalization.mk` and
  `MvPolynomial.isHomogeneous_X_pow`; `Proj.awayToSection` makes it the corresponding
  regular function on `Proj.basicOpen … (X a)`.
- Restriction to `Z ∩ D₊(z_a)` is the actual structure-sheaf pullback `i.app` on that
  chart. Its value equals zero as a section, not merely at residue-field-valued points.
- The equivalence `F.val ∈ I ↔ ∀ a, i.app … (…ChartFraction … F a) = 0` specifies exactly
  every `I_d`. The existential `I : HomogeneousIdeal …` asserts ideal closure and
  homogeneity together. Mathlib's `HomogeneousIdeal.ext'` says that these homogeneous
  pieces determine `I`; `I.isHomogeneous.mem_iff` identifies membership of a polynomial
  with membership of all its finitely many homogeneous components. Thus this is exactly
  the node's direct sum `I = ⨁ I_d`, not some ideal with the same projective zero set.
- `projectiveClosedSubschemeQuotientGrade R n I d` is the additive subgroup image of
  `B_d` under `Ideal.Quotient.mk I.toIdeal`, in the actual ring `B ⧸ I.toIdeal`.
  The existential `GradedRing` structure certifies this exact image grading; its
  components are already defined, not chosen from an existence proof. This avoids
  assuming a grading or replacing the quotient by a freely chosen graded ring.
- `projectiveClosedSubschemeQuotientMap R n I` has underlying ring homomorphism
  definitionally equal to `Ideal.Quotient.mk I.toIdeal`, with degree preservation
  witnessed by membership in that image. No arbitrary map is quantified over.
- The existential `h` is the irrelevant-ideal inequality required by Mathlib's
  canonical `Proj.map` API. It is a conclusion about the quotient map, not an added
  hypothesis. `IsClosedImmersion (Proj.map … h)` states the asserted closed immersion.
- `∃ e : Proj (…QuotientGrade …) ≅ Z, e.hom ≫ i = Proj.map … h` identifies the schemes
  over the specified ambient Proj. It preserves the full closed-subscheme structure.
- There is no `Nonempty Z`, `IsReduced Z`, `Nontrivial R`, or `0 < n` assumption.

Dependency declarations used:

- `def-weil-closed-immersion`: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion` (class definition at line 45).
- `def-pc-proj`: the node is a Mathlib leaf with no Lean record, as allowed by the brief.
  `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme`, `AlgebraicGeometry.Proj`,
  `AlgebraicGeometry.projIsoSpec`, and `ProjectiveSpectrum.basicOpen`; the newer scheme
  chart API `Proj.basicOpen`, `Proj.basicOpenIsoSpec`, `Proj.awayToSection` in
  `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic` is used directly.
- Degree-zero fraction constructor: `HomogeneousLocalization.mk`,
  `HomogeneousLocalization.NumDenSameDeg`, and `HomogeneousLocalization.Away` in
  `Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization`.
- Homogeneous ideals and maps: `HomogeneousIdeal`, `HomogeneousIdeal.ext'`,
  `HomogeneousIdeal.isHomogeneous`, and `GradedRingHom` in Mathlib's graded-algebra
  homogeneous-ideal and graded-ring-homomorphism modules. `Proj.map` is the existing
  `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor` construction.
- The natural-language proof uses the node's existing seven steps verbatim in substance:
  linearity and products, the quotient-induced immersion and cover, localized quotient
  kernels, homogenization, overlap vanishing and denominator clearing, a finite common
  exponent, and gluing the affine identifications. The module imports the recorded
  `WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality` proof interface and the
  Mathlib standard-open, affine, ideal-sheaf, localization, spectrum and gluing modules.
  The relevant gluing interface is `Scheme.Cover.glueMorphisms`; the affine closed-ideal
  interface is `Scheme.IdealSheafData` and its subscheme construction. No interface
  needed repair, and the docstring cites each existing proof-dependency node.

Edge cases checked mathematically before writing: `n = 0` gives the single chart
`D₊(z₀) = Spec R`, and for `Z = Spec(R/J)` the degree pieces are `J z₀^d`.
For empty `Z`, all pulled-back section rings are zero, `I = ⊤`, the quotient is zero,
and its Proj is empty. For the full projective space, `I = 0`. For a double point
cut out by `(z₁²)` in `P¹_k`, section vanishing retains `(z₁²)`, unlike the radical
pointwise vanishing ideal. `R = 0`, `d = 0`, empty individual charts, and base rings
with zero divisors require no changes; no denominator is cancelled in the proof.
The witness grading of the zero quotient is also legitimate.

Searches actually run (logged by the required wrapper):

- `msearch.py … leanfinder`, query “Closed subscheme of projective space over a ring is
  Proj of quotient by homogeneous ideal of polynomials vanishing on all standard charts”:
  eight hits including `AlgebraicGeometry.Proj`, `ProjectiveSpectrum.zeroLocus`,
  `vanishingIdeal`, and `isClosed_iff_zeroLocus`; none recovers an arbitrary closed
  subscheme scheme-theoretically. The `vanishingIdeal` definition was read in full:
  it intersects homogeneous prime ideals and loses nilpotents.
- `msearch.py … loogle`, query `"Proj", "Ideal"`: twelve hits about topological
  homogeneous vanishing ideals, none stating this theorem.
- `msearch.py … grep`, query `closed.*[Pp]roj|[Pp]roj.*closed|homogeneous.*ideal`,
  subdirectory `AlgebraicGeometry/ProjectiveSpectrum`: 24 hits on the Proj construction,
  topological homogeneous ideals, and the separatedness proof; no matching statement.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for homogeneous ideals and closed
  subschemes, and of the upstream source for the exact item tag: no declaration of this
  result. `ProjectiveSpace/CurveProjection.lean` has only the integral-field coordinate
  model, whose full signature was read; it excludes this node's arbitrary-ring,
  empty, and nonreduced cases. New helper and theorem names were searched across both
  project trees, Mathlib, and `dag/lean_names_upstream.json`: no collision.
- Read the Q03 report's identification of the existing duplicate DAG item
  `lem-per-projective-closed-subscheme-homogeneous-ideal`; no duplicate module or new
  node is introduced here, and that other item is not edited.

No `STATEMENT-DISPUTED` issue was found. The only change to the copied live node is
its `lean` field. No live source or git state was edited directly.

Validation: the initial server compile required marking the two quotient constructions
`noncomputable`, because the polynomial ring instance is noncomputable. Those markers
were added; final compile and delivery preflight outcomes are recorded below.

Final standalone server compilation passed in both sandbox (2.8 s) and library-name
(2.9 s) modes, without errors or warnings. The unused implicit degree binder in the
quotient map was renamed `_d` before that clean compile.

The required `deliver2.py Q16 … --no-push` completed successfully: commit
`15d349baa94` passed the server preflight and compilation, and printed `OK (dry run)`.
The direct delivery now submits the same Lean and node record for independent maintainer review.

## Second reading by Q16

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
