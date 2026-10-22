## Worker report

Repair of returned head bcbe744ef723, item
`lem-sfb-finite-norm-invertible-sections`, group ND, 2026-10-22 UTC.
The delivery supplies `Sheaf.AlgebraicGeometry.FiniteNormInvertibleSections`, with
one theorem, `AlgebraicGeometry.Scheme.Modules.exists_invertible_norm_sections`.
Its entire proof is `by sorry`. No definitions, auxiliary theorems, or new nodes
are introduced. The node is copied from the current live repository, with only
`lean` added. In particular `split_report` is unchanged.

Source read: `literature/stacks-project/divisors.tex`, Section 0BCX
(`section-norms`), Lemma 0BCY (`lemma-norm-invertible`), and Lemma 0BCZ
(`lemma-norm-map-invertible`), including 0BUT for local trivializations. The seven
steps of the live node's proof are carried in the theorem docstring: choose
frames independently of n and s; norm their transition units; glue N; norm and
glue the coefficients for each tensor-power section; prove one vanishing
implication using the residue hypothesis; prove the converse using closedness,
nonvanishing trivialization, and norms of units; identify the two set descriptions.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node | Lean |
| --- | --- |
| Schemes Y and Z, morphism p | `{Y Z : Scheme.{u}} (p : Y ⟶ Z)` |
| Finite and surjective | `[IsFinite p] [Surjective p]` |
| Integer d at least one | `(d : ℕ) (hd : 1 ≤ d)`; every positive integer has this natural-number representation |
| Norm on every open V | `ν : ∀ V : Z.Opens, Γ(Y, p ⁻¹ᵁ V) →* Γ(Z, V)` |
| Preserves multiplication and 1 | `→*` is a monoid homomorphism; it imposes precisely these two laws and does not impose additivity |
| Compatible with restriction | `hν_restrict`, for every `W ≤ V` and every b; source restriction is `Y.presheaf.map (homOfLE (p.preimage_mono h)).op`, target restriction is `Z.presheaf.map (homOfLE h).op` |
| Norm of pullback of a equals a to degree d | `hν_power`, with the canonical structure-sheaf map `p.app V` |
| b vanishing at y implies norm vanishing at p(y) | `hν_vanish`, quantified over V, b, y, and `hy : y ∈ p ⁻¹ᵁ V`; both values are the recorded `Scheme.evaluation` into residue fields |
| Every invertible M on Y | `(M : Y.Modules) [M.IsInvertible]` |
| One invertible N on Z | `∃ N : Z.Modules, N.IsInvertible ∧ ...` occurs before both n and s |
| Every positive tensor exponent n | `∀ (n : ℕ), 1 ≤ n → ...` |
| Every global s of M tensor n | `∀ (s : Γ(M.tensorPow n, ⊤)), ...` |
| There exists global t of N tensor n | `∃ t : Γ(N.tensorPow n, ⊤), ...` |
| Z_t equals the complement of p(Y outside Y_s) | First equality: `nonvanishingLocus (N.tensorPow n) t = (p '' (nonvanishingLocus (M.tensorPow n) s)ᶜ)ᶜ` |
| Z_t equals the points with entire fibre in Y_s | Second equality: `nonvanishingLocus (N.tensorPow n) t = {z : Z | p ⁻¹' {z} ⊆ nonvanishingLocus (M.tensorPow n) s}` |
| Recorded tensor powers and nonvanishing loci | `Scheme.Modules.tensorPow` and `Scheme.Modules.nonvanishingLocus`, from the dependency modules below |
| No ampleness requirement | There is no `IsAmple` hypothesis; only invertibility is required |

Statement dependencies read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `Scheme.Opens`, `Scheme.Hom.app`, and `Scheme.Hom.preimage_mono`.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`.
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`:
  `AlgebraicGeometry.Surjective`, the recorded surjectivity class.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.residue`, and `Scheme.evaluation`; the latter is explicitly germ
  followed by the residue quotient, so the zeros in `hν_vanish` are residue zeros.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `Scheme.Modules.IsInvertible` and `Scheme.Modules.tensorPow`.
- `WeilConjectures.AlgebraicGeometry.Ample`:
  `Scheme.Modules.nonvanishingLocus`, the germ-outside-maximal-ideal-times-stalk
  predicate recorded by `def-weil-pbc-ample-invertible-module`.

Already stated proof dependencies are imported privately:

- `WeilConjectures.AlgebraicGeometry.GlueComponentTransitionCocycle`,
  `AlgebraicGeometry.exists_invertible_of_cech_transition`.
- `WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor`,
  `Scheme.Modules.invertible_pullback_tensor`, especially tensor invertibility.
- `WeilConjectures.AlgebraicGeometry.NonvanishingSectionTrivializes`,
  `Scheme.Modules.nonvanishing_section_trivializes`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper` and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite`, for the finite-morphism
  properness instance and `Scheme.Hom.finite_preimage_singleton`; the former
  exposes `Scheme.Hom.isClosedMap` from UniversallyClosed.

The proof dependency `lem-sfb-finite-trivialize-invertible-upstairs` has no Lean
record or Mathlib match in the live node; its seven-step proof-plan reference
is retained in the docstring. It is not needed to type this sorry statement,
so no unstated module is imported or recreated. The maintainer can add its
private proof import when that independent statement lands.

Searches made before writing:

- `msearch.py ... leanfinder`, query: "A multiplicative norm for a finite morphism
  of schemes gives invertible sheaves and norm sections with fibrewise
  nonvanishing loci". Eight hits: `StructureSheaf.normalize_finite_fraction_representation`,
  `Scheme.Hom.normalizationDiagram`, `Algebra.norm_localization`,
  `Scheme.Hom.toNormalization_app_preimage`, `Scheme.Hom.normalizationDiagramMap`,
  `Scheme.Hom.normalization`, `Algebra.norm_eq_iff`, and the normalization
  integral-morphism instance. None states this theorem.
- `msearch.py ... loogle`, query: `"norm", "Invertible"`. Four hits:
  `Mathlib.Meta.NormNum.invertibleOfMul`, `invertibleOfMul'`,
  `NormedSpace.invertibleExp`, and `invertibleExpOfMemBall`; none concerns norms
  of invertible sheaves.
- `msearch.py ... leansearch`, query: "A norm of degree d for a finite morphism
  constructs norm invertible sheaves and sections with nonvanishing on entire
  fibres". Eight hits, including `Algebra.norm`, `FiniteField.norm_surjective`,
  normalization declarations, `IsFinite.mk`, and `Algebra.intNormAux`.
  These supply algebraic norms or unrelated geometry, not the theorem here.
- `msearch.py ... grep`, query:
  `[Nn]orm.*[Ii]nvertible|norm.*lineBundle|normSection`, subdirectory
  `AlgebraicGeometry`. Two hits in EllipticCurve/NormalForms about normal forms
  with 2 or 3 invertible; no matching statement.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf`, by norm/invertible/section
  patterns and the exact item id: no existing theorem. Read the related
  `FiniteLocallyFreeNormCharts`, `NormalIntegralFiniteSheafNorm`, and
  `FiniteNormalAmpleDescent`; the first treats determinant norms on function
  rings, the second constructs the hypotheses here, and the third uses this
  theorem to descend ampleness. They do not duplicate its conclusion.

Edge cases checked before writing: d = 1 and the identity morphism with the
identity norm recover N = M and t = s. The positive-exponent condition excludes
n = 0 exactly as in the node, while tensorPow still has its recorded zero-power
definition. No nonemptiness binder excludes empty schemes or empty opens; a
surjection from an empty Y forces Z empty and the section conclusion is valid.
For the zero section, `hν_power` at zero and d positive force norm zero, giving
the empty nonvanishing locus on both sides. Nonreduced schemes are retained:
the vanishing hypothesis uses residue-field evaluation, not equality of germs
or of global functions. No normality, integrality, flatness, quasi-compactness,
or ampleness assumptions were added. The sole universe u is explicit and
arbitrary. There is no statement dispute or statement correction.

Return points repaired: H1 now has a real theorem module and complete lean
record; H2 is fixed by starting from the live node and preserving all other
fields, including split_report; H11 is addressed by the detailed second reading
below; A6/A7 are addressed by supplying new stage-2 mathematical content rather
than repushing a cosmetic stage-1 change. No Git command was run in the shared
repository. Only the authorized wrappers compile and deliver this sandbox.

Validation: scompile.py compiled the file as sandbox and as its intended library
module, cleanly (2.5 s and 2.6 s respectively). There is exactly one postponed
theorem and no definition with postponed data. The signature in lean.statement
is copied verbatim from the theorem keyword up to its proof delimiter.

## Second reading by ND

A separate reading pass by this worker reopened the live node and the completed
module together after compilation. No second agent was started, as the dispatcher
brief explicitly forbids starting agents; the maintainer's independent review
remains separate from this worker's rereading.

The schemes, finite/surjective binders, positive d, all-open norm family, and
restriction equation match the first sentence. In particular `→*` supplies both
multiplication and one without accidentally requiring addition. The next two
hypotheses exactly render the power and residue-vanishing conditions: `p.app V`
is the actual pullback of functions, and both `evaluation` applications land in
the respective residue fields. The same `hy` is definitionally membership of
`p y` in V, which the clean compile confirms.

The binder `(M : Y.Modules) [M.IsInvertible]` covers every invertible module.
The existential `∃ N` and `N.IsInvertible` are outside all n/s binders; there is
no possibility of choosing a different N for different powers or sections.
Both tensor powers use the recorded `tensorPow`. Every s at the top open gets
a t at the top open, and both equalities use the recorded `nonvanishingLocus`.
The first complement is in Y and its image complement is in Z, exactly
`Z ∖ p(Y ∖ Y_s)`. The second uses preimage of the singleton under p, not image
of a singleton or existence of just one nonvanishing point. Its subset condition
therefore requires the whole fibre to lie in Y_s. The two equalities share the
same t, as the node requires. No `IsAmple` binder appears.

Rechecked the seven proof steps against divisors.tex: the frame convention
`e_i = u_ij e_j` entails `b_j = b_i u_ij^n`, so the norm coefficients glue in
the frames `f_i = ν(u_ij) f_j`. The converse nonvanishing implication uses a
unit after shrinking by the finite closed image, not an unjustified assertion
that ν detects every zero without shrinking. The final elementary set equality
and all three Stacks citations are present in the docstring.

No mathematical mismatch was found in this pass and no signature change was
needed. A field-by-field comparison with the current live node found exactly
one changed key, `lean`; split_report and the source/proof/dependency fields
were checked equal. The new report and theorem directly fix the returned
delivery's missing stage-2 content.
