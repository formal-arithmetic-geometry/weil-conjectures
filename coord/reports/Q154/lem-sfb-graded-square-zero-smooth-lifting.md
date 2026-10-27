## Worker report

The module `Sheaf.RingTheory.GradedSquareZeroSmoothLifting` states
`GradedAlgebra.exists_graded_squareZero_lift`, with its entire proof `sorry`.
It introduces no definitions or additional nodes. The node is unchanged except for `lean`.

Hypothesis and conclusion correspondence:

- A commutative base ring is `{R : Type u} [CommRing R]`.
- The commutative unital algebras are `{C : Type u} {D : Type v}` with
  `[CommRing C] [CommRing D] [Algebra R C] [Algebra R D]`.
- The integer gradings into R-submodules are `𝒞 : ℤ → Submodule R C` and
  `𝒟 : ℤ → Submodule R D`, with `[GradedAlgebra 𝒞] [GradedAlgebra 𝒟]`.
  Mathlib's GradedAlgebra is GradedRing for submodules: its DirectSum.Decomposition
  supplies existence and uniqueness of finite homogeneous expansions, while its
  SetLike.GradedMonoid supplies degree-zero unit and degree-additive multiplication.
  Since each piece is an R-submodule and the unit belongs to degree zero, every
  base scalar lies in degree zero (r = r • 1 after applying algebraMap).
- Smoothness of the specified map of spectra is
  `[AlgebraicGeometry.Smooth (AlgebraicGeometry.Spec.map
  (CommRingCat.ofHom (algebraMap R C)))]`, using exactly the recorded dependencies.
- The explicitly stated finite presentation is `[Algebra.FinitePresentation R C]`.
  Its defining field is a surjection from MvPolynomial (Fin n) R with FG kernel,
  exactly the node's quotient by a finitely generated ideal. It is retained even
  though smoothness already entails finite presentation in the affine case.
- The ideal is `(J : Ideal D)`; homogeneity is `(hJ : J.IsHomogeneous 𝒟)`.
  This says that every homogeneous component of every member belongs to J.
  Together with the ambient direct-sum decomposition, it says precisely
  J = ⨁ (J ∩ D_n), without adding a chosen decomposition of the ideal.
- Square-zero is `(hJ_sq : ∀ x ∈ J, ∀ y ∈ J, x * y = 0)`, literally the
  elementwise condition in the statement.
- The given map is `(h : C →ₐ[R] D ⧸ J)`. Its degree preservation is `hh`:
  for x ∈ 𝒞 n, h x belongs to `(𝒟 n).map (Ideal.Quotient.mkₐ R J).toLinearMap`.
  This submodule is exactly q(D_n), the quotient's degree-n component. By
  Submodule.mem_map, this says that h x has a representative of degree n.
  Homogeneity of J makes these images the quotient grading; no independent or
  arbitrary quotient grading is assumed. The statement only needs its pieces.
- The conclusion is existence of `h' : C →ₐ[R] D`; its first conjunct is
  `∀ (n : ℤ) (x : C), x ∈ 𝒞 n → h' x ∈ 𝒟 n`, precisely degree preservation.
  Its second conjunct `(Ideal.Quotient.mkₐ R J).comp h' = h` is q h' = h.
  AlgHom supplies preservation of addition, multiplication, unit, and R scalars.
- There are no hypotheses of Noetherianity, reducedness, Nontrivial, positive
  degree support, or finite support of the grading itself. Individual expansions
  are finite through DirectSum.Decomposition. D has its independent universe v;
  R and C share the universe needed for the stated map between their affine spectra.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec` and
  `AlgebraicGeometry.Spec.map`, recorded by def-weil-affine-spectrum.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`,
  recorded by def-sbc-smooth-morphisms. Its affine-local ring-map definition is
  the same smoothness notion as the node's formal-smoothness definition by Stacks 02H6.
- Proof-only import `Sheaf.AlgebraicGeometry.AffineFormallySmooth`:
  `AlgebraicGeometry.formallySmooth_spec_iff_ringHom_formallySmooth`, recorded by
  lem-weil-pbc-affine-formally-smooth-iff-ring-lifting. Its full signature and
  natural-language proof were read. The theorem docstring retains all three
  DAG proof steps and identifies this ordinary-lifting prerequisite.
- `Mathlib.RingTheory.GradedAlgebra.Basic`: GradedAlgebra, GradedRing,
  DirectSum.decomposeAlgEquiv, GradedAlgebra.proj (through Homogeneous.Ideal).
- `Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal`: Ideal.IsHomogeneous,
  with its signature and componentwise membership characterization read.
- `Mathlib.RingTheory.FinitePresentation`: Algebra.FinitePresentation.
- `Mathlib.RingTheory.Ideal.Quotient.Operations`: Ideal.Quotient.mkₐ and its
  quotient algebra instance. The quotient map is the canonical one throughout.

Sources opened: literature/stacks-project/algebra.tex, definition-formally-smooth
(Tag 00TI) and proposition-smooth-formally-smooth (Tag 00TN);
more-morphisms.tex, definition-formally-smooth (02H0) and
lemma-affine-formally-smooth (02H4). The grading refinement is the node's agent
argument, explicitly identified as such, rather than attributed verbatim to Stacks.
The current literature/blueprint/latest unit and direct-images proof were also read.

Edge cases checked mathematically before writing: J = 0 gives h itself under the
quotient identification; D = 0 and C = 0 are not excluded; if J = top and J is
square-zero, D is necessarily the zero ring, so no contradictory lift is demanded.
R = 0 forces its unital algebras to be zero, which is allowed. Degree-zero-only
algebras recover ordinary lifting. Negative degrees are fully included, and the
multiplicativity argument uses cancellation in ℤ, not nonnegativity. Infinite
sets of nonzero graded pieces are allowed because expansions, rather than the
gradings, have finite support. No source-based correction or statement dispute arose.

Searches (2026-10-24):

- msearch.py leanfinder: "A smooth integer graded commutative algebra lifts degree
  preserving algebra maps modulo a homogeneous square zero ideal" returned 8 hits:
  ExteriorAlgebra.GradedAlgebra.liftι; CliffordAlgebra.GradedAlgebra.lift_ι_eq;
  ExteriorAlgebra.GradedAlgebra.liftι_eq; ExteriorAlgebra.lift_ι_apply;
  ExteriorAlgebra.toTrivSqZeroExt; GradedAlgebra.ofAlgHom;
  ExteriorAlgebra.GradedAlgebra.ι_apply; ExteriorAlgebra.GradedAlgebra.ι.
  None gives the claimed graded smooth lifting theorem.
- msearch.py leansearch: "Every graded algebra homomorphism from a smooth integer
  graded algebra to a quotient by a homogeneous square zero ideal admits a graded
  lift" returned 8 hits: Ideal.Quotient.liftₐ, Algebra.FormallySmooth.exists_lift,
  DualNumber.lift, Algebra.FormallySmooth.lift, TrivSqZeroExt.lift,
  Algebra.FormallySmooth.liftOfSurjective_apply,
  Algebra.FormallySmooth.liftOfSurjective, liftOfDerivationToSquareZero_apply.
  The formal-smoothness hits give ordinary lifts and do not preserve a grading;
  the remaining quotient, dual-number, square-zero-extension and derivation
  constructions are not this theorem.
- msearch.py loogle: "Algebra.FormallySmooth, GradedAlgebra" returned 0 hits.
- msearch.py grep: "graded|equivariant|homogeneous" in RingTheory/Smooth returned
  5 hits, all in Mathlib/RingTheory/Smooth/NoetherianDescent.lean, concerning
  homogeneous polynomials in Noetherian descent, not this lifting assertion.
- Direct rg over lean/WeilConjectures and lean/Sheaf for the node id and
  graded/square-zero/smooth-lift patterns found no existing assertion of this
  theorem. Searches for GradedAlgebra, IsHomogeneous and quotient operations
  found the reused Mathlib interfaces; local Sheaf graded modules concern
  nonnegative grading or unrelated graded structures. grep/rg for the node id
  in WeilConjectures had no hits, and the proposed declaration name had no
  match in Mathlib, WeilConjectures, Sheaf, or dag/lean_names_upstream.json.

Validation: the prescribed scompile.py compiled the module both in sandbox and
library-path modes, cleanly, in 2.5 s and 1.4 s respectively. Every variable and
universe is explicit; there is one public theorem, one whole-proof sorry, and no
helper definitions, file-local notation, diagnostic commands, or proved lemmas.

## Second reading by Q154

I reread the node and completed Lean file clause by clause in a separate pass.
This is a self-check; no independent worker was started, as the dispatcher's
explicit instruction forbids starting other agents. The maintainer's independent
review remains the external second reading.

Checked the commutative-unital R-algebra structures, the two ℤ-indexed submodule
gradings, finite unique decomposition, degree-zero unit and scalars, and the
multiplication law against GradedAlgebra's actual two parent structures. Checked
that the spectrum map uses algebraMap R C (so its direction is Spec C → Spec R),
and that the finite-presentation instance is explicitly present. Checked that
homogeneity refers to the D-grading, square-zero quantifies over both members
of J, and the h-homogeneity condition uses the image of precisely the same D_n
under precisely the canonical quotient map. Checked that the conclusion includes
both degree preservation and equality of R-algebra maps after q, with neither
uniqueness nor a supplementary hypothesis. The degree-n representative condition
is a direct rendering of quotient grading, not an arbitrary lift of the whole
map. No mismatch was found and no statement change was needed. All three proof
steps are in the docstring; the recorded ordinary-lifting module is a plain
proof import, while the two statement dependency modules are public imports.
