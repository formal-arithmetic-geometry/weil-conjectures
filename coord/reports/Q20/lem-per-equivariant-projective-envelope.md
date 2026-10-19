## Worker report

The module `Sheaf.AlgebraicGeometry.EquivariantProjectiveEnvelope` states
`AlgebraicGeometry.exists_equivariant_projective_envelope`, with a single whole-proof `sorry`.
There are no definitions, new nodes, dependency repairs, or changes to the mathematical statement.
The node copy changes only `lean`. All universes and variables are explicitly bound and
`autoImplicit` is false. There are no local instances, local notation, hidden choices, or lets.

The previous worker's stale-assignment diagnosis conflated stage 1 with stage 2. The merge of
Q41 recorded at ledger line 41752 supplied the eight-step DAG split and one proof prerequisite;
its report expressly says it wrote no Lean file. The current item's `lean` and `reviewed_lean`
were absent, and the queue listed it at stage 2. This delivery performs that remaining stage.

Hypothesis-by-hypothesis reading:

- A commutative Noetherian ring: `(R : Type u) [CommRing R] [IsNoetherianRing R]`.
- S is Spec R: every base is literally `Spec (.of R)`; no independent scheme or identification.
- V to S: `(V : Scheme.{u}) (f : V ⟶ Spec (.of R))`.
- f has finite type: `[LocallyOfFiniteType f] [QuasiCompact f]`, the two conditions of the
  recorded `def-weil-finite-type-morphism` interface.
- A locally closed immersion into some P^n over S: `hV` existentially supplies a natural
  number n and `i : V ⟶ ℙ(ULift.{u} (Fin (n + 1)); Spec (.of R))`, with `IsImmersion i`
  and `i` followed by the projective-space structure map equal to f. Mathlib's
  `IsImmersion.isImmersion_iff_exists` says precisely closed immersion followed by open
  immersion, including closed into an actual open via `liftCoborder`. The ULift only puts
  the finite coordinate type in the scheme universe. n=0 is included.
- A finite group: `(H : Type v) [Group H] [Finite H]`, with independent group universe.
- An action by S-automorphisms: `(a : H →* Aut V)` and
  `ha : ∀ h, (a h).hom ≫ f = f`. The monoid hom supplies identity and composition laws.

Conclusion clause-by-clause reading:

- N is a nonnegative integer: existential `N : ℕ`.
- A homogeneous ideal in the standard polynomial algebra: `I : Ideal (MvPolynomial
  (Fin (N + 1)) R)` together with closure under every `MvPolynomial.homogeneousComponent`.
  This is the defining homogeneity condition, expanded to avoid a file-local instance
  activating Mathlib's deliberately non-global `MvPolynomial.gradedAlgebra`.
- A is R[z_0,...,z_N]/I: every subsequent ring is the actual type
  `MvPolynomial (Fin (N + 1)) R ⧸ I`, with its canonical quotient R-algebra structure.
  Neither a chosen replacement ring nor an existence-selected carrier is used.
- The grading has deg z_i=1: the existential `𝒜 : ℕ → AddSubgroup A` and
  `GradedRing 𝒜` satisfy, for every d and x, `x ∈ 𝒜 d` iff x is the quotient image of
  a polynomial `p.IsHomogeneous d`. These are exactly the quotient homogeneous pieces
  of the total-degree grading. This specifies all pieces, not only the generators.
- H acts by graded R-algebra automorphisms: `ρ : H →* (A ≃ₐ[R] A)` supplies algebra
  automorphisms and action laws. `φ : H → (𝒜 →+*ᵍ 𝒜)` and
  `∀ h x, φ h x = ρ (h⁻¹) x` assert preservation of every grade. Inversion is bijective
  on H, so this is equivalent to every ρ h being graded, in both directions.
- The induced left action on M=Proj(A): the ring map used for the h-action is precisely
  φ h, i.e. ρ(h⁻¹); `Proj.map` is contravariant. The witnesses `hφ h` are the
  irrelevant-ideal bounds required by Mathlib's canonical Proj.map, automatic for these
  graded automorphisms. No independent geometric action or arbitrary comparison is chosen.
  Identity and composition of this geometric action follow from the group laws for ρ
  and `Proj.map_id` / `Proj.map_comp`.
- The H-equivariant open immersion is `j : V ⟶ Proj 𝒜`, `IsOpenImmersion j`, and
  `∀ h, (a h).hom ≫ j = j ≫ Proj.map (φ h) (hφ h)`.
- M is a closed subscheme of the indicated P^N_S: `k : Proj 𝒜 ⟶
  ℙ(ULift.{u} (Fin (N + 1)); Spec (.of R))` and `IsClosedImmersion k`.
- All these maps use the specified base: `r₀ : R →+* 𝒜 0` has underlying map
  `algebraMap R A`; thus the base map of Proj is literally
  `Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom r₀)`. The two structure-map equations
  assert that k and j are over S. The defining equation for r₀ makes this the canonical
  degree-zero map, rather than an unrelated surjection.
- Surjectivity of R to A_0 is `Function.Surjective r₀`.
- Empty V and empty M are permitted: there is no nonempty/integral/reduced assumption
  on either scheme, nor `Nontrivial` on R or A. There is no faithful-action assumption
  and no invertibility, characteristic, tameness, or coprimality condition.

The extra existential grading/ring-map witnesses are just Mathlib's data for the specified
quotient grading and canonical maps, determined by the displayed equations. They impose no
additional mathematical hypothesis. `k` states the closed finite-projective-space embedding
required by `def-kun-projective` (the `IsHProjective` convention); the finite dimension is
explicit rather than encoded by an additional projectivity proposition.

Dependencies read and used (full signatures and docstrings, not only names):

- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing` (all ideals finitely generated).
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec` and `AlgebraicGeometry.Spec.map`.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`, and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`, `AlgebraicGeometry.QuasiCompact`.
- `def-weil-closed-immersion`: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion`; the locally closed factorization is the
  recorded `Mathlib.AlgebraicGeometry.Morphisms.Immersion` interface described above.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion`.
- `def-pc-proj`: its recorded Mathlib matches are `AlgebraicGeometry.Proj`,
  `AlgebraicGeometry.projIsoSpec`, and `ProjectiveSpectrum.basicOpen`; the first is the
  scheme in the statement, and the latter two describe its standard affine charts.
  The declaration is in `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme`.
- `def-kun-projective`: `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`,
  `AlgebraicGeometry.IsHProjective`, whose public projective-space API supplies ℙ and its
  projection. The current module was read using `scompile.py --source` because the older
  upstream checkout lacks it. This is the canonical finite-coordinate embedding convention.
- `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor`: `AlgebraicGeometry.Proj.map`
  is the actual induced morphism used in the equivariance equation; it carries the
  homogeneous localization maps on standard opens.
- `Mathlib.RingTheory.MvPolynomial.Homogeneous`: `MvPolynomial.IsHomogeneous` and
  `MvPolynomial.homogeneousComponent`; `Mathlib.RingTheory.Ideal.Quotient.Operations`
  supplies the actual algebra quotient. `Mathlib.CategoryTheory.Endomorphism` supplies Aut.

Statement dependencies are imported publicly, directly or via the public imports of
`Morphisms.Immersion`, `ProjectiveSpectrum.Functor`, and the canonical upstream
`Morphisms.Projective` module. Proof dependencies already stated are imported privately:
Mathlib Noetherian, IdealSheaf.Subscheme, the upstream ProjectiveSpace.Product
(including its Segre import), ChowLemma.ClosedModel, RelativeProj.Functoriality, and
Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper. The elementary closed-immersion
composition, base change and properness interfaces are already included by the statement
imports. The proof-only prerequisite `lem-per-projective-closed-subscheme-homogeneous-ideal`
has no recorded Lean declaration yet, so no nonexistent import is added. It is not required
to type the statement. There is no proof-import cycle. The docstring carries all eight DAG
proof steps and names that prerequisite for the eventual proof.

Source and edge-case reading:

I read Stacks constructions.tex Tag 01WD, including the product-coordinate Segre map, Tag
03GL in full, and morphisms.tex Tag 01R8. The given node is explicitly the combined
finite-group assertion, rather than a claim that any one of these tags states it verbatim.
Its full proof explains scheme-theoretic kernel invariance and inverse-action conventions.

For empty V one can take N=0, I=the unit ideal, A=0, all homogeneous pieces zero and empty
Proj; the canonical degree-zero map is still surjective. If R=0 every scheme over Spec R
is empty, giving the same case. For trivial H the product has one factor and the same
construction is just closure; for nonfaithful H duplicate translates cause no difficulty.
For n=0 the coordinate set remains nonempty, so N=0 is valid. In characteristic dividing
|H| all operations are permutations, kernels and quotients, with no averaging. For a
closure supported over R/J the correct zeroth piece is a quotient of R, which is why only
surjectivity is asserted, not an isomorphism. A nilpotent thickening is retained by the
ideal quotient and scheme-theoretic closure, with no radical ideal or reduced scheme used.
The group has arbitrary universe v; finite products can be indexed after enumerating H,
so it is not restricted to the base-ring universe. No statement dispute was found.

Searches made on 2026-10-19:

- msearch LeanFinder: `finite group equivariant projective compactification of a quasi
  projective scheme with homogeneous coordinate ring`: eight hits, chiefly Proj,
  Proj properness and structural maps. No equivariant envelope theorem.
- msearch Loogle: `"Proj", "MulSemiringAction"`: zero hits.
- msearch Mathlib grep under AlgebraicGeometry:
  `equivariant.*[Pp]roj|[Pp]roj.*equivariant`: zero hits.
- msearch LeanSearch: `equivariant projective compactification of a quasi projective
  scheme under a finite group`: eight hits on vector-space projectivization actions,
  one-point projective line actions, coinvariants and Proj quasi-compactness; no match.
- rg in `WeilConjectures` and `lean/Sheaf`:
  `equivariant.*[Pp]rojective|[Pp]rojective.*[Ee]nvelope|Graded.*[Aa]ction|graded.*[Aa]utomorph`.
  The finite-group quotient module cites this missing input in its proof docstring, but
  does not state it. Other hits concern tensor actions and log alterations, with different
  objects and conclusions. Searching the exact node id upstream found no declaration.
- rg for `exists_equivariant_projective_envelope|equivariantProjectiveEnvelope` in the
  upstream-name index, Mathlib, upstream WeilConjectures and lean/Sheaf found no collision.
- Searches for homogeneous quotient grading found no reusable quotient-grading declaration
  in the supplied sources. Instead of adding a private replacement, this statement uses
  ordinary `GradedRing` data and specifies its pieces by the quotient image equation.

Validation: `scompile.py Q20 lem-per-equivariant-projective-envelope` compiled this file
both as a sandbox module and under its actual library module name in 2.1 seconds each,
with no errors or warnings. The initial `.ofHom` abbreviation error was corrected to
`CommRingCat.ofHom`. All lines are at most 100 characters. No shared or upstream source
was edited and no direct Git command or global build was run.

## Second reading by Q20

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
