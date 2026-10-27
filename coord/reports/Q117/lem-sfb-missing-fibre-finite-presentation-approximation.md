## Worker report

The module `Sheaf.AlgebraicGeometry.MissingFibreFinitePresentationApproximation`
states `AlgebraicGeometry.exists_missingFibre_finitePresentationApproximation`.
Its only theorem proof is `sorry`; there are no new definitions or axioms.
The source is the complete statement and proof of Stacks Tag 05BD,
`literature/stacks-project/limits.tex`, `lemma-separate` (lines 3454–3555).
The explicit finite polynomial quotient is the choice of finitely presented
A-algebras made in that proof, as in the reviewed DAG node.

Hypothesis and conclusion correspondence:

- A commutative ring A and S = Spec A: `(A : Type u) [CommRing A]`, with the
  literal base `Spec (CommRingCat.of A)` in both structure maps.
- Schemes X, T, and the closed subscheme Z: `{X T Z : Scheme.{u}}`.
- Quasi-compact f: `(f : X ⟶ Spec (CommRingCat.of A)) [QuasiCompact f]`.
  There is no locally-finite-type hypothesis on f.
- Arbitrary g and t: `(g : T ⟶ Spec (CommRingCat.of A)) (t : T)`.
- The closed immersion into X_T: `(i : Z ⟶ pullback f g)
  [IsClosedImmersion i]`.
- Its fibre over t is empty: `ht : IsEmpty ((i ≫ pullback.snd f g).fiber t)`.
- An affine open neighbourhood: `∃ (V : T.Opens) (htV : t ∈ V)` and
  the conclusion `IsAffineOpen V`. The open subscheme is `V.toScheme` and
  its inclusion is the existing `V.ι`.
- Nonnegative integers r, m: `(r m : ℕ)`; the finitely many polynomials are
  `q : Fin m → MvPolynomial (Fin r) A`.
- T' is exactly the specified quotient spectrum: its expression throughout
  is `Spec (CommRingCat.of (MvPolynomial (Fin r) A ⧸ Ideal.span (Set.range q)))`.
  Its map to S is `Spec.map (CommRingCat.ofHom (algebraMap A ...))`.
  No extra arbitrary ring or arbitrary structure map is substituted.
- The S-morphism a: the existential map `a : V.toScheme ⟶ Spec ...`, together
  with `ha : a ≫ Spec.map ... = V.ι ≫ g`. The equality is bound before the
  canonical pullback map that uses its proof, without a statement-level let.
- A closed subscheme of X ×_S T': `(Z' : Scheme.{u}) (i' : Z' ⟶ pullback f ...)`
  and `IsClosedImmersion i'` in the conclusion.
- Its empty fibre over a(t): `IsEmpty ((i' ≫ pullback.snd f ...).fiber
  (a ⟨t, htV⟩))`. Here the subtype point is t considered as a point of V.
- The requested image containment is `Set.range (pullback.map ...) ⊆ Set.range i'`.
  The source of this actual canonical map is
  `pullback (i ≫ pullback.snd f g) V.ι = Z ×_T V`; its map to X is
  `i ≫ pullback.fst f g`, its map from V is a, and its map on bases is g.
  Its first commuting square is the defining pullback equality composed with i;
  its second is `ha.symm`. Thus it is precisely the restriction of the indicated
  map X ×_S V → X ×_S T', not an arbitrary morphism or a stronger factorization
  conclusion. The proof sketch obtains containment from a factorization.
- No finite-type, Noetherian, separatedness or quasi-separatedness condition
  occurs on X, T or A. A common arbitrary universe u accommodates their sizes;
  no smaller independent test universe is introduced.

Dependency declarations used, read with their signatures and docstrings:

- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec` and `AlgebraicGeometry.Spec.map`.
- `def-pc-scheme`: the same module, `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom`.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  whose imported `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact` gives
  `AlgebraicGeometry.QuasiCompact`; only the quasi-compact part of that node is used.
- `def-pc-fibre-product`:
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`, `pullback.map`.
  Scheme pullbacks are supplied by the existing geometry imports.
- `def-weil-closed-immersion`: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion`.
- `def-pc-scheme-fibre`: `Mathlib.AlgebraicGeometry.Fiber`,
  `AlgebraicGeometry.Scheme.Hom.fiber`.
- `def-weil-pbc-mv-polynomial-ring`: `Mathlib.Algebra.MvPolynomial.Basic`,
  `MvPolynomial`. Its recorded evaluation and uniqueness declarations were also
  read (`MvPolynomial.aeval`, `MvPolynomial.algHom_ext`); this statement only
  needs the polynomial ring itself.

The proof imports preserve the stated DAG route: the two upstream modules
`WeilConjectures.RingTheory.ColimitFinitelyPresentedAlgebras` and
`WeilConjectures.RingTheory.FilteredColimitAlgebrasTensorElementwise`, with
`CommAlgCat.isFiltered_and_isColimit_finitelyPresentedAlgebras` and
`CommAlgCat.filteredColimit_tensorProduct_elementwise` (and its two companion
clauses); the Mathlib fibre-localization and separatedness modules. The other
recorded proof leaves (finite affine covers, affine spectra pullbacks, unit-ideal
criterion, affine composition/base change, and scheme-image kernels) are exposed
by the geometry imports. The theorem docstring records all seven proof steps
and their DAG inputs. All seven statement dependencies have usable declarations;
no dependency repair is needed.

Edge cases checked before and after writing: r = 0 and m = 0 are allowed by
`Fin 0` and `Ideal.span (Set.range q)`; no nonempty generating family is assumed.
X and Z may be empty. Empty T has no t, exactly as in the source. A = 0 likewise
admits no such pointed T; the statement adds no nontriviality assumption. An
arbitrary, possibly non-affine T is allowed, and only its chosen neighbourhood
is affine. Non-quasi-separated X is allowed: the proof uses a finite affine
cover and an affine image map, not finiteness of intersections. The point a(t)
is not assumed closed. Both identity and non-injective algebra stage maps are
allowed by the proof route.

Searches for an existing statement (all with the prescribed msearch.py wrapper):

- LeanSearch: `closed subscheme empty fibre finitely presented approximation quasi
  compact morphism`: eight hits, including QuasiCompact, empty schemes, closed
  immersions from the empty scheme, compact fibres and LocallyOfFinitePresentation;
  no Tag 05BD statement.
- LeanFinder: `closed subscheme missing fibre finite presentation approximation`:
  eight hits, primarily LocallyOfFinitePresentation and finitePresentation_appLE;
  no approximation of a closed subscheme missing a specified fibre.
- Loogle: `AlgebraicGeometry.QuasiCompact, AlgebraicGeometry.IsClosedImmersion`:
  one hit, `AlgebraicGeometry.IsImmersion.isImmersion_iff_exists_of_quasiCompact`,
  which concerns factoring an immersion and is not this statement.
- Mathlib grep: `05BD|missing.fibre|lemma.separate` in AlgebraicGeometry: no hits.
- Direct rg of both `lean/WeilConjectures` and `lean/Sheaf` for Tag 05BD,
  `lemma.separate`, missing-fibre and finite-presentation approximation wording:
  no matching theorem. The existing AffineTransitionLimit approximations concern
  systems of entire morphisms, not the closed-subscheme separation assertion.
  The NormalCurveUniversalClosednessTest module only cites this DAG item in a
  proof docstring. Searching the exact item id likewise finds that citation only.

No node fault or disputed statement was found. No statement correction, new node,
or dependency module is needed. The sandbox node differs from its repository
copy only in `lean`; the recorded signature is extracted verbatim from the file.
The single delivered module compiled cleanly through scompile.py.

## Second reading by Q117

A second pass in this worker reopened the node and the final Lean file and checked
all hypotheses and clauses listed above. The dispatcher explicitly prohibits
starting other agents; the maintainer's independent review follows delivery.
The common base is literally Spec A in both structure maps. Only f is assumed
quasi-compact. Z is a closed immersion into the correct pullback and its empty
fibre is taken for its composite to T. V contains t and is affine. T' is the
literal quotient by the displayed finite family, and ha has the correct orientation
for being over S. The fibre point is a applied to t in V. The final containment
uses the canonical map with source Z ×_T V, with both squares checked from the
existing pullback relation and ha. Thus it neither forgets the restriction to V
nor strengthens image containment to an existential scheme factorization.
No mathematical mismatch was found and no statement change was made. Explicit
`set_option autoImplicit false`, the single `sorry` proof, and the absence of
additional hypotheses were rechecked. Maximum Lean line length is 91 characters.
