## Worker report

Stage 2, group N2, item `lem-trf-polynomial-diagonal-rhom-reduction`.

The module `Sheaf.TraceFormula.PolynomialDiagonalRhomReduction` defines two
components of this comparison, with real data, and states
`AlgebraicGeometry.polynomial_diagonal_rhom_reduction` with `sorry`.
This repair adds two existing-definition DAG records, with no new Lean construction.
There are no dependency module repairs, statement corrections, or disputed statements.
The item changes only in `lean` and `stmt_deps`. Its Lean module is unchanged.

### Hypotheses and clauses

- Commutative rings R and A: `(R A : Type u) [CommRing R] [CommRing A]`.
  The map R → A is its algebra map, specified by `[Algebra R A]`; an arbitrary
  given ring homomorphism is represented by its associated algebra structure.
- Both rings Noetherian: `[IsNoetherianRing R] [IsNoetherianRing A]`.
- Flatness: `hflat : RingHom.Flat (algebraMap R A)`.
- Finite presentation: `[Algebra.FinitePresentation R A]`.
- A chosen polynomial presentation in n variables is
  `(n : ℕ) (p : MvPolynomial (Fin n) R →ₐ[R] A)` with
  `(hp : Function.Surjective p)`. An R-algebra homomorphism includes the
  compatibility with R; no extra kernel or regularity condition is imposed.
- Ordinary unbounded module derived categories are `DerivedCategory (ModuleCat.{u} -)`.
  Explicit `HasDerivedCategory.{u}` binders select the usual localization size
  separately for R, A, P and B. All universe variables are declared, and
  `set_option autoImplicit false` is present. An ambient u can contain any of
  the given small rings and modules; no characteristic or nontriviality is imposed.
- `polynomialDiagonalDualizing R A n p.toRingHom` is exactly
  `((ModuleCat.derivedCoinduction p.toRingHom).obj (singleFunctor ... 0).obj P)[n]`.
  The term in the actual file includes the parentheses specifying the degree-zero
  P-module. `derivedCoinduction` is the total right derived coextension of scalars;
  its ordinary module carrier is Hom_P(A,-), with action `(a • h)(a') = h(a'a)`.
  Thus C has the precomposition A-action, not an arbitrary lift of an object of D(P).
  Shift notation is explicitly `⟦(n : ℤ)⟧`.
- B is `A ⊗[R] A`. The shared `relativeDualizingModuleDiagonal R A`
  restricts the ordinary A-module A along `Algebra.TensorProduct.lmul' R`,
  and then places it in degree zero. This is the multiplication B-module A.
- The coefficient extension in `polynomialDiagonalHom` is
  `relativeDualizingDerivedExtension includeLeft.toRingHom`.
  It is the already constructed K-flat left derived extension of scalars,
  so gives T tensor_{A,p1}^L B (written B tensor_A^L T in its implementation).
- The middle functor is `ihom (relativeDualizingModuleDiagonal R A)` in D(B).
  The last functor is `(ModuleCat.restrictScalars includeLeft.toRingHom).mapDerivedCategory`.
  The output is in D(A) along p1, never restriction along multiplication or p2.
- The family `e` takes an arbitrary T, `DerivedCategory.IsPseudoCoherent T`,
  and the expanded Tor condition: there exist integers a ≤ b such that for
  every R-module Q and integer i outside the interval, H^i of
  `(Res_R T) ⊗ singleFunctor(R,0)(Q)` is zero. Here tensor is the native
  derived tensor and `DerivedCategory.homologyFunctor` is H^i.
  The same single interval serves all Q; Q is not assumed flat or finite.
- Its value is the required isomorphism from `polynomialDiagonalHom R A` at T
  to `(ihom (polynomialDiagonalDualizing ...)).obj T`.
- Naturality is the final equality, for arbitrary permitted T,T' and arbitrary
  `f : T ⟶ T'`: `F.map f ≫ (e T').hom = (e T).hom ≫ G.map f`.
  The Tor witnesses for the two objects may use different intervals. No
  restriction on morphisms or extra condition on a diagonal class appears.
- In particular no dualizing, semidualizing, invertibility, diagonal-dualizing,
  A-perfectness, or B-Tor-amplitude hypothesis is imposed on T.

### Dependency declarations read and used

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` and its ideal-FG
  characterization (def-weil-pbc-noetherian-ring).
- `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat`, with
  `RingHom.flat_algebraMap_iff` (def-weil-pbc-flat-ring-map).
- `Mathlib.RingTheory.FinitePresentation`: `Algebra.FinitePresentation`, whose
  data is a surjective finite polynomial presentation with finitely generated
  kernel (def-weil-pbc-finitely-presented-algebra).
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `Q`, and `singleFunctor`
  (def-weil-abstract-derived-category).
- `Sheaf.RingTheory.RingPseudoCoherent`: `DerivedCategory.IsPseudoCoherent`,
  requiring a bounded-above finite free representative
  (def-pc-ring-pseudo-coherent-complex).
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses` is publicly imported,
  retaining the recorded generic K-injective ringed-site Hom interface
  (def-pur-derived-internal-hom). In ordinary module categories the native
  `ihom` supplied by upstream
  `WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory` is the
  derived Hom: its closed structure is derived using K-injectives, as explained
  in `WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Closed`.
  This is the ordinary module presentation used by the existing affine comparison
  and projective-Hom-model nodes, rather than a private second Hom construction.
- `Sheaf.Algebra.Homology.DerivedCoinductionAdjunction`:
  `ModuleCat.derivedCoinduction`, `ModuleCat.coinductionComplexFunctor`, and
  `ModuleCat.derivedCoinductionAdjunction_spec`. The full source was read,
  including its action, K-injective model, evaluation counit and naturality.
  The definition is now owned by `def-trf-derived-coinduction` in stmt_deps.
  The adjunction theorem stays in proof_deps only.
- `Sheaf.AlgebraicGeometry.AffineRelativeDualizingComparison`:
  `AlgebraicGeometry.relativeDualizingDerivedExtension`,
  `AlgebraicGeometry.relativeDualizingModuleDiagonal`,
  `AlgebraicGeometry.relativeDualizingModuleFirstPullback`, and
  `AlgebraicGeometry.relativeDualizingModuleHom` were read. The first two
  are used directly; `polynomialDiagonalHom` packages their functors with
  actual p1 restriction so that maps and naturality can be stated. This
  module's two used definitions are now owned by
  `def-trf-affine-diagonal-module-data` in stmt_deps. The affine-comparison
  theorem node is absent from stmt_deps. None of its notions is redefined.

All recorded, stated proof-dependency modules are imported without `public`.
The two not-yet-stated proof dependencies
`lem-trf-derived-bimodule-tensor-hom` and
`lem-trf-algebraic-shriek-derived-hom-adjunction` have no usable module to import;
they are only proof dependencies and are not needed to type this statement.
The full eleven-step DAG proof is in the theorem docstring, including its
explicit graph action, the K-flat computations, Koszul signs and the n-shift.

### Source and edge checks

Read the item's complete proof, its six original statement dependencies,
Stacks tag-to-label entries and the relevant source excerpts in more-algebra.tex
and dualizing.tex, as well as the stage-1 derivation/report Q55. This assertion
is explicitly agent-assembled, not claimed to be verbatim Stacks. Definition
0DHS confirms exactly pseudo-coherence and finite Tor dimension over R.

Checked the zero algebra: no Nontrivial instance is present, so D(A) and both
outputs are zero. Checked T=0. Checked n=0 and the identity presentation R=A:
C=A and both functors are the identity up to the usual comparisons. Checked
a redundant variable P=R[x] → R: RHom_P(R,P)=R[-1], so C=R after the +1 shift.
For A a polynomial algebra with its identity presentation, C=A[n] and the
right side is T[-n], agreeing with the graph Koszul computation on the left.
For a finite-dimensional non-Gorenstein algebra over a field, C is its vector
space dual: the signature imposes neither A-perfectness of C nor a dualizing
condition on T. Negative and shifted Tor intervals are allowed, and the
naturality equation accepts every derived morphism between admissible objects.
No finite Tor condition over B is inferred from the Tor condition over R.

### Searches

Searches were made with the prescribed msearch wrapper (group N2 and this item):

- LeanFinder query: “For a flat finitely presented algebra the diagonal derived
  Hom of induced coefficients is Hom from the polynomial relative dualizing complex”.
  Eight hits, including cotangent/Kaehler base-change declarations and
  `Algebra.Smooth.flat`; none is the derived diagonal comparison.
- LeanSearch query: “Polynomial diagonal derived Hom reduction for flat finitely
  presented algebras with relative dualizing complexes”. Eight ordinary
  finite-presentation/flatness hits, no derived Hom theorem.
- Loogle query `DerivedCategory, ModuleCat`: zero hits.
- Mathlib grep query `Hochschild|polynomialDiagonal|relativeDualizing`: one
  group-cohomology documentation mention of the Hochschild-Serre spectral
  sequence, no match.
- Direct rg in upstream WeilConjectures and shared lean/Sheaf for
  `polynomialDiagonal|polynomial_diagonal|lem-trf-polynomial-diagonal-rhom-reduction`:
  only the already landed consumer docstring in
  `Sheaf.RingTheory.AlgebraicRelativeDualizingIsomorphism` mentions the item;
  it does not state it. The exact blueprint id has no upstream declaration.
- Direct rg of Mathlib, WeilConjectures, shared lean/Sheaf and the upstream
  declaration-name table for all three proposed declaration names: no match.
- Searches for existing ordinary scalar extension, coinduction, diagonal Hom,
  and relative perfection found the shared affine-comparison definitions and
  derived coinduction now reused above. No separate construction was needed.

### Validation

The prescribed scompile.py compiled the final module cleanly, both as its
sandbox module (3.1 s) and under its library module name (2.7 s). The only
postponed declaration is the main theorem. An initial missing pair of
parentheses around the isomorphism-valued return type was repaired before this
clean compile; no change to the mathematical statement was involved.

## Second reading by N2

A separate pass reread the node against the final Lean file, checking each
binder and each composite in the definitions. R-algebra compatibility is
provided by p being an AlgHom; hp retains surjectivity; both Noetherian
hypotheses and the original flat finite presentation are present. The
coinduction target is D(A), and the shift is positive n. The outer restriction
uses includeLeft, while the diagonal alone uses multiplication. The Tor
quantifier is over all R-modules with one pair of bounds per T. The
isomorphism family is restricted to exactly the two stated conditions,
and the equation is natural for arbitrary morphisms. No new mathematical
mismatch was found and no statement correction was needed. All helpers have
real construction data and the only sorry is the named theorem. The
maintainer's independent review is the independent delivery review; this
worker did not start any other agents, as required by the dispatcher brief.

## New nodes

`def-trf-derived-coinduction` records `ModuleCat.derivedCoinduction` with
`existing: true` in `Sheaf.Algebra.Homology.DerivedCoinductionAdjunction`.
Its binders are the module's explicit R, B, ring structures, map f and independently
chosen derived-category universes. Its value is the already constructed total
right derived coextension, not a choice from the adjunction theorem. The source
is the construction preceding Stacks 0A70 and the K-injective model of 0A71.
The action and differential in the node match ordinary coextendScalars and its
complex functor. No boundedness, flatness or finiteness condition is introduced.

`def-trf-affine-diagonal-module-data` records the two existing definitions
`AlgebraicGeometry.relativeDualizingDerivedExtension` and
`AlgebraicGeometry.relativeDualizingModuleDiagonal`, with `existing: true` in
`Sheaf.AlgebraicGeometry.AffineRelativeDualizingComparison`. The first takes
arbitrary commutative rings A,B, a map φ and their derived-category structures;
it is exactly `(ModuleCat.extendScalars φ).leftDerivedFunctor`, with the shared
K-flat preservation instance. The second takes R,A and their algebra structure,
and is Q of single 0 applied to the regular A-module restricted along lmul'.
Thus the two clauses give precisely K-flat scalar extension and the
multiplication diagonal, with no geometry hypotheses. It cites the existing
`def-zl-ring-derived-scalar-extension` for the general scalar-extension notion;
that node's abstract adjoint API does not record these two concrete declarations.
The source is Stacks 0E2U and the K-flat construction in more-algebra, 06Y0.

For both new records, the fresh prescribed LeanSearch query “The total derived
coinduction and extension of scalars for modules and the multiplication diagonal
module” returned eight ordinary scalar-functor hits; Loogle
`ModuleCat.coextendScalars, ModuleCat.extendScalars` returned zero hits; Mathlib
grep of the three exact names returned zero hits. Direct rg found no upstream
WeilConjectures declaration and found the exact existing definitions in the two
landed modules. The DAG exact-name search found their ownership only in theorem
records. Blueprint semantic searches found no separate coinduction/diagonal
blueprint definition. The raw wrapper results are copied into mathlib_searches.
No Lean declaration is duplicated. Zero rings and zero complexes remain allowed;
the identity ring map gives ordinary identity coinduction/extension, and the
diagonal at A=R is the multiplication module in degree zero.

## Returned-delivery repair

The immutable-head review of 3ba1c8264a7b asked for definition ownership instead
of theorem nodes in stmt_deps. The two records above supply ownership of all
three named definitions in their current modules. Both theorem node entries
are removed from stmt_deps, and `lem-trf-derived-coinduction-adjunction` remains
unchanged in proof_deps. All six original definition dependencies remain.
Comparison with current shared main found only lean and stmt_deps differing
before this repair; the mathematical statement, proof and proof_deps are retained.

A further N2 reading opened both new records alongside the full source signatures
and bodies: all ring, map, algebra and universe binders match, the two affine
clauses are distinct and complete, and every object is defined by real data.
The main theorem signature and helpers are byte-for-byte unchanged from the
returned packet. The review's substantive acceptance therefore still applies;
this repair addresses the dependency classification finding only.
