## Worker report

The module `Sheaf.TraceFormula.AlgebraicShriekRelativePerfect` states
`AlgebraicGeometry.algebraicShriek_relative_perfect`, with one `sorry` and no
proofs of mathematical statements. The source is Stacks `dualizing.tex`,
Tag 0BZW, parts (1)(a--c) and (2)(a); I read the lemma and its proof in the
local source at lines 4825--4893. The node's mathematical statement is unchanged.

Hypotheses and objects, matched separately:

- Commutative rings R and A: `{R A : Type u} [CommRing R] [CommRing A]`.
  The common universe is arbitrary and can contain any given pair of rings.
- Both Noetherian assumptions: `[IsNoetherianRing R] [IsNoetherianRing A]`.
- The specified homomorphism: `(φ : R →+* A)`.
- Flatness: `hflat : RingHom.Flat φ`, literally flatness of A with the
  module structure induced by φ. The original scheme-flatness dependency is
  retained and imported; the already recorded ring-flatness node is added
  to disambiguate the node's ring-map usage.
- Finite type: `hfinite : RingHom.FiniteType φ`. This uses the existing
  ring-homomorphism definition, not an unrelated algebra structure.
- Any polynomial presentation: `(n : ℕ)` and
  `(p : MvPolynomial (Fin n) R →+* A)`, with `hp : Function.Surjective p`
  and `hcomp : p.comp MvPolynomial.C = φ`. The compatibility equation is
  exactly the assertion that the presentation is over R.
- K = RHom_P(A,P)[n] with its A-action: the helper
  `algebraicShriekPolynomialComplex n p` applies the actual
  `ModuleCat.coextendScalars p` termwise to the canonical functorial
  K-injective resolution of P[0], and then applies the cohomological shift n.
  `CoextendScalars.smul_apply` is `(a • h)(a') = h(a' * a)`, so this is the
  natural coinduced action, rather than RHom with its action forgotten.
  `DerivedCategory.Q.obj` of this complex is K in the theorem.
- The `HasDerivedCategory.{u}` binders specify a localization size, as in
  the abstract-derived-category dependency. The existing Grothendieck module
  machinery provides these instances. They introduce no finiteness,
  regularity, lci, boundedness, or site-size hypothesis.

Conclusion, clause by clause:

- Pseudo-coherent: `DerivedCategory.IsPseudoCoherent (Q.obj ...)` is the
  recorded definition, with an actual bounded-above finite free complex and
  an isomorphism in D(A), not a replacement finite-cohomology predicate.
- Bounded cohomology: there exist integers `a b`, with `a ≤ b`, such that
  for every `i`, `i < a ∨ b < i` implies `IsZero` of the i-th homology
  object of K.
- Finitely generated cohomology: `∀ i : ℤ, Module.Finite A
  ((DerivedCategory.homologyFunctor (ModuleCat A) i).obj K)`.
- Finite Tor amplitude over R: there exist `a b` with `a ≤ b` and
  `DerivedCategory.torAmplitudeIn (ModuleCat R) a b` of K restricted along φ.
  The restriction is the existing exact
  `(ModuleCat.restrictScalars φ).mapDerivedCategory`. The upstream
  `torAmplitudeIn` quantifies over every `ModuleCat.{u} R` object placed
  in degree zero and uses the K-flat derived tensor; its
  `homologyConcentratedIn` means cohomology vanishes outside the interval.
  These a,b are independent of the tested module and are not required to
  coincide with the A-cohomology bounds.
- The scalar map is an isomorphism: `IsIso (algebraicShriekScalarMap K)`.
  This helper is `singleFunctorObjUnitIso.hom` followed by
  `MonoidalClosed.curry' (𝟙 K)`. Its domain is literally A[0]; its target
  is `(ihom K).obj K`. The upstream derived closed structure uses actual
  K-injective internal Hom for the derived tensor. Transposition of the
  identity is the scalar multiplication map, so the conclusion asserts
  invertibility of this canonical arrow, not merely existence of some
  isomorphism of its source and target.
- There is no lci, smoothness, regularity, or projectivity hypothesis on A.

Dependency declarations read and used:

- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q` (abstract derived category).
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`:
  `CategoryTheory.derivedInternalHomOfUniverses` (recorded ringed-site
  interface, imported). Ordinary modules here use the existing upstream
  `DerivedCategory.monoidalClosed` / `ihom` specialization, whose construction
  and K-injective description were read in
  `WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Closed`.
  No second implementation of RHom is introduced.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`,
  retained original dependency; `Mathlib.RingTheory.RingHom.Flat`:
  `RingHom.Flat`, recorded ring-map notion.
- `Sheaf.RingTheory.RingPseudoCoherent`:
  `DerivedCategory.IsPseudoCoherent`, its full representative definition.
- `Mathlib.RingTheory.RingHom.FiniteType` / `Mathlib.RingTheory.FiniteType`:
  `RingHom.FiniteType`; `Mathlib.Algebra.MvPolynomial.Basic`: `MvPolynomial`, `C`.
- `WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude`:
  `DerivedCategory.torAmplitudeIn`, via the public FlatModel import.
- `Mathlib.Algebra.Category.ModuleCat.ChangeOfRings`:
  `ModuleCat.coextendScalars` and its literal multiplication action.
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution`:
  `CochainComplex.kInjectiveResolutionFunctor`.
- Proof imports for the recorded dependencies that have Lean statements:
  `Sheaf.TraceFormula.AlgebraicShriekCalculus`
  (`nonempty_algebraicShriekCalculus` and the full coinduction-model fields),
  `Sheaf.TraceFormula.FlatPolynomialQuotientPerfect`
  (`DerivedCategory.flat_polynomial_quotient_perfect`), and
  `Sheaf.RingTheory.NoetherianPseudoCoherentCohomologyCriterion`
  (`DerivedCategory.isPseudoCoherent_iff_boundedAbove_finite_homology`).
  The other three proof nodes have no recorded Lean module in the inspected
  DAG, so they are named in the proof docstring but have no import to add.

Edge cases checked before writing: n=0 is admitted (`Fin 0` is empty and the
shift is zero); arbitrary redundant polynomial generators remain allowed;
A=0 and R=0 are allowed (no nontriviality binder); K and its cohomology can
be zero, with any suitable nonempty integer interval; the degree and Tor
bounds range over all integers, including negative ones. All test R-modules
of the chosen module universe are included, with no flatness or finite
presentation assumption. There is no test-universe parameter below R.
Flat singular examples are not excluded, including finite type algebras over
fields with non-lci singularities.

Searches actually made with msearch.py, followed by source inspection:

- leanfinder: "For a flat finite type Noetherian algebra the shifted derived
  coinduction of a polynomial ring has pseudo coherent bounded finite
  cohomology finite relative Tor amplitude and scalar endomorphism
  isomorphism". Eight hits, concerning smooth flatness and ordinary Tor;
  no statement of the node.
- loogle: `RingHom.Flat, DerivedCategory, Module.Finite`. Zero hits.
- grep: `homothety|relativeDualizing|algebraicShriek`, Mathlib/Algebra.
  Two hits about Bruhat--Tits homothety, no match.
- leansearch: "The relative dualizing complex of a flat finite type map of
  Noetherian rings has bounded finite cohomology finite Tor amplitude and
  its scalar endomorphism map is an isomorphism". Eight hits, chiefly
  `RingHom.Flat`, smoothness and flat-module criteria; no match.
- rg in the upstream WeilConjectures sources, shared lean/Sheaf and
  dag/lean_names_upstream.json for the item id, algebraicShriek,
  relative dualizing, scalar-map and RHom names: the upper-shriek calculus,
  the polynomial-perfect prerequisite and the scheme-relative scalar map
  exist; none states the item. The scheme map belongs to sheaves on a
  scheme and is not the ordinary A-module map here. The new scalar helper
  uses existing `MonoidalClosed.curry'` directly. New helper names have no
  existing declaration in those source trees.

No statement fault or STATEMENT-DISPUTED issue was found. No new DAG node or
dependency replacement is needed: the two concrete helper constructions belong
to the polynomial object and scalar arrow of this item and are listed in
`lean.declarations`. Existing ring-map and polynomial definition nodes are
added to `stmt_deps`; no existing dependency is copied or redefined.

## Second reading by Q148

In-thread self-review, with both the copied node and module open; the
maintainer's independent review is separate. I checked both CommRing binders,
both Noetherian assumptions, φ, flatness and finite type, arbitrary n,
surjective p and its R-compatibility; each has exactly the counterpart listed
above. I unfolded the polynomial complex to verify that its action is
coinduced and that its shift has positive n in the cohomological convention.
I unfolded IsPseudoCoherent and torAmplitudeIn; the former supplies the stated
finite-free model, and the latter tests every ordinary R-module and vanishes
on both sides of one interval. I checked that boundedness and finiteness of
A-cohomology are separate conjuncts. Finally I read curry' and the unit
comparison: the arrow is the scalar-action arrow with domain A[0], not an
unspecified isomorphism. No mathematical mismatch was found. The first compile
found a public-import visibility error for mapDerivedCategory, repaired by
publicly importing its exact-functor module. No theorem was proved.
