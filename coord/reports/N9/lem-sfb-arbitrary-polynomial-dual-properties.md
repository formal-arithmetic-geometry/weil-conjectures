## Worker report

The module `Sheaf.Algebra.Homology.PolynomialRelativeDualProperties` states
`ModuleCat.polynomialRelativeDual_properties`, with proof `sorry`, and defines its
polynomial dual by the existing derived-coinduction construction followed by shift.
The repair adds one definition node owning the canonical scalar-action map in its
own standalone module. There are no new axioms or postponed construction lemmas.

Hypotheses and all clauses of the node match as follows:

- Arbitrary commutative rings R and A: `{R A : Type u} [CommRing R] [CommRing A]`.
  The universe u is arbitrary. Both rings can be placed in a common universe;
  no cardinal bound or nontriviality assumption is imposed.
- The specified ring map R → A is encoded by `[Algebra R A]`. Its flatness is
  `[Module.Flat R A]`, equivalent to `RingHom.Flat (algebraMap R A)`. Finite
  presentation is `[Algebra.FinitePresentation R A]`.
- Every polynomial presentation with n≥0 is `(n : ℕ)` and
  `(p : MvPolynomial (Fin n) R →ₐ[R] A) (hp : Function.Surjective p)`.
  The AlgHom condition expresses compatibility with the specified R → A, rather
  than allowing a different base map. There is no condition on the kernel beyond
  the given finite-presentation hypothesis.
- Ordinary unbounded module derived categories are `DerivedCategory (ModuleCat.{u} R)`,
  the analogous A-category, and the polynomial-ring category, each with
  `[HasDerivedCategory.{u} ...]`. This is the existing Grothendieck module
  localization at the module morphism universe, available from
  `HasDerivedCategory.ofIsGrothendieckAbelian`; these are choices of localization,
  not extra mathematical hypotheses. No site/object/morphism universes are identified.
- C = C_{P→A}(P[0])[n] is `polynomialRelativeDual n p.toRingHom`.
  Its definition is literally `(derivedCoinduction p).obj` of the single P-module P
  in degree zero, then `⟦(n : ℤ)⟧`. `derivedCoinduction` is the K-injective right
  derived functor of `coextendScalars`, whose action is `(a h)(a')=h(a'a)`.
- A[0] perfect over P is the first conjunct `IsPerfectRingComplex` applied to
  restriction along `p.toRingHom` of `(singleFunctor (ModuleCat A) 0).obj (of A A)`.
  The recorded predicate means precisely a bounded complex of finite projective modules.
- C is R-perfect is expanded as the second conjunct `IsPseudoCoherent C` over A
  and the third conjunct `∃ a b : ℤ, a ≤ b ∧ torAmplitudeIn (ModuleCat R) a b (U_R C)`.
  Expanding the existing `torAmplitudeIn` says that for every R-module Q, the
  derived tensor of U_R C with Q[0] has cohomology concentrated in [a,b].
  The underlying tensor structure is the K-flat localization, not ordinary tensor.
  `homologyConcentratedIn` uses the canonical t-structure, hence is exactly the
  stated vanishing outside the interval. The interval is uniform in Q.
  The node's inline definition of R-perfect is rendered by these two conjuncts;
  no separate duplicate relative-perfect predicate is introduced.
- The restriction of C to P is perfect is the fourth conjunct
  `IsPerfectRingComplex ((restrictScalars p.toRingHom).mapDerivedCategory.obj C)`.
- The canonical scalar arrow is exactly `ModuleCat.derivedModuleScalarActionMap C`,
  whose source is A[0] and target is `(ihom C).obj C`. Its definition is the
  degree-zero-unit identification followed by `MonoidalClosed.curry' (𝟙 C)`.
  The last conjunct is `IsIso` of this particular arrow, not an abstract
  isomorphism between the endpoints. The ordinary-module internal Hom is the
  existing `ordinaryModuleDerivedInternalHom A`, an abbreviation for precisely
  the closed bifunctor used by `ihom` here.
- No Noetherian, finite-type-only, domain, field, lci, or nonzero assumption occurs.

Dependency declarations read and used:

- `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat`, and the equivalent
  `Module.Flat` algebra-map form `RingHom.flat_algebraMap_iff`.
- `Mathlib.RingTheory.FinitePresentation`: `Algebra.FinitePresentation`.
- `Mathlib.Algebra.MvPolynomial.Basic`: `MvPolynomial` (publicly available through
  finite presentation), with its polynomial structure and R-algebra maps.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.singleFunctor` (through the dependency imports).
- `Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom`:
  `CategoryTheory.ordinaryModuleDerivedInternalHom`, definitionally the existing
  closed internal-Hom bifunctor, so `ihom` is its fixed-first-variable presentation.
- `Sheaf.Algebra.Homology.DerivedCoinductionAdjunction`:
  `ModuleCat.derivedCoinduction`, using `coextendScalars.rightDerivedFunctor`, and
  `ModuleCat.derivedCoinductionAdjunction_spec` (proof dependency).
- `WeilConjectures.RingTheory.RingPseudoCoherent`: `DerivedCategory.IsPseudoCoherent`.
- `WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat`:
  `CategoryTheory.MorphismProperty.kFlat`, used by the existing derived monoidal
  construction exposed through the ordinary-module internal-Hom dependency.
- `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`:
  `DerivedCategory.IsPerfectRingComplex`, whose terms use `Module.Projective` from
  `Mathlib.Algebra.Module.Projective`, with `Module.Finite`.
- `Sheaf.Algebra.Homology.DerivedModuleScalarActionMap`:
  `ModuleCat.derivedModuleScalarActionMap`, owned by the new definition node
  `def-sfb-derived-module-scalar-action-map`. Its real data is the existing
  `DerivedCategory.singleFunctorObjUnitIso` followed by `MonoidalClosed.curry'`
  of the identity. The main module no longer imports the Noetherian
  relative-perfect theorem module, nor cites its theorem node.
- `WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude` is now imported
  directly and publicly for `DerivedCategory.torAmplitudeIn`.

The stated proof's available modules are imported as proof dependencies, including
BoundedFlatKFlat, FlatModel, Mathlib Tor, RingPseudoCoherentFiniteTorPerfect,
RingedDerivedClosedSymmetricMonoidal, PerfectComplexDerivedBiduality,
PseudoCoherentBoundedFiniteFreeModel, and AlgebraicShriekDerivedHomAdjunction.
The three proof dependencies lem-sfb-flat-fp-polynomial-pseudocoherent,
lem-trf-base-flat-polynomial-tor-bound, and lem-sfb-flat-fp-quotient-pseudocoherent
have no recorded Lean module, and consequently supply no import yet.
The six-step natural-language proof is included in the theorem docstring.

Edge cases checked before writing:

- n=0: `Fin 0` is empty; the polynomial algebra, single functor and zero shift
  remain defined, including arbitrary surjections from the base ring.
- A=0: no `Nontrivial A`; coinduction produces zero module objects and the scalar
  arrow is the unique arrow between zero objects, hence can be invertible.
- R=0: an R-algebra is itself zero and remains admitted.
- The zero dual allows the interval a=b=0; ordered Tor bounds are required explicitly.
- No regularity of R or finite global dimension of R is asserted. The polynomial
  perfection proof uses the stated arbitrary-base hypotheses and n-variable Tor bound.
- The map is genuinely the scalar action, with its normalization fixed by currying
  identity and the supplied precomposition action; an isomorphism of objects alone
  would not give the final clause.

Sources opened: `literature/stacks-project/dualizing.tex` at
`lemma-relative-dualizing-algebraic` (0BZW), and `more-algebra.tex` at
`lemma-flat-finite-presentation-perfect` (067J), `lemma-perfect-over-polynomial-ring`
(068X), `lemma-more-relative-pseudo-coherent-is-moot` (0E1T), and the following
`definition-relatively-perfect`. The source 0BZW is explicitly Noetherian;
this node explicitly claims its arbitrary-base extension using those general
algebra inputs. The statement is preserved, without silently applying the
Noetherian theorem to arbitrary rings. No statement correction or dispute is needed.

Searches (all 2026-10-24):

- msearch LeanFinder: “For a flat finitely presented algebra over an arbitrary ring
  the polynomial relative dual is relatively perfect and its scalar action map is
  an isomorphism”: 8 hits, smooth/étale/formally unramified algebra APIs; none states
  the derived relative duality assertion.
- msearch Loogle: `"DerivedCategory", "dual"`: 0 hits.
- msearch LeanSearch: “Derived polynomial dual of a flat finitely presented algebra
  is relatively perfect with scalar endomorphisms”: 8 hits, finite-presentation,
  ordinary projective-module duality and smoothness; no exact statement.
- msearch grep: `semidualiz|homothety|relative.*dualizing|polynomial.*perfect`:
  25 hits (perfect fields and geometric homotheties), no derived polynomial duality.
- rg in `lean/WeilConjectures` and `lean/Sheaf` for homothety, scalar maps,
  polynomial dual and relative perfectness, followed by focused searches in
  CategoryTheory, RingTheory, Algebra/Homology, and TraceFormula: found the
  Noetherian `algebraicShriek_relative_perfect` and its reusable scalar map;
  found `semidualizing_rhom_conservative` (a different assertion), and the
  consumer `ArbitraryPolynomialGraphClassBaseChange`. No arbitrary-base theorem
  or general `polynomialRelativeDual` declaration was found.
- grep of the item id in `lean/WeilConjectures`: no matches. Search of the upstream
  name index for the item and new names found no declaration. Read the dependency
  signatures and docstrings rather than inferring their types from names.

Validation after H2 repair: scompile.py compiled both files separately in dependency
order in private overlay, sandbox and library module modes. The new scalar-action
module took 6.8 s in library mode and the main module 3.9 s; no warnings or errors
were printed. The wrapper builds the delivery against current published live sources.

## Second reading by N9

This is the worker's explicit rereading; no independent reader or subagent was
started, as the dispatcher brief forbids that. The maintainer supplies the
independent delivery review.

Reopened the node and the complete Lean file. Checked that the hypotheses are
exactly a flat finitely presented R-algebra and an arbitrary compatible surjective
n-variable polynomial presentation. The restriction in the first conjunct is of
A[0], whereas the restriction in the fourth is of the shifted dual, so these two
perfectness conclusions are both present and distinct. The middle pair is exactly
pseudo-coherence over A plus finite Tor dimension over R with ordered bounds,
not perfectness over A. Read `torAmplitudeIn` and its cohomology-concentration
predicate to check the quantifier over every R-module. Read the helper definitions
to verify that the dual has the precomposition action and positive cohomological
shift n, and that the final `IsIso` concerns the specified scalar arrow. Zero
rings and n=0 are admitted. No mismatch requiring a node correction was found.
The rejected dependency on the Noetherian theorem node has been removed. The sole
addition to the current main branch's stmt_deps is the new definition node, whose
entire scalar-action construction was read alongside its node. The definition
binds arbitrary A and K, and defines the map by the exact formula specified in
its TeX statement. It has neither finiteness hypotheses nor an assertion that the
map is invertible for every K. The final conjunct of the main theorem alone
asserts invertibility for the polynomial dual. The node cites precisely the two
required definition dependencies, and all H12 fields and searches are supplied.
TorAmplitude is a direct statement import. No additional theorem is proved.


## Repair of H2 on immutable head 2ee3b9b43a0c

The return found one defect: the delivered stmt_deps added the theorem node
`lem-trf-algebraic-shriek-relative-perfect` solely to obtain its plain scalar-map
definition. Comparing the retained sandbox against current main showed exactly
the delivered Lean record and this additional dependency; current main still
has no Lean record for the item and no competing scalar-map definition node.

Replaced that theorem dependency with the new definition node
`def-sfb-derived-module-scalar-action-map`. Its module defines
`ModuleCat.derivedModuleScalarActionMap` separately, the option explicitly allowed
by the return, with the identical unit-iso/curry-of-identity formula. The
trace-formula module is not edited. The new helper module imports only the
ordinary derived category, the recorded ordinary-module internal Hom and the
existing unit-identification construction. The item imports the new module and
TorAmplitude directly. It uses the new scalar map in its final conjunct.
The five conclusions, hypotheses, coinduction object, shift and six proof steps
are preserved. No statement correction is made. The prescribed delivery wrapper
rebases the repaired packet on current main in its private worktree.

## New nodes

`def-sfb-derived-module-scalar-action-map` defines, for any commutative A and any
K in D(A), the map A[0] → RHom_A(K,K) obtained by transporting A[0] to the tensor
unit and currying the identity of K. The equivalent unit-action transpose is
exactly its Lean formula. It requires only `def-weil-abstract-derived-category`
and `def-pur-derived-internal-hom`; its source is Stacks 0BZW(1)(c), the scalar
arrow whose invertibility is studied there. Zero A and zero K are admitted;
for general K it makes no invertibility assertion. Its data contains no sorry.

The required searches are recorded in the node with their actual msearch outputs:
LeanSearch found 8 ordinary scalar/identity/extension results; LeanFinder found
8 ordinary ModuleCat closed-tensor formulas; Mathlib grep found generic currying
APIs, including `MonoidalClosed.curry'`. These existing primitives are reused.
Repository grep found `algebraicShriekScalarMap` in the Noetherian theorem module
and the expanded scalar formula in the coinduction-adjunction comparison module,
not a definition-node-owned standalone map. No WeilConjectures declaration
matches. DAG definition-statement searches found only the different normalized
dualizing-complex definition, and the blueprint search found coefficient scalar
actions rather than this standalone arrow. The new definition's id and declaration
name have no existing match. `blueprint_refs.py ancestor` returns None for this
item, so the new node records null and preserves the item's source chain with
this item prepended. Creating the separate standalone map despite the occurrence
of its formula in the theorem module is explicitly the correction requested by
the immutable-head H2 return, and avoids importing that theorem to state this item.

Preflight schema repair: the first dry run required `import_flags` on the new
definition node. Added the empty list, matching the current server schema.
