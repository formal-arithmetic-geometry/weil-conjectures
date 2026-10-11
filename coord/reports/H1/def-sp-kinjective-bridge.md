## Worker report

The module `Sheaf.CategoryTheory.KInjectiveBridge` realizes the node's generic resolution
convention and the choice-dependent complex-level definitions. There are four declarations,
all definitions or data structures, no theorems and no `sorry`. No node statement or dependency
list changed, and no additional nodes or dependency modules are needed.

Clause-by-clause reading:

- A complex in an abelian category is `K : CochainComplex C ℤ`, with explicit
  `{C : Type u₁} [Category.{v₁} C] [Abelian C]`. The generic resolution data are
  `CochainComplex.KInjectiveResolutionChoice K`: `complex` is `I`, `map : K ⟶ complex`
  is the augmentation, `quasiIso : QuasiIso map` says it is a quasi-isomorphism, and
  `isKInjective : complex.IsKInjective` says the target is K-injective.
- The acyclic-Hom-complex condition uses the SAME Mathlib `CochainComplex.IsKInjective`
  recorded by def-weil-pbc-kinjective-resolutions. Its null-homotopy formulation in degree
  zero, applied to all shifts of an acyclic source, is the acyclicity in every degree of
  the Hom complex. No separate predicate or Hom-complex definition is introduced.
  The dependency's `IsKInjectiveResolution T R` is specifically for étale module sheaves;
  this node expressly replaces that category by an arbitrary abelian category, so the
  structure bundles its recorded generic component declarations `QuasiIso` and
  `CochainComplex.IsKInjective`. The dependency record itself is usable for exactly the
  specialized statement it states and does not need replacement.
- In a Grothendieck abelian category, `[IsGrothendieckAbelian.{w} C]` is the hypothesis of
  `grothendieckKInjectiveResolutionChoice`. Its input is every `K : CochainComplex C ℤ`,
  without a boundedness restriction. Its complete data come directly from the recorded
  functorial-existence dependency: `kInjectiveResolutionFunctor`, `toKInjectiveResolution`,
  `monoQuasiIso_toKInjectiveResolution_app`, and
  `isKInjective_kInjectiveResolutionFunctor_obj`. It therefore also gives the claimed
  resolution for every bounded-below complex; no new existence assertion is postulated.
- Both categories for the bridge are abelian: the second category has independent object
  and morphism universes `{D : Type u₂} [Category.{v₂} D] [Abelian D]`.
  The functor is `(F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]`. These are exactly
  the additive and left-exact notions recorded by def-sp-left-exact-additive; for additive
  functors between abelian categories preserving kernels is equivalent to preserving
  finite limits. Enough injectives is used for the dependency's object-level functors,
  not needed when a complex-level resolution is already supplied.
- `K ∈ Ch⁺(C)` is `(K : CochainComplex.Plus C)`. Mathlib defines this full subcategory by
  `∃ n : ℤ, K.IsStrictlyGE n`, so it means termwise bounded below with an arbitrary
  integer lower bound, rather than just complexes in nonnegative degrees.
- The chosen resolution is the explicit argument
  `(r : CochainComplex.KInjectiveResolutionChoice K.obj)`.
  `rightDerivedComplexWithResolution F K r :=
  (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj r.complex` is precisely `RvK := v(I)`:
  Mathlib's functor applies `F.obj` to each term and `F.map` to each differential.
- The integer degree is `(p : ℤ)`. `rightDerivedCohomologyWithResolution F K r p :=
  (F.rightDerivedComplexWithResolution K r).homology p` is precisely `R^p v(K) := H^p(RvK)`.
- The final paragraph is an explicit forward reference to lem-sp-kinjective-computes,
  not a new theorem of this node. The module docstring and cohomology docstring retain
  this convention: independence and agreement with ordinary `Functor.rightDerived` on
  degree-zero objects are deferred. Keeping `r` in both signatures renders the present
  dependence on the chosen resolution exactly.

Dependency declarations read and used:

- def-sp-grothendieck-abelian: `CategoryTheory.IsGrothendieckAbelian`,
  Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic. Its docstring and class fields
  give locally small homs, exact filtered colimits and a separator, with small colimits
  inferred. The auxiliary size universe is explicitly bound.
- def-sp-left-exact-additive: `CategoryTheory.Functor.Additive`,
  Mathlib.CategoryTheory.Preadditive.AdditiveFunctor; `CategoryTheory.Limits.PreservesFiniteLimits`,
  Mathlib.CategoryTheory.Limits.Preserves.Finite. Read also
  `Functor.preservesFiniteLimits_of_preservesKernels` in
  Mathlib.CategoryTheory.Preadditive.LeftExact, and `Functor.rightDerived` and
  `InjectiveResolution.isoRightDerivedObj` in Mathlib.CategoryTheory.Abelian.RightDerived.
  The ordinary rightDerived declaration has domain C (objects), not Ch⁺(C), so it cannot
  substitute for this bridge. This module imports LeftExact for the recorded left-exact API.
- def-weil-pbc-kinjective-resolutions: read its full module
  Sheaf.AlgebraicGeometry.KInjectiveResolutions and the Mathlib declaration/docstring in
  Mathlib.Algebra.Homology.HomotopyCategory.KInjective. Reuse the recorded generic
  `CochainComplex.IsKInjective` and `QuasiIso` components, without importing the unused
  scheme-specific wrapper or copying its predicates.
- lem-weil-pbc-kinjective-functorial-existence: all four recorded declarations in
  WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution are used directly
  to construct `grothendieckKInjectiveResolutionChoice`. Read full signatures and docstrings.

Edge cases checked before writing: the zero complex, zero functor and zero abelian category
are permitted. Lower bounds can be negative, positive or zero, and bounded-below complexes
may have infinitely many positive-degree terms. The chosen target I has no unnecessary
termwise injectivity or boundedness requirement. All integer cohomology degrees, including
zero and negative degrees, are available. The existence definition includes unbounded K.
Category object and morphism universes are independent for C and D; the Grothendieck size
universe is independent as in the recorded existence theorem. There is no characteristic,
ring or scheme restriction.

Searches for reuse (2026-10-11):

- msearch.py leanfinder: "K-injective resolution of a complex and applying additive functor
  termwise to compute right derived cohomology" — eight hits, including Functor.rightDerived,
  InjectiveResolution.isoRightDerivedObj and toRightDerivedZero; these concern ordinary
  injective resolutions of objects, not the chosen-resolution convention on complexes.
- msearch.py loogle: "CochainComplex.IsKInjective, Functor.mapHomologicalComplex" — zero hits,
  unknown identifier Functor.mapHomologicalComplex; direct source search found and read the
  qualified declaration CategoryTheory.Functor.mapHomologicalComplex in Homology.Additive.
- msearch.py grep: "KInjectiveResolution|kInjective.*Derived|derived.*KInjective" — two Mathlib
  hits, imports in Injective.Ext and DerivedCategory.Plus, not a definition of this bridge.
- msearch.py leansearch: "K-injective resolution derived functor on bounded below complexes"
  — service unavailable, Internal Server Error; recorded as unavailable.
- rg over WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json for
  "def-sp-kinjective-bridge|rightDerived.*Complex|derived.*Resolution|KInjectiveResolutionData"
  — no attachment for this node. Existing rightDerivedPlusComplex is for objects X : C,
  while rightDerivedFunctorObjQIso compares objects in localized derived categories;
  neither defines the chosen representative v(I) with the argument K ∈ Ch⁺(C).
- rg over Mathlib Homology, WeilConjectures and lean/Sheaf for KInjective/kinjective — found
  the reusable generic Mathlib K-injectivity, the recorded existence theorem, and the
  specialized étale resolution wrapper. No generic bundled choice of a resolution was found.
- Exact proposed names KInjectiveResolutionChoice, grothendieckKInjectiveResolutionChoice,
  rightDerivedComplexWithResolution and rightDerivedCohomologyWithResolution were searched
  in Mathlib, WeilConjectures, lean/Sheaf and the upstream-name index — no collisions.

Validation: scompile.py on the server passes with exit code 0, no warnings, 1.5 seconds.
Every universe and variable is explicitly bound. No statement dispute or node fault found.



Recheck after the earlier blocked attempt (2026-10-11): read the item, all four
statement dependency nodes, their recorded source declarations and docstrings,
and the original blueprint file over read-only SSH. The original blueprint has
bounded-below existence; the reviewed DAG explicitly extends existence to every
complex via the recorded functorial-existence node. The supplied module implements
that reviewed statement. No mathematical or Lean repair was needed. Only `lean`
differs from the repository node, its signature is verbatim, and every Lean line
has at most 100 characters.

Repeated reuse searches with msearch.py: LeanFinder query "chosen K-injective
resolution of bounded below complex applying additive functor termwise" returned
eight object-resolution and K-injectivity results, no exact bridge; Loogle query
`"IsKInjective"` returned twelve reusable predicate/lemma results; grep query
`KInjectiveResolutionChoice|rightDerivedComplexWithResolution|rightDerivedCohomologyWithResolution`
returned no Mathlib hits. Direct rg of the same names and the item id in Mathlib,
upstream WeilConjectures, and repository lean/Sheaf returned no matches.

The required deliver2.py --no-push recheck printed OK: preflight and clean server
compilation pass. The earlier repository-root report.md tool blocker did not
recur; no manual repository mutation or tool workaround was performed. Nothing
was pushed. The existing second-reading section below was inherited from the
sandbox's earlier attempt, not written by this worker.

## Earlier second reading (a previous round; superseded)

Independent reading of the node, all four dependency nodes, the delivered module,
Mathlib signatures, and the upstream existence module. I read the source blueprint
on the server at its recorded path (the local literature checkout omits it), and
Stacks `derived.tex` at labels definition-K-injective and
lemma-enough-K-injectives-implies (070H/070K), plus `injectives.tex` at
label theorem-K-injective-embedding-grothendieck (079P), using the local copies in
`/home/ubuntu/c1-stacks-review/`. The blueprint gives the chosen-resolution
convention and defers independence. Stacks 070H assumes only an abelian category;
079P assumes Grothendieck abelian and covers all complexes, justifying the node's
reviewed existence clause. There are no implicit scheme or ring hypotheses.

Objects, hypotheses, and clauses checked individually:

1. An arbitrary abelian category and its integer-indexed complex K are
   `{C : Type u₁} [Category.{v₁} C] [Abelian C] (K : CochainComplex C ℤ)`
   in `KInjectiveResolutionChoice`. Verdict: exact, not the specialized étale category.
2. A resolution K → I is `complex : CochainComplex C ℤ`, `map : K ⟶ complex`,
   `quasiIso : QuasiIso map`, `isKInjective : complex.IsKInjective`.
   Verdict: exactly the data requested; no monomorphism, injective terms, or
   boundedness imposed. Read `IsKInjective`'s field: every map from an acyclic
   complex has a null homotopy. This is the Stacks definition; applying it to
   every shift of the acyclic source kills every degree of the external Hom
   complex. It is the SAME generic predicate recorded by the dependency node,
   whose scheme-specific `IsKInjectiveResolution` abbreviation is inapplicable
   to general C. No private predicate or replacement dependency is needed.
3. Grothendieck existence for every complex is
   `[IsGrothendieckAbelian.{w} C]` and `grothendieckKInjectiveResolutionChoice K`.
   Verdict: exact. Read Basic.lean's class, its colimits instance, and the four
   recorded upstream signatures: `kInjectiveResolutionFunctor`,
   `toKInjectiveResolution`, `monoQuasiIso_toKInjectiveResolution_app`, and
   `isKInjective_kInjectiveResolutionFunctor_obj`. The data constructor uses
   those declarations directly; it states no new theorem and does not add the
   upstream monomorphism property to the resolution structure.
4. Abelian A and B with left exact additive v are the independent C and D
   binders, `[Abelian C] [Abelian D]`, `(F : C ⥤ D) [F.Additive]`
   and `[PreservesFiniteLimits F]` in both bridge definitions.
   Verdict: exact. Read the Additive class, finite-limit preservation, and
   `preservesFiniteLimits_of_preservesKernels`: in abelian categories this
   is the recorded dependency's kernel-preserving additive notion. Enough
   injectives belongs to that dependency's object-level construction, not
   the present definitions with supplied resolution data.
5. K ∈ Ch⁺(A) is `(K : CochainComplex.Plus C)`. Verdict: exact.
   Read `CochainComplex.plus`: there exists an integer lower bound with
   `K.IsStrictlyGE n`; it is not restricted to nonnegative terms.
6. Choose K → I is `(r : CochainComplex.KInjectiveResolutionChoice K.obj)`.
   Verdict: exact, explicitly chosen before computing either result.
7. RvK = v(I) is
   `(F.mapHomologicalComplex (ComplexShape.up ℤ)).obj r.complex`.
   Verdict: exact. Read Additive.lean's definition: terms are `F.obj (I.X i)`
   and differentials are `F.map (I.d i j)`. Its zero-preserving requirement
   follows from additivity. The output need not have bounded-below terms,
   since the node does not bound the chosen I.
8. R^p v(K) = H^p(RvK) is `(p : ℤ)` followed by
   `(F.rightDerivedComplexWithResolution K r).homology p`.
   Verdict: exact, every integer degree and the same chosen representative.
9. Independence and agreement on degree-zero objects are the forward
   reference to `lem-sp-kinjective-computes`, retained in the module and
   cohomology docstrings. Verdict: exact; neither is asserted prematurely.
   The current definitions deliberately retain r.

Edge cases: the zero complex, zero functor and zero abelian category are
allowed; abelian categories themselves cannot be empty because they have a
zero object. Empty schemes are irrelevant to this generic node and are not
excluded by a scheme binder. There is no index family, characteristic,
Noetherian, finiteness, or ring restriction. Bounds of either sign and zero,
unbounded positive tails, and p negative/zero/positive are all admitted.
Existence also covers unbounded K. The object and morphism universes of C
and D are independently explicit, and w is independent. Taking w = v₁
recovers the dependency's exact ordinary Grothendieck notion; the additional
size parameter excludes none of those cases.

Independent reuse searches, 2026-10-11 (recorded by msearch.py):

- LeanFinder: “Apply an additive functor to a chosen fibrant replacement of a
  bounded below cochain complex and take homology”: eight hits, including
  `Functor.rightDerived`, `DerivedCategory.homologyFunctor`, and localization
  functors. Their signatures concern objects or localized complexes, not
  the chosen complex representative with explicit resolution input.
- Loogle: `"IsKInjective"`: twelve hits, including the generic predicate,
  its constructor, shift closure, and cocycle-boundary lemmas. These provide
  the reused notion, not this bridge definition or a bundled resolution.
- msearch grep: `ResolutionChoice|rightDerivedComplex|rightDerivedPlusComplex|rightDerivedFunctorObjQIso`:
  no Mathlib hits.
- LeanSearch: “A chosen quasi-isomorphism from a cochain complex to a K-injective
  complex used to define derived cohomology”: Internal Server Error,
  recorded unavailable; no mathematical verdict inferred from that failure.
- Independently rg-searched Mathlib Homology and RightDerived, upstream
  WeilConjectures, repository lean/Sheaf, and dag/lean_names_upstream.json
  for resolution structures, derived-complex names, KInjective declarations
  and the item's id. Opened upstream `rightDerivedPlusComplex (X : C)`:
  only objects, using ordinary injective resolutions. Opened
  `rightDerivedFunctorObjQIso (I : CochainComplex C ℤ) [I.IsKInjective]`:
  an isomorphism after localization, with HasDerivedCategory hypotheses,
  not the present choice-dependent definition. No exact reusable bridge,
  generic bundled choice, or name collision was found.

H5/H6/H8/H9: all four declarations are genuine structures/definitions with
concrete data, no sorry, no theorem proved. Every declaration and the module
have source docstrings and the exact blueprint id. The node has empty proof,
so no proof steps are missing from a theorem docstring. Imports serve the
bounded-below, termwise functor, left-exact and existence APIs. All variables
and universes are explicitly bound. No new nodes, dependency modules, or
statement correction occur, so H12/H13 and correction-citer review are
inapplicable.

Mismatch and repair: no mathematical mismatch found, and the Lean module
was left intact. The node's lean.statement was whitespace-normalized rather
than literally verbatim; replaced it with the exact multiline signature from
the file, stopping before :=. No node statement or dependency list changed.

Validation: single-file server compilation and delivery dry run are run
by this second reader; the delivery tools enforce clean compilation and
preflight before pushing.


## Second reading by H1

Independent second reading on 2026-10-11. I opened the sandbox node and module,
all four statement-dependency nodes, their recorded declarations and docstrings,
and the original blueprint source over read-only SSH. I also read Stacks
`derived.tex`, definition-K-injective (070H) and lemma-enough-K-injectives-implies
(070K), and `injectives.tex`, theorem-K-injective-embedding-grothendieck (079P),
in `/home/ubuntu/c1-stacks-review`. Definition 070H assumes an arbitrary abelian
category; 079P assumes a Grothendieck abelian category and includes unbounded
complexes. No ambient scheme, ring, finiteness or characteristic assumption is
present. The original blueprint mentions bounded-below existence; the already
reviewed repository node explicitly includes all complexes using 079P and the
recorded functorial-existence dependency. This delivery does not correct the node.

Objects, hypotheses and clauses of the node, matched individually:

1. An abelian category and an integer-indexed complex K: the structure binds
   `{C : Type u₁} [Category.{v₁} C] [Abelian C] (K : CochainComplex C ℤ)`.
   Verdict: exact, with no specialization to the étale category.
2. A resolution K → I: `complex : CochainComplex C ℤ`, `map : K ⟶ complex`,
   `quasiIso : QuasiIso map`. Verdict: exactly the target and quasi-isomorphism;
   no monomorphism or termwise injectivity is required of supplied resolutions.
3. K-injectivity of I: `isKInjective : complex.IsKInjective`. I read Mathlib's
   class field `nonempty_homotopy_zero`: every map from an acyclic complex is
   null-homotopic. This is precisely Stacks 070H. Degree-n cycles of Hom(A,I)
   are maps from the corresponding shift of A; its boundaries are null-homotopic
   maps. Since shifts of acyclic complexes are acyclic, all Hom-complex
   cohomology vanishes. Verdict: the dependency's recorded generic predicate
   is the same notion. Its specialized `IsKInjectiveResolution T R` abbreviation
   cannot be applied to arbitrary C; bundling its recorded generic components
   here adds no private predicate or replacement dependency.
4. Every complex in a Grothendieck abelian category has such a resolution:
   `grothendieckKInjectiveResolutionChoice` binds
   `[IsGrothendieckAbelian.{w} C]` and arbitrary `K : CochainComplex C ℤ`.
   Its four fields use the recorded `kInjectiveResolutionFunctor`,
   `toKInjectiveResolution`, `monoQuasiIso_toKInjectiveResolution_app` (second
   component), and `isKInjective_kInjectiveResolutionFunctor_obj` directly.
   Verdict: exact, including bounded-below complexes, using existing data.
   I read the class's AB5, separator and locally-small fields and its inferred
   colimits instance. Taking w = v₁ recovers the dependency's stated size
   convention; the independent w also permits its standard shrinking formulation.
5. Abelian A and B, left exact additive v: the bridge binds independent C and D,
   their Category and Abelian instances, `(F : C ⥤ D) [F.Additive]` and
   `[PreservesFiniteLimits F]`. I read AdditiveFunctor and LeftExact, including
   `preservesFiniteLimits_of_preservesKernels`. Verdict: equivalent to the
   dependency's additive, kernel-preserving notion in abelian categories.
   Enough injectives is needed by that dependency's object-level right derived
   functors, not by the present construction with a supplied resolution.
6. K in Ch⁺(A): `(K : CochainComplex.Plus C)`. I read the defining property
   `∃ n : ℤ, K.IsStrictlyGE n` and its full subcategory. Verdict: arbitrary
   integer lower bounds, not a restriction to nonnegative terms.
7. Choose K → I before forming RvK: the argument
   `(r : CochainComplex.KInjectiveResolutionChoice K.obj)` follows F and K.
   Verdict: the choice is explicit and the quantifier order is correct.
8. RvK = v(I): `rightDerivedComplexWithResolution` returns
   `(F.mapHomologicalComplex (ComplexShape.up ℤ)).obj r.complex`.
   I read Homology.Additive's implementation, with terms `F.obj (I.X i)` and
   differentials `F.map (I.d i j)`. Verdict: exactly termwise application.
9. R^p v(K) = H^p(RvK): `rightDerivedCohomologyWithResolution` binds `(p : ℤ)`
   and returns `(F.rightDerivedComplexWithResolution K r).homology p : D`.
   Verdict: all integer degrees and the same chosen resolution.
10. Independence and the object-in-degree-zero comparison are forward references
    to lem-sp-kinjective-computes, not assertions proved here. The module and
    declaration docstrings explicitly preserve that convention; both definitions
    retain r. Verdict: exact, no premature well-definedness theorem.

Edge cases: zero complexes, the zero functor and the zero abelian category are
allowed. All integer lower bounds and degrees (including p = 0 and negative p)
are allowed; infinitely many nonzero positive-degree terms are allowed. I need
not be bounded below or termwise injective. The existence constructor also
accepts unbounded K. There is no index-family binder that excludes an empty
set. Empty schemes and characteristic restrictions do not arise in this
arbitrary-category statement. Object, morphism and Grothendieck size universes
are explicitly and independently bound; no variable is auto-implicit.

Independent reuse searches, using words different from the worker's:

- msearch.py LeanFinder: "bounded below cochain complex right derived functor
  represented by image of a K-injective replacement"; eight hits, including
  Functor.rightDerived, DerivedCategory.Q and mapDerivedCategoryFactors.
  These are object-level functors or localized-category constructions, not
  the chosen complex representative defined by this node.
- msearch.py Loogle: `"KInjective"`; twelve hits, including the reusable
  CochainComplex.IsKInjective and its homotopy/shift lemmas, no bridge definition.
- msearch.py grep: `rightDerivedComplex|KInjectiveResolutionChoice|derivedCohomology`;
  no Mathlib hits.
- msearch.py LeanSearch: "right derived complex defined by applying a left exact
  additive functor to a chosen K-injective resolution"; unavailable with
  Internal Server Error. Recorded as unavailable, not a negative search result.
- Direct rg on Mathlib Homology, upstream WeilConjectures, repository lean/Sheaf
  and dag/lean_names_upstream.json for the delivered names and
  `[Rr]ightDerived.*[Cc]omplex|[Dd]erived.*[Rr]esolution`. I opened the candidate
  `Functor.rightDerivedPlusComplex`: its input is X : C, not a complex K.
  I also opened the upstream DerivedCategory/KInjective module: its declarations
  compare two resolutions, rather than define the bridge. Ordinary rightDerived
  and localized derived functors likewise do not supply this node's definitions.
  No duplicate of the generic bundled choice or either bridge definition found.

No mathematical mismatch found; no Lean or node changes made. No new definition
nodes or dependency modules were supplied or needed. The existing source and
blueprint docstrings meet the convention; this definition node has empty proof
steps and introduces no theorem. There is no sorry or hollow data. The node's
lean.statement is verbatim the main signature before :=, all Lean lines are at
most 100 characters, and names have no Sheaf namespace prefix.

Fresh server validation: scompile.py compiled the sole module in 1.4 seconds,
exit code 0, with no warnings. This section is the new independent reading;
the earlier superseded reading remains as historical report text.
