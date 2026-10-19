## Worker report

The module `Sheaf.Paper.LocalizingExceptionalAdjoint` states
`AlgebraicGeometry.ProEtale.CondensedRing.exists_localizingExceptionalAdjoint` with one
`sorry`. Its two data-bearing helpers are the canonical restriction
`localizingLowerShriek` and its inherited coherent shift instance
`localizingLowerShriekCommShift`. Both have real definitions; neither chooses an
arbitrary functor or assumes an exceptional adjoint. The item's node changes only in `lean`.
No definitions or prerequisite statements are added as new nodes.

The source read is the current main-20261015 unit `_section.md` and its
`sk-prop-sf-existence.proof.md`, together with the expanded DAG statement and proof.
The older upstream exceptional-adjoint declarations concern ordinary etale sheaves,
bounded-below etale-origin objects, or conditional ambient adjoints. They do not state
this localizing-closure module-object result and cannot be recorded as an exact match.

Clause-by-clause correspondence:

- Prime ell: `(ℓ : ℕ) [Fact ℓ.Prime]`.
- A field of positive characteristic p different from ell: `(k : Type u) [Field k]`,
  `[Fact (ringChar k).Prime]` and `[Fact (ringChar k ≠ ℓ)]`. Field characteristic is
  prime when positive, so this expresses exactly the positive-characteristic setting.
- The schemes X and Y over k: their `Scheme.Over (Spec (.of k))` instances.
- Both schemes are separated and finite type over k: `IsSeparated`,
  `LocallyOfFiniteType` and `QuasiCompact` on each structure morphism.
- The separated finite-type k-morphism f: `(f : X ⟶ Y)`, its `IsOver` instance,
  and `IsSeparated f`, `LocallyOfFiniteType f`, `QuasiCompact f`.
- The chosen factorization with quasi-compact open immersion and proper second map:
  `c : Compactification.BoundaryCompactification f`. Its underlying compactification
  `c.obj.obj` contains the middle scheme, the two arrows, their properties and the
  factorization equality; `QuasiCompactObjects` adds quasi-compactness of the open map.
  Boundary-preserving morphisms of this category impose no extra condition on its objects.
  The statement quantifies over each choice, rather than fixing a special one.
- The commutative condensed coefficient ring is the parameter Λ with `MonObj` and
  `IsCommMonObj`. `_hΛ` is the explicit admissibility disjunction. Its first branch
  is a finite discrete commutative ring A with `∃ n, (ℓ ^ n : A) = 0`.
  The other branches are Z_ell, Q_ell, the valuation ring and field of a finite
  intermediate extension of Q_ell in its algebraic closure, and Qbar_ell.
  Ring-object isomorphisms allow arbitrary presentations of those coefficient rings.
  The Qbar term is the existing finite-subextension condensed ring; this follows the
  current framework convention and does not replace it with all continuous Qbar maps.
- Dctf and its localizing closure are exactly `localizingClosureProEtale Λ X` and
  `localizingClosureProEtale Λ Y`, with their `FullSubcategory`. That recorded definition
  uses `constantModelBoundedConstructible` intersected with `finiteTorAmplitude` inside
  the ordinary unbounded derived category of internal modules over `condensedRingObj`.
  There is no completeness restriction or replacement by the ambient derived category.
- The functor is `rightDerivedLowerShriekOfCompactification Λ c.obj.obj`, namely the
  separately derived extension by zero followed by derived proper pushforward.
  The conclusion supplies its membership proof h. `localizingLowerShriek` applies the
  standard `ObjectProperty.lift` to that exact composite, on objects and on morphisms.
- Exactness of this restricted functor is `.IsTriangulated`, for the canonical
  shift comparison inherited through the fully faithful inclusions. The proofs hX,hY
  that the closures are triangulated are existential conclusions, and their category
  structures are Mathlib's induced ambient structures, not arbitrary triangulations.
- Existence of small direct sums is stated by `Nonempty (HasCoproducts.{u + 1} ...)`
  for both closures. Small coproduct preservation by the lower shriek is
  `∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I) ...`.
- The exceptional functor is `∃ G : Loc(Y) ⥤ Loc(X)` with `∃ adj : F ⊣ G`.
  An `Adjunction` includes the natural Hom equivalences in both M and N and both
  triangle identities; this expresses the displayed natural bijections for every object.
- Exactness of G is `∃ s : G.CommShift ℤ`, followed by `G.IsTriangulated` using
  precisely that coherent shift comparison through an explicitly applied instance lambda.
- Preservation of all small direct sums by G is
  `∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I) G`.
  There is no nonempty or finite restriction on I. This is the fixed larger indexing
  universe used for the sheaf/derived constructions, above the scheme universe u.
- Uniqueness is explicit: for every other J and every `adjJ : F ⊣ J`, there is
  exactly one `e : G ≅ J` with `F.map (e.hom.app N) ≫ adjJ.counit.app N = adj.counit.app N`
  for every N. Counit compatibility determines the isomorphism, equivalently the
  adjunction-compatible unique isomorphism in the node.

Dependency declarations read and used:

- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  `AlgebraicGeometry.ProEtale.CondensedRing.compactificationOverField` and its docstring
  give the standing over-field/Nagata convention. This module is imported; the theorem
  uses explicit standing binders and the arbitrary chosen compactification from the node.
- `Sheaf.Paper.CondensedConstantConstructibility` (publicly reexported by LocalizingClosure):
  `IsConstantModelConstructible`, `constantModelBoundedConstructible`,
  `ConstantModelConstructibleFiniteTor`. These are used through the recorded closure.
- `Sheaf.Paper.LocalizingClosure`: `CategoryTheory.localizingClosure`,
  `CategoryTheory.IsLocalizingSubcategory`, `AlgebraicGeometry.ProEtale.localizingClosureProEtale`.
- `Sheaf.Compactification.BoundaryRefinement`:
  `AlgebraicGeometry.Compactification.BoundaryCompactification`, `QuasiCompactObjects`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek`
  (publicly reexported by BoundedConstructible):
  `AlgebraicGeometry.ProEtale.CondensedRing.rightDerivedLowerShriekOfCompactification`.
- Mathlib's `ObjectProperty.lift`, inherited full-subcategory shifts/triangulation,
  `Functor.CommShift`, `Functor.IsTriangulated`, `Adjunction`, `HasCoproducts`, and
  `PreservesColimitsOfShape` provide the categorical interfaces without copies.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated`
  provides the actual ambient derived shift comparison used in the helper instance.
- All currently stated proof dependencies are imported: Nagata's
  `WeilConjectures.Compactification.Dense`, `Sheaf.CategoryTheory.BrownRepresentabilityRightAdjoint`,
  `Mathlib.CategoryTheory.Yoneda`, `Mathlib.CategoryTheory.Triangulated.Adjunction`,
  `Mathlib.CategoryTheory.Adjunction.Unique`. The compact-object and triangle exactness/
  cone-zero modules are also reached through these imports. The unstated proof nodes
  sk-lem-brown-hypotheses, det-sf-comp-coherence-single and det-brown-hypotheses-generation
  have no module to import and are retained in the theorem's proof plan.

Edge cases checked before writing: empty X or Y impose no new nonemptiness condition;
identity and open/proper special cases retain the same composite; the zero coefficient
ring is included by the finite branch (n = 0 is allowed exactly when 1 = 0); finite
nonregular coefficient rings are not replaced by fields. The empty coproduct and all
infinite small families are included. No boundedness is imposed on objects of Loc(Dctf),
and the source and target of G have the required reversed order.

Searches (2026-10-18):

- `msearch.py ... leanfinder "Exceptional inverse image right adjoint to compact support
  direct image on localizing closures of constructible sheaves"`: categorical adjoint
  ingredients only; no exact geometric module-object statement.
- `msearch.py ... leanfinder "A coproduct preserving exact functor has a right adjoint by
  Brown representability"`: eight generic representability/adjoint results, no match.
- `msearch.py ... loogle "CategoryTheory.Adjunction.isTriangulated_rightAdjoint,
  CategoryTheory.Functor.IsLeftAdjoint"`: zero results.
- `msearch.py ... leansearch "Exceptional inverse image on the localizing closure of
  constructible finite Tor amplitude pro-etale module objects"`: eight results about
  Bousfield localization, extension-closed properties and unrelated geometry; no match.
- `msearch.py ... grep "rightDerivedUpperShriek|localizingClosure|[Bb]rown" CategoryTheory`:
  three author-name hits in Mathlib, no geometric functor or theorem.
- `rg` of the upstream WeilConjectures tree and `lean/Sheaf` for the node id,
  `rightDerivedUpperShriekAdjunction` and `localizingClosureProEtale`: upstream ordinary
  etale/conditional ambient declarations and the existing localizing definition and its
  proper/open consumer; no declaration of this result. The newer module-object sources
  were read in the shared `lean/WeilConjectures` overlay, as the brief requires.
- `rg` for `exists_localizingExceptionalAdjoint|localizingLowerShriek` in upstream and
  the shared side-project sources: no existing declarations with these names.
- `rg` for admissible condensed coefficient predicates: no existing predicate for this
  exact six-way disjunction; the existing `ProEtaleProperOpenInterchange` theorem uses
  the same explicit coefficient disjunction, so no duplicate definition was introduced.

One proof-plan scope issue was noticed: det-brown-hypotheses-generation currently states
zero detection only in the algebraic-closure-of-a-finite-field setting, whereas this
unit quantifies over every positive-characteristic field. The full compact-generation
conclusion of sk-lem-brown-hypotheses already supplies zero detection for the standing
setting. The docstring therefore makes that dependence explicit and treats the narrower
node as the detailed finite-field instance of the same cone argument. The theorem statement
and node fields are unchanged. No statement is disputed.

Validation: scompile.py compiles both the sandbox and final library module paths cleanly
under the standard per-file limit. The first attempts identified a missing explicit
restricted shift instance and a missing public import of the right-derived triangulation
interface; both were repaired using the existing canonical constructions. All universes
and binders are explicit, and autoImplicit is disabled.

## Second reading by NI

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
