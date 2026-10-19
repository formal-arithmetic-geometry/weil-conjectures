## Worker report

The module `Sheaf.AlgebraicGeometry.AllowableTorsionDerivedCategories` defines the bounded
and bounded-below allowable-torsion derived categories of **abelian** etale sheaves.
Its namespace is `AlgebraicGeometry.Etale`. All definitions have explicit data; the four
structure/strict-fullness theorems are statements with `sorry`, as required by stage 2.
No node statement, dependency, or target was changed. No new nodes or dependency modules
are needed: the auxiliary object properties express clauses already introduced by this node.

Clause-by-clause correspondence:

- A scheme T is the binder `(T : Scheme.{u})`, without any finiteness or characteristic
  restriction. The set of primes is encoded by `(P : Set ℕ)` and only tested on prime
  natural numbers. Nonprime members are ignored, giving every set of primes.
- Abelian etale sheaves are `Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}`,
  exactly the coefficient-free category specified by def-weil-pbc-derived-categories.
  `DerivedCategory` is Mathlib's derived category of this category; no coefficient ring
  or equivalence with integer-module sheaves is substituted.
- `allowableTorsionSheafProperty T P` quantifies over `(Ω : Type u) [Field Ω]
  [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ T)`. These are the geometric points for the
  small etale site, with the same universe convention as its recorded stalk definition.
  Separably closed fields suffice for etale geometric points, as in `Scheme.pointSmallEtale`.
- The geometric stalk is `((Scheme.pointSmallEtale s).sheafFiber
  (A := AddCommGrpCat.{u + 1})).obj F`. Every element is quantified by `x` in that group.
  `∃ n : ℕ, 0 < n` supplies a positive integer; `n • x = 0` is its annihilator equation;
  `∀ p : ℕ, p.Prime → p ∣ n → p ∈ P` is exactly the allowable-prime-divisor condition.
- `DerivedCategory.homologyProperty (allowableTorsionSheafProperty T P)` quantifies
  over every integer degree, applying `DerivedCategory.homologyFunctor` to K. It is
  the clause on every cohomology sheaf, with no uniform annihilator or bound imposed.
- `allowableTorsionPlusProperty` intersects that property with
  `DerivedCategory.TStructure.t.plus`, the existing bounded-below property.
  `allowableTorsionBoundedProperty` uses `.bounded`, the existing bounded property.
- The two `AbelianDerivedCategory...TorsionOfPrimes` abbreviations are the corresponding
  `ObjectProperty.FullSubcategory`. Fullness is built into this construction. They are
  realized as full subcategories of D(T_et) whose objects satisfy the boundedness condition,
  rather than nesting two full-subcategory wrappers. This has exactly the same objects and
  morphisms as the full subcategory of D^+ or D^b in the node, with the canonical inclusion
  into the appropriate bounded category obtained by retaining the boundedness witness.
- The two `_isClosedUnderIsomorphisms` theorem instances state strict fullness. The two
  `_isTriangulated` theorem instances supply zero, shift, and triangle closure. Mathlib's
  `ObjectProperty.FullSubcategory` instances then supply the inherited category, shifts,
  distinguished triangles, and triangulated structure on both abbreviations. They do not
  choose an arbitrary triangulation. Their docstrings spell out the weak-Serre argument
  from the node's split report: zero killed by 1, subgroup/quotient closure, product of
  annihilators for extensions, exact stalks, and the generic cohomology lemma.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.DerivedCategories`: its documentation specifies coefficient-free
  `DerivedCategory (Sheaf T.smallEtaleTopology AddCommGrpCat.{u+1})` and Mathlib cohomology.
  Its `AlgebraicGeometry.Etale.DerivedCategory.torsionCohomology` is module-valued and
  does not encode allowable primes; that predicate is therefore not misapplied here.
- `Mathlib.CategoryTheory.Sites.Point.Basic`:
  `CategoryTheory.GrothendieckTopology.Point.sheafFiber`, specialized through
  `Mathlib.AlgebraicGeometry.Sites.EtalePoint`, `AlgebraicGeometry.Scheme.pointSmallEtale`.
  Both declaration bodies and docstrings were read: the fiber is the colimit over pointed
  etale neighborhoods, as required, rather than a Zariski stalk.
- `Sheaf.Paper.CohomologyInWeakSerreSubcategory`:
  `CategoryTheory.cohomology_in_weak_serre_subcategory`. This dependency is imported and
  is the exact generic lemma prescribed in the structure-theorem proof plans.
  Its imported `DerivedCategory.homologyProperty` is used directly, not copied.
- Exact geometric stalks: the recorded Mathlib finite-limit-preserving sheafFiber instance
  in `Point.Basic`, the left-adjoint instance in `Point.Skyscraper` (imported for the
  postponed proof), and `CategoryTheory.ShortComplex.ShortExact.map_of_exact`. Their
  signatures were read. They supply the exactness step of the named structure theorems.

Edge cases checked before writing:

- P empty forces each stalk element to be killed by 1, hence zero; n=1 is permitted and
  has no prime divisors. Zero sheaves and zero complexes are therefore included.
- P all primes gives all torsion cohomology. A singleton gives primary torsion, without
  imposing a common exponent across elements, points, or degrees.
- n=0 is excluded by `0 < n`; a torsion-free nonzero stalk cannot satisfy the condition.
- Negative cohomological degrees are included by `homologyProperty`'s integer quantifier.
  Bounded-below objects may have arbitrarily high nonzero cohomology; bounded objects may
  have any finite cohomological range, with no fixed bounds.
- The empty scheme has the vacuous geometric-point condition; no nonemptiness, invertible
  primes on T, or characteristic restrictions were added. Geometric-point fields use T's
  universe, following the existing stalk API; stalk groups live in the prescribed u+1.

Searches for an existing definition:

- msearch LeanFinder, query `full subcategory derived category abelian etale sheaves
  allowable prime torsion cohomology`: eight results, all standard DerivedCategory
  IsGE/IsLE and representing-complex lemmas; no matching definition.
- msearch Loogle, query `DerivedCategory.Plus, DerivedCategory.Bounded`: zero hits.
- msearch LeanSearch, query `derived category abelian sheaves torsion prime set`:
  service unavailable, Internal Server Error; no result inferred.
- msearch grep of Mathlib, query
  `allowable|torsionHomologyOfPrimes|IsTorsionSheafOfPrimes`: zero hits.
- rg over WeilConjectures and lean/Sheaf for allowable/Allowable and torsion/prime
  combinations, plus rg for the node id in WeilConjectures: upstream
  `Scheme.IsTorsionSheafOfPrimes`, `Etale.DerivedCategory.Plus.torsionHomologyOfPrimes`,
  `Etale.DerivedCategoryPlusTorsionOfPrimes`, and
  `Etale.DerivedCategory.Plus.boundedTorsionHomologyOfPrimes` were read in full.
  Each uses `Sheaf ... (ModuleCat Λ)`, not abelian sheaves; the bounded upstream property
  additionally lives inside D^+. No existing declaration defines this node's abelian
  categories. `Scheme.HasTorsionEtaleCohomology` in lean/Sheaf has abelian coefficients
  but no allowable-prime condition. No matching project declaration was found.
- rg for the proposed names over Mathlib, WeilConjectures, lean/Sheaf and
  dag/lean_names_upstream.json: no collisions.

Validation uses only scompile.py on the server, nice 19, two threads, 60 seconds per file.
No local Lean compiler or lake build was run. The initial elaboration required specifying
`A := AddCommGrpCat` on `sheafFiber` to disambiguate its concrete target category.

The final module compiled cleanly in 1.6 s. A subsequent temporary `#synth` check
confirmed that both category abbreviations inherit `CategoryTheory.IsTriangulated`
through Mathlib’s `ObjectProperty.instIsTriangulatedFullSubcategory` (1.7 s).
The probes were removed from the delivered module.

## Second reading by NF

I independently read the node copy, the complete candidate module, its four dependency
nodes and their recorded declarations, the master blueprint definition and its containing
unit, and Stacks derived.tex Tag 06UQ (including bounded intersections). The item's source
is the blueprint definition, rather than a separate Stacks definition. It assumes no
Noetherian, finiteness, coefficient-ring, characteristic, or invertibility hypothesis.
The Lean says exactly what this node says. No mathematical or metadata repair was needed;
only this independent review was appended. The worker report above is retained.

The object/hypothesis/conclusion checklist, with the Lean rendering and verdict:

1. An arbitrary scheme T: `(T : Scheme.{u})` on every declaration. No additional
   instance on T is required. Pass.
2. A set of primes P: `(P : Set ℕ)`, used only under `p.Prime`. Extra nonprime
   members have no effect, so this represents every set of primes without an added
   hypothesis. Pass.
3. Abelian etale sheaves on T: `Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}`.
   I opened `Sheaf.AlgebraicGeometry.DerivedCategories`: its module documentation
   explicitly records this coefficient-free derived category, while its new
   `DerivedCategory.torsionCohomology` is module-valued and is correctly not used.
   The candidate uses Mathlib `DerivedCategory` of precisely the abelian category. Pass.
4. Every cohomology sheaf in every integer degree: `DerivedCategory.homologyProperty
   (allowableTorsionSheafProperty T P)`. I opened the upstream HomologyProperty module:
   its body is `fun M ↦ ∀ n : ℤ, P ((homologyFunctor A n).obj M)`.
   This is cochain cohomology, with no sign reversal or omitted degrees. Pass.
5. Every geometric stalk: `∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
   (s : Spec (.of Ω) ⟶ T)`. I read `Scheme.pointSmallEtale` in EtalePoint:
   its fiber is the set of lifts of s to an etale neighborhood. I also read
   `Point.presheafFiber` and `Point.sheafFiber` in Point.Basic: these take the colimit
   over the opposite category of elements and then restrict to sheaves. Consequently
   the explicit `(Scheme.pointSmallEtale s).sheafFiber` is the recorded dependency's
   geometric stalk, not a Zariski stalk. Separably closed test fields and the shared
   universe follow that API and the existing stalk node. Pass.
6. Each element x has its own allowable positive annihilator:
   `∀ ... (x : ...), ∃ n : ℕ, 0 < n ∧
   (∀ p : ℕ, p.Prime → p ∣ n → p ∈ P) ∧ n • x = 0`.
   The existential is inside the point and element quantifiers and, through
   homologyProperty, inside the degree quantifier. There is no uniform exponent. Pass.
7. The bounded-below category: `allowableTorsionPlusProperty` is the intersection
   of that homology property with `DerivedCategory.TStructure.t.plus`, and
   `AbelianDerivedCategoryPlusTorsionOfPrimes` is its `FullSubcategory`. I opened the
   t-structure definitions: plus is `∃ n : ℤ, t.IsGE X n`, and Mathlib's
   `DerivedCategory.Plus` is this property's full subcategory. Pass.
8. The bounded category: the analogous bounded property intersects with `t.bounded`,
   which is `t.plus ⊓ t.minus`; `AbelianDerivedCategoryBoundedTorsionOfPrimes` is
   its full subcategory. This allows any finite cohomological range. Pass.
9. Fullness and inherited triangulation for both categories: `FullSubcategory` supplies
   all ambient morphisms; the two `_isClosedUnderIsomorphisms` theorem instances
   supply strict fullness; the two `_isTriangulated` theorem instances supply zero,
   all integer shifts and triangle closure. I opened Mathlib Triangulated.Subcategory:
   its full-subcategory distinguished triangles are the inverse image of ambient
   distinguished triangles, and its final instance inherits IsTriangulated. Thus no
   arbitrary triangulation is chosen. Using one intersection wrapper inside D instead
   of two nested wrappers inside D^+ or D^b retains exactly these objects and morphisms:
   the canonical inclusion into D^+/D^b simply keeps the boundedness witness. Pass.
10. The node prescribes weak-Serre closure and exact stalks for well-definedness.
    I opened `CategoryTheory.cohomology_in_weak_serre_subcategory`: its hypotheses are
    zero, isomorphism, kernel, cokernel and extension closure, and its conclusion has
    exactly the unbounded, plus and bounded IsTriangulated clauses. The candidate's
    structure-theorem docstrings give those steps (annihilator 1; subgroup/quotient
    closure; product mn for extensions; exact stalks; the generic lemma).
    Point.Basic preserves finite limits; Point.Skyscraper supplies a left adjoint;
    `ShortComplex.ShortExact.map_of_exact` takes preservation of finite limits,
    finite colimits and zero morphisms. I read these signatures and the adjunction.
    Their specialization to abelian stalks is usable. Pass.

Edge cases: P empty permits n=1 and forces zero stalks; all primes allow every torsion
stalk; a singleton permits primary torsion of unbounded exponent. Zero sheaves and zero
complexes are included. n=0 is excluded explicitly. On the empty scheme the point condition
is vacuous, as it should be. Negative degrees are quantified, plus permits infinitely many
positive nonzero degrees, and bounded has no fixed range. No condition ties P to residue
characteristics or invertibility. The single declared universe u is bound everywhere;
schemes/test fields use u and coefficient groups u+1, as in the dependency's recorded API.
There is no independent smaller test universe and no unbound implicit variable.

Independent H4 searches (different queries from the first reader):

- msearch LeanFinder: `derived subcategory cohomology stalk primary torsion abelian groups`.
  Eight hits, including Sheaf.H, cohomologyPresheaf and DerivedCategory IsLE/IsGE lemmas;
  none defines these allowable-torsion abelian derived categories.
- msearch Loogle: `ObjectProperty.IsTriangulated`: unknown identifier, no usable hits.
- msearch LeanSearch: `bounded derived category of abelian sheaves with primary torsion
  geometric fibers`: service unavailable (Internal Server Error); no verdict inferred.
- rg over upstream WeilConjectures for `torsionHomologyOfPrimes`,
  `boundedTorsionHomologyOfPrimes`, `IsTorsionSheafOfPrimes` and
  `DerivedCategoryPlusTorsionOfPrimes`; I opened each defining signature and body in
  TorsionSheaf and SmoothBaseChange.Derived. They use `ModuleCat Λ`, and the bounded
  predicate lives inside module-valued D^+. They do not directly define the node's
  abelian-sheaf objects; substituting integer modules would require a comparison and
  would change the literal ambient category. The candidate correctly preserves the
  node's abelian encoding.
- rg for allowable and torsion/prime combinations over the project's lean/Sheaf and
  Mathlib Algebra/Homology and CategoryTheory found no matching definition; proposed
  names have no occurrence in dag/lean_names_upstream.json. Existing generic
  homologyProperty and boundedness properties are used directly, not duplicated.

There are no new nodes or dependency modules in this delivery, no statement_change,
no private definitions, no hollow data definitions, and no proved theorems. The four
named structure theorems use only `sorry` proofs and have source-tagged proof plans;
all declarations have the item's blueprint tag. The node's lean.statement is verbatim
`abbrev AbelianDerivedCategoryBoundedTorsionOfPrimes (T : Scheme.{u}) (P : Set ℕ) : Type _`,
matching the file's signature.

Validation: reran scompile.py on the candidate module. It compiled cleanly on the server
in 1.6 seconds, nice 19, two threads, 60-second per-file limit (the dependency module
compiled in 1.0 seconds). No error or unexpected warning. No local compiler or lake build.
