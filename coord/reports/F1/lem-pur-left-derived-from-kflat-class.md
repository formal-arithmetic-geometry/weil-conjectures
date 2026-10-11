## Worker report

The module `Sheaf.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass` states
`CategoryTheory.Functor.leftDerived_from_resolvingClass`, with a single `sorry` proof.
It defines no new notions and changes only the item's `lean` record.

Hypothesis and clause correspondence:

- An arbitrary abelian category A is `(A : Type u) [Category.{v} A] [Abelian A]`.
- The category K(A) is `HomotopyCategory A (ComplexShape.up ℤ)`. Its objects are
  complexes (the quotient identifies homotopic morphisms, not objects).
- D(A) and its localization Q are `DerivedCategory A` and `DerivedCategory.Qh`.
  `[HasDerivedCategory.{w} A]` chooses the localization with its morphism universe;
  it is the size convention already present in the dependency's Mathlib match.
  The instance `HasDerivedCategory.standard` gives a choice for every abelian category.
- The triangulated target is `(D' : Type u') [Category.{v'} D']` together with
  `Preadditive`, `HasZeroObject`, integer `HasShift`, additive shifts,
  `Pretriangulated`, and `CategoryTheory.IsTriangulated`. These are precisely the
  structures in `def-weil-triangulated-category`, not restrictions on the target.
- The exact functor F is `(F : HomotopyCategory A (ComplexShape.up ℤ) ⥤ D')`
  with `[F.CommShift ℤ] [F.IsTriangulated]`. Additivity follows from Mathlib's
  `Functor.IsTriangulated` instance and is not a separate extra hypothesis.
- The arbitrary class of complexes is `P : Set (HomotopyCategory A (ComplexShape.up ℤ))`.
  It need not be closed under cones, shifts, or isomorphisms.
- Hypothesis (1) is `hres`: for every X there exist X' and `s : X' ⟶ X`, with
  `X' ∈ P` and `HomotopyCategory.quasiIso A (ComplexShape.up ℤ) s`.
- Hypothesis (2) is `hinv`: for all X, X' and `s : X ⟶ X'`, membership of both
  endpoints in P and the quasi-isomorphism property imply `IsIso (F.map s)`.
- Everywhere-defined left derivation is the first conclusion,
  `F.HasPointwiseLeftDerivedFunctor (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))`.
  This is pointwise existence at every homotopy-category object, using the
  Stacks-to-Kan bridge already named in the item's proof, rather than mere global existence.
- The total functor and natural comparison are existential binders
  `(LF : DerivedCategory A ⥤ D') (ε : DerivedCategory.Qh ⋙ LF ⟶ F)`.
  Lean writes composition in application order, so `Qh ⋙ LF` means LF composed with Q.
- Universality among all pairs is
  `LF.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))`.
  Its field is `LF.IsRightKanExtension ε`, which says the pair is terminal in
  `Functor.RightExtension Qh F`. Thus for every pair `(G, β : Qh ⋙ G ⟶ F)` there
  is a unique compatible natural transformation from G to LF.
- Exactness is the existential choice `comm : LF.CommShift ℤ`, installed by
  the explicit class-valued binder in the lambda `(fun (comm : LF.CommShift ℤ) => LF.IsTriangulated) comm`. The shift compatibility is data and
  is explicitly existentially bound, never supplied by a `sorry` definition.
- Computation on P is `∀ X, X ∈ P → IsIso (ε.app X)`, for the very same comparison
  transformation ε and the very same LF as above.

Dependency declarations read and used:

- `def-sp-abelian`: `CategoryTheory.Abelian` in
  `Mathlib.CategoryTheory.Abelian.Basic`, imported transitively by the first import.
  Its signature, docstring, and fields give finite products, kernels, cokernels,
  preadditivity and normal monos/epis; zero objects and finite biproducts follow.
- `def-weil-abstract-derived-category`: `DerivedCategory`, `HasDerivedCategory`,
  `DerivedCategory.Qh`, and its localization and triangulated instances in
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`. This is the precise dependency
  Mathlib match, including its chosen universe. `HomotopyCategory.quasiIso` from
  `Mathlib.Algebra.Homology.Localization` means isomorphism on every cohomology object.
- `def-weil-triangulated-category`: `CategoryTheory.Pretriangulated` in
  `Mathlib.CategoryTheory.Triangulated.Pretriangulated`,
  `CategoryTheory.IsTriangulated` in `Mathlib.CategoryTheory.Triangulated.Triangulated`,
  and `CategoryTheory.Functor.IsTriangulated` in
  `Mathlib.CategoryTheory.Triangulated.Functor`, imported transitively by the first import.
  Read all three signatures and docstrings, including the octahedral axiom.
- The second import `Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived`
  supplies `HasPointwiseLeftDerivedFunctor`; its imported `LeftDerived` supplies
  `IsLeftDerivedFunctor`. Their full signatures and docstrings, and the defining
  `IsRightKanExtension` signature/docstring in `Functor.KanExtension.Basic`, were read.

Sources checked: the local `literature/stacks-project/derived.tex` is absent on this
machine. Read the primary-source pages https://stacks.math.columbia.edu/tag/06XN
(the dual resolving-class hypotheses and computation conclusion) and
https://stacks.math.columbia.edu/tag/05SE (exactness of the everywhere-defined derived
functor). These agree with the node; no statement correction or dispute is needed.
The declaration's docstring carries all four node proof steps and their dependency ids.

Edge cases checked before writing:

- The zero category and zero functor are allowed. Identity resolutions satisfy the
  hypotheses, and the zero category still has all required triangulated structure.
- An empty P cannot satisfy `hres`, since an abelian category has a zero complex;
  the theorem does not artificially impose nonemptiness or exclude this implication.
- P may contain just chosen resolutions, without being closed under isomorphisms.
- Taking all complexes for P recovers the case where F already inverts every
  quasi-isomorphism; the counit is then an isomorphism at every object.
- Complexes are unbounded and indexed by all of ℤ. No boundedness, enough-projectives,
  monoidal structure, K-flatness, or coproduct assumption has been imposed.
- All object, hom, derived-hom and target universes are separately bound (`u`, `v`,
  `w`, `u'`, `v'`). No smallness equality restricts A or D'. Every variable is explicit.

Searches for an existing full statement (2026-10-11):

- `msearch.py ... leanfinder "left derived functor exists from resolving class of
  complexes and is exact triangulated"`: eight hits, including `mapDerivedCategory`,
  `HasLeftDerivedFunctor.mk'`, and exact-functor derived-category constructions.
  None states the arbitrary resolving-class criterion.
- `msearch.py ... loogle "CategoryTheory.Functor.HasLeftDerivedFunctor,
  CategoryTheory.Functor.IsTriangulated"`: zero hits.
- `msearch.py ... grep "HasLeftDerivedFunctor|IsRightKanExtension|Qh"
  CategoryTheory/Functor/Derived`: ten hits in LeftDerived and PointwiseLeftDerived;
  these supply the existing predicates/construction, not the resolving-class theorem.
- `msearch.py ... leansearch "left derived functor computed by resolving class in
  homotopy category"`: unavailable, Internal Server Error; no result asserted.
- `rg` on Mathlib's Algebra/Homology and CategoryTheory trees found and located
  the existing homotopy quasi-isomorphism, pointwise derived and exact functor APIs.
- `rg "lem-pur-left-derived-from-kflat-class|resolving.class|leftDerived.*[Cc]lass|kFlat"`
  in the source `WeilConjectures` and project `lean/Sheaf` found specialized K-flat
  constructions but no full criterion. Read
  `WeilConjectures/CategoryTheory/DerivedCategory/LeftDerivedFunctor/Defs.lean`,
  especially `derives_kFlat`, `leftDerivedFunctor`, and the counit computation lemma:
  they impose monoidal/flat-resolution structure and a specific induced functor,
  so do not express this arbitrary F, P and triangulated-target statement.
- `rg "leftDerived.*resolv|derived.*resolving|left_derived_from_resolving_class|
  lem-pur-left-derived-from-kflat-class"` in `dag/lean_names_upstream.json`, source
  `WeilConjectures`, and project `lean/Sheaf`: no hits.

Validation: the server single-file compile passed cleanly after fully qualifying
`CategoryTheory.IsTriangulated` for the target category to avoid the Functor namespace
name collision. No `#check` lines, local extra declarations, or proofs remain.

Preflight observation: its signature/proof parser stops at the first `:=`, even when
that token belongs to a `letI` inside a theorem type. Replaced that local-instance
expression with the definitionally equivalent explicit-binder lambda above; no script was changed.

## Second reading by F1

Independent reading, 2026-10-11. I opened the sandbox node and module, all three
statement-dependency nodes and their recorded Mathlib declarations. I also read the
bridge node to check the interpretation of pointwise existence. No new definition
nodes, dependency modules, or statement correction are present in this delivery.

Source check: the local Stacks checkout is absent. I fetched and read the primary
`derived.tex` from https://raw.githubusercontent.com/stacks/stacks-project/master/derived.tex,
especially `situation-derived-functor`, `definition-right-derived-functor-defined`,
`lemma-find-existence-computes`, and `proposition-derived-functor`. I checked the
corresponding pages [06XN](https://stacks.math.columbia.edu/tag/06XN),
[05S8](https://stacks.math.columbia.edu/tag/05S8),
[05S9](https://stacks.math.columbia.edu/tag/05S9), and
[05SE](https://stacks.math.columbia.edu/tag/05SE). The inherited hypotheses are
triangulated source and target, exact F, and a saturated multiplicative system
compatible with triangles. In this specialization the source is K(A) and that
system is the quasi-isomorphisms; these properties hold for any abelian A.
The Karoubian assumption in part (8) of 05SE belongs to its additional saturation
conclusion, not the exactness assertion used here, and is correctly absent.

Object, hypothesis, and conclusion checklist, extracted from the node:

1. An arbitrary abelian category A: `(A : Type u) [Category.{v} A] [Abelian A]`.
   Verdict: exact. I read `Abelian` at Basic.lean:112; its finite products, kernels,
   cokernels and normal monos/epis express `def-sp-abelian`, with zero and biproducts
   supplied by its existing instances.
2. K(A), the homotopy category of unbounded cochain complexes:
   `HomotopyCategory A (ComplexShape.up ℤ)`. Verdict: exact. P is a predicate on
   its objects, not on isomorphism classes; no closure condition is introduced.
3. D(A) and the localization Q: `DerivedCategory A` and `DerivedCategory.Qh`.
   Verdict: exact. I read DerivedCategory/Basic.lean:74-177, including Qh's
   localization instance. `[HasDerivedCategory.{w} A]` is the dependency node's
   chosen morphism-universe convention, not enough projectives or a smallness
   hypothesis. `HasDerivedCategory.standard` supplies a choice for every A.
4. A triangulated target D': its Category, Preadditive, HasZeroObject, HasShift,
   additive shifts, Pretriangulated and `CategoryTheory.IsTriangulated` binders.
   Verdict: exact. I read TR1-TR3 in Pretriangulated.lean:65 and the octahedral
   axiom in Triangulated.lean:305; these are the dependency's recorded notions.
5. An exact F from K(A) to D': `(F : ... ⥤ D') [F.CommShift ℤ]
   [F.IsTriangulated]`. Verdict: exact. Functor.lean:186 requires preservation of
   distinguished triangles; its instance at :237 supplies additivity.
6. An arbitrary class P: `P : Set (HomotopyCategory A (ComplexShape.up ℤ))`.
   Verdict: exact; no closure, flatness, boundedness, or finite-generation condition.
7. Every X has a quasi-isomorphism from an object of P: `hres` quantifies X first,
   then existentially binds X' and `s : X' ⟶ X`, followed by membership and quasiIso.
   Verdict: exact, including direction. I read HomotopyCategory.quasiIso in
   Algebra/Homology/Localization.lean:104: isomorphism on homology in every degree.
8. F inverts quasi-isomorphisms between any two P objects: `hinv` quantifies both
   endpoints and s, then assumes both memberships and quasiIso, concluding
   `IsIso (F.map s)`. Verdict: exact; it does not require all arrows to be inverted.
9. Everywhere-defined derivation: `F.HasPointwiseLeftDerivedFunctor quasiIso`.
   Verdict: the node's specified pointwise Kan formulation. I read its definition
   in PointwiseLeftDerived.lean:43-55: existence at every object, not just global
   universality. Stacks essential constancy implies this via the bridge named in
   the node's proof; I do not assume the converse for arbitrary diagrams.
10. A functor LF on D(A) and comparison LF composed with Q to F:
    `∃ (LF : DerivedCategory A ⥤ D') (ε : DerivedCategory.Qh ⋙ LF ⟶ F)`.
    Verdict: exact objects and direction; Lean composition is in application order.
11. Universal among all pairs, without requiring competing G to be exact:
    `LF.IsLeftDerivedFunctor ε quasiIso`. Verdict: exact. LeftDerived.lean:54
    reduces this to `LF.IsRightKanExtension ε`; KanExtension/Basic.lean:77 says
    terminal in RightExtension. This gives the unique compatible map G to LF.
12. That same LF is exact: `∃ (comm : LF.CommShift ℤ),
    (fun (comm : LF.CommShift ℤ) => LF.IsTriangulated) comm`.
    Verdict: exact. The lambda binder installs the existential shift structure
    as the instance used by IsTriangulated; it asserts existence of actual shift
    data and preservation of triangles, without an extra hypothesis on LF.
13. The same comparison computes F on every P object:
    `∀ X : HomotopyCategory A (ComplexShape.up ℤ), X ∈ P → IsIso (ε.app X)`.
    Verdict: exact. Both LF and ε remain the preceding existential witnesses.

Edge cases: zero categories and the zero functor are included. Empty P makes
hres impossible because K(A) has a zero object; no extra nonemptiness assumption
is needed. P need not be replete or stable under shifts/cones. P equal to all
objects gives computation everywhere. All integer degrees, including zero and
negative degrees, occur; there is no boundedness restriction. Empty schemes,
characteristics and n-dependent torsion assumptions are not parameters of this
abstract categorical statement; its applicability imposes none. The five universe
parameters w, v, u, v', u' are explicit and independent, with the localization
universe chosen as in the dependency. No variable or universe is unbound.

Independent searches (different semantic query from the worker):

- `msearch.py F1 lem-pur-left-derived-from-kflat-class leanfinder
  "right Kan extension exists using quasi-isomorphic replacement objects on which
  a triangulated functor inverts weak equivalences"`: eight hits, including Qh's
  exactness, HasLeftDerivedFunctor.hasRightKanExtension, and exact additive
  functors' induced derived functors. None states this resolving-class criterion.
- `msearch.py ... loogle "CategoryTheory.Functor.HasPointwiseLeftDerivedFunctor"`:
  nine hits. The inverts criterion requires inversion on all objects; derivability
  structure results require a supplied localizer morphism and derivability structure.
  Neither is the full theorem for arbitrary P in this delivery. Some service hits
  mention a newer PointwiseLeftDerived derivability module absent from the pinned
  checkout; I checked the available Basic/Derives APIs rather than treating those
  remote hits as available declarations.
- `rg` for `resolving`, `HasPointwiseLeftDerivedFunctor`, and the delivered name
  over project `lean/Sheaf`, upstream `WeilConjectures`, and Mathlib's derivability
  files found no full matching theorem. I read upstream LeftDerivedFunctor/Defs.lean
  (including its binders, derives_kFlat and existence instance): it assumes monoidal
  and flat-resolution structures and treats the induced functor from an additive
  functor of abelian categories, not arbitrary exact F to arbitrary D'.

Mismatch and repair verdict: no mathematical or signature mismatch found. I kept
the correct module and node unchanged, and appended this independent review only.
The header, namespace, imports and source/blueprint docstrings meet the conventions.
The declaration docstring follows all four node proof steps and cites the bridge,
localization, quasi-isomorphism and exactness nodes. There is one named theorem,
one `sorry` proof, no definitions, no hollow data and no additional proved statements.
The node's lean.statement is verbatim the theorem signature before `:=`.

Validation: `scompile.py F1 lem-pur-left-derived-from-kflat-class` on the delivered
module returned exit code 0, compiled in 1.3 seconds, with no warnings or errors.

## Reviewer fix (R-ldk0933, 2026-10-11)

The exactness clause `∃ (comm : LF.CommShift ℤ), (fun (comm : LF.CommShift ℤ) =>
LF.IsTriangulated) comm ∧ ∀ X ...` was replaced by the equivalent, beta-reduced
`(∃ (_ : LF.CommShift ℤ), LF.IsTriangulated) ∧ ∀ X ...`. A probe confirmed that the
existentially bound shift structure is the instance used by `Functor.IsTriangulated`
(the goal after `refine ⟨?c, ?_⟩` mentions `?c`). Mathematics unchanged; recompiled clean.
