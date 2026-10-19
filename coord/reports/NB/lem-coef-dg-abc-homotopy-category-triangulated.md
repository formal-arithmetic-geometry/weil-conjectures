## Worker report

The module `Sheaf.CategoryTheory.DgAbcHomotopyCategoryTriangulated` imports
`Sheaf.CategoryTheory.DgAbcData` and states the item
as `CategoryTheory.IntegralDGCategory.ABC.abc_homotopy_category_triangulated`.
The sole postponed theorem is that declaration. All supporting definitions have
real data and equations. No definition chooses data from an existence theorem.

I read Stacks `dga.tex`, section-review through Situation ABC (Tag 09QJ), the
boundary construction in lemma-get-triangle (Tag 09P6), the triangle comparisons
(09QU), and proposition-ABC-homotopy-category-triangulated (09QY). The node's
statement is unchanged. Its additional statement dependency is the new definition node
`def-coef-dg-abc-data`. That definition cites the already landed
`lem-coef-dg-semi-free-homotopically-projective`, which owns the existing
`IntegralDGCategory` definition used here. The full dependency closure was checked
for a return path to this item; none exists. No independent notion is duplicated.

The precise correspondence, hypothesis by hypothesis and clause by clause, is:

* Small integral cochain dg category: `A : IntegralDGCategory.{u, v}` from
  `Sheaf.CategoryTheory.SemiFreeDGModule`, declaration
  `CategoryTheory.IntegralDGCategory`. Its fields are the object type, actual
  `CochainComplex AddCommGrpCat ℤ` Hom objects, additive-in-both-factors composition,
  closed units, identity laws, associativity, and the signed Leibniz rule. Object
  and morphism universes remain independent. The definition and its docstring
  were read in full; the semi-free theorem is not used as an assumption.
* Closed degree-zero maps (`Z⁰` arrows): `Closed A x y` is exactly the kernel
  subgroup of the differential `(A.hom x y).d 0 1`. This uses the existing Hom
  complex, with its inherited group operations, and introduces no replacement
  differential or enrichment. Only this arrow type is needed to quantify over
  `Z⁰`; a separate category instance on cycles is unnecessary for the signature.
* Axiom (A), `hA : AxiomA A`: its first conjunct asserts a dg zero object, whose
  Hom groups in both directions vanish in every integer degree. Its second
  conjunct gives `Nonempty (Biproduct A x z)` for every pair of objects. `Biproduct`
  contains the four closed degree-zero maps and all five biproduct identities.
* Axiom (B), `S : Shifts A`: `obj` and the chain maps `map` specify each dg functor;
  `map_unit` and `map_comp` are the dg functor laws. `obj_zero`, `map_zero`,
  `obj_add`, and `map_add` impose the strict identity and addition laws on objects
  and every homogeneous arrow. `homShift` is the actual cochain-complex
  isomorphism `A.hom x (obj n y) ≅ (A.hom x y)⟦n⟧`. The imported Mathlib cochain
  shift has degree-j term `X (j+n)` and differential `n.negOnePow • d`, as read in
  `HomotopyCategory/Shift.lean`. `homShift_precomp` and `homShift_postcomp` spell
  out compatibility with composition, including the `(-1)^(n*p)` sign for a
  shifted homogeneous arrow of degree p. `HEq` only transports the canonically
  equal integer degrees and strictly equal shifted objects.
* Admissible sequences: `Admissible A x y z` contains closed `a` and `b`, graded
  degree-zero `π` and `s`, and exactly `π_a`, `b_s`, `a_π_s_b`, `b_a`, `π_s`,
  in the composition order of the node. There is no closedness assumption on
  the two splitting maps. `boundary E` is the literal degree-one `π d(s)`.
* Axiom (C), `hC`: for every pair and every closed f, it supplies a `Cone S f`.
  This has the object c(f), the admissible sequence `y → c(f) → x[1]`, and
  `boundary_eq` equating `π d(s)` with the shifted f under `homShift`. This is
  equality in the Hom complex, rather than merely equality of cohomology classes.
* The H⁰ category and its induced translations: the conclusion is a
  `TriangulatedRealization A S` on the literal type `A.Obj`. Its `classMap` is
  additive and surjective; `class_eq` says exactly that two closed arrows have
  the same class iff their difference is d(h) for some degree-minus-one h.
  Thus its Hom groups are precisely the quotients defining H⁰, not an arbitrary
  category with the same objects. `class_identity` and `class_comp` normalize
  composition. `shift_obj` and `shift_map` fix the shifts to be those induced by
  S on objects and all closed representatives. The existential packaging supplies
  the category operations rather than assuming any triangulated structure.
* Triangulated category in the recorded sense: the result includes Mathlib's
  `Pretriangulated` (TR1--TR3) and `IsTriangulated` (TR4), with `Preadditive`,
  `HasZeroObject`, `HasShift ℤ`, and additive shift functors.
* Distinguished triangles from admissible sequences: `admissible_iff` is an iff
  with an isomorphism to `Triangle.mk [a] [b] [δ]`, with δ a closed degree-zero
  representative whose shifted-Hom image is exactly `boundary E`. It quantifies
  over all splittings, so the description includes boundary independence.
* Precisely the cone triangles: `cone_iff` is a second iff, quantifying over every
  closed representative f and every `Cone S f`, and requiring an isomorphism to
  `(x, y, c(f), [f], [i], -[p])`. The negative projection is explicit.

The recorded triangulated-category dependency is Mathlib:
`CategoryTheory.Pretriangulated` in
`Mathlib.CategoryTheory.Triangulated.Pretriangulated`, with
`CategoryTheory.IsTriangulated` in
`Mathlib.CategoryTheory.Triangulated.Triangulated`. Both signatures and docstrings
were read, including the octahedral field and `IsTriangulated.mk'`. The other three
proof-dependency nodes currently have no Lean record; there is no corresponding
module to import. Their roles, and the octahedron criterion's role, are explained
step by step in the main theorem's proof docstring. The module contains the
complete ten-step natural-language proof plan from the item.

Edge cases: the empty object type cannot satisfy (A), because (A) supplies a zero
object, exactly as in the source. The one-object zero dg category is allowed.
No boundedness, projectivity, cofibrancy, nonzero-object or characteristic
assumption is introduced. Shifts and Hom degrees range over all integers, including
zero and negative degrees. The zero closed map and all its admissible cone choices
are included in (C) and in `cone_iff`. A degenerate splitting with zero object
summands obeys the same five equations. Independent object and Hom universes are
explicit, and `autoImplicit` is disabled.

Searches actually run with `msearch.py`:

* `leanfinder`, query `abstract dg category satisfying axioms A B C homotopy category
  triangulated`: eight hits, including `HomotopyCategory.instIsTriangulatedIntUp`
  and `instPretriangulatedIntUp`; these are for ordinary complexes in a fixed
  preadditive category and do not state the arbitrary-dg-category ABC theorem.
* `loogle`, query `CategoryTheory.IsTriangulated, CategoryTheory.Pretriangulated`:
  twelve hits, including the generic classes and `IsTriangulated.mk'`; these
  provide the target interface and axiom criterion, not this theorem.
* `grep`, query `IntegralDGCategory|ABCData|situation.?ABC`, subdirectory
  `CategoryTheory`: no Mathlib hit.
* `leansearch`, query `differential graded category admissible sequence cone
  triangulated category`: eight hits, the generic triangulated interfaces and
  ordinary derived/homotopy-category instances; no exact ABC theorem.

Additional `rg` searches across Mathlib, `WeilConjectures`, and `lean/Sheaf` found
no existing ABC triangulation theorem. A DAG-wide scan for statements mentioning
small dg categories located the published `IntegralDGCategory` definition and
other enrichments; this delivery reuses the integral one. The upstream node-id
`grep -rn` found no existing declaration. A search for the new namespace's names
found no existing declarations. The upstream name index had no match for 09QJ/09QY.

Validation: both delivered modules are compiled separately, in dependency order,
with the prescribed `scompile.py`. The files contain concrete equations for every
assumption and both triangle classes. No warnings remain.

## New nodes

`def-coef-dg-abc-data` defines the shared ABC interface: degree-zero cycles,
strict dg shifts with signed Hom identifications, admissible splittings, dg
biproducts, axiom (A), the actual boundary element, cone data satisfying (C),
and normalized triangulated H⁰ realizations. Its source is Stacks `dga.tex`,
section-review and Tags 09QJ, 09P6, 09QU, 09QY. This is a definition of the
interface, with no theorem asserting existence; the only existence assertion is
the item theorem. Its own module is `Sheaf.CategoryTheory.DgAbcData`, and all eight
supporting declarations are recorded in `lean.declarations`. No definition has
postponed data or proof. The item cites this node; it does not repeat its notions.

Before creating it, `blueprint_refs.py search 'dg category'` and
`search 'axioms A B C'` found zero blueprint nodes. The broader `admissible`
search found geometric admissibility notions, not this definition. DAG-wide and
chapter searches found only the ABC theorem statements recalling this terminology,
not a definition node. `blueprint_refs.py ancestor` confirmed the inherited
ancestor `prop-coef-integral-exceptional-adjoint`. The new node keeps that ancestry
and the item's unit and chapter.

The new node records the actual complete outputs of all three `msearch.py`
searches: LeanSearch `small differential graded category admissible sequence graded
splitting shifts cone axioms ABC`, LeanFinder `differential graded category
admissible sequence graded splitting shifts cone axioms ABC`, and grep
`structure.*(Admissible|Shifts)|situation.?ABC|IntegralDGCategory` in CategoryTheory.
The first two found ordinary-complex split triangles, differential objects and
generic triangulated interfaces; the grep's sole hit concerns opposite shifts.
None supplies the abstract dg ABC definitions. Searches of the project and source
found the existing `IntegralDGCategory`, which is reused, and no ABC definitions.

## Second reading by NB

No independent second reader was started: the dispatcher brief prohibits starting
other agents, and the maintainer performs the independent delivery review. My own
semantic reread checked both modules and the new definition node against the source:
the five splitting identities, exact cone-boundary equality, quotient equality
relation, induced translations, both directions of both triangle descriptions,
the minus sign on p, and the independent universe binders. This is an author's
self-check, not a claim of independent review.
