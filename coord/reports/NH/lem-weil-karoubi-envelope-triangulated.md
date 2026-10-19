## Worker report

Reuse the existing upstream implementation; no Lean module is written. The main declaration is
`CategoryTheory.Idempotents.Karoubi.isTriangulated` in
`WeilConjectures.CategoryTheory.Idempotents.Triangulated`, line 81. Its public imports expose
all the constructions and the exactness declaration needed for the complete node statement.
The node's `lean.declarations` records those interfaces together. The main signature is copied
verbatim, with its ambient binders described below. The existing proof is preserved, as required
by the one-definition-per-notion rule. Only the node's `lean` field changes.

Clause and hypothesis correspondence:

- “Let T be a triangulated category”: the ambient binders are `{C : Type*} [Category* C]`,
  `[Preadditive C] [HasZeroObject C] [HasShift C ℤ]`,
  `[∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]`, followed by the
  theorem's `[IsTriangulated C]`. These are exactly the recorded Mathlib interpretation of
  `def-weil-triangulated-category`. They impose no hypothesis on `Karoubi C`.
- “The category Kar(T) of def-weil-karoubi-envelope”: this is Mathlib's
  `CategoryTheory.Idempotents.Karoubi C`, not a different category. The objects are `X, p, idem`;
  a morphism satisfies `P.p ≫ f ≫ Q.p = f`; identity has underlying arrow `P.p` and composition
  is inherited. In diagrammatic composition this is exactly the node's `u = d u e`.
- “With the shift (K,e)[1]=(K[1],e[1])”: upstream `Karoubi.hasShift` in
  `WeilConjectures.CategoryTheory.Idempotents.Shift` extends the shift by the canonical
  `functorExtension₂`. The lemmas `Karoubi.shiftFunctor_obj_X`,
  `Karoubi.shiftFunctor_obj_p` and `Karoubi.shiftFunctor_map_f` give these identities by `rfl`
  for every shift index, hence for 1. Coherences are the restricted source coherences.
- “Distinguished triangles ... isomorphic to direct summands, in the category of triangles,
  of images of distinguished triangles of T”: `Karoubi.distinguishedTriangles C` in
  `WeilConjectures.CategoryTheory.Idempotents.Pretriangulated`, lines 217–222, is
  `fun T ↦ ∃ (T' : Triangle C) (_ : T' ∈ distTriang C),
  Nonempty (Retract T ((toKaroubi C).mapTriangle.obj T'))`.
  Thus the retract data are triangle morphisms, not independent objectwise retracts.
  `Retract` has `i ≫ r = 𝟙 T`, precisely the source's section–retraction condition.
  `Karoubi.isomorphic_distinguished` absorbs an arbitrary triangle isomorphism, so omitting
  a redundant outer existential isomorphism neither strengthens nor weakens the class.
  Balmer–Schlichting Definition 1.10 explicitly equates this with being a direct factor.
- “Is an ordinary triangulated category”: `Karoubi.pretriangulated` (lines 331–340) sets
  `distinguishedTriangles := Karoubi.distinguishedTriangles C` and supplies TR1–TR3.
  `Karoubi.mem_distTriang_iff` confirms the exact class by definitional equality.
  The main theorem `Karoubi.isTriangulated` supplies TR4 for this very instance.
- “The canonical functor ... is exact”: the functor is Mathlib's `toKaroubi C`, whose object
  and map formulas are exactly the dependency node's inclusion. Mathlib already makes it
  additive. Upstream `toKaroubi.commShift` in `Idempotents.Shift` uses
  `toKaroubiCommShiftIso`, with underlying identity components. The instance
  `toKaroubi.isTriangulated` in `Idempotents.Pretriangulated`, lines 346–349, sends a source
  distinguished triangle to its own reflexive retract. This is exactly the node's definition
  of an exact functor, with the specified shift identification.
- The parenthetical historical source note introduces no further mathematical hypothesis or
  conclusion. The matched declarations cite the same Balmer–Schlichting Theorem 1.12.

Dependency declarations read and used:

- `def-weil-karoubi-envelope` is a Mathlib leaf: `CategoryTheory.Idempotents.Karoubi` and
  `CategoryTheory.Idempotents.toKaroubi`, in `Mathlib.CategoryTheory.Idempotents.Karoubi`.
  Read the structures, category instance, identity/composition formulas, inclusion,
  full-faithfulness and preadditive/additive instances.
- `def-weil-triangulated-category` is a Mathlib leaf: `CategoryTheory.Pretriangulated` in
  `Mathlib.CategoryTheory.Triangulated.Pretriangulated`, `CategoryTheory.IsTriangulated` in
  `Mathlib.CategoryTheory.Triangulated.Triangulated`, and
  `CategoryTheory.Functor.IsTriangulated` in `Mathlib.CategoryTheory.Triangulated.Functor`.
  Read the full signatures and docstrings, including all ambient structure binders.
- All the proof dependencies are Mathlib leaves too: `fullyFaithfulToKaroubi`,
  `Triangle.yoneda_exact₂`, `Triangle.yoneda_exact₃`, `Triangle.coyoneda_exact₂`,
  `Triangle.coyoneda_exact₁`, `comp_distTriang_mor_zero₁₂`,
  `productTriangle_distinguished`, and the triangle two-out-of-three isomorphism lemmas.
  The existing implementation imports their defining Mathlib interfaces through its public
  imports; no new proof imports or dependency repair modules are necessary.

Source and edge cases:

Read the node, all its proof steps, both statement-dependency records and their exact Mathlib
interfaces. Read Balmer–Schlichting Definitions 1.2 and 1.10 and Theorem 1.12 with its preliminary
lifting lemma (PDF pp. 2–4), and the upstream Shift, Pretriangulated and Triangulated interfaces.
The source's direct-factor condition is explicitly a retract in the triangle category.
The idempotents 0 and 1 are included by the very same Karoubi type and shift formulas. The
zero category and zero triangle are admitted. There are no boundedness, nonzero-object,
field, characteristic, countability or t-structure hypotheses. Independent object and
morphism universes are retained: `Type*` and `Category*` in the existing source are generalized
separately; `Karoubi C` lives in their maximum and does not force them equal. The source's
integer shifts include zero and negative shifts. Exactness does not assert equivalence or
that every distinguished triangle is an image without taking retracts. No statement dispute,
correction, missing dependency, new node, or dependency module was found.

Searches (2026-10-16):

- `msearch.py` LeanFinder: “The Karoubi envelope of a triangulated category is triangulated
  with distinguished triangles the retracts of images and the inclusion is exact”:
  8 hits, all triangulated localization/derived-category interfaces; no Mathlib match.
- `msearch.py` Loogle: `CategoryTheory.Idempotents.Karoubi, CategoryTheory.IsTriangulated`:
  0 hits.
- `msearch.py` LeanSearch: “idempotent completion triangulated category distinguished
  triangles retracts”: 8 hits on the Karoubi definition, idempotent-completeness and generic
  distinguished-triangle structures; no Mathlib theorem matching this node.
- `msearch.py` grep: `Karoubi|Idempotents` in `CategoryTheory/Triangulated`: 0 hits.
- `rg` for `karoubi|Karoubi|lem-weil-karoubi-envelope-triangulated` in the upstream project,
  `lean/Sheaf`, and `dag/lean_names_upstream.json`: the upstream
  `CategoryTheory/Idempotents/Triangulated.lean` explicitly names this blueprint node and
  states `Karoubi.isTriangulated`. Its imported `Pretriangulated.lean` names the same node
  on both the pretriangulation and the exactness instance. Side-library hits concern
  applications or the bounded-t-structure theorem, not a different required construction.
  The upstream-name index had no matching entry; direct source inspection found the match.
- Read the full relevant declarations rather than relying on search result names.
  `scompile.py --source WeilConjectures.CategoryTheory.Idempotents.Triangulated` confirmed
  the current compiler source contains the matching theorem and the public imports.

Validation: the required `deliver2.py --no-push` compiles real `#check` probes for every recorded
existing declaration and runs the server preflight. The dry run printed `OK`: all seven existing declarations compiled and the server
preflight passed except for the independent second reading, which the second reader supplies.
No warning or error was reported; nothing was pushed. A field comparison confirmed that
`lean` is the only changed node field.

## Second reading by NH

Independent reading on 2026-10-16. I opened the sandbox node and compared it with the base
node, its two statement dependencies and their exact Mathlib declarations, the blueprint
source, and the upstream Shift, Pretriangulated and Triangulated modules. There is no repair
note for this item. The sandbox differs from the base only in `lean`; it introduces no
module, dependency module, definition node, or statement correction.

The node's objects, hypothesis and conclusions, in order:

1. An arbitrary triangulated category T. The main declaration's ambient binders are
   `{C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]`,
   `[∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]`, with
   `[IsTriangulated C]` on the theorem. I read Mathlib's `Pretriangulated` fields (TR1--TR3)
   and `IsTriangulated.octahedron_axiom` (arbitrary three distinguished cone triangles).
   These are precisely `def-weil-triangulated-category`, not extra completeness or
   idempotent-splitting assumptions. Binary biproducts follow from pretriangulation.
   Verdict: exact hypothesis match.
2. Its Karoubi envelope. Mathlib's `CategoryTheory.Idempotents.Karoubi C` has fields
   `X`, `p`, `idem : p ≫ p = p`; its `Hom.comm` is `P.p ≫ f ≫ Q.p = f`, its identity
   has underlying map `P.p`, and composition uses the original composition. Translating
   diagrammatic to functional composition gives exactly `u = d u e` in
   `def-weil-karoubi-envelope`. Verdict: same category and no private replacement.
3. The specified shift. `Karoubi.hasShift` is the source shift composed with
   `functorExtension₂ C C`. `Karoubi.shiftFunctor_obj_X`, `shiftFunctor_obj_p` and
   `shiftFunctor_map_f` identify its objects and arrows with `(K[n],e[n])` and `u[n]`.
   The displayed coherence formulas in Shift restrict the original coherence maps by
   the projectors. In particular the specified formula holds at 1. Verdict: exact.
4. The distinguished class consists of triangles isomorphic to direct summands of images
   of distinguished source triangles, with the summand taken in the triangle category.
   `Karoubi.distinguishedTriangles C` says, for each candidate `T`,
   `∃ (T' : Triangle C) (_ : T' ∈ distTriang C),
   Nonempty (Retract T ((toKaroubi C).mapTriangle.obj T'))`.
   Mathlib's `Retract` has triangle maps `i`, `r` and `i ≫ r = 𝟙 T` here, not just
   three unrelated objectwise retractions. `Karoubi.isomorphic_distinguished` transports
   such data along triangle isomorphisms, so an outer isomorphism existential is
   redundant. Verdict: exact class, quantifier order and strength.
5. With those structures the envelope is an ordinary triangulated category.
   `Karoubi.pretriangulated` sets its distinguished class to exactly item 4;
   `Karoubi.mem_distTriang_iff` is `Iff.rfl` for that instance. The recorded
   `Karoubi.isTriangulated [IsTriangulated C] : IsTriangulated (Karoubi C)` supplies TR4
   for that instance. It does not assume any preexisting triangulation of the envelope.
   Verdict: the full conclusion, with the specified structures.
6. The canonical functor is exact. Mathlib's `toKaroubi C` sends `X` to `(X,𝟙 X)`
   and `f` to `f`, as the dependency requires. `toKaroubi.commShift` uses the natural
   isomorphisms `toKaroubiCommShiftIso`, with underlying identity components.
   `toKaroubi.isTriangulated` has type `(toKaroubi C).IsTriangulated`; its
   `map_distinguished` uses the image triangle's reflexive retract. Mathlib's
   `Functor.IsTriangulated` is exactly preservation of distinguished triangles with
   this shift identification, and implies additivity. Verdict: exact inclusion and
   exactness, with no equivalence or essential-surjectivity claim.
7. The source parenthesis is explanatory, not another conclusion. I read the local
   Balmer--Schlichting PDF, Definition 1.2, Definition 1.10 and Theorem 1.12. The source
   assumes only a triangulated category, defines the same shift, and explicitly
   identifies direct factors with section--retraction data in the triangle category.
   I also read Stacks `homology.tex` Section 12.4 (09SF/09SG/09SH/05QV), which concerns
   Karoubianity rather than this triangulation, and `derived.tex`'s triangulated-category
   and exact-functor definitions. No missing standing hypothesis was found.

Edge cases: zero and identity idempotents are admitted without a nonzero condition; the
zero category and zero triangle are covered. An empty category is not a triangulated
category, because a zero object is required. There is no index set, scheme, coefficient
field, characteristic or positivity assumption. The shifts include 0 and negative integers.
The compiled types retain independent morphism and object universes `v` and `u`, and the
envelope has object universe `max u v`, morphism universe `v`. No equality or smallness
hypothesis is added.

Independent H4 searches used different wording from the first worker:

- LeanFinder via `msearch.py`: “idempotent completion of a triangulated category carries a
  triangulation making the canonical inclusion exact”: eight generic localization/derived
  category hits, no replacement Mathlib theorem.
- Loogle via `msearch.py`: `CategoryTheory.Idempotents.toKaroubi,
  CategoryTheory.Functor.IsTriangulated`: zero hits.
- LeanSearch via `msearch.py`: “A triangulated category has a triangulated idempotent
  completion with an exact embedding”: eight Karoubi-definition or idempotent-completeness
  hits, not a triangulation theorem.
- `msearch.py` grep for `Karoubi|idempotent completion` in `CategoryTheory/Triangulated`:
  zero hits. Direct `rg` in all Mathlib, upstream `WeilConjectures` and the project's
  `lean/Sheaf` found the matching declarations in the upstream three modules; project
  uses do not supply a competing definition. I opened their actual signatures and data.

H5/H6/H8/H9: this existing match adds no definitions, theorem proofs, imports, local notation
or new docstrings. The upstream construction has real data; its modules identify this
blueprint node and the Balmer--Schlichting source. I read the pretriangulation construction
and the octahedron theorem's complement/padding argument against the node's proof.
The recorded `lean.statement` is verbatim the theorem signature before `:= by`.
There are no unbound binders. No semantic mismatch or correction was found; I preserved
all seven recorded declarations and the entire node record.

Validation: `scompile.py --source WeilConjectures.CategoryTheory.Idempotents.Triangulated`
confirmed that the current server source has the same theorem and public imports. A scratch
probe compiled through `scompile.py`, checking all seven declarations and using the theorem
and both inclusion instances with explicit independent universes. Its final version has no
warnings or errors. `#print axioms` for both `Karoubi.isTriangulated` and
`toKaroubi.isTriangulated` lists exactly `propext`, `Classical.choice`, `Quot.sound`.
The only delivered change made by this second reading is this independent report section.
`deliver2.py NH lem-weil-karoubi-envelope-triangulated --no-push` then printed
`OK (dry run)`: the delivery passes the server preflight and compiles, with only the node
and report staged. No Lean module is delivered because this is an existing exact match.
