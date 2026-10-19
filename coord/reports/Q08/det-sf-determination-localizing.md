## Worker report

The module `Sheaf.CategoryTheory.Triangulated.LocalizingIsoLocus` states
`CategoryTheory.NatTrans.isoLocus_localizing`, with its entire proof `by sorry`.
It states the full claim of `det-sf-determination-localizing`: the isomorphism
locus is triangulated, closed under arbitrary small coproducts and direct
summands, and contains the localizing closure of any class on which the
transformation is invertible. The node's statement, statement dependencies,
proof and proof dependencies are unchanged. No new nodes or definitions are
introduced, and no other DAG node is stated in the delivery.

The source was read in full at
`literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-lem-sf-determination/det-sf-determination-localizing.md`,
along with the unit's `_section.md`. The current delivery base has statement dependencies
`def-weil-triangulated-category`, `def-weil-triangulated-subcategory` and
`def-weil-pbc-category-colimit`, all Mathlib leaves. Their statements,
recorded interfaces, source signatures and docstrings were read. No repair
note exists for this item.

Hypotheses and clauses, in order:

- The triangulated categories T and T' are `C : Type u₁` and `D : Type u₂`,
  with independently bound category universes `v₁`, `v₂`, zero objects,
  preadditive structures, integer shifts with additive shift functors,
  `Pretriangulated` structures and `IsTriangulated` (the octahedron axiom).
  These are Mathlib's full triangulated-category data, rather than an
  assumption of a merely pretriangulated category.
- Arbitrary direct sums are `[HasCoproducts.{w} C]` and
  `[HasCoproducts.{w} D]`. The index universe `w` is independent of the
  object and morphism universes, and is used consistently for existence,
  preservation and subcategory closure. There is no countability or
  nonempty-index restriction.
- The arbitrary class S is `S : ObjectProperty C`, with no smallness or
  nonemptiness assumption. Object properties define full subcategories by
  `ObjectProperty.FullSubcategory`.
- The two exact functors are `F₁ F₂ : C ⥤ D`, each with `CommShift ℤ` and
  `Functor.IsTriangulated`. The shift structures give their specified
  coherent shift isomorphisms; `IsTriangulated` says distinguished triangles
  are preserved. Additivity follows from Mathlib's existing exact-functor
  instance; no extra additivity hypothesis is imposed on the functors.
- Preservation of arbitrary direct sums is the pair of binders
  `[∀ I : Type w, PreservesColimitsOfShape (Discrete I) F₁]` and its `F₂`
  analogue. These require exactly discrete colimits, not all colimits.
- The natural transformation is `η : F₁ ⟶ F₂`, and
  `[NatTrans.CommShift η ℤ]` is precisely compatibility with the two given
  functor shift structures.
- C_eta is the EXISTING upstream property `η.isoLocus`, whose full definition
  is `fun X ↦ IsIso (η.app X)`. There is no second isomorphism-locus definition.
- Triangulated closure is the first conjunct `η.isoLocus.IsTriangulated`.
  This includes zero, all integer shifts and distinguished-triangle closure.
- Closure under arbitrary direct sums is
  `∀ I : Type w, Nonempty (η.isoLocus.IsClosedUnderColimitsOfShape (Discrete I))`.
  `IsClosedUnderColimitsOfShape` is Mathlib's closure structure, and
  `Nonempty` expresses existence of that structure as a propositional
  conjunct. This quantifies over all coproduct presentations, so closure
  under isomorphic coproduct objects is included.
- Direct summands are expressed by `Nonempty η.isoLocus.IsStableUnderRetracts`.
  A direct summand is a retract; conversely a retraction in a triangulated
  category has a complement obtained from its distinguished triangle.
  Thus this is the usual direct-summand closure in this setting.
- The antecedent of the final conjunct, `S ≤ η.isoLocus`, says exactly that
  every generator is in C_eta. Its conclusion compares the defining
  intersection
  `sInf {P : ObjectProperty C | S ≤ P ∧ P.IsTriangulated ∧
    ∀ I : Type w, Nonempty (P.IsClosedUnderColimitsOfShape (Discrete I))}`
  with `η.isoLocus`. This is Loc(S) spelled out, using Mathlib's existing
  lattice and closure notions. In particular, singleton coproduct cocones
  imply that every such P is closed under isomorphisms; no repleteness
  condition is lost by Mathlib's non-replete `IsTriangulated` convention.
  Intersections preserve these closure properties, and the class of
  candidates contains top, so this intersection is exactly the smallest
  full triangulated coproduct-closed subcategory described by the node.
- The parenthetical source `Loc(S) → T'` is also covered: take `C` to be
  that triangulated category with its inherited coproducts, and take S to
  be its class of generators as objects of C. The same conclusion applies
  inside that source, whose localizing closure of those generators is top.
  No ambient extension of the two functors is assumed. The statement is
  category-general and does not replace its source by a derived category.

Definitions and declarations reused (full signatures and docstrings read):

- `WeilConjectures.Mathlib.CategoryTheory.Triangulated.Generators`:
  `CategoryTheory.NatTrans.isoLocus`, and its existing isomorphism, retract,
  shift and triangulated closure instances. The same module's
  `isIso_app_of_retract` and `isIso_app_shift_iff` support the proof plan.
- `Mathlib.CategoryTheory.Triangulated.Subcategory`:
  `CategoryTheory.ObjectProperty.IsTriangulated` and its inherited
  full-subcategory structures, supplied transitively by the public import.
- `Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape`:
  `ObjectProperty.ColimitOfShape`, `ObjectProperty.colimitsOfShape`,
  `ObjectProperty.IsClosedUnderColimitsOfShape`.
- `Mathlib.CategoryTheory.ObjectProperty.Retract`:
  `ObjectProperty.IsStableUnderRetracts`, imported through the upstream
  module, for direct-summand closure.
- `Mathlib.CategoryTheory.Limits.Shapes.Products`: `HasCoproducts`, and
  `Mathlib.CategoryTheory.Limits.Preserves.Basic`:
  `PreservesColimitsOfShape` (discrete shapes only).
- `Mathlib.CategoryTheory.Shift.CommShift`: `Functor.CommShift` and
  `NatTrans.CommShift`; `Mathlib.CategoryTheory.Triangulated.Functor`:
  `Functor.IsTriangulated`.

The statement-dependency declarations are reused directly:
`def-weil-triangulated-category` has Mathlib match
`CategoryTheory.Pretriangulated`, with `IsTriangulated` and
`Functor.IsTriangulated` in its match description;
`def-weil-triangulated-subcategory` has Mathlib match
`CategoryTheory.ObjectProperty.IsTriangulated`;
`def-weil-pbc-category-colimit` records
`Mathlib.CategoryTheory.Limits.HasLimits` and `CategoryTheory.Limits.colimit`,
with `Cocone`, `IsColimit` and `colimit.desc`. The corresponding colimit
notions occur through `HasCoproducts`, `PreservesColimitsOfShape` and
`ObjectProperty.IsClosedUnderColimitsOfShape`. The colimit module is also
publicly imported explicitly. None of these Mathlib leaves needs a private
replacement definition.

The sole non-elementary proof input on the current base is
`lem-sf-triangle-two-out-of-three`, whose recorded module is
`WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor` and whose three
`NatTrans.isIso_app_obj...` variants are available through the public upstream
Generators import. The current proof computes retract inverses directly and
uses ambient minimality in both domain cases. There is no downstream
constructible-specialization import or generating-class counterexample import.

Edge cases checked mathematically before drafting:

- Empty S: the localizing closure still contains zero. No `S.Nonempty` binder
  is imposed; the final implication uses the same intersection for empty S.
- Empty coproduct: the two exact functors preserve zero; the empty family is
  included among `I : Type w`. There is no nonempty-index assumption.
- Arbitrary singleton coproduct presentations: any object isomorphic to a
  summand is a colimit of that singleton diagram, giving exactly repleteness
  in the candidate subcategories and locus.
- Zero objects and zero generators: components between zero objects are
  automatically invertible, and the definition includes them.
- Positive, zero and negative shifts: the integer CommShift structures and
  compatibility apply to every integer; there is no one-sided shift closure.
- Retracts without global idempotent completeness: the conclusion concerns
  actual retracts, and does not ask for all idempotents to split.
- Distinct object, morphism and coproduct-index universes remain independent;
  source and target categories are not constrained to have equal universes.
- Functors defined only on the localizing source need no extension to the
  ambient category, since the category parameter can be that full subcategory.

Searches for an existing statement:

- `msearch.py leanfinder`: `The objects where a natural transformation between exact coproduct preserving triangulated functors is an isomorphism form a localizing subcategory` — 8 hits: CategoryTheory.Functor.essImageDistTriang_mem_of_iso, CategoryTheory.Functor.isHomological_of_localization, CategoryTheory.Functor.distTriang_iff, CategoryTheory.Triangulated.Localization.pretriangulated, CategoryTheory.Functor.map_distinguished_exact, CategoryTheory.Functor.complete_distinguished_essImageDistTriang_morphism, CategoryTheory.Triangulated.Localization.isTriangulated, CategoryTheory.Triangulated.Localization.instIsTriangulatedLocalization'.
- `msearch.py loogle`: `CategoryTheory.Triangulated, CategoryTheory.ObjectProperty.IsTriangulated, NatTrans.CommShift` — loogle: unknown identifier 'CategoryTheory.Triangulated'; 0 hits: .
- `msearch.py grep`: `localizing|Localizing|isoLocus|IsoLocus` in `CategoryTheory` — 6 hits: Mathlib/CategoryTheory/Triangulated/LocalizingSubcategory.lean, Mathlib/CategoryTheory/Triangulated/LocalizingSubcategory.lean, Mathlib/CategoryTheory/Triangulated/LocalizingSubcategory.lean, Mathlib/CategoryTheory/Triangulated/LocalizingSubcategory.lean, Mathlib/CategoryTheory/Triangulated/LocalizingSubcategory.lean, Mathlib/CategoryTheory/Sites/Over.lean.
- `msearch.py loogle`: `CategoryTheory.NatTrans.CommShift` — 12 hits: CategoryTheory.NatTrans.CommShift.id, CategoryTheory.NatTrans.CommShift.isoRefl_hom, CategoryTheory.NatTrans.CommShift, CategoryTheory.Functor.CommShift.ofIso_compatibility, CategoryTheory.NatTrans.CommShift.of_core, CategoryTheory.NatTrans.CommShift.leftUnitor, CategoryTheory.NatTrans.CommShift.rightUnitor, CategoryTheory.NatTrans.CommShift.of_iso_inv.
- `msearch.py leansearch`: `Isomorphism locus of natural transformation of triangulated functors is closed under shifts cones retracts and coproducts` — 8 hits: CategoryTheory.Functor.isTriangulated_of_iso, CategoryTheory.Functor.isTriangulated_iff_of_iso, CategoryTheory.ObjectProperty.instIsTriangulatedClosed₃OfIsTriangulated, CategoryTheory.ObjectProperty.instIsStableUnderShiftByIsoClosure, CategoryTheory.ObjectProperty.instIsClosedUnderIsomorphismsShift, CategoryTheory.Functor.ShiftSequence.induced.isoZero, CategoryTheory.Functor.IsHomological.of_iso, CategoryTheory.ObjectProperty.instIsStableUnderShiftIsoClosure.

- Local `rg` over Mathlib CategoryTheory, upstream `WeilConjectures`, and
  project `lean/Sheaf`, for `localizing`, `Localizing`, `isoLocus`,
  `IsTriangulated`, `isIso_app` and combinations: found the upstream
  `NatTrans.isoLocus` and its closure instances, which are reused. The
  existing upstream thick-envelope theorem has no arbitrary coproduct
  closure or localizing-closure conclusion and is not the whole target.
  Mathlib's `IsVerdierLeftLocalizing` and `IsVerdierRightLocalizing` concern
  Verdier localizations, not the localizing hull under arbitrary sums.
- Project search found `ShiftSaturatedIsoLocus` and
  `PerfectLocalizingIsoLocus`: the former uses a different all-shifts
  predicate without shift compatibility; the latter is specific to perfect
  complexes on schemes. Both files were read and neither is this statement.
- DAG search for localizing closure found `sk-def-localizing-closure` and
  `det-def-localizing-closure-existence`, whose statements concern specific
  pro-etale module-object derived categories. No declaration of either is
  used or recreated here: this category-general statement uses only the
  explicit defining intersection and existing Mathlib closure operations.
- `rg` for `det-sf-determination-localizing` in upstream `WeilConjectures`
  found no declaration. The proposed declaration name
  `CategoryTheory.NatTrans.isoLocus_localizing` was checked in Mathlib,
  upstream, the project's Lean files and `dag/lean_names_upstream.json`:
  no collision.

Validation: `scompile.py Q08 det-sf-determination-localizing` compiled the
final single delivered file cleanly with the authorized local overlay, both
as a sandbox and as its library module (34.3 s and 19.9 s). No errors or
warnings were emitted. The delivery dry run also checks its compilation
and the refreshed node record against current server preflight rules. The file has no auto-bound variables, local instances or
notation; its only new declaration is the named theorem with proof `sorry`.
The full source proof appears in its declaration docstring. There are no
statement corrections and no STATEMENT-DISPUTED findings.

The first dry run detected a stale shared-checkout DAG record: it was still
`imported` with no statement dependencies, while the fetched delivery base
already contained the reviewed stage-1 split. Read the current node and all
three Mathlib leaf records from the wrapper's read-only delivery-base
checkout; recopied that node intact with only `lean` added. Its mathematical
statement is identical. Preserved its current dependencies, proof, proof
dependencies and other fields; removed the superseded generating-class
proof import, and updated the proof docstring to all six current proof steps.
This is a base refresh, not a statement correction.

## Second reading by Q08

I independently read the sandbox node, module and worker report against the
blueprint statement and its unit, and read Stacks `derived.tex`, Section 13.3
(Tags 0145, 014V and 05QM, including the full-subcategory criterion), and
`categories.tex`, Tag 002F. The source introduces no base ring, field,
Noetherian, finiteness or idempotent-completeness hypothesis. The shared local
node is an older imported record with no dependencies; the sandbox preserves
the reviewed six-step split on the worker's refreshed delivery base. Its
mathematical statement agrees verbatim with the blueprint. There is no repair
note, statement correction, new node or dependency module to review.

Object, hypothesis and conclusion checklist (each verdict: matches):

1. Ambient triangulated categories T and T': `{C : Type u₁} {D : Type u₂}`,
   `[Category.{v₁} C]`, `[Category.{v₂} D]`, and for each category
   `HasZeroObject`, `HasShift ... ℤ`, `Preadditive`, additive shift functors,
   `Pretriangulated`, and `IsTriangulated`. I opened the recorded
   `def-weil-triangulated-category` Mathlib match: these are precisely its
   data and TR1--TR4. Binary biproducts follow from pretriangulation; there is
   no missing additive-category requirement or stronger ambient assumption.
2. Arbitrary small direct sums in both categories: `[HasCoproducts.{w} C]`
   and `[HasCoproducts.{w} D]`, with the same arbitrary index universe `w`.
3. An arbitrary class S: `(S : ObjectProperty C)`. It is a predicate on all
   objects, not a small type enumerating a restricted class.
4. The smallest full triangulated coproduct-closed subcategory Loc(S):
   `sInf {P : ObjectProperty C | S ≤ P ∧ P.IsTriangulated ∧
   ∀ I : Type w, Nonempty (P.IsClosedUnderColimitsOfShape (Discrete I))}`.
   I read `ObjectProperty.IsTriangulated` and `IsClosedUnderColimitsOfShape`:
   the former includes zero, every integer shift and extension closure up
   to isomorphism; the latter concerns all colimit presentations. Singleton
   coproduct presentations force repleteness of every candidate P. Thus the
   intersection has the actual closure properties (not merely closure up to
   a possibly absent representative), contains S, and is the desired least
   subcategory. Top is a candidate. No extra retract-closure condition has
   been inserted into this defining intersection.
5. Exact functors: `(F₁ F₂ : C ⥤ D)` with their `CommShift ℤ` structures and
   `IsTriangulated` instances. I read the Mathlib definitions and the
   additivity instance: exactness includes the specified shift maps and
   preservation of distinguished triangles, and implies additivity.
6. Preservation of direct sums: the two instances
   `∀ I : Type w, PreservesColimitsOfShape (Discrete I) F₁` and its F₂
   counterpart. They require precisely coproduct preservation.
7. The natural transformation and its compatibility: `(η : F₁ ⟶ F₂)` and
   `[NatTrans.CommShift η ℤ]`. I checked `shift_app_comm`: in degree one its
   equation is exactly the source's commutative square. Coherence extends
   this condition from degree one to every integer; this is not an extra
   restriction on transformations of exact functors.
8. The full isomorphism locus: `η.isoLocus`, whose upstream definition I
   opened, is `fun X ↦ IsIso (η.app X)`. Full subcategories are Mathlib's
   `ObjectProperty.FullSubcategory`, not a different category of morphisms.
9. Triangulatedness of that locus: the first conjunct
   `η.isoLocus.IsTriangulated`, using the recorded
   `def-weil-triangulated-subcategory` interface. Its inherited triangles and
   octahedral structure are supplied by the existing subcategory API.
10. Closure under arbitrary direct sums: the second conjunct quantifies over
    every `I : Type w` and asserts
    `Nonempty (η.isoLocus.IsClosedUnderColimitsOfShape (Discrete I))`.
    `Nonempty` is propositionally equivalent to the underlying closure
    class (which is itself Prop); it changes no mathematical assertion.
11. Closure under direct summands: `Nonempty η.isoLocus.IsStableUnderRetracts`.
    I read the retract interface and the upstream locus instance. Actual
    retracts in a triangulated category have complements via a split
    distinguished triangle; hence this expresses the source's summands
    assertion without requiring global splitting of all idempotents.
12. The consequence: `S ≤ η.isoLocus → ... ≤ η.isoLocus` has exactly the
    source's antecedent, order of quantifiers, and localizing containment.
13. Alternative domain Loc(S): the category parameter C may itself be this
    full subcategory, with inherited shifts, triangles and coproducts.
    Its generator class is S viewed in that domain. To check the final
    conclusion against the ambient formulation, pull any internal replete
    triangulated coproduct-closed class back to an ambient object predicate
    by taking its essential image under inclusion. Fullness and the inherited
    structures make that predicate an ambient candidate containing S.
    Ambient minimality therefore makes the internal closure of S all of C.
    The final conjunct then gives invertibility throughout Loc(S). This
    covers functors defined only there, without an ambient extension.

Dependency signatures were opened, not inferred from their names:
`Pretriangulated`/`IsTriangulated`, `ObjectProperty.IsTriangulated`, and the
chosen-colimit/cocone/universal-property interface of
`def-weil-pbc-category-colimit`. I also read the entire upstream
`Triangulated.Generators` and `Triangulated.Functor` modules. The latter's
three `NatTrans.isIso_app_obj...` variants give exactly the recorded proof
input `lem-sf-triangle-two-out-of-three`, with no extra hypothesis. The
former supplies the reused locus and its existing shift, triangulated,
isomorphism and retract instances. None needs repair under §1(B).

Edge cases: empty S is allowed; the intersection then still includes the
zero objects. Empty coproducts are included, since there is no `Nonempty I`
assumption. The zero category and zero generators are covered. The shift
parameter includes zero, positive and negative integers. All five universes
are explicitly bound and independent; no category-size equality or bounded
size of S is imposed. The index universe is the same in existence,
preservation, and closure. Schemes, characteristics and coefficient rings
play no role in this category-general statement. The restricted-domain
argument also applies to empty S. No edge case is excluded.

Independent searches used different phrases from the first worker:

- `msearch.py leanfinder`, "A shift compatible natural transformation of exact
  functors preserving arbitrary coproducts is invertible on the smallest
  coproduct closed triangulated subcategory generated by a class": eight
  hits about image triangles, exactness and localization, no full match.
- `msearch.py loogle`, `CategoryTheory.ObjectProperty.IsClosedUnderColimitsOfShape`:
  twelve hits; confirmed the existing generic closure predicate and its
  interface, not a theorem asserting this entire node.
- `msearch.py leansearch`, "The class of objects on which a natural
  transformation is invertible is closed under coproducts preserved by both
  functors": eight sum/comparison hits, no full match.
- `msearch.py grep`, `isIso_app_coconePt|isoLocus|isIso.*colimit` in
  CategoryTheory: found `isIso_app_coconePt_of_preservesColimit`. I opened its
  signature: it gives the coproduct step as a special case but says nothing
  about triangles or the localizing closure, so it is not this node.
- Direct `rg` in Mathlib, upstream WeilConjectures, and project `lean/Sheaf`
  for `isoLocus`, `isomorphism locus`, `isIso_app.*(coproduct|localiz)` and
  `locali[sz]ing.*(closure|subcategor)` found the upstream locus API. I read
  the alternative `ShiftSaturatedIsoLocus` and `PerfectLocalizingIsoLocus`
  statements: they respectively use an all-shifts predicate without
  compatibility, and a scheme-specific perfect generating class. Neither
  is the full abstract statement here. Mathlib's `LocalizingSubcategory`
  defines Verdier factorization conditions, not arbitrary-sum closure.
  The proposed full name is absent from the upstream name index and sources.

No mathematical or Lean mismatch was found; no existing correct code was
rewritten. The only change of this second reading is this independent report.
The theorem's docstring follows all six node proof steps, including explicit
coproduct and retract inverses and both domain cases; source and blueprint
markers are present. There is one named theorem, its entire proof is `sorry`,
and no new definition, hidden data, local notation or private declaration.
The node's `lean.statement` was checked programmatically equal verbatim to
the file signature; all variables and universes were also checked by eye.

Second-reader validation: the prescribed `scompile.py` command compiled the
single delivered file both in the sandbox and as its library module, with no
errors or warnings (14.8 s and 14.9 s). The 100-character line-width check
passes. Delivery preflight and its fresh compile are run below through the
prescribed `deliver2.py` wrapper.
