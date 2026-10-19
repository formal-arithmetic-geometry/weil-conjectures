## Worker report

Recorded an exact existing statement; no Lean module or proof is added.
The declaration is `AlgebraicGeometry.ProEtale.constructibleCocone_essSurjObj` in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit`, line 622 of the
current server source obtained with `scompile.py --source`. The blueprint source is
`literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/` followed by
`sk-thm-sfb-qlbar-two-colimit/lem-sfb-constructible-cocone-obj.md`, order 1772. Its Lean
frontmatter names this very declaration. No repair note exists for this item.

The signature, verbatim from the keyword to the assignment, is:

```lean
theorem constructibleCocone_essSurjObj : (constructibleCocone X ℓ).EssSurjObj
```

The explicit surrounding context is `universe u`, `(X : Scheme.{u}) (ℓ : ℕ)` with
`[Fact ℓ.Prime]` and `[TopologicalSpace.NoetherianSpace X]`. Every hypothesis and clause
matches as follows:

- A prime ℓ is `(ℓ : ℕ) [Fact ℓ.Prime]`.
- A scheme X is `(X : Scheme.{u})`, for arbitrary universe u.
- The underlying space is Noetherian: `[TopologicalSpace.NoetherianSpace X]`.
- The specified constructible cocone is exactly `constructibleCocone X ℓ`, already
  recorded on `def-sfb-constructible-cocone`; its Φ is `constructibleToPadicAlgCl X ℓ E`.
- Every K in D_cons(X,Qbar_l) is the universal quantifier in `EssSurjObj`, whose vertex
  here is `PadicAlgClConstructible X ℓ`. This abbreviation is the full subcategory
  `BoundedConstructible (padicAlgClRingObj X ℓ)` of the ambient module derived category.
- A finite extension E inside Qbar_l is the existential index
  `E : PadicAlgCl.FiniteIntermediateField ℓ` in `EssSurjObj`; it is an intermediate
  field finite-dimensional over Q_l, not an arbitrary field supplied as extra data.
- K_E in D_cons(X,E) is the existential object `x : PadicSubfieldConstructible X ℓ E`,
  namely `BoundedConstructible (padicSubfieldRingObj X ℓ E)`.
- The desired isomorphism is `Nonempty ((c.Φ E).obj x ≅ K)` with
  `c = constructibleCocone X ℓ`. This is scalar extension to Qbar_l; an isomorphism in
  the opposite displayed orientation in the informal sentence is equivalent by symmetry.

Dependency declarations read, including their docstrings and full signatures:

- `def-sfb-constructible-cocone`: module
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit`, declaration
  `AlgebraicGeometry.ProEtale.constructibleCocone`. It uses precisely the finite-subfield
  categories, scalar-extension functors and transitivity isomorphisms in the node.
- `sk-def-sfb-filtered-two-colimit`: module
  `WeilConjectures.CategoryTheory.FilteredTwoColimit`, declaration
  `CategoryTheory.CategoryCocone.IsFilteredTwoColimit`. Its `essSurjObj` field has type
  `c.EssSurjObj`; the latter is defined as
  `∀ d : D, ∃ (i : I) (x : C i), Nonempty ((c.Φ i).obj x ≅ d)`.

Also checked the abbreviations `PadicSubfieldConstructible`, `PadicAlgClConstructible`,
`constructibleToPadicAlgCl` and `constructibleCocone` in the first dependency module,
and `boundedConstructible` and `BoundedConstructible` in
`WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory`.
They use bounded cohomology and stratified locally finitely presented module objects,
with no derived completeness condition. This matches the proof's coefficient convention.
The general arbitrary-coefficient Serre-closure correction does not add a hypothesis to
this concrete finite-field theorem: those closure results are proof inputs upstream.

Edge cases checked by reading the definitions and the existing proof: the empty scheme
is permitted (no nonemptiness hypothesis); zero/acyclic complexes are included by bounded
constructibility and the triangulated-image/Postnikov argument; ℓ=2 is permitted; ℓ=0,1
are excluded exactly by primality. The finite intermediate-field index includes the base
field and is nonempty, so the existential conclusion has no empty-index defect. No fixed
cohomological interval, positive rank, integral model or completeness hypothesis is added.

The existing proof follows the six node steps: the same coefficient categories and
extension maps are used; an ambient cocone is formed, its image is triangulated using
Hom-surjectivity, constructible sheaves descend by `exists_constructible_finiteCoefficient_model`,
and `DerivedCategory.prop_of_bounded` performs finite Postnikov induction. The final
`fullyFaithfulι.preimageIso` returns the ambient isomorphism to the required full subcategory.
No assertion of proof closure or of removal of upstream sorries is made by this binding.

Searches made on 2026-10-19:

- msearch LeanFinder: “Every bounded constructible pro-etale complex over Q_l algebraic
  closure descends to a finite coefficient subextension”. Eight hits, starting with
  `Algebra.Etale.exists_subalgebra_fg`; none states this pro-etale derived descent.
- msearch LeanSearch: “Every bounded constructible pro-etale complex over the algebraic
  closure of Q_l descends to a finite subextension”. Eight hits about ordinary étale
  algebra descent and étale morphisms; none is this statement.
- msearch Loogle: `CategoryTheory.CategoryCocone.EssSurjObj,
  AlgebraicGeometry.ProEtale.constructibleCocone_essSurjObj`. Zero hits; the external
  index reports the project identifier unknown.
- msearch Mathlib grep: `constructibleCocone|EssSurjObj|finite.*coefficient.*descent`.
  Zero hits.
- rg on `lean/WeilConjectures` and `lean/Sheaf`, query
  `constructibleCocone|EssSurjObj`: found the exact theorem at TwoColimit.lean:622,
  the cocone at :310, the predicate at FilteredTwoColimit.lean:77, and an existing
  consumer in `Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp`.
- rg for `lem-sfb-constructible-cocone-obj` in `lean/WeilConjectures`: no ID-tag match.
  Searching by declaration and reading the source nevertheless found the exact match.
- Read the current server module through `scompile.py --source`; this resolved the
  initially stale local source view. No duplicate definition or theorem was created.

Validation attempted: the delivery wrapper checks the existing declaration with a server
`#check` probe before maintainer preflight. The first dry run timed out in both the primary
compile and server confirmation (60 seconds each). A fresh dry run failed at import with:

```text
import Sheaf.AlgebraicGeometry.EtaleCohomologyFilteredColimit failed, environment already
contains AlgebraicGeometry.Scheme.etaleModuleCohomology_isColimit_of_isFiltered
from WeilConjectures.AlgebraicGeometry.EtaleCohomologyFilteredColimit
```

The generated probe imports only the required upstream TwoColimit module. Neither duplicate
module is a direct import chosen by this delivery. A local read-only import-graph analysis
found both branches inside its existing closure: one goes through
`Sheaf.AlgebraicGeometry.FiniteTypeDirectImageConstructibility` and upstream Gabber, the other
through `Sheaf.AlgebraicGeometry.ComparisonDirectImage`, affine comparison vanishing, and
`Sheaf.AlgebraicGeometry.EtaleLimitCohomologyDegreeZeroDescent`. Both originate in
`Sheaf.Paper.CondensedSheafExtContinuity`. Fixing those published imports requires edits
outside this worker sandbox and its node-binding packet. A smaller import cannot expose
the exact existing theorem: its owning module is TwoColimit. Creating a duplicate statement
or cocone would violate one-definition-per-notion. Nothing was pushed; preflight was not
reached. The separate import-only diagnostic through scompile.py confirmed the identical duplicate
declaration error at line 1, before any statement or #check command; server confirmation
took 57.5 seconds. The diagnostic contains only the upstream TwoColimit import and lives
under scratch/, outside the delivery module paths. No delivered .lean files need compilation.
Only the item's `lean` field changes; no new nodes, dependency repairs or statement
corrections are needed. No statement dispute was found.

## Second reading by NQ

No second worker was started: the dispatched brief requires direct delivery and reserves
independent review for the maintainer. A final self-check reread the node and source:
prime, arbitrary scheme universe, Noetherian underlying space, every vertex object,
one finite coefficient subfield, a bounded constructible source object, and isomorphism
under the specified scalar-extension functor all match. The statement is the Obj field,
not the stronger full two-colimit theorem. No mismatch or source modification was needed.

## Resumed validation, 2026-10-19

Rechecked the retained binding against the live source returned by
`scompile.py --source WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit`,
the two dependency node records and declaration signatures, and the current blueprint
item. The existing theorem still states the item exactly; no replacement declaration
or dependency-interface repair is warranted. No repair-note file exists for this item.

Ran the required dry run again. Its retained output is `scratch/dry-run-resume.log`:
the server rejected the upstream-module import in 7.4 seconds with the same duplicate
`AlgebraicGeometry.Scheme.etaleModuleCohomology_isColimit_of_isFiltered` declaration.
An independent import-only `scompile.py NQ lem-sfb-constructible-cocone-obj
scratch/ImportOnly.lean` reproduced the collision in 3.4 seconds; its output is
`scratch/import-only-resume.log`. The probe contains only the required upstream
TwoColimit import. Read-only searches confirm that both published filtered-colimit
modules declare the name at line 154. The item theorem is declared only in TwoColimit;
other matches are consumers, so a smaller import cannot expose it.

Finally invoked the prescribed delivery wrapper without `--no-push`. After the provider
interruption, inspected its retained output before considering any repeat: the output in
`scratch/deliver-final-resume.log` explicitly says `COMPILE FAILED on the server, nothing
pushed`, with the same import collision. No delivery process remained running. No push
was repeated. The failure precedes preflight and checking the existing declaration.

The packet has no Lean modules whose imports can be narrowed. Repair would require
changing already-published modules outside the only writable sandbox and outside this
item's permitted node/module packet. Those sources and launcher tools were left untouched.
The retained binding and report are ready for rerunning the wrappers after that published
import closure is repaired.

## Latest interrupted-turn recovery, 2026-10-19

Inspected all saved wrapper logs before repeating any delivery operation. The prior final
delivery explicitly ended with `COMPILE FAILED on the server, nothing pushed`; no delivery
or compilation process was still running. Started the required fresh dry run, with output
saved as `scratch/dry-run-current.log`. It exited 1 after 33.0 seconds, again before preflight:
the sole existing-declaration probe cannot import TwoColimit because importing
`Sheaf.AlgebraicGeometry.EtaleCohomologyFilteredColimit` encounters the declaration
`AlgebraicGeometry.Scheme.etaleModuleCohomology_isColimit_of_isFiltered` already loaded from
`WeilConjectures.AlgebraicGeometry.EtaleCohomologyFilteredColimit`.

Fetched the current server TwoColimit source successfully using the prescribed
`scompile.py --source` command; the retained diagnostic source is
`scratch/TwoColimit-current-source.txt`. Its line 622 still has exactly the recorded theorem
and its explicit context remains the prime and Noetherian hypotheses matched above.
Fresh searches of both live Lean trees find that theorem declaration only in TwoColimit,
and find the conflicting cohomology declaration at line 154 of both published modules.
Thus changing the probe to a smaller import cannot expose the existing theorem. There is
no delivery module with imports to narrow. A duplicate theorem or private cocone is not an
authorized repair; resolving the collision requires a published-library import repair,
outside the writable sandbox. No launcher script, published module, or live node was edited.
Compared the sandbox node to the refreshed shared node: the only changed field is `lean`.
No push was repeated after this failed dry run.
