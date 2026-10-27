## Worker report

`Sheaf.CategoryTheory.SheafDgAcyclicHull` states
`CategoryTheory.SheafDg.exists_acyclicHull`, with its only proof `sorry`.
The natural-language item, its eight-step proof plan, and its proof dependencies
are unchanged. The module now imports the landed graded-module definition and
writes the differential-forgetting functor inline using upstream `mapMod`.
No definition node or dependency module is delivered.

Hypothesis and clause correspondence:

- The topological space is `{X : TopCat.{u}}`, and the commutative coefficient
  ring sheaf is `(S : TopCat.Sheaf CommRingCat.{w} X)`.
- The size convention is represented by explicit universes `u w` and
  `[EssentiallySmall.{w} (TopologicalSpace.Opens X)]`, inherited from the
  dg-module dependency. No additional equality of universes is imposed.
- The sheaf dg algebra is `(A : Algebra S)`. Its left dg modules are
  `LeftModule A`, with the recorded signed-shift convention.
- Gr(A) is the landed `GradedLeftModule (underlyingGradedAlgebra A)`:
  `Mod (Graded S)` over the actual algebra obtained by forgetting A's
  differential. Objects have arbitrary integer grading and associative unital
  left action; maps have degree zero and preserve the action.
- F is
  `(HomologicalComplex.forget (ringedSiteModules.{w} (rings S)) (.up ℤ)).mapMod A.X`.
  The landed `forgetComplexMonoidal` instance comes from the induced total
  tensor. Its tensorator is the identity, so `mapMod` retains the actual action,
  all sheaf components and the degree-zero module maps, forgetting the differential.
- The reverse functor is quantified by
  `∃ G : GradedLeftModule (underlyingGradedAlgebra A) ⥤ LeftModule A`.
- `Nonempty (G ⊣ F)` asserts natural Hom bijections in both variables.
  These adjunction data are only existentially asserted, never chosen as a
  definition from a postponed existence proof.
- For every graded module N and every integer n, the vanishing clause is
  `IsZero ((cohomology A n).obj ((q A).obj (G.obj N)))`.
  The dependency's cohomology is the underlying complex homology functor
  descended to the homotopy quotient. Thus it is exactly sheaf cohomology
  vanishing before any quasi-isomorphism localization.
- `G.PreservesMonomorphisms` quantifies over all categorical monomorphisms
  and states that their images are monomorphisms.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.GradedSheafModule` (landed definition node
  `def-sfb-graded-sheaf-module-category`): `CategoryTheory.SheafDg.Graded`,
  `gradedMonoidal`, `GradedAlgebra`, `forgetComplexMonoidal`,
  `underlyingGradedAlgebra`, and `GradedLeftModule`.
- `Sheaf.CategoryTheory.SheafDgModuleLocalization`: `rings`, `Complex`,
  `complexMonoidal`, `Algebra`, `LeftModule`, `q`, `cohomology` in
  `CategoryTheory.SheafDg`. The recorded general-site coefficient category
  `CategoryTheory.ringedSiteModules` is publicly imported from
  `Sheaf.CategoryTheory.RingedSiteModules`, also supplying the proof dependency
  `def-weil-sheaf-of-modules-category`.
- `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod`:
  `CategoryTheory.Functor.mapMod`, whose action is the tensorator followed by
  the image of the original action. This smaller defining module suffices.
- `Mathlib.CategoryTheory.Adjunction.Basic`: `CategoryTheory.Adjunction`.
  `Mathlib.CategoryTheory.Functor.EpiMono`:
  `CategoryTheory.Functor.PreservesMonomorphisms`.

Sources: Stacks sdga.tex, definition-gm including the left-module convention,
0FSK (lemma-dg-hull), 0FSL (lemma-dg-hull-acyclic), and the application in
0FSS. The retained theorem docstring gives all eight proof steps: the explicit
two-coordinate signed action and differential, functoriality, mutually inverse
Hom assignments and naturality, sectionwise kernel=image, and cancellation
proving preservation of monomorphisms.

Edge cases checked: empty X; zero coefficient ring, algebra or graded module;
nonzero algebra differential; positive, zero and negative integer degrees;
characteristic two; unbounded modules. There is no connectivity, boundedness,
nonemptiness, graded commutativity, injectivity or enough-points assumption.
The direct-sum graded tensor and the signed left convention are inherited from
the same landed definitions in every case. No STATEMENT-DISPUTED issue remains.

Searches retained from the original investigation (prescribed msearch.py):

- LeanFinder, "The forgetful functor from sheaf differential graded modules to
  graded modules has a left adjoint with acyclic values and preserves
  monomorphisms": generic free/sheafification adjunctions, no hull theorem.
- Loogle, "GradedObject, Mon, Mod": no hits; short GradedObject identifier
  unrecognized by the index.
- Mathlib grep, "dgHull|dg_hull|GradedModule|gradedForget|forgetDifferential":
  ordinary graded module constructions only.
- LeanSearch, "Category of integer graded sheaves of modules over a graded
  algebra and forgetting a differential": generic graded objects and
  `HomologicalComplex.forget`, which the statement now uses inline.
- Mathlib grep, "mapMod|modObjObj" in CategoryTheory: the mapMod TODO;
  direct rg in WeilConjectures found the implemented upstream functor used here.
- Direct rg in WeilConjectures and Sheaf originally found no hull theorem.
  The repair reread the current DAG and the server source with
  `scompile.py --source Sheaf.CategoryTheory.GradedSheafModule`, locating the
  now-landed shared graded category. The old negative category search is
  superseded by this positive match; no new definition is supplied.

## Repair of H4/H12 (A4)

Return reviewed immutable head `82d3cd1423a0`. The prior packet independently
introduced `def-sfb-sheaf-dg-graded-module` and
`Sheaf.CategoryTheory.SheafDgGradedModule`, colliding with the parallel Q33
packet `e3dbba14550b`. Both the copied node and that Lean module have been
removed from this sandbox's delivery. This is a substantive interface repair,
not an unchanged re-push.

The current main branch resolves the shared notion through Q25's subsequently
landed `def-sfb-graded-sheaf-module-category` and
`Sheaf.CategoryTheory.GradedSheafModule`; the Grothendieck lemma uses that same
interface. Q33's suggested `GradedModule A` and its file are absent from the
current main branch and from the live server source. Accordingly this repair
uses the actual landed `GradedLeftModule (underlyingGradedAlgebra A)` and adds
only its owning definition node to the item's statement dependencies. This
implements the return's instruction to reuse the single shared Gr(A) notion
with the interface that actually landed.

F is inline as requested, using the existing `forgetComplexMonoidal` and
`mapMod`. No replacement `forgetDifferential` is introduced and no landed
definition module is overwritten. The node copy was refreshed from current
main before applying only the item's lean record and added definition dependency;
its lean.statement is the signature verbatim, and its date is the current UTC
date. The theorem's hypothesis and conclusion correspondence above is unchanged
mathematically. The return's positive mathematical checks still apply.

Validation: scompile.py compiled the repaired file with exit code 0 and no
warnings or errors. deliver2.py --no-push then passed server preflight and
compilation (dry-run commit 61f54d31637). The staged packet contains exactly
the item module, its node file and this report; no definition node or dependency
module is staged. The delivery command repeats these checks before pushing.

## Second reading by Q36

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
