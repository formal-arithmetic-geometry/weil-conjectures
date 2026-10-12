## What changed

Proved both original theorems in
`Sheaf.AlgebraicGeometry.RingedSpaceTensorPullbackAbsoluteAux`, preserving their signatures,
visibility. The second reading replaces the public pointwise-derived import by the smaller
public left-derived API and keeps pointwise construction as a proof-only import. Added
three fully proved private helpers:
K-flatness of canonical inverse image, existence of a derived comparison from a resolving
class without triangulated hypotheses, and absoluteness of a comparison invertible on a
resolving class. No definitions or other modules changed.

The concrete existence proof constructs extension of scalars sectionwise and sheafifies it;
the object/map equations give the natural isomorphism to the supplied functor P. Exact inverse
image and the existing change-of-rings quasi-isomorphism lemma give invariance on K-flat
complexes. The resolving-class essential-constancy theorem and Kan bridge construct the
universal pair and its invertible K-flat comparison.

For absoluteness, construct the derived pair for F followed by any H. Its universal lift from
L followed by H is invertible on K-flat objects by its factorization equation, on all localized
objects by naturality along resolutions, and everywhere by essential surjectivity. This uses
no exactness or additivity assumption on H. The supplied hK already suffices; the stronger hL
and the concrete tensor-pullback formulas are unnecessary for this categorical argument.

Both node copies now describe this proof and its actual dependencies. Local single-file
compilation completed without errors or warnings. No bound on a complex, nonemptiness of a
space, or flatness of the structure morphism was introduced; the argument also covers empty
spaces and zero complexes. The generic helper handles independent source/target universes.

## Proved and sorry left

Closed 2 original holes:

- `AlgebraicGeometry.RingedSpace.exists_tensorPullback_leftDerived`
  (`q3-ringed-space-tensor-pullback-left-derived`).
- `AlgebraicGeometry.RingedSpace.leftDerived_tensorPullback_absolute`
  (`q3-ringed-space-tensor-pullback-absolute-postcomposition`).

No sorry remains in the delivered module. No hole added or split off. Existing imported
lemmas retain their own proof dependencies; this delivery does not claim those are all closed.

## No longer needed

Removed the proof imports `Sheaf.Algebra.Homology.DerivedChangeOfRings` and
`Sheaf.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass`. The former is replaced by
its smaller existing quasi-isomorphism lemma; the latter by the essential-constancy/Kan
argument, omitting triangulated exactness, which neither statement requests.

The following library modules leave this module's transitive import closure. Other target
routes may still need them, so this is not a claim that they leave the whole target closure:

- `Sheaf.Algebra.Homology.DerivedChangeOfRings`: `lem-pur-derived-change-of-rings`
- `Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantCofinal`: `lem-pur-essential-constant-cofinal-0a1s`
- `Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantProCriterion`: `lem-pur-essential-constant-pro-criterion-05py`
- `Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantProHomColimit`: `lem-pc-essentially-constant-pro-hom-colimit`
- `Sheaf.CategoryTheory.DerivedCategory.LeftDerivedExactOfLocalization`: `lem-pur-left-derived-exact-chosen-localization`
- `Sheaf.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass`: `lem-pur-left-derived-from-kflat-class`
- `Sheaf.CategoryTheory.DerivedFunctorInverts`: `lem-pur-derived-functor-inverts-05sb`
- `Sheaf.CategoryTheory.DerivedFunctorShift`: `lem-pur-derived-functor-shift-05su`
- `Sheaf.CategoryTheory.DerivedFunctorTriangles`: `lem-pur-derived-functor-triangles-05sc`
- `Sheaf.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem`: `def-pur-saturated-triangulated-localization`
- `Sheaf.CategoryTheory.LeftDerivedExactWhenDefined`: `lem-pur-left-derived-exact-when-defined`
- `Sheaf.CategoryTheory.LeftDerivedValueMorphism`: `lem-pur-derived-functor-morphisms-05sa`
- `Sheaf.CategoryTheory.RightLocalizationHomColimit`: `lem-pc-right-localization-hom-colimit`
- `Sheaf.CategoryTheory.TriangleCommonRefinement`: `lem-pur-triangle-common-refinement-ms3-05r9`
- `Sheaf.CategoryTheory.TriangleMorphismCategory`: `lem-pur-triangle-morphism-category-05r9`
- `Sheaf.CategoryTheory.Triangulated.DenominatorTriangleCompletion`: `lem-pur-triangle-completion-ms6-05r9`

The absoluteness node no longer needs the existence node as a proof dependency: the K-flat
comparison hypothesis already supplies everything needed. The existence declaration remains
proved and available for its other callers. The public imports supplying `moduleRings` and `tensorPullbackRingMap` remain; the
pointwise construction import is proof-only, with its smaller left-derived API public.

## Where the brief, the DAG or earlier work was wrong

The planned use of `derivedChangeOfRings` is stronger than needed and fixes the two auxiliary
derived-category universes to be the same; constructing its underlying extension functor and
using `changeOfRings_kFlat_quasiIso` avoids that restriction. Likewise the resolving-class
statement requests triangulated-functor instances that are unnecessary for these conclusions.
Its essential-constancy and Kan-bridge dependencies give exactly the needed universal pair.
The old absoluteness plan does not expose a ready-to-apply postcomposition theorem; the
universal-lift/naturality argument above supplies that missing glue in Lean.

Searches were run using leanfinder, loogle and grep through msearch, and rg over the library.
LeanFinder found the generic derived-functor API; Loogle did not recognize the abbreviated
query identifier. The existing exact inverse-image and change-of-rings results were found
in the local library. No new mathematical statements or DAG nodes were needed. The unit's
realized statement and proof steps are untouched.

## Second reading by P3

1. Compared the entire Lean module and both node files with the repository. Both existing
   theorem signatures are byte-for-byte identical; no definition or target changed. The
   only new declarations are three proved private helpers. Both nodes change only `proof`,
   `proof_deps`, and `proof_origin`. Verdict: unchanged statements and data.
2. Compiled the delivered module with `lcompile.py`: no error or warning. A scratch copy
   with `#print axioms` for both public declarations reports only `propext`, `Classical.choice`,
   `Quot.sound`, and imported `sorryAx`; there is no local sorry or forbidden declaration.
   In particular, `E₀` is constructed sectionwise, not selected from an unproved existence
   theorem. `totalLeftDerived` is determined by its Kan universal property. Verdict: genuine
   proofs from the stated dependency interfaces; imported holes are not claimed closed.
3. There are no split-off statements, added holes, or new nodes. Read all three private
   helper proofs. The inverse-image helper transports acyclicity in the correct direction
   along the tensor comparison. The existence helper uses the bridge's identity leg and
   uniqueness of limit cones. The absolute helper uses naturality to invert `F(s)` between
   resolving objects, then the lift equation to invert its comparison, and finally
   resolutions and essential surjectivity to extend invertibility. Its argument uses no
   exactness or additivity of `H`. Empty spaces, zero complexes, and distinct derived-category
   universes introduce no extra hypotheses. Verdict: true reductions, not restatements.
4. Independently searched LeanFinder for absolute derived functors from resolving classes,
   Loogle for the fully qualified `CategoryTheory.Functor.IsLeftDerivedFunctor`, and grep/rg
   for inversion, comparison lifts, and eventual constancy. Read Mathlib's derived-functor
   API and the existing `leftDerived_from_resolvingClass` and `derivedChangeOfRings` proofs.
   The former unnecessarily requires triangulated instances here; the latter ties together
   the derived-category universes. The chosen smaller interfaces avoid both restrictions.
   The report names every removed old proof dependency, including the existence node
   removed from the absoluteness proof. Independently recomputed the project-module import
   closure difference: it is exactly the sixteen modules listed above. The unit record
   `sk-thm-picard-duality` has `realized = {statement: [], steps: [[]]}`; neither reviewed
   auxiliary is a realized unit step, and no unit record or route changed. Verdict: valid
   pruning. Found one visibility fault: `PointwiseLeftDerived` was public although only
   its smaller `LeftDerived` API occurs in the signatures. Repaired it by publicly importing
   `LeftDerived` and privately importing `PointwiseLeftDerived`; `KFlatPullback` remains
   public because it defines the signature's `tensorPullbackRingMap`.
5. Matched each proof step with the declarations in its dependency nodes: canonical exact
   inverse image and its tensor comparison, K-flat pullback preservation, change-of-rings
   quasi-isomorphism preservation, K-flat resolutions, quasi-isomorphism fraction calculus,
   resolving-class essential constancy, the pointwise Kan bridge, and Mathlib assembly.
   The absolute node correctly omits tensor-change-of-rings and the existence theorem:
   its supplied K-flat comparison suffices. The elementary naturality and lift calculations
   are written out in Lean and described in the nodes. Verdict: DAG agrees with Lean.

Changed only import visibility/granularity and this report; retained both correct proofs
and both proof-node records. No statement, definition, hole count, or unit changed.

The first dry run required a change record for the public-import repair. Added
`coord/changes/RingedSpaceTensorPullbackAbsoluteAux-imports.md` with every downstream
module and its holder. The sole direct importer already publicly imports
`PointwiseLeftDerived` itself, so all downstream public environments retain that API;
no forced adaptation or target review is needed. This records the repair explicitly.
