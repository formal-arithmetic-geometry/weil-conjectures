## What changed

Replaced the sorry in `AlgebraicGeometry.Scheme.Modules.exists_globalTensorPullback_derived_data`
by a K-flat derivability-structure proof, preserving its signature. Added the proof-only
imports `Sheaf.Paper.GlobalTensorPullbackKFlat`,
`Sheaf.Paper.GlobalTensorPullbackTensorDescent`, and upstream `Derives`.
The new tensor module imports `DerivesTwo` and `Whiskering` for its proved generic helper.
Second reading removed its unused `GlobalDerivedHom`, derived-adjunction and
`KFlatPullback` imports, and removed the unused homotopy oplax import from the
new K-flat module.

The new K-flat lemma supplies only preservation of K-flat objects and inversion of
quasi-isomorphisms between them. The item constructs an actual universal left derived
pair using the upstream API. Invertibility on the resolving class proves absoluteness
under every required postcomposition. Two derived tensor bifunctors and their explicit
comparison counits give the tensor isomorphism by uniqueness of left derived
bifunctors in a proved private generic helper. Its specialization to the concrete
module categories is split off as tensor descent. The original item uses that
obligation to supply naturality and the exact displayed normalization. Private, completely
proved helpers keep the chosen Kan-extension functors abstract during elaboration.
No arbitrary object is chosen from a mere unproved existence assertion.

Updated the item DAG proof and its dependencies to this route. The unit
`sk-prop-av-cube` has no realized node attached to this item, and its cube-theorem
statement and route are unchanged.

## Proved and sorry left

Closed one existing hole:
`AlgebraicGeometry.Scheme.Modules.exists_globalTensorPullback_derived_data`
(node `lem-sc-global-tensor-pullback-derived-data`). There is no sorry left in the item.

Added two holes:
`AlgebraicGeometry.Scheme.Modules.globalTensorPullback_kflat`
(node `lem-sc-global-tensor-pullback-kflat`), in
`Sheaf.Paper.GlobalTensorPullbackKFlat`. It is the point-evaluation transport of the
K-flat preservation and quasi-isomorphism preservation argument, with no derived
functor, absoluteness or tensor comparison in its conclusion. This delivery is a
two-hole decomposition, not a net decrease of the hole count: one closed, two added.
`AlgebraicGeometry.Scheme.Modules.globalTensorPullback_tensorDescent`
(node `lem-sc-global-tensor-pullback-tensor-descent`), in
`Sheaf.Paper.GlobalTensorPullbackTensorDescent`, is the second hole. It assumes a
fixed derived pair and comparison invertibility, and supplies only tensor descent.
It does not reassert the original theorem. All private helpers are proved without sorry.

The new statement was checked on the zero ring, zero/acyclic complexes, the empty
scheme, identity maps, and unbounded complexes. Evaluation at a singleton still is
an equivalence over the zero ring, and the K-flat pullback proof uses stalkwise
extension of scalars without a flatness assumption on the global-sections ring map.
A quasi-isomorphism between K-flat complexes is preserved because exact inverse
image precedes change of rings; arbitrary quasi-isomorphisms are not claimed.

## No longer needed

Removed the proof-only import `Sheaf.AlgebraicGeometry.RingedSpaceTensorPullbackAbsolute`.
The item no longer uses node `lem-pc-ringed-space-tensor-pullback-absolute`, its full
ringed-space derived-functor existence/transport theorem, or module
`Sheaf.AlgebraicGeometry.RingedSpaceTensorPullbackAbsoluteAux`. The new lemma uses
only the lower point-evaluation, K-flat pullback, exact inverse-image, identity-ring
comparison and change-of-rings quasi-isomorphism interfaces. In particular no
transport of a prechosen derived functor across a point equivalence is needed.
The former proof-dependency nodes `def-pc-global-derived-rhom` and
`lem-pc-kflat-pullback-preservation` remain needed by the new lemma and/or signatures;
`def-pc-scheme-derived-tensor-structure` remains a proof dependency of the item.
No public import of the item was removed. The new tensor-descent module no longer
imports `Sheaf.AlgebraicGeometry.GlobalDerivedHom`,
`Mathlib.CategoryTheory.Functor.Derived.Adjunction`, or
`Sheaf.Algebra.Homology.KFlatPullback`; the new K-flat module no longer imports
`WeilConjectures.Algebra.Homology.HomotopyCategory.OplaxMonoidal`. These removals
are redundant imports in new modules, not additional pruned dependency nodes.

Source-import traversal finds the following 29 Sheaf modules absent from the new
item import closure. This is item-local pruning, not a claim that no other target
reaches them; global pruning and net progress remain the maintainer ledger's count.

- `Sheaf.Algebra.Homology.DerivedChangeOfRings`
- `Sheaf.Algebra.Homology.QuasiIsoSaturatedTriangulated`
- `Sheaf.AlgebraicGeometry.RingedSpaceTensorPullbackAbsolute`
- `Sheaf.AlgebraicGeometry.RingedSpaceTensorPullbackAbsoluteAux`
- `Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantCofinal`
- `Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantPro`
- `Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantProCriterion`
- `Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantProHomColimit`
- `Sheaf.CategoryTheory.DerivedCategory.LeftDerivedExactOfLocalization`
- `Sheaf.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass`
- `Sheaf.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge`
- `Sheaf.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy`
- `Sheaf.CategoryTheory.DerivedFunctorShift`
- `Sheaf.CategoryTheory.DerivedFunctorThirdValue`
- `Sheaf.CategoryTheory.DerivedFunctorTriangleRetractionHomColimit`
- `Sheaf.CategoryTheory.DerivedFunctorTriangles`
- `Sheaf.CategoryTheory.DerivedFunctorValueTriangle`
- `Sheaf.CategoryTheory.DerivedFunctorValueTriangleCompatibility`
- `Sheaf.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem`
- `Sheaf.CategoryTheory.LeftDerivedExactWhenDefined`
- `Sheaf.CategoryTheory.LeftDerivedKanSourceTriangles`
- `Sheaf.CategoryTheory.LeftDerivedKanTriangleValueComparison`
- `Sheaf.CategoryTheory.LeftDerivedValueMorphism`
- `Sheaf.CategoryTheory.RightKanExtensionCoherentShift`
- `Sheaf.CategoryTheory.ThirdValueConstruction`
- `Sheaf.CategoryTheory.TriangleCommonRefinement`
- `Sheaf.CategoryTheory.TriangleMorphismCategory`
- `Sheaf.CategoryTheory.Triangulated.DenominatorTriangleCompletion`
- `Sheaf.CategoryTheory.TriangulatedHomColimitComparison`

## Where the brief, the DAG or earlier work was wrong

No mathematical error in the existing statement was found. The originally suggested
transport route is unnecessary: the upstream K-flat derivability structure constructs
L directly on the module category, and uniqueness of derived bifunctors proves the
normalized tensor comparison. The exact-monoidal left-derived-functor module cannot
be applied directly because P need not preserve finite limits. Instead only
K-flat inversion and K-flat preservation are required.

Searches through msearch (Lean Finder, Loogle, LeanSearch, grep) and local rg found
supporting upstream derivability and sheaf pullback declarations but no existing
point-evaluation K-flat transport theorem. LeanSearch returned an Internal Server
Error, recorded as unavailable. Read Stacks Tags 06YC, 06YJ and 079U directly, and the
upstream `Derives`, `DerivesTwo`, `LeftDerivedTwo`, `Monoidal.KFlat`, and
`LeftDerivedFunctor.Monoidal` source APIs. The local Stacks source tree is absent.

## New nodes

`lem-sc-global-tensor-pullback-kflat` is the strictly smaller preservation interface
used before constructing L. Its new module has a public theorem with a whole-proof
sorry, source citation and complete proof in words. Its DAG proof specifies point
monoidal evaluation, concrete K-flat pullback, exact module inverse image and change
of rings, with the corresponding existing dependency nodes. No signature/definition
change, change record, or forced adaptation is needed.

`lem-sc-global-tensor-pullback-tensor-descent` splits the tensor-only step after L is
fixed. The generic private descent proof is complete; concrete monoidal-instance
specialization is the remaining glue. Full applications repeatedly exceeded the
60-second file limit, including after explicit instances and reduced transparency.
No wall-clock limit was changed. This remaining step is separated as a true smaller
statement, and no internal proof hole remains in the original item.

All sandbox modules compile: K-flat transport (9.1 s), tensor descent (30.0 s),
and the item (53.6 s). The tensor-descent statement was checked on zero objects,
identity functors and unbounded complexes; its hypotheses supply exactly the
isomorphisms used by the generic argument.

For tensor descent, an additional Lean Finder search returned Tor constructions and
`Localization.Monoidal.functorCoreMonoidalOfComp`; the latter requires monoidal
localization, while Qh is only lax monoidal on arbitrary homotopy objects. Loogle
reported an unknown identifier for `Functor.IsLeftDerivedFunctor`. These searches,
with the earlier grep search, are recorded in the new node.

LeanSearch for tensor descent also returned Internal Server Error; its unavailability
is recorded explicitly, alongside Loogle/LeanFinder and source grep.

## Second reading by D4

1. Compared every delivered source with the repository. The sole existing public
   declaration, `exists_globalTensorPullback_derived_data`, retains its signature
   byte for byte. Its local instances and definitions are unchanged. No target,
   existing definition, or public import of the item changed; no change record is
   required. The two additional modules and their nodes are new. Verdict: pass.

2. Read the existence, computation, postcomposition, and tensor steps, including
   both completely proved generic tensor helpers. The main proof uses the upstream
   universal total left derived functor, rather than arbitrary data from an
   unproved existence assertion. The only direct sorries are the two named public
   theorems listed above, each an entire proof. There are no forbidden declarations
   or hollow definitions. Local compilation and the axiom probe are required by
   the delivery gate. Verdict: pass; source compilation, explicit axiom checks and delivery probes passed.

3. Checked the two new obligations against their docstring proofs, the concrete
   pullback and inverse-image interfaces, and Stacks Tags 06YC, 06YJ and 079U.
   Point evaluation is an exact equivalence commuting with tensors and coproduct
   totalization; its inverse therefore preserves K-flatness. Exact inverse image
   and change of rings between K-flat complexes prove the inversion clause. The
   tensor statement assumes a fixed pair and K-flat invertibility, and only asks
   for tensor descent; the generic helper proves precisely that reduction. Neither
   reasserts derived existence or absoluteness. Zero rings, the empty scheme, zero
   and acyclic complexes, identity functors, and unbounded complexes require no
   extra hypothesis. Independent Lean Finder, Loogle, msearch grep and source rg
   searches found supporting results, no duplicate. The source's exact monoidal
   derived comparison imposes exactness unavailable here; the concrete private
   pullback helper does not transport point evaluation. Verdict: pass.

4. The proof starts with K-flat inversion, constructs the universal pair, derives
   absoluteness by preservation of isomorphisms under postcomposition, then applies
   only tensor descent. Read `sk-prop-av-cube` and its empty realized lists: this
   below-unit reduction changes neither the cube statement nor its prescribed
   step. The removed old proof dependency is the absolute ringed-space pullback
   theorem; global-derived-Hom and K-flat pullback still occur in the signatures
   or the smaller new obligation, and derived tensor remains used. Removed four
   unused imports from the new modules after successful isolated compile checks.
   Verdict: pass.

5. Checked all three node records, their declaration names and statements, sources,
   proof plans, origins, creation/blueprint records and searches. Each proof_deps
   list is exactly the union of uses in its proof steps. The existing node changes
   only proof, proof_deps and proof_origin. New nodes match the two remaining
   obligations and have existing Lean interfaces for every planned dependency.
   Verdict: pass.

Changes by the second reader: restricted transparency for the final tensor-descent
application in the main proof, preserving its term and signature; pruned three
unused imports from tensor descent and
one from K-flat transport; recorded the independent searches; corrected the new
tensor module's author attribution to D4. A bounded attempt at the concrete tensor
specialization did not close the remaining hole within the file limit, so its
whole-proof sorry and complete mathematical argument remain explicit. No signature
or definition was changed. The hole accounting remains one existing hole closed
and two lower holes added, a decomposition with net minus one.

Final source compilation after these changes: K-flat transport 9.5 s, tensor descent
39.6 s, main item 59.4 s, all without errors or warnings.

Explicit `#print axioms` in a scratch module importing the compiled delivery showed
only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` for the main theorem
and each of the two split obligations. The upstream `leftDerived₂NatIso` has only
the three standard axioms. The remaining `sorryAx` is expected from the stated
open obligations; this is not a claim that the item is axiom-free yet.

The second reader ran `deliver3.py D4 Sheaf.Paper.GlobalTensorPullbackDerivedData
--no-push`: OK, compilation and the full preflight passed, with review class CODEX
(new nodes and modules). No proof or signature changes followed that successful
gate; only this report records its result.
