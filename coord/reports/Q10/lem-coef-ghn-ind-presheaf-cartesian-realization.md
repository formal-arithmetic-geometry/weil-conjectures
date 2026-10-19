## Worker report

The module `Sheaf.CategoryTheory.GhnIndPresheafCartesianRealization` states the
relative-cone Ind realization of GHN, Definition 9.1, Propositions 9.12 and 9.16,
and Corollary 9.17. Source read at https://arxiv.org/html/1501.02161v3, especially
the slice-limit explanation in the proof of Proposition 9.16. No mathematical
statement correction is made. The only postponed proof in the new module is
`SSet.Enhanced.GhnInd.ghn_ind_presheaf_cartesian_realization`.

Hypotheses and clauses, in order:

- The smaller universe is `u`; `A E : SSet.{u}` have small simplices, and the
  presheaf and Ind categories have simplices in `u + 1`. Classifying functors
  take values in `CatInfinity.{u + 1}`, whose simplices live in `u + 2`.
  All universes and variables are explicitly bound, with `autoImplicit false`.
- `Quasicategory A` and `Quasicategory E` encode the coherent infinity categories.
  `κ : Cardinal.{u}` and `hκ : κ.IsRegular` encode the infinite regular cardinal;
  Mathlib regularity includes infinitude.
- `F0 : ulift A ⟶ compactRex κ` is the entire coherent functor into small
  categories admitting κ-small colimits and functors preserving those colimits.
  The published `compactRexSubcomplex` imposes those conditions, including the
  empty diagram, on its vertices and enriched mapping simplices.
- `p : E ⟶ A`, `hp : cocartesianFibration p`, and `q0`, `hq0`, `hF0` say p is
  associated to F0. Here `S0` is the published straightening package, `q0` is the
  naturally marked representative of p, `hq0` identifies its entire projection
  with p, and `hF0` identifies its entire straightening with the composite of F0
  and the canonical inclusion. These are the presentation of the word
  “associated”, including all higher simplices, rather than vertexwise tests.
- `R : CompactIndRight.{u, 0} κ` is the supplied coherent right-adjoint Ind
  construction. Its `models` compare every value to the actual `indKappa` and
  Yoneda, and its `extensions` identify every edge with the right adjoint of the
  filtered-colimit-preserving extension. The H in the statement is exactly
  `opFunctor.map (uliftFunctor.map F0) ≫ R.diagram`.
- `relativePresheafCylinder p`, `relativePresheafBase p` and
  `relativePresheafFree p` are the already published actual simplicial pushout,
  base inclusion j and free-endpoint inclusion. They are not defined again.
  `restrict` is the internal-Hom precomposition map for the native presheaf model.
- For clause (i), `cylinder p φ` is precisely the opposite relative-cylinder data
  postcomposed with the entire coherent presheaf. `edgeSquare p φ e` restricts
  its first variable to the opposite of e and retains its interval variable.
  Its four corners are φ(target e), φ(source e), X(p(target e)), X(p(source e)).
  `EdgeCondition` quantifies over every p-cocartesian edge and requires the
  *specified* `SuspensionComparison.SquareCone` of that square to be limiting.
  Both its apex and its coherent path are fixed by the dependency definition.
- For clause (ii), `baseValue p φ a` is X(a). `IsFiberSlice` characterizes the
  canonical functor `(fiber p a)^op ⟶ S_/X(a)` by fixing its entire arrow
  projection to the curried relative-cylinder transformation restricted to that
  fiber. The target is the published `fixedTargetArrows`. The two projections
  determine the map to that pullback; there is no arbitrary functor or choice.
  `FiberCondition` requires this canonical functor to exist and to send every
  κ-small colimiting coherent cocone in the fiber to its actual limiting cone.
  `SendsCoconeToLimit` fixes the apex and gives an equation in every simplicial
  degree for the entire reversed image cylinder. This is exactly the slice
  formulation explicitly included in the node and GHN's proof of 9.16; it avoids
  the nonexistent literal ordinary-join inclusion into the relative pushout.
- `subcategory p κ` is the vertexwise full subcomplex on precisely the conjunction
  of those two conditions. `projection p κ` is its inclusion followed by j*.
  The conclusion first supplies both quasicategory structures and then
  `cartesianFibration` for this particular projection, including inner horns and
  cartesian lifts, rather than assuming fibration existence.
- The conclusion supplies the whole coherent W on P(A)^op.
  `Classifies` identifies the actual opposite projection with a naturally marked
  cocartesian representative and identifies its full straightening, followed by
  `opCat`, with W. Taking opposite total spaces changes each fiber to its opposite,
  so the final Cat-infinity opposite involution is essential. `S` and `hopCat`
  are the existing canonical straightening and opposite interfaces, supplied as
  parameters instead of choosing data from unproved existence theorems.
- `PreservesSmallLimits W` tests every small simplicial shape, including empty,
  using the existing `PreservesLimitsOfShape` predicate, which retains the full
  cone and its legs. The following natural equivalence is W along y^op equals H,
  with every universe lift written explicitly. The final quantified clause says
  any other limit-preserving extension of H is coherently naturally equivalent
  to W, expressing uniqueness of the extension up to equivalence.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `fullSubcomplex`, `coneCategory`,
  `coconeCategory`, `IsLimiting`, `IsColimiting`, `AreNaturallyEquivalent`.
- `Sheaf.CategoryTheory.PresentableInfinityCategory`: `IsKappaSmall`.
- `Sheaf.CategoryTheory.InfinityFibrationsOverSimplicialBases`, reexporting
  `InfinityFibrations`: `cocartesianFibration`, `cartesianFibration`,
  `IsCocartesianEdge`, `fiber`.
- `Sheaf.CategoryTheory.IndKappaPresentability`: `indKappa` and the construction
  underlying the published `CompactIndRight.models`.
- `Sheaf.CategoryTheory.IndRightAdjointCoherent`, publicly reexporting
  `SmallRightAdjointDiagramCompactModel`: `compactRex`, `compactRexSubcomplex`,
  `CompactIndRight`, whose complete signatures and normalization fields were read.
- `Sheaf.CategoryTheory.RelativeConePresheafFibers`: `relativePresheafCylinder`,
  `relativePresheafBase`, `relativePresheafFree`, `relativePresheafInterval`,
  `relativePresheafCylinderDiagram`.
- `Sheaf.CategoryTheory.InfinityPresheafIndCriterion`: `presheafMap`,
  `presheafObject`, `presheafTransformationMap`, `presheafOppositeCoconeMap`;
  it reexports `InfinityPresheafYoneda.infinityPresheaves` and `infinityYoneda`.
- `Sheaf.CategoryTheory.SuspensionSquareComparison`: `square`, `boundary`,
  `SquareCone`, owned also by the landed `def-coef-finite-limits-square-cones`.
- `Sheaf.CategoryTheory.InfinityYonedaPresheafLimits`: its publicly reexported
  `PreservesLimitsOfShape`.
- `Sheaf.CategoryTheory.CocartesianStraightening`: `Statement`, `coCart`, `object`,
  `classify`; it reexports `CatInfinityOppositeInvolution.IsCatInfinityOpposite`.
- The available proof-dependency modules are imported. The DAG proof interfaces
  `lem-coef-relative-functor-cocartesian-classifier` and
  `lem-coef-cartesian-maps-presheaf-extension` have no Lean record on the read base,
  so their imports cannot yet be included. They are proof dependencies only;
  no missing statement notion is replaced or assumed.

Additional statement dependencies are these already landed interfaces used by the
helpers, together with the dependency compilation repair described below. There
are no new nodes and no duplicate definitions of the relative cone, presheaves,
Ind categories, squares, fibrations, slice categories or straightening.

Edge cases checked before writing:

- Empty A permits empty E and no fiber tests; F0 and all extension equations are
  still coherent maps. The base P(empty) has its terminal presheaf.
- For A a point, condition (i) gives the usual family of Ind objects parametrized
  by the space X; the slice in condition (ii) is over that actual X.
- For empty K, κ-smallness is satisfied, and `SendsCoconeToLimit` still fixes
  Q(initial) as the apex of a terminal cone in S_/X(a). Thus the initial-object
  value is equivalent to the identity of X(a), exactly Ψ(c) → X(a) an equivalence.
- Empty X(a) is permitted: the slice is not replaced by an arbitrary space of
  components. Every coherent transformation and its higher simplices remain.
- κ = aleph_0 retains precisely the finite-colimit tests. No uncountability or
  nonempty indexing assumption is added.
- Identity and degenerate edges are included in `EdgeCondition`; arbitrary
  cocartesian edges, not only a selected cleavage, are tested.

Searches for an exact existing statement:

- msearch LeanFinder: “Presheaves on the relative cone of a cocartesian fibration
  satisfying cocartesian pullback and fiber colimit conditions classify the limit
  preserving Ind extension”: eight hits, including ordinary
  `CategoryTheory.Presheaf.uniqueExtensionAlongYoneda` and ordinary strongly
  cocartesian universal properties; no infinity-categorical relative-cone result.
- msearch Loogle: `"Ind", "Cartesian"`: zero hits.
- msearch grep: `relativeCone|relativePresheaf|IndKappa|CatInfinity` in
  Mathlib/CategoryTheory: zero hits.
- msearch LeanSearch: “Presheaves on a relative cone model the Cartesian fibration
  classified by the right adjoint Ind completion and its limit preserving Yoneda
  extension”: eight hits, all ordinary categorical Ind/Yoneda/adjunction results.
- rg on upstream WeilConjectures for the item id and
  `ghn|GhnInd|relativePresheafCylinder|IndRightAdjoint`: no exact declaration.
- rg on side `lean/Sheaf/CategoryTheory` found the relative-cone construction,
  coherent Ind interface and straightening, reused here; no existing realization.

## Dependency modules

`lem-coef-space-valued-straightening`: the first prescribed compile failed in the
published dependency `Sheaf.CategoryTheory.SpaceValuedStraightening` at the
abbreviation `Diagrams`, because it depends on noncomputable `smallSpaces`.
The current source was read using `scompile.py --source` and compared with the
read checkout. This delivery marks that abbreviation `noncomputable` and otherwise
preserves the entire module, declarations, proof plan and node statement. Only its
node's `lean` record changes, with a repair note. The repaired dependency is
compiled separately before the consumer through the wrapper. This is a compiler
annotation repair, with no altered mathematical interface.

`lem-coef-relative-cone-presheaf-fibers`: the next compile exposed the same
missing annotation on its existing `relativePresheaves` abbreviation, which
depends on noncomputable `transportDiagrams`. The delivery marks it
`noncomputable`, preserving all definitions and theorem signatures. The complete
module remains attached to the same node, whose only changed field is `lean`.

Validation: the prescribed scompile wrapper compiled every delivered module
separately, both as sandbox text and under its actual library module name, without
errors or warnings. The new realization module took 2.7 seconds under its library
name; the repaired dependency modules took 6.6 and 3.5 seconds. The first consumer
compile caught the internal-Hom currying order; inserting the canonical product
symmetry makes the normalized fiber arrow map have exactly the required type.

## Second reading by Q10

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Maintainer review fix

The hypothesis presenting p as the cocartesian fibration associated to F0 gave only
`HEq (object q0).obj.hom.val p`. An `HEq` of maps whose types are `X ⟶ A` and `E ⟶ A`
does not identify the represented total space X with E, so the hypothesis did not tie
p to F0, and the theorem could not be used or proved. The statement now also assumes
`hE0 : (CocartesianStraightening.object q0).obj.left.underlying = E`. This is the same
pair of equations the module's own `Classifies` already uses (`underlying = C.op` together
with the `HEq`). It is the missing half of "associated" and does not add any mathematical
assumption. The node's `lean.statement` is read again from the fixed file.
