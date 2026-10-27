## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceProperSupportBoundedCoherentImage` states
`AlgebraicGeometry.AlgebraicSpace.derivedDirectImage_bounded_coherent_of_proper_support`,
with one `sorry` and no new definitions. Source read: Stacks spaces-perfect.tex,
Tag 08GK, lemma-direct-image-coherent, together with 0CZC and 0CZI for proper support.
The current blueprint unit sk-thm-sf-ctf-stability was also read: this is a supporting
structure-sheaf theorem, not a change to that unit's coefficient statement.

Hypothesis and clause correspondence:

- The universe convention is `universe u w`, `S : Scheme.{u}`, and independent chosen
  localization size `HasDerivedCategory.{w}` on the two existing SmallModules categories.
  The small-model restriction equivalence identifies these with all modules on the
  original small etale ringed sites. No site/coefficient universe equality is added.
- `X Y : AlgebraicSpace S` and `f : X ⟶ Y` are the given algebraic spaces and map.
- `hf : MapIsLocally (@LocallyOfFiniteType) f` is local finite type on every compatible
  pair of etale scheme charts. There is no quasi-compactness or properness binder on f.
- Noetherian Y is the conjunction of `hYln` (locally Noetherian on every etale chart),
  `hYqc : CompactSpace (Point Y.obj.obj)`, and `hYqs` (each fibre product of a pair of
  affine scheme maps into Y is quasi-compact). The last condition is absolute
  quasi-separatedness, independent of the base S.
- `E : X.DerivedModules` is in the ambient unbounded derived category, not D(QCoh).
  Every occurrence of H^i(E) uses `DerivedCategory.homologyFunctor X.SmallModules i`.
  `X.smallModuleEquivalence.inverse.obj` returns that cohomology to the original modules.
- `hcoh` asserts for each integer i that this module is `IsQuasicoherent` and its
  Zariski restriction on every affine etale scheme chart has `Module.Finite` global
  sections. Local finite type over locally Noetherian Y makes X locally Noetherian;
  consequently these are precisely the Noetherian affine charts of the statement.
  A quasi-coherent module on such an affine is the tilde of these sections, so this
  renders exactly the statement's finite-module definition of coherence.
- `hbounded : ∃ a b : ℤ, ∀ i, i < a ∨ b < i → IsZero (...)` is cohomological
  vanishing outside a finite interval. No preselected interval is imposed.
- `hsupport` is degreewise existence of a representable closed immersion `j : Z ⟶ X`,
  `IsReduced Z`, equality `pointImage j.hom.hom = moduleSupport H^i(E)`, and
  `MapIsProper (j ≫ f)`. A reduced closed subspace with exactly that image is precisely
  the reduced induced closed structure on the support; hence no arbitrary containing
  carrier or annihilator structure replaces the support. Closedness follows already
  from coherent finite type support on locally Noetherian X. `MapIsProper` unfolds to
  separatedness, finite type and universal closedness, exactly as the node specifies.
- The conclusion repeats those same coherence clauses on Y for the canonical
  `(derivedDirectImage f).obj E`, and the same existential boundedness clause.
  `derivedDirectImage` is the existing right derived functor computed by K-injectives.
  No tensor or pullback operation appears in the theorem, so the standing K-flat
  convention requires no extra binder or construction.

Dependency declarations used (full source signatures and docstrings read):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`, its
  `EtaleSite`, `etaleForget`, `Modules`, `IsRepresentableWith` and regular-function sheaf.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, a
  transparent abbreviation for Mathlib `SheafOfModules` on the arbitrary ringed site.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic` and `.HomologySequence`:
  `HasDerivedCategory`, `DerivedCategory`, `DerivedCategory.homologyFunctor`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh` uses the same
  Mathlib `SheafOfModules.IsQuasicoherent` predicate used in hcoh and the conclusion.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`: `ModuleDirectImageModel`,
  `moduleDirectImage` and its adjoint normalization. The derived calculus conjugates
  exactly this direct image by the small-model equivalences.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules`: `DerivedModules`,
  `smallModuleDirectImage`, `derivedDirectImage`; its small-model dependency supplies
  `SmallModules` and `smallModuleEquivalence`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsLocally`,
  `MapIsProper`, with `LocallyOfFiniteType` from Mathlib.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleSupport`: `moduleSupport` is the
  nonzero geometric-germ support, retaining all refinements rather than a chosen stalk.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `Point`, `pointImage`, and
  `pointTopologicalSpace` provide the support equality and quasi-compactness tests.
- `Sheaf.AlgebraicGeometry.ReducedAlgebraicSpace`: `IsReduced` tests all etale charts.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction`: `schemeRestriction` is
  the canonical Zariski-open restriction retaining the actual sections and scalars.
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`; and
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.

The last six relevant landed definition nodes were added to stmt_deps. No dependency
record was repaired and no node statement, proof, or proof_deps changed. Every already
recorded proof-dependency module is imported without `public`; Mathlib leaves use their
recorded modules. Unstated proof dependencies remain only in the complete six-step proof
docstring, ready for stage 3. No cycle is introduced by the imported proof modules.

Edge cases checked before writing and again after compilation:

- E=0 and zero cohomology in any degree: the empty reduced closed subspace is the
  support witness and is proper. An arbitrary interval, such as [0,0], is allowed.
- Empty X or Y: all cohomology is zero, and all chart/point conditions have their usual
  vacuous or empty interpretation. No nonemptiness assumption occurs.
- A single shifted coherent sheaf: the interval may consist of any one integer,
  including negative degrees. All degrees are integers throughout.
- f=id: the support hypothesis restricts the input as the node does, and the canonical
  derived identity has the required cohomology. No extra conclusion is asserted.
- Non-quasi-compact f: there is no binder requiring quasi-compactness; the proof uses
  finite bounds only on each proper cohomology carrier.
- An arbitrary, possibly non-quasi-separated base S: the pairs-of-affine-charts hYqs
  condition is absolute. An initial relative-diagonal expression was replaced during
  self-review before delivery; both the original and final module compiled cleanly.
- Positive characteristic and arbitrary module/cohomology shifts remain unrestricted.

Searches made with msearch.py and direct source searches:

- LeanFinder: "Derived direct image of a bounded coherent complex with proper
  cohomology supports along a locally finite type algebraic space morphism to a
  Noetherian target is bounded coherent". Eight hits concerned scheme local finite
  type or standard derived t-structure facts; no match to this algebraic-space theorem.
- LeanSearch: "A locally finite type morphism to a Noetherian algebraic space sends
  bounded coherent complexes with proper cohomology supports to bounded coherent
  complexes". Eight scheme finite-type/properness hits; no match.
- Loogle: `"AlgebraicGeometry", "coherent"`. Seven tilde and quasi-coherence
  declarations, none this theorem.
- Mathlib grep via msearch.py: `directImage.*coherent|pushforward.*coherent|AlgebraicSpace`
  under AlgebraicGeometry. One result, Modules/Tilde.lean, about underived affine
  quasi-coherent pushforward; no algebraic-space derived coherent-image theorem.
- rg of lean/WeilConjectures and lean/Sheaf for bounded/coherent, derivedDirectImage,
  properSupport, moduleSupport, and the exact item id/declaration name. Existing
  DirectImageBoundedCoherent and NoetherianProperBoundedCoherentImage results concern
  schemes, not algebraic spaces. The algebraic-space search located and reused all
  the canonical definitions listed above. The new full theorem name had no match.

No STATEMENT-DISPUTED flag or source correction is needed. The final module compiled
through scompile.py in both sandbox and library modes, with no errors or warnings.
The prescribed deliver2.py preflight and compilation are the final validation gate.

## Second reading by Q08

No independent second worker was started: the dispatch brief prohibits other agents
and assigns independent review to the maintainer. The clause-by-clause checks above
are the author's self-review, not a claimed independent reading.
