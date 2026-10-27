## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceModuleFlatChartTest` states
`AlgebraicGeometry.AlgebraicSpace.module_flat_iff_chart_stalk` with a single `sorry`.
No definitions, auxiliary assertions, or proofs are added. The statement is unchanged.

Clause-by-clause rendering:

- The base scheme is `{S : Scheme.{u}}` and the algebraic space is
  `(X : AlgebraicSpace S)`. An S-scheme target is `(T : Over S)`, retaining its
  structure map, and the given S-morphism is `(f : X ⟶ schemeSpace T)`.
- The module is `(M : X.Modules) [M.IsQuasicoherent]`, the recorded Mathlib
  local-presentation predicate used by `QCoh`. The full-subcategory wrapper is
  unnecessary for a theorem about a given module.
- Any representable etale scheme map p is `(U : X.EtaleSite)`; its stored property
  is `IsEtale U.obj.hom`, which includes representability. Its independent
  surjectivity hypothesis is `(_hU : IsSurjective U.obj.hom)`, the scheme-test
  surjectivity predicate, not an unspecified set-theoretic surrogate.
- The corresponding Zariski module F is `(X.schemeRestriction U).obj M`.
  This is actual precomposition on open subschemes with the canonical ring map.
  On a quasi-coherent module it is precisely the inverse Zariski/etale comparison
  of p^*M: etale pullback is restriction on the localized small etale site, and
  the inverse comparison is restriction to opens. Thus neither an arbitrary F
  nor an arbitrary comparison is quantified. The tensor pullback construction
  and Zariski/etale comparison modules are imported publicly.
- Every geometric point in the fixed section universe is quantified as
  `(Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)` and
  `(x : yoneda.obj (Over.mk s) ⟶ X.obj.obj)`. The image geometric point is
  `x ≫ f.hom.hom`. This includes every S-geometric point, including all choices
  of algebraically closed field of that size; no independent smaller universe
  makes the quantifier vacuous.
- The target geometric local ring is `stalkRing s (x ≫ f.hom.hom)`. The module
  geometric stalk is `(stalkModel s x).modules.obj M`. These are the recorded
  colimits of actual sections on pointed affine etale neighbourhoods in the
  fixed small basis. The affine basis gives the same stalk as all pointed
  etale scheme neighbourhoods. Its module action on germs is part of StalkModel.
  The canonical induced scalar map is `stalkMap f s x`, characterized by
  pullback of regular-function germs. `ModuleCat.restrictScalars` explicitly
  uses this map before asking `Module.Flat` over the target ring.
- The equivalence is Lean `↔`. Its right side quantifies `∀ u : X.etaleForget.obj U`.
  The ordinary map fp is `(yoneda.preimage (U.obj.hom ≫ f.hom.hom)).left`.
  Its value at u is t, and `T.left.presheaf.stalk (...)` is O_(T,t).
  `RingedSpace.moduleStalkFunctor ... u` applied to F gives the ordinary stalk F_u.
  Restriction of scalars along the ordinary `stalkMap u` gives exactly the
  action O_(T,t) → O_(U,u) → End(F_u).
- No finite presentation, separation, Noetherian, nonempty, or flatness hypothesis
  on f or M appears. Every U satisfying the given atlas condition is quantified
  as an argument. `Module.Flat` is module flatness; `RingHom.Flat` is only the
  special case of the same predicate for a ring regarded as a module.

Recorded dependencies read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `EtaleSite`,
  `etaleForget`, `Modules`, `IsEtale`, `IsSurjective`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh` and the
  instances making the underlying `SheafOfModules.IsQuasicoherent` available.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`:
  `moduleTensorPullback`, specified as the left adjoint to the normalized
  compatible-chart direct image.
- `Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence`:
  `scheme_zariski_etale_quasiCoherent_equivalence`, its
  `ZariskiEtaleModuleContext.restriction`, and its restriction-to-opens formula.
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic`:
  `Scheme.Modules.IsFlatOver`. Its documented equivalent stalk criterion is
  expanded explicitly in the right side, as the node requests.
- `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat` and its underlying `Module.Flat`.
- Additional already-landed nodes are added to stmt_deps to record the actual
  interfaces used: `def-trf-scheme-algebraic-space` (`schemeSpace`, module
  `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`),
  `def-trf-space-module-scheme-restriction` (`schemeRestriction`, module
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction`),
  `def-sfb-space-geometric-stalk-models` (`SingleComplex.stalkModel`, `stalkRing`,
  `stalkMap`, module `Sheaf.AlgebraicGeometry.AlgebraicSpaceGeometricStalkModels`),
  and `def-pc-module-stalk-functor` (`RingedSpace.moduleStalkFunctor`, module
  `WeilConjectures.Algebra.Homology.ModuleStalkFunctor`). Their source signatures
  and docstrings and their node statements and lean records were read.
- The size-convention node is metatheoretic; it has no declaration to import.
  Its fixed universe convention is rendered by the explicit universe u.

The already-stated proof dependencies are plain imports: SpaceStrictLocalFlatness,
StrictHenselizationFaithfullyFlat, FlatnessFaithfullyFlatExtension,
StrictHenselizationModuleFlatness, and AlgebraicClosure. The geometric-point
IsAlgClosed API is also exposed by the statement imports. The two remaining proof
nodes `lem-sfb-space-quasicoherent-geometric-stalk-tensor` and
`lem-sfb-etale-geometric-point-specified-lift` have no recorded declaration in the
read clone and are not required to state this theorem; no guessed import is added.
The complete four-step node proof is included in the theorem docstring.

Edge cases checked before writing: empty U forces X empty by the same scheme-test
surjectivity, so both universal conditions are vacuous; the zero module is flat
on both sides; identity atlas on a scheme reduces to strict-henselization
flatness descent; a nonflat module remains permitted and can make both sides
false. The scalar maps are canonical even if f is nonflat. Neither the ring nor
module quantifiers exclude positive characteristic or zero stalk modules.
Source read: literature/stacks-project/spaces-morphisms.tex, lemma-flat-at-point
(Tag 05VU), statement and complete proof, lines 6114–6180. Its proof uses any
chosen compatible charts, permitting the fixed arbitrary atlas and identity
scheme target chart here. No statement fault or dispute was found.

Searches made (2026-10-24):

- msearch.py leanfinder: “Relative flatness of a quasi coherent module on an
  algebraic space is detected on any surjective etale atlas by geometric stalks”.
  Eight hits, chiefly `AlgebraicGeometry.Flat.iff_flat_stalkMap`, `of_stalkMap`,
  `stalkMap`, `flat_iff`; these concern flat scheme morphisms, not an arbitrary
  quasi-coherent module over an algebraic space.
- msearch.py loogle: `"Flat", "stalk"`. Six hits: the same scheme-morphism
  results and module rank/free-locus results; no exact statement.
- msearch.py leansearch: “Relative flatness of a quasi coherent module on an
  algebraic space is detected on a surjective etale chart”. Eight hits on
  algebraic flatness descent and flat scheme morphisms; no exact statement.
- msearch.py grep in Mathlib/AlgebraicGeometry:
  `geometric.*[Ff]lat|[Ff]lat.*geometric|AlgebraicSpace`. Eleven unrelated hits
  concerning geometrically reduced/integral flat scheme morphisms.
- rg in lean/WeilConjectures and lean/Sheaf for geometric stalk flatness,
  module flatness/chart names, and the final declaration name; grep for this
  item's blueprint id in WeilConjectures. No existing theorem matches. Nearby
  SpaceStrictLocalFlatness is ring-map flatness, not arbitrary module flatness.
  The searches located the already-owned canonical stalk, scheme-space and
  scheme-restriction APIs above, which are reused without new definitions.
- rg in dag/lean_names_upstream.json, Mathlib, WeilConjectures and Sheaf for
  `module_flat_iff_chart_stalk|SpaceModuleFlatChartTest`: no existing declaration.

Validation: prescribed scompile.py compiled this file independently in both the
sandbox and final module positions against the live published build, cleanly
(1.8 s each). `set_option autoImplicit false` enforces explicit binding.

## Second reading by Q97

With the JSON statement and complete Lean signature reopened, checked S/X/T/f,
quasi-coherence, the arbitrary etale atlas and its separate surjectivity
hypothesis, the two independently restricted scalar actions, and both global
quantifiers. In particular the left side uses the target etale stalk, not the
ordinary target stalk, while the right uses the ordinary target stalk. F is
canonical restriction to Zariski opens, so no arbitrary sheaf or extra
comparison hypothesis was introduced. The explicit ordinary stalk predicate
was retained instead of replacing it textually with the affine-open IsFlatOver
predicate. No mismatch was found; added ownership dependencies for the canonical
stalk, scheme-space, ordinary module-stalk, and scheme-restriction APIs already
landed in the project. This is the author's second pass; the dispatcher brief
forbids starting another agent, and independent review is the maintainer's.
