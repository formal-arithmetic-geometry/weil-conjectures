## Worker report

Q76 states `AlgebraicGeometry.AlgebraicSpace.CoherentExterior.abelian_coherent_exterior_base_change`
in `lean/Sheaf/AlgebraicGeometry/AbelianCoherentExteriorBaseChange.lean`.
There is exactly one postponed theorem, that declaration, with proof `by sorry`.
All helper definitions have actual data. The helper presentation is data together
with normalization equations; it is existentially supplied by the conclusion,
never assumed as additional geometric input. No existing source was edited.
No statement correction, new node, dependency repair, or disputed statement is needed.

### Hypotheses and every conclusion

- The base is `{S : Scheme.{u}} [IsLocallyNoetherian S]`. No global Noetherian,
  quasi-compact, connected, reduced, or nonempty hypothesis is added.
- `A : AlgebraicSpace S` and `group : CommutativeSpaceGroup A` give the actual
  natural commutative group law, including identity. The map to the represented
  base is `groupSpaceProjection A`, not an arbitrary unrelated morphism.
- `hA : Poincare.IsAbelianFamily (groupSpaceProjection A)` expands into
  `MapIsProper`, chartwise `MapIsLocally (@Smooth)`,
  `MapIsLocallyOfFinitePresentation`, and `HasAbelianFibres`. Properness means
  separated, finite type and universally closed. Its quasi-compactness and
  separated diagonal make local finite presentation equivalent to finite
  presentation here. `HasAbelianFibres` quantifies over algebraically closed
  fields and their scheme points and asks for a representing proper smooth
  connected scheme. Its group is inherited from `group`. This matches the
  geometric-fibre clause; it assumes no dual Picard object.
- `∀ T : Over S` includes every scheme over S, without Noetherian, reduced,
  affine, flatness, or finiteness assumptions. `family A T` is the existing
  sheaf fibre product; `projection A T` is its second projection.
- `image f n` is degree n homology of the existing canonical `derivedDirectImage f`
  applied to the degree-zero structure module. All cohomology is in the existing
  module category on the actual small affine etale basis.
- `IsIso (zero (projection A T))` states the structural degree-zero isomorphism.
  `zero` is the regular-function structure map followed by the canonical
  ordinary-to-right-derived-zero comparison and the existing homology comparison.
  Since module direct image is left exact, this is exactly O_T -> f_* O.
- `(zariskiImage A T 1).IsFiniteLocallyFree` uses variable finite rank and the
  Zariski module category of T. `Poincare.schemeModule T` is the recorded small
  model equivalence followed by restriction at the represented identity chart.
  Thus this is Zariski finite local freeness, not merely etale local freeness.
- `ExteriorOnCharts` uses Mathlib's `⋀[R]^n M` (the exterior-power submodule of
  its exterior algebra, the tensor-algebra quotient by v tensor v). Each affine
  etale chart has a linear equivalence in every degree, including zero.
  Its zero equation is the structural unit; its degree-one equation is the
  identity. The concatenation equation identifies the image of every pure wedge
  with the iterated actual relative cup product. Pure wedges span exterior powers,
  so this specifies the full graded algebra map and its inverse degreewise.
  The restriction equation glues these maps on the affine etale basis. Since V
  is quasi-coherent and finite locally free, exterior powers commute with affine
  chart sections, so this is the sheaf exterior algebra assertion.
- `product` calls the dependency's `moduleCupWith` with the structure sheaf
  multiplication (the left unitor). Its only further transport is the equality
  between the two notations for p+q. `Presentation` retains the actual ordinary
  adjunction unit, derived adjunction and computation counit. Ordinary functors
  are compared by natural isomorphisms, allowing the existing chart-limit and
  extension-of-scalars models to differ as constructions. The free derived
  functor fields of the ringed edge are fixed to the already published functors.
  Its additive proof field is the established additivity of tensor pullback;
  it is not an additional hypothesis on the group space.
- For every `T'`, every `g : T' ⟶ T`, and any representation of the cartesian
  square (`hp : IsPullback ...`), `IsIso (exchange ...)` gives derived base change.
  `exchange` is the adjunction mate of the normalized pullback square and counit,
  followed by the canonical structure-module pullback map. It is a constructed
  arrow, not a chosen isomorphism. The additional isomorphisms `c n` have domain
  the *ordinary* pullback of `image f n`. `BaseChangeNormalization` fixes them
  on every representative where the derived counit computes pullback termwise:
  lift pulled-back cycles by their inclusion equation, then take their actual
  homology classes and the homology of `exchange`. Such representatives exist
  by K-flat resolutions; tensor pullback preserves the epi from cycles to classes,
  so the formula determines c uniquely. It is the canonical higher-image
  comparison, not an arbitrary equivalence of modules. This normalization also
  retains identity and composition cases. `BaseChangeProducts` explicitly states two further equations for these same c.
  On every compatible pair of pointed affine etale charts and every scalar b,
  `baseChangeSection (p+q) b (cup m n)` equals the cup of
  `baseChangeSection p b m` and `baseChangeSection q 1 n`.
  Its second equation sends b tensor the exterior image of a pure wedge to b
  times the target exterior image of the degree-one classes pulled back with scalar 1.
  The source and target families w,w' satisfy `ExteriorOnChartsWith`, including
  structural units, degree-one identity, Fin.append products and restrictions.
  Pure wedges and the displayed local tensors generate, so these equations state
  both full cup compatibility and naturality of the exterior isomorphisms.
  The normalized exterior maps are uniquely determined by their unit and pure-cup
  formulas; using existential presentations here does not allow unrelated maps.
  No flatness instance or assumption on g appears.
- For every commutative ring R and `a : T.left ≅ Spec (.of R)`, `AffineConclusion`
  uses the actual additive-sheaf cohomology `additiveH`, namely right-derived
  `Sheaf.Γ` of the underlying additive structure sheaf. `affineH` bundles its
  R-action: the dependency's canonical transported global-cohomology module
  action, restricted along `affineGlobalScalar` (regular-function pullbacks).
- The affine degreewise equivalences are R-linear exterior-power equivalences.
  Their degree-zero formula is normalized by `affineZero`, actual pullback of
  regular functions and the zeroth right-derived unit. Together with the standard
  exterior-power-zero identification, this states H0=R through its structural map.
  Degree one is identity; the concatenation formula uses `globalCupWith`, so the
  isomorphisms are the actual global cup-product maps. The tilde comparisons use
  `Scheme.Modules.tensorPullback a.inv` and Mathlib `tilde`, retaining the stated
  identification of H1 with V_T (and its implied version in every degree).
- `∀ n, Module.Finite R ... ∧ Module.Projective R ...` says finite projectivity,
  not freeness. `∃ N, ∀ n, N < n → Subsingleton ...` is precisely eventual
  vanishing. The bound is allowed to depend on the affine base and its finite
  trivializing cover, so no globally bounded rank on a non-quasi-compact S is imposed.

### Dependency declarations read and used

The original seven statement dependencies were read with their full signatures
and docstrings: `Scheme` (Mathlib.AlgebraicGeometry.Scheme), `AlgebraicSpace`
(Sheaf.AlgebraicGeometry.AlgebraicSpace), `ringedSiteModules`
(Sheaf.CategoryTheory.RingedSiteModules), `IsLocallyNoetherian`
(Mathlib.AlgebraicGeometry.Noetherian), `Smooth`
(Mathlib.AlgebraicGeometry.Morphisms.Smooth), `LocallyOfFinitePresentation`
(Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation), and `moduleCupWith`,
`globalCupWith`, `globalCohomologyModule`, `globalUnderlyingSections`
(Sheaf.CategoryTheory.RingedSiteModuleCupProduct).

Additional already-recorded interfaces are cited in stmt_deps, not restated:

- Sheaf.AlgebraicGeometry.AbelianSpacePoincareData: `Poincare.IsAbelianFamily`,
  `HasAbelianFibres`, `product`, `snd`, `schemeModule`; the underlying
  `CommutativeSpaceGroup`, `groupSpaceProjection` and `schemeSpace` are reused.
- Sheaf.AlgebraicGeometry.SpaceDerivedTensorPullback: `smallModuleTensorPullback`
  and its additive instance; Sheaf.AlgebraicGeometry.SpaceDerivedPullback:
  `spaceDerivedPullback` and `spaceDerivedPullbackCounit`.
- Sheaf.AlgebraicGeometry.SpaceAffineHomComparison: `spaceSmallTensorAdjunction`
  and `spaceDerivedAdjunction`.
- Sheaf.AlgebraicGeometry.RelativeDualizingTracePair:
  `traceSmallStructureMap` and `traceDerivedStructureMap`, owned by
  `def-sfb-relative-dualizing-trace-pair`. These are the canonical regular-function
  structure map and its derived-adjunction transpose. The pullback-square
  isomorphism is inlined in `exchange` using `spaceDerivedPullbackComp` and the
  equality of composite paths, both directions fixed. Neither theorem node
  `lem-sfb-space-relative-flat-closed-kernel-base-change` nor
  `lem-sfb-space-derived-etale-chart-calculus` remains in stmt_deps or imports.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules:
  `derivedDirectImage`, `smallModuleDirectImage`, `derivedStructure`, owned by
  `def-sfb-space-derived-module-calculus`.
- Sheaf.AlgebraicGeometry.RegularGroupSpace: `CommutativeSpaceGroup`,
  `groupSpaceProjection`, `groupSchemeMap`, owned by `def-sfb-smooth-integral-group-space`.
- Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite: `schemeSpace`, owned by
  `def-trf-scheme-algebraic-space`.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceGeometricStalkModels:
  `SingleComplex.Neighbourhood`, `neighbourhoodChart`, `ringDiagram`, `Compatible`,
  owned by `def-sfb-space-geometric-stalk-models`. Only chart definitions are used;
  the statement quantifies over arbitrary scheme points G, not only field points.
- Sheaf.AlgebraicGeometry.AlgebraicSpacePullbackTensorComparison:
  `SingleComplex.localSection`, owned by `def-sfb-space-pullback-tensor-comparison`.
  This is the already recorded local adjunction-unit tensor b tensor m, transported
  through the small-model equivalence; it has actual data.
- Sheaf.Algebra.Homology.RingedSiteGlobalHomIdentification: `corner`, `tensorModel`.
- Sheaf.AlgebraicGeometry.SpaceAffineGlobalSections: `affineGlobalScalar`.
- WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree:
  `SheafOfModules.IsFiniteLocallyFree` (variable finite rank).
- Mathlib.LinearAlgebra.ExteriorAlgebra.Basic and ExteriorPower.Basic:
  exterior powers and `exteriorPower.ιMulti`; Mathlib.AlgebraicGeometry.Modules.Tilde:
  `tilde`; WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatNat:
  the canonical single-object homology/right-derived comparison
  `CategoryTheory.Functor.homologyRightDerivedFunctorObjSingleFunctorIso`, whose
  owner `src-right-derived-functor-plus-compatibility` is now cited explicitly.
  Its defining module is PlusCompatibility, publicly imported by PlusCompatNat.

Every proof dependency with a recorded module is imported privately unless its
interface is also used in the statement. The unstated proof prerequisites remain
in the original proof and its complete eight-step theorem docstring; they are not
needed to type the statement, and no extra theorem was introduced to bypass them.

### Edge cases and sources

Checked degree zero (empty wedge and structural unit), degree one (identity),
zero rank, characteristic two (squares vanish by the exterior quotient, not by
inverting 2), empty scheme and zero ring (no Nontrivial binder), nonflat and
nonreduced base changes, identity and composite base changes, varying rank,
non-quasi-compact base, and arbitrary non-Noetherian T. All schemes, rings and
geometric points use the same universe u; no smaller test universe makes a
hypothesis vacuous. All variables and universes are explicit; autoImplicit and
relaxedAutoImplicit are false.

Read Milne's local PDF: Remark I 8.7(e), printed p.37, identifies H1(O) with the
tangent space of the dual abelian variety; Lemma I 12.2, printed p.55, is the field Hopf/exterior input.
The relative statement is correctly described as agent assembly, not attributed
to those field-only passages. Read the current blueprint unit under
literature/blueprint/latest and the node's eight-step proof and sources. The
module reproduces that entire proof plan, including its dependency identifiers,
without modifying it.

### Searches actually performed

- LeanFinder: “Coherent cohomology of abelian schemes is exterior algebra on H1
  and commutes with base change”: eight unrelated cotangent-H1 results; no match.
- LeanSearch: “coherent cohomology of an abelian scheme is an exterior algebra
  on its first cohomology”: eight results, including ExteriorAlgebra and general
  sheaf/group cohomology; no relative abelian theorem.
- Loogle: `ExteriorAlgebra, AlgebraicGeometry.IsAbelianVariety`: unknown latter
  identifier and zero results, not evidence of absence. Repeated with
  `ExteriorAlgebra`: twelve results, including the existing exterior algebra,
  exteriorPower, iota and multi-iota constructions, which the module reuses.
- Mathlib grep via msearch: `exterior.*cohomology|cohomology.*exterior|abelian.*base.change`
  under AlgebraicGeometry: zero matches.
- rg on WeilConjectures and Sheaf for the item identifier and exterior/cohomology,
  abelian/base-change combinations: only unrelated Koszul, lattice and general
  algebra material, no statement of this relative theorem. The precise item id
  has no existing declaration. Searched DAG definition owners and their Lean
  records for exterior algebra, variable finite local freeness, abelian space
  data and all canonical module/base-change interfaces; reused the recorded ones.

Search wrapper results are retained in sandbox searches.jsonl. Compiler validation
uses only the authorized scompile.py wrapper, for the single delivered file.

## Second reading by Q76

I performed a separate second pass with the node and source file open. The
explicit dispatcher instruction prohibits starting other agents, so this is
self-review; the maintainer's independent delivery review remains independent.
This report does not claim that a second agent read the file.

The second pass found and repaired three interface issues: degree zero of the
relative exterior equivalences now has an explicit structural-unit formula;
per-degree base-change isomorphisms now carry the cocycle normalization fixing
the canonical arrows; the ordinary ringed presentation uses natural isomorphisms
rather than equality of different pullback constructions. Derived functors and
adjunctions remain the published ones, and the representative computation counit
is retained. The affine scalar action is explicitly restricted from the actual
global cohomology module action, with no unbound instance parameters.

The hypothesis/clause audit above found no node statement correction necessary.
No independent notion was redefined: every helper belongs to the particular
canonical cup/base-change/exterior assertion of this node. All helper names are
listed in lean.declarations. Only the main theorem is sorry, with the original
complete natural-language proof plan attached.

The original delivery was head 330df3167d13 (dry-run e79e8a013f9); the validation
below concerns the repaired module, not an unchanged re-push.

## Repair of returned head 330df3167d13

- H2, theorem dependencies used only for definitions: selected the review's
  definition-owner alternative. The structural maps now come from
  `def-sfb-relative-dualizing-trace-pair`, and the pullback square is the explicit
  composition of `spaceDerivedPullbackComp` and equality of the two paths inside
  `exchange`. Removed both unnecessary theorem dependencies and imports.
- H2, uncited owners: added all four requested ids:
  `def-sfb-space-derived-module-calculus`, `def-sfb-smooth-integral-group-space`,
  `def-trf-scheme-algebraic-space`, and
  `src-right-derived-functor-plus-compatibility`. Their statements, recorded
  modules, full relevant signatures and docstrings were read. The new local-tensor
  formulas also cite the two existing definition owners for pointed chart data and
  `SingleComplex.localSection`; no dependency node record was changed.
- H3, missing compatibility conjunct: added `BaseChangeProducts ... c` beside
  `BaseChangeNormalization ... c` in the theorem. Both use the identical family c.
  `baseChangeSection` is a real composite of the existing local tensor section,
  c, and the two `presentationImage` isomorphisms. The predicate explicitly asserts
  preservation of every cup product and of every pure-wedge exterior comparison,
  including degree zero, on all compatible affine etale charts. The old
  `ExteriorOnCharts` assertion is factored through `ChartExterior` and
  `ExteriorOnChartsWith` to expose the same normalized family for this equation;
  its original clauses are unchanged.

Reread Stacks Tag 0H9A, sites-cohomology.tex,
`lemma-base-change-cup-product`: its commutative derived square identifies the
relative cup products through the base-change mate and tensor pullback comparison.
The two displayed local formulas above are its cohomological pure-tensor formula
and the resulting pure-wedge formula, as required in the node proof's step 7.
The scalar b occurs on the first factor only in the binary cup formula; it occurs
once outside the whole target wedge, so the equation does not incorrectly multiply
by b to the nth power. In degree zero the second equation retains the structural
unit. Empty charts/zero ring, rank zero, characteristic 2 and nonflat base maps
still require no extra hypothesis.

Compared the retained sandbox node with current main by parsing JSON: all original
non-Lean fields except stmt_deps agree. The statement and eight-step proof remain
verbatim, and the dependency changes are only the reviewed owner additions relative
to main's seven original dependencies. No statement correction or new node is needed.
All new helper declarations are listed in lean.declarations and have source/blueprint
docstrings. There is still exactly one sorry, in the main theorem.

Validation: repaired sandbox and final library module both compiled cleanly through
scompile.py on 2026-10-24 (29.1 s and 26.5 s), with no errors or warnings.
The repaired deliver2.py --no-push run passed preflight and compilation:
OK (dry run), commit f1b8034fd11. Nothing outside the sandbox was edited directly.

