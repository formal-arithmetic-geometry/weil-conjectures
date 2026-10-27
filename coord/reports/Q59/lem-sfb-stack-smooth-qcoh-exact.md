## Worker report

Item: `lem-sfb-stack-smooth-qcoh-exact`, stage 2, group Q59.
Module: `Sheaf.AlgebraicGeometry.StackSmoothQcohExact`.
The existing node's only changed field is `lean`; no statement correction, new node,
or dependency repair is needed. Both theorems have `sorry` proofs. Both helper
functors are explicit constructions, with no postponed data or choice of maps.

The module states the two clauses in `stack_smooth_qcoh_exact` and
`stack_smooth_scheme_qcoh_restriction_exact`. `moduliQcohPullback` restricts the
recorded literal module precomposition to the full quasi-coherent subcategories,
using `ObjectProperty.lift` and the recorded proof of quasi-coherence.
`ModuliQuasicoherentPrecomposition.tensor_comparison`, `.tensor_sections` and
`.tensor_naturality` identify this exact functor, on objects AND arrows, with
canonical tensor pullback. `moduliQcohSchemeRestriction` lifts the recorded
Zariski restriction in precisely the same way. It does not copy either notion.
These helpers belong to this node's functors and are listed in `lean.declarations`.

Hypotheses and clauses, matched with the Lean:

| Node | Lean |
| --- | --- |
| The size convention | Explicit `universe u v w`; `Scheme.{u}` and `BasedCategory.{v, w}` retain distinct site morphism and object universes. The common ambient module universe is `max (u + 1) v w`, as in the recorded dependency. |
| A scheme S | `{S : Scheme.{u}}`. |
| Algebraic stacks Z and X over S | `(Z X : BasedCategory.{v, w} (Over S))`, `(hZ : IsAlgebraicModuliStack Z)`, `(hX : IsAlgebraicModuliStack X)`. |
| A morphism f | `(f : BasedFunctor Z X)`, a functor over the specified base. |
| f smooth on smooth scheme charts | `_hsmooth` gives `U V : Over S`, smooth surjective atlases `a` and `b`, `q : U ⟶ V` with `Smooth q.left`, and `Nonempty (a.comp f ≅ (discreteModuliMap (yoneda.map q)).comp b)`. This retains the actual 2-commutative square and does not require representability of f. |
| Big fppf quasi-coherent module categories | `ModuliQCoh X hX.1.1` and `ModuliQCoh Z hZ.1.1`, the dependency's full subcategories for `SheafOfModules.isQuasicoherent` on `moduliModuleRings`. The predicate is the existing local-presentation definition, not a new cartesian-module notion. |
| Their abelian structures | Import `StackQcohAbelian`, whose `stack_qcoh_abelian` supplies exactly these full subcategories. Exactness uses the underlying categorical limits/colimits and is independent of any chosen witnesses to those structures. No arbitrary Abelian structure or new instance is assumed. |
| Tensor pullback f* | `moduliQcohPullback P`. The witness `P : ModuliQuasicoherentPrecomposition hZ.1.1 hX.1.1 f` supplies the already-recorded continuity and quasi-coherence proofs, and the normalized tensor comparison. Existence for every f is `exists_moduliSchemeRestriction X hX.1.1 |>.2 Z hZ.1.1 f`. The theorem holds for every such witness and adds no geometric hypothesis. |
| Exactness, carrying every short exact sequence to a short exact sequence | `PreservesFiniteLimits (moduliQcohPullback P) ∧ PreservesFiniteColimits (moduliQcohPullback P)`, the Mathlib definition of exact functor. In abelian categories this is equivalent to an additive functor preserving short exact sequences. |
| The scheme case Z=T and F maps to F_f | The second theorem takes `(T : Over S)` and its actual map `(f : BasedFunctor (discreteModuli (yoneda.obj T)) X)`. It evaluates `R.restriction` at `f.obj (CostructuredArrow.mk (𝟙 (yoneda.obj T)))`, exactly the object over T defining F_f. `R` is the recorded `ModuliSchemeRestriction`, not an arbitrary functor. |
| Smoothness for the scheme case | Its expanded `_hsmooth` quantifies over every scheme test `W,t` and gives `HasSpaceBaseChange f W t A p ∧ SpaceMapIsSmooth A W p`. This is smoothness on all etale charts of the actual algebraic-space projections. It imposes no surjectivity on f. For a scheme mapping to an algebraic stack representability by spaces follows from the representable diagonal, so this is the scheme specialization of the same smoothness. |
| Quasi-coherent Zariski target | `SchemeTestQCoh.{u, max (u + 1) v w} (schemeTestBase X x)` is exactly the full quasi-coherent subcategory of the coefficient-lifted ordinary Zariski module category in the dependency. The base of x is canonically T by `BasedFunctor.w_obj`; no replacement ringed site is used. |
| Kernels, cokernels and monomorphisms in these categories | Finite-limit preservation includes the kernel diagrams and preserves monomorphisms; finite-colimit preservation includes cokernel diagrams. Both preservation assertions are stated for `moduliQcohSchemeRestriction R x` with its full quasi-coherent codomain. |
| No quasi-compactness, finite generation, representability or Noetherian assumption on f | There are no such binders; the only geometric assumptions are algebraicity and smoothness. Objects are arbitrary quasi-coherent modules. |

Smoothness is an equivalent expanded definition, not an extra hypothesis:
Stacks `stacks-morphisms.tex`, `definition-smooth` (075U), refers to
`lemma-local-source-target` (06FM). Its condition (2) is a smooth square with
surjective left vertical map and smooth horizontal map. One may require both
vertical arrows to be smooth surjective scheme atlases: for a smooth f choose
an atlas V of X, then an atlas U of Z times_X V. Their composite U to Z is a
smooth surjection and q is smooth by condition (1). Conversely the stated square
is already condition (2). Thus this condition covers arbitrary, including
nonrepresentable, smooth maps; it neither restricts to representable morphisms
nor presupposes the exactness being stated.

The common pair `v,w` is the common-bound site convention of the scheme-restriction
dependency; neither is equated with u or with the other. Independently sized
stacks can be viewed in a common larger bound. The existing ambient coefficient
lift, including all its canonical tensor comparisons, is retained verbatim.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms;
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`;
  `Mathlib.CategoryTheory.Abelian.Basic`: `CategoryTheory.Abelian`.
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`: `IsAlgebraicModuliStack`,
  `IsSmoothModuliAtlas`, `SpaceMapIsSmooth`; these retain the actual base-change
  projections. This and the smooth/scheme imports are publicly re-exported by
  `StackQcohAbelian`.
- `Sheaf.AlgebraicGeometry.StackQuasiCoherentAlgebra`: `moduliFppfTopology`,
  `moduliModuleRings`, `IsQuasicoherentModuliAlgebra` and its underlying general-site
  predicate. The ring values are the canonical ULifts of regular functions, not
  independent rings. Publicly re-exported by both statement dependencies.
- `Sheaf.CategoryTheory.RingedSiteModules`: `ringedSiteModules`, the exact
  `SheafOfModules` abbreviation, and Mathlib's category of module sheaves.
- `Sheaf.AlgebraicGeometry.StackQcohAbelian`: `stack_qcoh_abelian`.
- `Sheaf.AlgebraicGeometry.StackQuasiCoherentSchemeRestriction`:
  `ModuliQCoh`, `SchemeTestQCoh`, `schemeTestBase`, `schemeTestModuleRings`,
  `ModuliSchemeRestriction`, `ModuliQuasicoherentPrecomposition`,
  `moduliModulePrecomposition`, `exists_moduliSchemeRestriction`.
- `Mathlib.CategoryTheory.ObjectProperty.FullSubcategory`: `ObjectProperty.lift`;
  `Mathlib.CategoryTheory.Limits.ExactFunctor`: exactness is the conjunction of
  `PreservesFiniteLimits` and `PreservesFiniteColimits`.

All currently recorded proof dependencies have plain imports when they are not
already public statement imports: `SmoothFiber`, `SchemeBigFppfQuasicoherentEquivalence`,
`AlgebraicStackFibreProducts`, `QuasicoherentKernel`, `QuasiCoherentCokernelImage`,
`FlatModulePullbackExact`, `EtaleTensorSectionsSheaf`. The six remaining proof
nodes have no recorded Lean module on the base: groupoid stack presentations,
space-groupoid module descent, flat-space-groupoid kernels/cokernels,
representable-smooth calculus, stack smooth presentation criterion, and the
scheme-etale exact/finiteness comparison. Their mathematical steps remain in
our proof docstrings; there is no import of a nonexistent module. No missing
proof theorem is made an assumption of either statement.

Edge cases checked before writing:

- Empty schemes and empty stacks: atlases and smooth chart maps may be empty;
  neither theorem requires nonemptiness or surjectivity of f. Restriction at an
  empty scheme test is included. Empty finite limit/colimit shapes include the
  zero-object requirement.
- Identity and isomorphism maps: identity atlas squares satisfy the smoothness
  hypothesis; pullback remains the recorded literal precomposition. The
  scheme-test functor retains the normalized identity/composition comparisons.
- Nonrepresentable smooth maps, for example a classifying-stack projection for a
  smooth group: the main hypothesis asks only for an atlas square and never a
  representable base change of f. It does not accidentally require `ModuliSpaceTest`
  for the general stack map.
- Non-surjective smooth scheme tests, including open immersions: the second
  hypothesis has smooth projections and no field-lifting/surjectivity clause.
- Arbitrary modules, zero modules, non-finite modules and non-Noetherian bases:
  no finiteness condition occurs. There is no characteristic restriction or
  integer degree parameter.
- Kernel and cokernel preservation refer to the full quasi-coherent categories,
  not sectionwise exactness of values or exactness of their ambient inclusions.

Searches (2026-10-24):

1. `msearch.py ... leanfinder "Smooth pullback of quasi coherent modules on algebraic stacks is exact"`:
   eight scheme pullback/additivity/composition results, including
   `Scheme.Modules.pullback` and `instAdditivePullback`; no stack exactness result.
2. `msearch.py ... loogle '"Quasicoherent", "Exact"'`: zero hits.
3. `msearch.py ... grep 'quasi.?coherent.*[Ee]xact|[Ee]xact.*quasi.?coherent|algebraic.?[Ss]tack' AlgebraicGeometry`:
   four hits in `Modules/Tilde.lean`, all scheme tilde comparisons, no match.
4. `msearch.py ... leansearch "Smooth pullback preserves short exact sequences of quasi coherent modules on algebraic stacks"`:
   eight hits on scheme/general ringed-site pullback, adjunction and additivity,
   plus an abelian pullback-square exact complex; none is this stack assertion.
5. `rg` in `lean/WeilConjectures` and `lean/Sheaf` for stack/moduli exactness,
   `ModuliQCoh`, `IsSmooth.*Moduli`, and smooth-map definitions: found the recorded
   scheme restriction, quasi-coherent abelianity and atlas predicates, but no exact
   stack pullback or exact scheme-test quasi-coherent restriction. A literal
   search for the item id in the upstream source has no matches.
6. DAG/source concept searches for smooth stack morphisms found the existing
   `lem-sfb-stack-smooth-presentation-criterion`; its statement is read, with no
   Lean record. Smoothness can be expanded directly using the existing atlas
   predicates, so no new definition or missing-theorem assumption is needed.

Sources read: the local Stacks `stacks-cohomology.tex` flat-pullback and
check-exact lemmas and proofs, `stacks-morphisms.tex` smooth definition and
local-source-target criterion; all statement-dependency records and the actual
signatures/docstrings of their declarations. There is no `STATEMENT-DISPUTED`
or identified node fault.

Validation: `scompile.py Q59 lem-sfb-stack-smooth-qcoh-exact` compiled the module
both under its sandbox name and its actual library name successfully. The initial
run requested `noncomputable` for the existing precomposition construction;
marking the public section noncomputable fixed it without changing the statement.

## Second reading by Q59

A separate second pass by this same worker reread the node and completed Lean
file. No sub-agent was started, as expressly required by this dispatch; the
maintainer supplies the independent delivery review. This section does not claim
an independent worker review.

The rereading checked both clauses against the table above, in particular the
nonrepresentable stack case, the non-surjective scheme-test case, the specified
2-isomorphism, the actual full subcategories, and preservation of kernel/cokernel
universal properties rather than sectionwise exactness. It checked that P and R
are the recorded existence interfaces and determine the canonical functors, not
extra geometric restrictions or arbitrary maps. Both helpers contain actual
functor data. Only the two statement proofs are `sorry`. No hypothesis or clause
mismatch was found and no mathematical statement change was made. The required
noncomputability annotation is the only compile repair.
