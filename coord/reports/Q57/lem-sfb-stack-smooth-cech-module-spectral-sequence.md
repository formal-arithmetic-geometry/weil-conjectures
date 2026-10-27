## Worker report

This delivery states `CategoryTheory.stack_smooth_cech_module_spectral_sequence` in
`Sheaf.AlgebraicGeometry.StackSmoothCechModuleSpectralSequence`, with a `sorry` proof.
It reuses Q22's reviewed big-etale module interface and supplies the relative nerve
constructions and the existing, unstated injective-transport prerequisite. The item’s
mathematical statement, proof plan and proof dependencies are unchanged.

Returned head `b5cde6d86b3e` is repaired point by point:

1. `def-sfb-surjective-moduli-map` now owns the use of `IsSurjectiveModuliMap`.
   The added statement dependency on the chartwise-calculus theorem is removed.
2. `def-sfb-spectral-sequence-pages-from-two` is a new `existing: true` definition
   binding for `SimplicialSlice.augmentationPagesFromTwo`. The added statement
   dependency on the site-augmentation theorem is removed. Its module is still
   imported for the plain definition, without using the theorem conclusion.
3. The helper, transport statement and item now use `ModuliBigEtaleModules`,
   `moduliBigEtalePrecomposition`, `moduliBigEtaleDirectImage` and
   `moduliBigEtaleHigherImage` from `def-sfb-stack-big-etale-module-functors`.
   Q57's duplicate rings, module category, image functors and their foundational
   theorems are deleted. The helper retains composition, relative restrictions,
   tuple nerve data, fibredness and algebraicity, plus real instance data exposing
   additivity and the defining right adjunction of the shared functors.

Q22's reviewed commit `2d61515984da666c32cd6f6159a8d15e3a12df9e` was read in a
sandbox-only read clone. Its node and module are absent from live main and the
prescribed server source lookup. Therefore the packet carries that exact unchanged
module and its original definition node as a prerequisite, retaining Q22's authorship
and created provenance. Only its lean record adds this delivery's reuse note and date.
This uses the accepted owner and its exact public names; it creates no competing notion.

Sources read: Stacks `stacks-sheaves.tex`, Tag 072G,
`proposition-smooth-covering-compute-direct-image` (1)(b), its module lemma 072E,
`lemma-cech-to-cohomology-relative-modules`, including the proof and the four hypotheses;
`homology.tex`, Tag 0132, `lemma-first-quadrant-ss`. The item is an auxiliary node,
not the statement of a blueprint unit. The current blueprint path was searched; the
node has inherited `blueprint.from.node: null`, which is retained in the new node.

The hypothesis and clause correspondence is as follows.

| Node text | Lean |
| --- | --- |
| Scheme S and size convention | `S : AlgebraicGeometry.Scheme.{u}`; morphism universe `v`; total objects, module values and ring values in the common bound `max (u + 1) v w`. All universe variables are declared. This bound includes the scheme universe and allows an arbitrarily larger bound `w`; it imposes no equality of scheme, object and morphism universes. |
| Algebraic stacks U, X, Y over S | `U X Y : BasedCategory.{v, max (u + 1) v w} (Over S)` and `hU hX hY : IsAlgebraicModuliStack ...`. Their fibred-groupoid proofs are the first conjuncts of their stack descent predicates. |
| Maps f and u over S | `f : BasedFunctor X Y`, `a : BasedFunctor U X`. These preserve the base projection, including on arrows. |
| u representable by algebraic spaces | `ha : IsRepresentableByAlgebraicSpaces a`, the existing scheme-test 2-base-change predicate. |
| u smooth | `hsmooth : ModuliSpaceTest (@AlgebraicGeometry.Smooth) a`. Its signature tests the actual space projection on each etale scheme chart after every scheme base change. It does not require U or X to be DM. |
| u surjective, with field-extension-local lifts | `hsurj : IsSurjectiveModuliMap a`, read in `StackChartwiseSmoothEtaleCalculus.lean`; it quantifies over each field object, an extension field and a vertical comparison 2-isomorphism. |
| Big etale site, all objects and arrows | `moduliBigEtaleTopology` from the shared Q22 module. It is the comap of the scheme etale precoverage on the whole total category, not a lisse site or a category of cartesian modules. |
| Structure sheaf on x/T is regular functions | `moduliBigEtaleRings` uses the existing `moduliStructurePresheaf`, with its explicit `ULift` of scheme global sections and its original regular-function pullbacks. The sheaf condition and ring construction are the shared Q22 declarations. |
| All module sheaves F | `ModuliBigEtaleModules` is the existing `ringedSiteModules`/`SheafOfModules` of these rings. There is no quasi-coherent, cartesian or finiteness predicate. The theorem is in the functor category on this entire source category, so evaluation gives the assertion for every F and its naturality. |
| Pullback is precomposition | `moduliBigEtalePrecomposition` is `SheafOfModules.pushforward` for the total-category functor, with the canonical ring isomorphism induced by equality of the scheme projections. This API is named pushforward by Mathlib because its direction is precomposition. |
| Direct image is compatible sections on the test 2-fibre | `moduliBigEtaleDirectImage` is the right adjoint to exactly that precomposition, with `Adjunction.ofIsLeftAdjoint`. The adjunction uniquely characterizes the compatible-family functor, including its scalar action; no arbitrary direct-image functor is a hypothesis. The existence docstring spells out the pairs `(x,a(x)->y)` and their cartesian identification with the test fibre. |
| Higher images by injective resolutions in all modules | `moduliBigEtaleHigherImage` is `Functor.rightDerived`; `moduliBigEtale_hasInjectiveResolutions` supplies Mathlib's nonnegative injective resolutions. |
| U_p is the (p+1)-fold 2-product over X, with projection | `fibredModuleCechLevel a p` is the existing `FibredCechTuple a (p+1)` with its common-target projection `fibredModuleCechProjection`. Objects retain each entry, the common target, and all vertical comparison isomorphisms. Degree zero is the one-entry tuple presentation, canonically equivalent over X to U; it does not replace the stack by its isomorphism classes. |
| E1^(p,q) = R^q(f u_p)_* u_p^* F | `e₁ p q` identifies `(E.page 1).X (p,q)` with `stackCechModuleDerivedTerm ... p q`, defined as the actual inverse image along u_p followed by `moduliBigEtaleHigherImage` along its composite with f. |
| Canonical face maps | `fibredModuleCechFace` is tuple deletion via `j.succAbove`. `fibredEtaleRelativeRestrictionApp` is the adjunction mate of the restricted counit. `stackCechModuleDerivedCoface` derives this actual restriction and conjugates it by the canonical pulled-back-resolution comparisons. No existential or arbitrary face maps occur. |
| d1 is their alternating sum | The first conjunct is the equality `(E.page 1).d ... ≫ e₁.hom = e₁.hom ≫ ∑ j, (-1 : ℤ)^j • stackCechModuleDerivedCoface ... j`. For p=0 this is omission 0 minus omission 1. |
| First quadrant, bidegree (r,1-r), actual page homology | `CohomologicalSpectralSequenceNat ... 1` is Mathlib's `SpectralSequence` with indices `ℕ × ℕ`, its actual cohomological complex shapes and page-to-next-page homology isomorphisms. |
| Each entry eventually stabilizes | The second conjunct supplies an isomorphism to the stable page for every `r > max p (q+1)`. `pageInfinity` is the existing stable value at page p+q+2, after the existing restriction from E1 to E2. |
| Abutment R^(p+q) f_* F | The final conjunct is `AbutsTo (fun n ↦ moduliBigEtaleHigherImage ... f n)` in the functor category. |
| Finite filtration, F0=Hn and F(n+1)=0 | `SpectralSequence.Abutment.filtration_zero` and `.filtration_succ_self`, read in the upstream spectral-sequence module, assert exactly these subobject equalities. |
| Graded pieces Fp/F(p+1) = E_infty^(p,n-p) | `Abutment.nonempty_gradedIso` is the cokernel of the inclusion of consecutive subobjects, isomorphic to the stable page for every p+q=n. Its functor-category placement includes naturality of the filtrations and quotients. |
| No qcqs, Noetherian, finite type, or quasi-coherence assumption | None of these predicates occurs in the statement, category or hypotheses. In particular nothing is imposed on f beyond being a map over S between the three algebraic stacks. |

Dependency declarations were read, with their signatures and docstrings:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`: `IsAlgebraicModuliStack`,
  `SpaceMapIsSmooth`, `IsSmoothModuliAtlas`.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`: `IsFibredInGroupoids`,
  `ModuliTwoIso`, `moduliTwoFiberProduct`, `HasSpaceBaseChange`,
  `IsRepresentableByAlgebraicSpaces` and the base-preserving functor vocabulary.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, its representability,
  etale and surjectivity predicates.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `ringedSiteModules`, transparently
  `SheafOfModules`; its general ringed-site signature is retained.
- `Mathlib.CategoryTheory.Preadditive.Injective.Resolution`: `InjectiveResolution`;
  `Mathlib.CategoryTheory.Abelian.RightDerived`: `Functor.rightDerived`.
- `Mathlib.Algebra.Homology.SpectralSequence.Basic`: `SpectralSequence`,
  `CohomologicalSpectralSequenceNat` and its homology/page maps.
- `Sheaf.AlgebraicGeometry.StackBigEtaleModuleFunctors`: `moduliBigEtaleTopology`,
  `moduliBigEtaleRings`, `ModuliBigEtaleModules`, `moduliBigEtalePrecomposition`,
  `moduliBigEtaleDirectImage`, `moduliBigEtaleHigherImage` and the shared abelian,
  sheafification, additive direct-image and injective-resolution instances.
- `Sheaf.AlgebraicGeometry.StackQuasiCoherentAlgebra`:
  `moduliSchemeForget`, `moduliStructurePresheaf`; its fppf module category and
  its algebra direct image are not substituted for the big-etale module category.
- `Sheaf.CategoryTheory.FibredRelativeCech`: `fibredBigEtaleTopology`,
  `FibredCechTuple`, `fibredCechTupleProjection` and `fibredCechTupleReindex`.
- `Sheaf.AlgebraicGeometry.DmStackMorphismProperties`: `ModuliSpaceTest`;
  `Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus`:
  `IsSurjectiveModuliMap`. Both signatures allow arbitrary based categories.
- `WeilConjectures.CategoryTheory.Abelian.RightDerived.Comp`:
  `Functor.compRightDerivedObjIso`, including its exactness and acyclicity hypotheses.
  Injective acyclicity is the existing `Functor.rightAcyclic_of_injective`.
- `WeilConjectures.Mathlib.Algebra.Homology.SpectralSequence.Basic`:
  `SpectralSequence.pageInfinity`, `SpectralSequence.Abutment` and `.AbutsTo`;
  `Sheaf.CategoryTheory.SiteAugmentationSpectralSequence`:
  `SimplicialSlice.augmentationPagesFromTwo`. Only this general restriction helper
  is used from that module, not its total-site spectral-sequence theorem.

The initial searches were leanfinder "Smooth atlas Cech spectral sequence of higher direct
images of arbitrary modules on the big etale site of an algebraic stack" (8 hits on module
presentations, manifold sheaves and scheme etale topologies), loogle `"Cech",
"SpectralSequence"` (0 hits), and Mathlib grep
`smooth.*cover.*spectral|Cech.*spectral|cech.*spectral` (0 hits). Project searches in
`lean/WeilConjectures` and `lean/Sheaf` found the existing abelian-sheaf relative Cech
construction, the fppf structure presheaf, and generic spectral-sequence and derived
comparison interfaces. Searching the exact item id in `WeilConjectures` found no binding.
No declaration already states the item.

The original foundational searches are retained in the narrowed helper node for provenance;
the return's exact Q22 match supersedes their initial no-match conclusion. Its source was
read in full, including the ring isomorphism, all section-ring universes, literal
precomposition, rightAdjoint direct image, and rightDerived definition. No source declaration
was guessed from its name. The canonical relative restriction and tuple nerve declarations
remain additional constructions; no existing owner for them was found.

For the page-restriction node, LeanSearch queried "restrict a cohomological spectral sequence
from page one to page two" (8 unrelated group-cohomology/spectral-object results), leanfinder
queried "Restrict a first page spectral sequence to start at its second page" (8 complex restriction and truncation results, not spectral-sequence page restriction), and Mathlib grep queried `augmentationPagesFromTwo|SpectralSequence.*restrict|restrict.*SpectralSequence`
(0 hits). Project grep found the exact plain definition in SiteAugmentationSpectralSequence,
and no counterpart in WeilConjectures. DAG grep found only its listing under the theorem
node; `blueprint_refs.py search augmentationPagesFromTwo` returned zero blueprint nodes.
The node records the actual tool output and binds that existing definition without a copy.

Edge cases checked before and during writing:

- p=0 uses one actual tuple entry; its deletion maps in the first differential have
  exactly the two required signs. The projection equivalence with U preserves the base.
- q=0 uses rightDerived 0, canonically direct image since direct image is a right adjoint.
- n=0 has the two filtration endpoints H0 and zero, and the only quotient is E_infty^(0,0).
- The identity atlas is covered: the tuple model retains comparisons instead of
  silently identifying groupoids with sets; it is equivalent over X to the identity nerve.
- Zero modules are included. Empty schemes and empty source/target cases are not
  excluded by an index, nonemptiness hypothesis, or an affine/finite atlas assumption.
  An empty atlas over a nonempty stack fails the actual surjectivity hypothesis, as it should.
- The common bound includes every scheme and coefficient ring, while v remains independent;
  no independent lower universe is used for test fields or schemes. Field tests use Type u
  exactly as the imported definition of surjectivity does.

All delivered files are checked through the prescribed server compiler. Definitions contain
actual data; every postponed theorem has its owning node and full source/proof docstring.
No diagnostic command, private notion, local notation or auto-bound implicit remains.
There is no statement dispute or statement correction.

## New nodes

`def-sfb-stack-big-etale-module-functors` is the exact shared Q22 prerequisite described
above. Its original source, mathematical text, searches, data and names are retained.
It introduces all modules, precomposition with canonical ring transport, uniquely adjoint
direct image, and higher images at general independent universes. Q57 does not alter it.

`def-sfb-fibred-big-etale-modules` is now narrowed to canonical relative restrictions and
nerve cofaces on that shared interface. Source: Stacks 06WX, 06X3, 06X7 and algebraic 04TF.
`fibredEtaleInverse_comp` is the canonical composition law. The mate in
`fibredEtaleRelativeRestrictionApp` uses the actual adjunction counit and the composition
law, not a chosen map. Its naturality theorem is explicitly part of the node statement.
`fibredModuleCechLevel`, projection, face, term and coface use existing tuples and reindexing.
The fibredness and algebraicity statements cover the exact tuple presentation. The two
exposed instances for the shared functors contain real data: sectionwise `map_add := rfl`
and `(Adjunction.ofIsLeftAdjoint _).isRightAdjoint`. They introduce no new functors.

`def-sfb-spectral-sequence-pages-from-two` binds the existing plain definition in
`Sheaf.CategoryTheory.SiteAugmentationSpectralSequence`. It retains each actual page and
homology identification for every r≥2. Its source is Homology 0132, its only prerequisites
are the abelian-category and spectral-sequence definition nodes, and its lean record has
`existing: true` and no file. Its full signature is copied verbatim. No sorry or new data
is introduced by this binding.

## Dependency modules

`lem-sfb-stack-representable-module-injective-transport` was a genuine, unstated prerequisite:
its record was null, not an exact upstream/Mathlib match. The dispatcher's instruction to
state missing genuine nodes in this same delivery is applied here. Only its `lean` field
changes. `stack_module_injective_transport` states exactness of the shared precomposition
as preservation of finite limits and finite colimits, its adjunction to the shared direct
image, preservation of injectives by that direct image, and preservation by precomposition
under representability. hA/hB are the original algebraic-stack hypotheses; no smoothness,
flatness, finiteness, quasi-coherence or separation is added. The direct-image formula and
restrictions are fixed by the big-etale construction's geometric adjunction. Its six proof
steps are carried into the docstring. Available stated proof dependencies are imported;
unstated ones are named in that docstring rather than replaced by extra assumptions.

The item's statement dependencies also gain the already published owners of
`ModuliSpaceTest`, `IsSurjectiveModuliMap` and the general E1-to-E2 restriction helper,
so the imported notions have their original DAG owners. The transport prerequisite is added
because the actual canonical first-page comparison uses its exactness and injectivity.

## Second reading by Q57

The dispatcher prohibits other agents and specifies the maintainer's independent review.
This is a clause-by-clause second pass by the same worker, not a claimed independent review.

I reopened the item, four module sources and five node records. The item has exactly
hU/hX/hY, f, a, ha, hsmooth and hsurj. Its first page uses the shared precomposition
followed by the shared higher image; the transport conclusion supplies exactness and
injective preservation to the canonical compRightDerivedObjIso construction. There is
no added hypothesis. The comparison remains pinned to that construction, and the coface
is its conjugate of the derived canonical counit mate. The d1 sum has exactly p+2 terms
and alternating signs, beginning with plus in degree zero. Stabilization remains every
r>max p (q+1), and AbutsTo remains the actual higher images of f in the whole functor
category, with all finite filtration endpoints and quotient identifications. These are
unchanged mathematical clauses from the reviewed delivery, now on the shared interface.

I compared the carried Q22 source byte for byte with its reviewed delivery. Q57's helper
contains no definition of a ring sheaf, module category, inverse image, direct image or
higher image. Its composition and relative restriction use Q22 functors directly; the
adjunction is their defining Adjunction.ofIsLeftAdjoint. Nerve levels and deletion maps
retain the common target, including p=0, and algebraicity applies to those same levels.
The transport theorem refers to the same shared functors in all five assertions; its
other node fields are identical to live main. The new page-restriction binding is a def,
with exactly the existing page and iso fields, and has no theorem conclusion as data.
The item no longer cites either returned theorem merely to obtain a plain definition.
