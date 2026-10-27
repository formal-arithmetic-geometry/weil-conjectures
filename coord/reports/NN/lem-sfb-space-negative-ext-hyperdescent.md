## Worker report

The main declaration is `AlgebraicGeometry.AlgebraicSpace.space_negative_ext_hyperdescent`
in `Sheaf.AlgebraicGeometry.SpaceNegativeExtHyperdescent`. Its proof is `sorry`.
The item's natural-language statement, accepted split, proof and proof dependencies are
unchanged. Its statement dependencies gain three missing definition nodes and the already
landed `def-sfb-space-derived-module-calculus`. No stage-1 re-split is attempted. The current
stage-2 handoff explicitly supersedes the inherited stage-1 already-split refusal.
This repairs the returned packet based at 034a2a314716; delivery wrappers rebuild the
packet against the current live branch. The theorem and its coherent-system and
hypercover definitions are retained.

Hypothesis and clause correspondence:

- `S : Scheme.{u}` and `X : AlgebraicSpace S` are the arbitrary base scheme and algebraic
  space. There is no noetherian, quasi-compact, separated, representability, characteristic,
  or boundedness restriction. The shared `[∀ A, HasDerivedCategory.{w} A.SmallModules]`
  chooses localization models in the arbitrary morphism universe `w`, following the
  existing derived-category convention; it is not a geometric hypothesis. In the standard
  universe the standard localization supplies these models for every space.
- `U : SimplicialObject (Over X)` is exactly an augmented simplicial space: its slice maps
  are the augmentations `u_n` and `(U.map φ.op).left` are its actual structure maps.
  `hU : IsSpaceFppfHypercover U` requires an fppf proper-face matching arrow in every degree.
  It uses the published matching-arrow predicate, etale-chart flatness and local finite
  presentation, and field-extension point surjectivity. It does not demand that space
  maps be representable by schemes.
- `SpaceDerivedSystem U` has `obj`, `qcoh`, `transition`, `identity`, and `composition`.
  These are precisely the objects K_n, quasi-coherent cohomology, isomorphisms for every
  simplicial operator, and compatibility under the canonical derived comparisons.
  Both faces and degeneracies occur. Derived pullbacks are the total left derived functors
  of the existing ordinary tensor pullbacks, transported through the existing affine
  ringed-site equivalences. Ordinary tensor comparisons are uniquely fixed on all local
  pure tensors, and the derived comparisons are fixed by their actual derived counits.
  `spaceDerivedPullback` is an abbreviation of O3's `derivedTensorPullback.{u,w,w}`;
  it constructs no additional derived functor.
- The first conjunct quantifies over every such system D, with `∀ n i, i < 0 →
  Subsingleton (D.obj ... ⟶ (D.obj ...)⟦i⟧)` for the negative self-Hom vanishing.
  Hom sets have their zero arrow, so Subsingleton means that every arrow is zero.
  It produces `K : X.DerivedModules`, `X.derivedQCohProperty K`, and component
  isomorphisms `e`. The equality quantified over every `φ : m ⟶ n` is precisely
  compatibility with the supplied transition, including the augmentation comparison.
- The second conjunct quantifies over M,N with the two quasi-coherent cohomology
  hypotheses and exactly the negative cross-Hom hypotheses at every degree n.
  `Function.Injective` for the actual degree-zero functor map gives uniqueness of
  descent. For every degree-zero map a, equality of its two canonical
  `spaceDegreeOneRestriction` maps is equivalent to the existence of a global b whose
  restriction is a. Together these say the required bijection onto the equalizer.
  The final `∀ i < 0, Subsingleton (M ⟶ N⟦i⟧)` gives global negative cross-Hom vanishing.
- The third conjunct detects zero objects from all augmentation pullbacks, on objects
  with quasi-coherent cohomology. The fourth detects isomorphisms of arrows between
  such objects. Both clauses stand outside the negative-Ext hypotheses, exactly as in
  the node. There is no arbitrary substitute restriction map.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme`, the locally affine
  locally ringed space with its actual scheme morphisms.
- Sheaf.AlgebraicGeometry.AlgebraicSpace: `AlgebraicGeometry.AlgebraicSpace`,
  `EtaleSite`, `structureSheaf`, `Modules`. This is the existing category of fppf
  sheaves with representable diagonal and an etale surjective scheme atlas.
- Sheaf.CategoryTheory.RingedSiteModules: `CategoryTheory.ringedSiteModules`, the
  transparent specialization of `SheafOfModules`, not a new module category.
- Mathlib.Algebra.Homology.DerivedCategory.Basic: `HasDerivedCategory`,
  `DerivedCategory`, `DerivedCategory.Q`; HomologySequence provides the cohomology functors.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule:
  `AlgebraicGeometry.AlgebraicSpace.QCoh`, using Mathlib's
  `SheafOfModules.IsQuasicoherent`, its arbitrary local free presentations and the existing
  slice sheafification instances.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules: `DerivedModules` and
  `derivedQCohProperty`. These define the already established unbounded small-model
  derived category and test quasi-coherence after its inverse module equivalence.
  The same module's `derivedDirectImage` is the canonical K-injective direct image;
  it is not replaced or newly defined in this delivery.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel: `SmallModules`,
  `smallModuleEquivalence`, `smallModuleRestriction`; the actual restriction
  equivalence is used in the new conjugated tensor pullback.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations: `ModuleChart`,
  `moduleChartScalar`, `moduleTensorPullback`, `moduleTensorSection`,
  `moduleTensorAdjunction`. The identity comparison is normalized by their actual
  pure tensor sections and restriction maps; composition reuses the landed comparison.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties: `MapIsFlat` and
  `MapIsLocallyOfFinitePresentation`; AlgebraicSpaceJointSurjectivity:
  `IsJointlySurjective`, which allows lifting field-valued points after field extension.
- Mathlib.AlgebraicTopology.SimplicialObject.Basic: `SimplicialObject`, all simplex maps;
  Sheaf.CategoryTheory.SiteHypercoverDisjointUnion:
  `SimplicialObject.IsProperFaceMatchingArrow`, including terminal degree zero,
  binary product degree one and the finite higher boundary diagrams.
- Mathlib.CategoryTheory.Functor.Derived.LeftDerived: `totalLeftDerived`, its counit,
  and `leftDerivedUnique`. Comparisons are determined by these universal properties,
  not selected from a bare Nonempty isomorphism.

The five current proof dependencies have no Lean bindings, so there are no available
proof-dependency modules to import. The main docstring contains all six assembly steps,
including recovery of degeneracy compatibility from a face retraction. Their accepted
statements and sources were read; this delivery supplies the notions needed to state the
item, and does not try to formalize those independent proof prerequisites prematurely.

Edge cases checked before completing the statement: the empty base or empty space is
allowed; every simplex degree includes n=0; negative shifts are integers with strict
`i < 0`, never a vanishing claim in degree zero; zero objects cause no exceptional
case; an identity hypercover is included; degeneracies need not be flat and are still
included in all coherence conditions; no cohomological bound is introduced. Degree-zero
matching is terminal in the slice, not terminal in all spaces. Degree-one matching is
the fibre product over X. Detection does not inherit self- or cross-Ext assumptions.
The two restrictions conjugate by augmentation comparisons so their sources and targets
really coincide. Small-model transport keeps section universe u with site objects u+1,
and imposes no equality of these universes. There is no statement dispute or correction.

Searches: retained msearch LeanFinder query “Derived quasicoherent algebraic spaces fppf
hypercover descent negative Ext vanishing” returned only cohomology and general Ext hits;
Loogle query `"DerivedCategory", "Hypercover"` returned none; msearch grep
`hyperdescent|negativeExt|neg_ext|[Hh]ypercover.*[Dd]erived` returned only elementary
projective/injective Ext files. The three further LeanSearch queries for derived tensor
pullback, fppf matching hypercovers and coherent derived systems, and a LeanFinder query
combining these notions, returned ordinary tensor comparison, simplicial and cover APIs,
not these notions. Exact output is included in each new node's mathlib_searches. Mathlib
grep for the four prospective names returned zero hits. Searches of lean/WeilConjectures,
lean/Sheaf, and dag/nodes found the already existing module calculus and matching-arrow
notions, which were reused. `blueprint_refs.py search hypercover` and search `derived
pullback` found scheme/pro-etale formulations only. The ancestor query returns null,
matching the accepted item's existing ancestry. No new ancestor is invented.

The first retained draft had a missing simplicial import, causing failed elaboration and
a timeout. The import was supplied; no timeout limit was raised. The duplicate derived
category and quasi-coherence abbreviations were removed in favor of the landed module
calculus. The hypercover definition was changed to use the published matching predicate.
All four resulting modules have compiled through scompile.py, each under the fixed
60-second limit; only expected sorry diagnostics are permitted. The final deliver2 dry
run will recheck the complete packet and compile every delivered module.

## New nodes

`def-sfb-space-derived-pullback` owns SpaceDerivedPullback.lean, now titled
“Canonical identity and composition comparisons for algebraic-space derived pullback”.
It cites `def-sfb-space-derived-tensor-pullback` and uses its `derivedTensorPullback`,
`smallModuleTensorPullback`, `smallTensorPullbackComplex` and existing additive and
left-derivability instances. It additionally cites the theorem-owned
`lem-sfb-space-flat-direct-image-base-change` to reuse `moduleTensorComposition`;
there is no local copy of its composite chart, uniqueness theorem or ordinary comparison.
This node supplies the uniquely multiplication-normalized identity comparison, its
small-model transport, and canonical derived identity/composition comparisons with their
specified counits. Its primary declaration is `spaceDerivedPullbackComp`.
Sources are Stacks 03D7/03LV for identity tensor normalization and 06YY/0D6D for the
derived comparisons. The remaining named proof obligations (ordinary identity uniqueness,
composite and identity derived universal properties) occur explicitly in the statement and
lean.declarations and retain their complete proof docstrings. Every definition has real
data; the chosen ordinary identity is determined uniquely by its local normalization.
The updated live grep records the landed tensor functor and composition construction,
and found no existing declaration of the retained comparison names.

`def-sfb-space-fppf-hypercover` owns SpaceFppfHypercover.lean. It defines fppf for a space
map and the augmented matching-cover condition using existing flatness, finite
presentation, surjectivity and matching-arrow predicates. Its source is
spaces-simplicial.tex section-fppf-hypercovering, with Tag 0186 matching objects. The
searches found scheme/pro-etale and one-step hypercovers; none gives this predicate for
arbitrary algebraic spaces. Both definitions have real data and no theorem is postponed.

`def-sfb-space-simplicial-derived-system` owns SpaceDerivedSystem.lean. It defines the
actual equality transports, canonical augmentation and structure comparisons, coherent
systems, and the two canonical degree-one morphism restrictions. Its sources are
spaces-simplicial.tex definition-cartesian-derived-modules and 0DLA/0DL9, with 0D6D for
canonical derived composition. Existing general pseudofunctor descent data do not give
this algebraic-space derived family or its canonical maps; their underlying tensor and
simplicial ingredients are reused. All definitions are real constructions.

The initial dry run compiled all files and found only record-shape faults: the current
server requires an empty import_flags list on new nodes, and the signature extractor had
stopped at a named argument instead of the theorem body. Both records were repaired; the
Lean statement itself was unchanged.

## Repair self-check

The saved packet initially passed `deliver2.py --no-push` (38a618b6f50), but its
comparison module did not import O3's new module, so that check could not detect the
joint-import clash. The repair addresses every point in the return:

- H12/H4: import `Sheaf.AlgebraicGeometry.SpaceDerivedTensorPullback`; remove the local
  `smallModuleTensorPullback`, `smallModuleTensorPullback_additive`,
  `spacePullbackComplex`, and `spacePullbackComplex_hasLeftDerived`. Also remove the
  now-unneeded local `moduleTensorPullback_additive`. The retained
  `spaceDerivedPullback` abbreviates `derivedTensorPullback.{u,w,w}`, and its counit is
  the existing `smallTensorPullbackComplex.totalLeftDerivedCounit`. The new node's
  statement now describes comparison data and cites O3's landed node.
- H9: re-grep every retained full declaration name against live `lean/Sheaf` and
  `lean/WeilConjectures`; none is already declared. Importing O3 directly makes the
  repaired module itself a joint-import check.
- Advisory: reuse `moduleTensorComposition g f` from
  `Sheaf.AlgebraicGeometry.SpaceFlatDirectImageBaseChange`, removing the local chart
  composite, its triangle theorem, `moduleTensorPullbackComp_existsUnique`, and
  `moduleTensorPullbackComp`. The new node explicitly cites its owning theorem node.
- Compare the retained main theorem, hypercover, and coherent-system statements with
  their saved signatures and source clauses: there is no mathematical change. In the
  comparison node, the common universe is precisely the old functor's `{u,w,w}`
  specialization; no equality is imposed between the site and localization universes.
  Identity and arbitrary-composite maps, empty spaces, zero complexes, negative integer
  shifts, degree zero, and degeneracies are retained.

Lean instance search does not unfold `derivedTensorPullback` during the uniqueness
construction. The two comparisons therefore pass the existing totalLeftDerived and
its existing totalLeftDerivedCounit explicitly to leftDerivedUnique. This changes no
construction and introduces no additional theorem or assumption.

Validation after repair: all four delivered modules compiled cleanly using scompile.py,
with per-file times 13.3 s (SpaceDerivedPullback), 24.1 s (SpaceDerivedSystem),
9.7 s (SpaceFppfHypercover), and 7.1 s (SpaceNegativeExtHyperdescent). This includes
joint imports of the two landed constructions and the three-module consumer chain.
No compiler errors or unexpected warnings remained. Source checks confirmed 100-column
Lean lines, explicit variable/universe binders, the reduced declaration inventory, and
verbatim primary signatures. The item's only base-relative field changes are lean and
the authorized stmt_deps additions; its statement, proof and proof_deps are unchanged.

## Second reading by NN

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
