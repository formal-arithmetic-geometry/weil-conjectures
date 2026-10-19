## Worker report

The module [FramedHornCriterion.lean](lean/Sheaf/CategoryTheory/FramedHornCriterion.lean)
defines the simplicial coend diagram `framedHornCoendDiagram`, its colimit
`framedHornCoend`, the induced maps `framedHornCoendMap` and
`framedHornCoendMapObj`, the framed resolution structure `FramedHornResolution`,
and the boundary map `framedHornCorner`. It states `framed_horn_criterion` with
`sorry` as its proof.

The theorem binds a model category `C` with limits, colimits, and both functorial
model factorizations, and an arrow `s : A ⟶ B`. Its first conjunct gives framed
resolutions of `A` and `B`, a map between them, the Reedy cofibration condition,
and the augmentation square. The second conjunct gives simultaneous choices for
every small family `I → Arrow C`. The third conjunct states cofibration of each
boundary corner and cofibrancy of the simplex and boundary coend objects. The
last conjunct states that, for every fibrant `Z`, both framed function complexes
are Kan, the induced map is a Kan fibration, its trivial-fibration condition is
equivalent to lifting against every boundary corner, and this is equivalent to
its weak homotopy equivalence.

The dependency declarations used are:

- `Sheaf.CategoryTheory.CosimplicialFrameMapping`, including
  `CategoryTheory.CosimplicialFrame` and `CategoryTheory.frameHom`/`frameHomPre`.
- `Sheaf.CategoryTheory.ReedyModelStructure`, including
  `HomotopicalAlgebra.Reedy.leftClass` and the Reedy conventions.
- `Sheaf.AlgebraicTopology.KanQuillenRightProper`, including the Kan--Quillen
  lifting classes and weak homotopy equivalences.
- Mathlib `CategoryTheory.Functor.Elements` and simplicial boundaries.

Edge cases checked in the statement are `n = 0` (the boundary is the empty
subcomplex), empty indexing families, and arbitrary arrows including identities.
The coend index uses the full category of elements, so degenerate simplices and
all simplex operators remain included.

Searches made: `rg` over `WeilConjectures/` and `lean/Sheaf/` for
`lem-cbc-framed-horn-criterion`, `cosimplicial frame`, `framed horn`, `coend`,
and `relativeLatching`; Mathlib grep for coends, simplicial tensors, and horn
corner APIs; and the prescribed LeanSearch/Loogle/LeanFinder searches recorded
in the node's `mathlib_searches`. No existing declaration states this criterion.

The file compiles cleanly with `scompile.py`; the only postponed proof is
`CategoryTheory.framed_horn_criterion`.

## Earlier second reading (a previous round; superseded)

I reread the node statement and the completed module. The model-category hypotheses,
arrow `s`, simultaneous small-family clause, boundary-indexed cofibration and
cofibrancy clauses, and every fibrant-target mapping-space equivalence all appear
in the theorem signature. The helper declarations render the coend, augmentation,
Reedy cofibration, and boundary map used by those clauses. The file was recompiled
with `scompile.py` after the final edits and is warning-free.

## Second reading by N2

I read the node and the source independently of the worker's rendering. The source
is Hirschhorn, not a Stacks tag. I opened the linked book at Definition 3.3.8(1),
Proposition 3.3.9(1), Lemma 3.3.11(1), Definition 16.3.1, Proposition 16.1.22(1),
Corollaries 16.3.11(1) and 16.5.4(1), Theorem 17.8.4(2)-(3), and Propositions
17.8.8(2)-(3) and 17.8.14(1). The hypotheses throughout are a model category;
there is no enrichment, properness, combinatoriality, or endpoint-cofibrancy
hypothesis on the original arrow. The source confirms the node as written.
[Hirschhorn's book](https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/pshmain.pdf)
is the source read; no change to the node's mathematical statement is needed.

Object, hypothesis, and conclusion checklist (each verdict refers to the final file):

1. An arbitrary complete and cocomplete model category, with the functorial
   factorization convention: `C : Type u`, `[Category.{v} C]`, `[HasLimits C]`,
   `[HasColimits C]`, `[ModelCategory C]`, and both
   `MorphismProperty.HasFunctorialFactorization` instances. Verdict: exact.
   I opened `lem-coef-cosimplicial-frame-mapping` and its module: those are its
   conventions. Mathlib's model-category class alone gives only finite limits
   and colimits, so the completeness binders are necessary.
2. The derived localization convention: `K : SSet.{max u v t}`, the actual
   `q : FiniteReedy.largeNerve C ⟶ K`, and
   `hq : FiniteReedy.IsLocalization (weakEquivalences C) q`. Verdict: exact
   parametrization of the localization implicit in the node's Map^h notation.
   I read `FiniteReedy.IsLocalization` and `object`, `frameSpaceQ`,
   `frameHomLarge`, `frameQEdge`, and `FrameMappingRelation`, including the
   latter's actual evaluation-map equality. No arbitrary precomposition map
   replaces the canonical one.
3. Any original arrow: `{A B : C} (s : A ⟶ B)`. Verdict: exact; neither endpoint
   is assumed cofibrant or fibrant.
4. Reedy-cofibrant cosimplicial resolutions with objectwise weak augmentations:
   `FramedHornResolution.obj`, `.augmentation`, `.augmentation_weak`, `.latching`,
   and `.latching_cofibration`. Verdict: exact. The canonical proper-face
   diagrams/cocones are the dependency's `frameLatchingDiagram` and
   `frameLatchingCocone`, whose signatures I opened. Its `CosimplicialFrame`
   additionally fixes degree zero and normalizes its augmentation, so it is not
   directly a resolution of an arbitrary noncofibrant original object.
5. A Reedy-cofibration arrow of resolutions commuting with s: the first
   existential binds `RA`, `RB`, and `s'`; its two clauses are
   `Reedy.leftClass (monomorphisms SimplexCategory) (cofibrations C) s'` and
   `RA.augmentation ≫ (Functor.const _).map s = s' ≫ RB.augmentation`.
   Verdict: exact. I opened `Reedy.relativeLatching`, `Reedy.leftClass`, and
   `simplex_reedy_structure`: the positive simplex maps are monomorphisms.
6. Simultaneous small-family choices: `∀ (I : Type w) (S : I → Arrow C), ∃ RA RB s',
   ∀ i, ...` includes both the same relative-latching condition and the square
   for `(S i).hom`. Verdict: exact, including the augmentation squares the
   original worker omitted. No colimit over I is formed.
7. The coend in a simplicial set K: `framedHornCoendDiagram A K` followed by
   its actual `colimit`; the index is `K.Elementsᵒᵖ`, not merely the face poset.
   `framedHornCoendMap` and `framedHornCoendMapObj` are the two induced colimit
   maps. Verdict: exact; all simplex operators and degeneracies impose the
   coend relations. K lives in the hom-set universe v, whose colimits exist
   by cocompleteness; `hasColimitsOfSizeShrink` supplies the mixed index sizes.
8. The boundary pushout corner: `framedHornCorner s' n` has domain
   `pushout (framedHornCoendMap RA.obj (SSet.boundary n).ι)
   (framedHornCoendMapObj s' (SSet.boundary n))` and codomain
   `framedHornCoend RB.obj (SSet.stdSimplex.obj ⦋n⦌)`; its body is the canonical
   `pushout.desc` on the two coend maps. Verdict: exact after repair.
9. Every such corner is an original cofibration with cofibrant endpoints:
   the third conjunct binds arbitrary `RA`, `RB`, `s'`, then assumes their
   Reedy-cofibration condition and augmentation square; its `∀ n` clause is
   `Cofibration (framedHornCorner s' n)` and `IsCofibrant` of the actual pushout
   domain and simplex codomain. Verdict: exact. The original claim for every
   arbitrary s' was stronger and false; the necessary restrictions are now
   present. The unrelated extra boundary-object-cofibrancy conclusion was removed.
10. For every originally fibrant Z: `∀ Z, IsFibrant Z → ...` gives the two
    `SSet.KanComplex (frameHom ... Z)` clauses and
    `SSet.modelCategoryQuillen.J.rlp (frameHomPre s' Z)`. Verdict: exact Kan
    objects and Kan fibration. I opened the recorded Kan--Quillen declaration:
    J is horn lifting and I is boundary lifting, including dimension zero.
11. Representation of the actual derived map from B into A: existential
    comparison isomorphisms `cA` and `cB` from the large strict complexes to
    the localized mapping spaces, with `FrameMappingRelation K (frameQEdge q s)
    (K.σ 0 (FiniteReedy.object q Z)) ... cA.inv
    (cB.inv ≫ frameSpaceQ.map (frameHomLargePre s' Z))`.
    Verdict: exact; the relation specifies the canonical precomposition action
    through the two evaluation maps, rather than only unrelated isomorphic
    mapping objects. This clause was absent from the worker's rendering.
12. Trivial Kan fibrancy iff lifting against every boundary corner:
    `I.rlp (frameHomPre s' Z) ↔ ∀ n, HasLiftingProperty
    (framedHornCorner s' n) (terminal.from Z)`. Verdict: exact.
13. The further equivalence with the derived mapping equivalence:
    `SSet.Enhanced.IsWeakHomotopyEquivalence (frameHomPre s' Z) ↔ I.rlp ...`.
    Together with item 11, this is exactly equivalence of the derived map.
    Verdict: exact, using the dependency's realization-based weak equivalence.
14. The final clause: under those equivalent conditions, `∀ n, ∃ e` between
    the localized mapping spaces from the corner codomain and its actual
    pushout domain into Z, with `FrameMappingRelation` for
    `frameQEdge q (framedHornCorner s' n)` and the degenerate edge at qZ,
    using `(𝟙 _)` and `e.hom`. Verdict: exact. The evaluation-map relation fixes
    e to be the induced restriction map. This conclusion was entirely missing
    from the original worker statement and is now included.

Edge cases: n = 0 is included in each `∀ n : ℕ`; Mathlib `SSet.boundary_zero`
identifies its boundary with the empty subcomplex, and the coend then has an
empty index category. The corner domain is the pushout along the initial
boundary coend, so the corner reduces up to its canonical isomorphism to the
zero-degree arrow. The family I may be empty (no `Nonempty` assumption).
The terminal category, an initial/zero object when present, arbitrary identity
and zero arrows, and empty mapping spaces are not excluded. Schemes and
characteristic play no role. Object universe u, hom universe v, localization
bound t, and family universe w remain independent; the old need for all
u-indexed colimits has been removed. No equality between universes is imposed.

Independent searches used different terms from the worker's report. The prescribed
LeanFinder query `framed horn criterion` returned ordinary simplicial horn filler
lemmas; Loogle `framedHornCoend` found no declaration. LeanSearch queried a
cosimplicial-object/simplicial-set tensor as a colimit over simplices and returned
Mathlib's generic `Limits.coend`, ordinary cosimplicial-object APIs, and standard
simplicial objects. The generic coend is a multicoequalizer of a bifunctor, not
an existing cosimplicial-tensor or framed-horn criterion; the module's coend
helper specifies this tensor by its equivalent simplex colimit. A further
LeanFinder search used relative latching, boundary pushout corners, cofibrant
domains, and homotopy orthogonality. `rg` searches of Mathlib, the upstream
`WeilConjectures` tree, and project `lean/Sheaf` for coends, relative latching,
cosimplicial tensors/resolutions, and framed horns found no exact statement or
existing tensor for arbitrary model categories. Project coend realizations
such as `PinchedRigidification.realization` have a fixed SSet-valued resolution
and do not define this arbitrary-C tensor. No module can be replaced by an
`existing: true` match. No new DAG nodes or dependency modules were needed.

Repairs made: replaced the false simplex-only corner with the boundary pushout;
used the recorded relative-latching class directly and removed the private
Reedy-cofibration predicate; restricted the universal consequences to compatible
Reedy-cofibration arrow resolutions; restored each family augmentation square;
replaced inappropriate object-universe colimits with the dependency's complete/
cocomplete conventions and hom-universe coend; added the actual derived-map
comparison and final boundary-corner equivalence; removed the extra
boundary-object-cofibrancy assertion; expanded the docstring to all six DAG proof
steps and added the available proof-dependency imports. The mathematical node
statement was already correct, so there is no `statement_change`.

All constructions contain real data. The pushout compatibility follows from
componentwise naturality and the colimit universal property inside the actual
construction; no additional postponed theorem is introduced. The only `sorry`
is `CategoryTheory.framed_horn_criterion`. The final module was compiled through
`scompile.py` with no errors or warnings; `autoImplicit` is false and every
universe/variable is explicitly bound. The node's `lean.statement` is the
verbatim theorem signature. The unstated proof prerequisite
`lem-coef-infinity-yoneda-presheaf-limits` has no recorded module, so it has no
import yet; every proof prerequisite with a recorded module is imported.
