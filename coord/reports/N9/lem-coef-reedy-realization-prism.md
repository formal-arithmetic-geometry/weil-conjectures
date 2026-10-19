## Worker report

The module `Sheaf.CategoryTheory.ReedyRealizationPrism` states
`CategoryTheory.SimplicialModelRealization.reedy_realization_prism` with `sorry`.
Its only additional declaration is the real construction `prismInclusion`: evaluation
of the tensor universal element at one of the two actual standard-interval vertices,
converted from a mapping-space vertex to an ordinary arrow by `homEquiv'.symm`.
No data are chosen from an existence theorem. There is one postponed theorem, exactly
the item; its docstring supplies the complete skeletal/SM7/prism proof plan.

Hypothesis and clause correspondence:

- The arbitrary simplicial model category is `{M : Type u} [Category.{v} M]
  [ModelCategory M] [HasLimits M] [HasColimits M]` with both
  `MorphismProperty.HasFunctorialFactorization` model pairs, `[SimplicialCategory M]`,
  `T : SimplicialTensorCotensor M`, and `SatisfiesSM7 M`. These are exactly the model
  convention of the recorded simplicial-model dependency, including completeness and
  functorial factorizations beyond Mathlib's finite-limit model-category convention.
- The two simplicial objects are `X Y : SimplicialObject M`. Their two Reedy-cofibrancy
  assumptions are `Reedy.leftClass (epimorphisms SimplexCategory).op (cofibrations M)
  (initial.to X)` and the identical condition for `Y`. The positive maps of the opposite
  simplex Reedy category are precisely the opposites of surjections. These are the
  recorded dependency's actual relative-latching cofibration tests on the initial map.
- For every `Z`, `realization T Z` is the existing explicit coequalizer of
  `relationLeft T Z` and `relationRight T Z`. Its diagonal summands are
  `T.tensor (SSet.stdSimplex.obj n) (Z.obj (op n))`; its relation summands range over
  every simplex operator. The left map applies `Z.map alpha.op` and the right map
  transposes `stdSimplex.map alpha` composed with the chosen tensor unit. This is
  exactly the formula in the item, including degeneracies, rather than fat realization.
- The first conjunct is `IsCofibrant (realization T X)`.
- The cylinder object is literally `T.tensor Δ[1] (realization T X)` throughout.
  Its inclusions are `prismInclusion T (realization T X) 0` and `... 1`. This evaluates
  `T.tensorUnit Δ[1] A` on `stdSimplex.objEquiv.symm (SimplexCategory.const [0] [1] i)`.
  The tensor representing property identifies this with the canonical tensor of the
  vertex map after `Δ[0] ⊗ A ≅ A`. There is no arbitrary endpoint or unit choice.
- The projection is the existing `SimplicialUndercategory.tensorCollapse T Δ[1] A`,
  the transpose of the constant identity family. This is tensoring with the unique
  `Δ[1] → Δ[0]` followed by the canonical unit identification.
- The next two conjuncts explicitly say `i_0 ≫ p = 𝟙 _` and `i_1 ≫ p = 𝟙 _`.
- `WeakEquivalence (tensorCollapse ...)` states exactly that the projection is weak.
- `Cofibration (coprod.desc i_0 i_1)` states exactly the coproduct-inclusion cofibration.
- Finally, for all `f g : X ⟶ Y` and each `_H : SimplicialObject.Homotopy f g`, there
  exists `h : T.tensor Δ[1] (realization T X) ⟶ realization T Y` with
  `i_0 ≫ h = map T f` and `i_1 ≫ h = map T g`. The Mathlib Homotopy is the exact
  combinatorial degree-raising prism family from the recorded dependency, including
  both outer-face equations and all face/degeneracy identities. In degree zero the
  edge has face 1 equal to `f_0` (vertex zero) and face 0 equal to `g_0` (vertex one),
  so the orientation of the two equations agrees with the item.

Dependency declarations read and reused:

- `Sheaf.CategoryTheory.SimplicialModelNerveLocalization`:
  `CategoryTheory.SimplicialModelLocalization.SatisfiesSM7` (and `cornerMap`), with
  the category/model/tensor convention of `CategoryTheory.simplicial_model_nerve_localization`.
- `Sheaf.CategoryTheory.SimplicialTensorCotensor`:
  `CategoryTheory.SimplicialTensorCotensor`, `.tensor`, `.tensorUnit`, and the
  existing `tensorMap` used by the realization and realization-map constructions.
- `Sheaf.CategoryTheory.ReedyModelStructure`:
  `HomotopicalAlgebra.Reedy.leftClass`, `relativeLatching`, `model_structure`, and
  `simplex_reedy_structure`, establishing the precise opposite-surjection convention.
- Mathlib's `SSet`, `SimplexCategory`, `SSet.stdSimplex`, and `stdSimplex.objEquiv`;
  `Mathlib.AlgebraicTopology.SimplicialObject.Homotopy`:
  `CategoryTheory.SimplicialObject.Homotopy`. The recorded extra-degeneracy source
  `ExtraDegeneracy.homotopy` and its hypotheses/section were read; only its underlying
  general combinatorial homotopy notion is needed here. `ExtraDegeneracy` is imported
  to retain the recorded dependency, not to assume an augmentation or contraction.
- `Sheaf.CategoryTheory.SimplicialModelRealization`:
  `CategoryTheory.SimplicialModelRealization.realization`, its summands and relation maps.
- `Sheaf.CategoryTheory.SimplicialModelRealizationMap`:
  `CategoryTheory.SimplicialModelRealization.map`, the canonical coequalizer descent.
- `Sheaf.CategoryTheory.SimplicialUndercategoryModel`:
  `CategoryTheory.SimplicialUndercategory.tensorTranspose` and `.tensorCollapse`.

The last three existing owning nodes were added to stmt_deps, as allowed for landed
nodes. No dependency interface was repaired and no new node was needed. The module
imports no downstream realization homotopy-invariance theorem.

Edge cases: degree zero has no lower latching objects and correctly requires `X_0`
cofibrant. The two distinct Fin 2 vertices are retained. The initial simplicial diagram
and constant diagrams are allowed whenever their stated Reedy conditions hold; there
is no nonempty or fibrancy hypothesis. Zero/initial realizations and equal maps are
allowed. Object universe u and hom/mapping-simplicial-set universe v remain independent;
all universes and variables are explicitly bound, with `autoImplicit false`.
Cofibrancy of Y is kept because the node assumes it, though the transfer construction
itself does not need that assumption. No disputed statement or correction.

Searches for an existing declaration (all through the prescribed search wrapper):

- LeanFinder: `Reedy cofibrant simplicial object tensor realization combinatorial
  homotopy cylinder` returned generic Cylinder cofibration/cofibrancy declarations,
  not this realization theorem.
- Loogle: `SimplicialObject, realization, Homotopy` returned zero hits (unknown
  identifier `SimplicialObject`).
- Mathlib grep: `realization|coend|tensorMap`, restricted to AlgebraicTopology,
  returned 12 hits for topological realization (`SSet.toTop`) and its properties,
  not arbitrary simplicial-model tensor realization.
- LeanSearch: `tensor realization takes simplicial homotopies to cylinder homotopies`
  returned `SSet.toTop`, relative simplicial-set homotopy and generic precylinder
  left-homotopy declarations, none with this statement.
- `rg` in upstream WeilConjectures and project lean/Sheaf for the item id,
  `tensorRealization|TensorRealization|reedyRealization|simplicialRealization`, followed
  by the exact names `reedy_realization_prism|prismInclusion`, found no exact theorem
  or conflicting new name. The project search found the already landed tensor
  realization and realization map, which are reused. `dag/lean_names_upstream.json`
  likewise has no collision for either name.

Source checked online: https://pages.uoregon.edu/ddugger/hocolim.pdf, formula (3.2)
printed p.9, skeletal pushout in Theorem 3.5 printed pp.10-11, and Section 19.1
printed p.90. These support the coequalizer, skeletal cofibrancy argument and SM7
respectively. As the node itself records, the combinatorial-prism transfer formulation
is agent-written; the docstring does not attribute it to a numbered Dugger theorem.

Validation: the prescribed `scompile.py N9 lem-coef-reedy-realization-prism` passed
for this module in both sandbox and actual library-path checks, with no diagnostics.


## Second reading by N9

I independently read the item node and its sandbox module, the eight
statement-dependency nodes and their recorded source declarations, and the node's
eight proof steps. There is no repair note for this item. No statement_change,
new definition node or dependency-module delivery is present or needed.

Source: I opened [Dugger's paper](https://pages.uoregon.edu/ddugger/hocolim.pdf)
independently, checking formula (3.2), the latching/skeletal discussion and pushout
in Theorem 3.5 (printed pp.9-11), and Section 19.1 (printed p.90). The initial
sections use topological spaces; Section 19.1 explicitly supplies the enriched
tensor/cotensor adjunctions and SM7 that generalize these constructions. The node
correctly labels its prism theorem as an agent argument, rather than a numbered
Dugger theorem or a Stacks result. There is no Stacks .tex source for this item.
The completeness/functorial-factorization convention is explicitly inherited from
lem-coef-simplicial-model-nerve-localization, not an added restriction borrowed
from the topological special case.

My object/hypothesis/conclusion checklist, with the file open:

1. Arbitrary simplicial model category M: `{M : Type u} [Category.{v} M]
   [ModelCategory M] [HasLimits M] [HasColimits M]`, the two displayed functorial
   factorization instances, `[SimplicialCategory M]`, `T : SimplicialTensorCotensor M`
   and `_hSM7 : SimplicialModelLocalization.SatisfiesSM7 M`. PASS. I read
   `cornerMap` and `SatisfiesSM7`, not merely the localization theorem's name:
   the corner uses actual pre/postcomposition, is Kan-fibrational and weak when
   either input is trivial. I also read `SimplicialTensorCotensor`: its universal
   elements give isomorphisms of enriched mapping simplicial sets, so it supplies
   the enriched adjunctions and tensor associativity used in the proof.
2. Two simplicial objects: `(X Y : SimplicialObject M)`. PASS: both are functors
   from the full opposite simplex category, with every face and degeneracy map.
3. Reedy cofibrancy of each: `_hX` and `_hY` are `Reedy.leftClass
   (MorphismProperty.epimorphisms SimplexCategory).op (cofibrations M)` on their
   initial maps. PASS. I read `LatchingIndex`, `latchingProjection`, `latchingTo`,
   `relativeLatching`, `leftClass`, `model_structure`, and `simplex_reedy_structure`
   in the recorded Reedy module. The positive maps for the opposite simplex
   category are opposite surjections, so these are the stipulated latching tests,
   not an objectwise-cofibrant substitute. Both assumptions are present even
   though the transfer of a homotopy does not require target cofibrancy.
4. Realization for every Z: the reused `realization T Z` is `coequalizer
   (relationLeft T Z) (relationRight T Z)`. PASS. I read `summand`, `Operator`,
   `relationSummand` and both relation maps. A relation is indexed by an arbitrary
   `alpha : [m] → [n]`; its tensor object is `T.tensor Δ[m] (Z.obj (op [n]))`.
   The left arrow is tensorMap of `Z.map alpha.op` into summand m, and the right
   arrow is tensorTranspose of `stdSimplex.map alpha` followed by the tensor
   universal element into summand n. Thus the node's exact coequalizer, including
   degeneracies, is reused. The reversal of written tensor order is the node's
   explicit convention, not a change of construction.
5. Cofibrant realization: `IsCofibrant (realization T X)`. PASS: the first conjunct.
6. Specified cylinder P_X and endpoints: every occurrence of the cylinder is
   literally `T.tensor Δ[1] (realization T X)` and the endpoint maps are
   `prismInclusion T (realization T X) 0` and `... 1`. PASS. I read
   `stdSimplex.objEquiv` and `SimplicialCategory.homEquiv'`: evaluating the tensor
   universal element on the constant `[0] → [1]` with value i and inverting the
   ordinary-arrow/vertex equivalence gives precisely the canonical endpoint map
   under the tensor-unit identification. This is actual data, with no existence
   witness, arbitrary arrow or extra chosen isomorphism.
7. Specified projection p: `SimplicialUndercategory.tensorCollapse T Δ[1]
   (realization T X)`. PASS. In the recorded module it is `tensorTranspose` of
   `SSet.const (homEquiv' _ _ (𝟙 _))`; I read the transpose construction using the
   inverse enriched representing isomorphism. Hence this is collapse along the
   unique simplicial map to Δ[0], with the canonical unit identification.
8. Both cylinder retraction identities: the second and third conjuncts explicitly
   assert `prismInclusion ... 0 ≫ tensorCollapse ... = 𝟙 _` and the identical
   equation at 1. PASS, correct composition order in Lean.
9. Projection weak equivalence: `WeakEquivalence (tensorCollapse ...)`. PASS.
10. Coproduct endpoint cofibration: `Cofibration (coprod.desc
    (prismInclusion ... 0) (prismInclusion ... 1))`. PASS: the source is the actual
    coproduct of two copies of |X|, not separate cofibration tests on each leg.
11. Arbitrary maps and each combinatorial homotopy: `∀ (f g : X ⟶ Y)
    (_H : SimplicialObject.Homotopy f g), ∃ h : T.tensor Δ[1] (realization T X)
    ⟶ realization T Y, ...`. PASS: the quantifier order is exactly the node's.
    I read Mathlib Homotopy's data and all seven identity fields at lines 48-67,
    and ExtraDegeneracy's section and homotopy at its recorded source. The former
    is precisely the general combinatorial notion, without assuming that a given
    homotopy comes from an augmentation or extra degeneracy.
12. Both restrictions: `prismInclusion ... 0 ≫ h = map T f` and
    `prismInclusion ... 1 ≫ h = map T g`. PASS. I read the realization-map module's
    `mapLeg`, `map_condition` and `map`: these are tensoring the components of the
    specified map followed by canonical coprojections and coequalizer descent.
    Homotopy's `h_last_comp_δ_last` is f at the all-zero end and
    `h_zero_comp_δ_zero` is g at the all-one end, agreeing with the vertices 0/1.

Edge cases: at n=0 the opposite-simplex latching category is empty, and the
Reedy condition demands cofibrancy of X_0 (and Y_0). The prism has one edge with
last face f_0 at vertex zero and zeroth face g_0 at vertex one, so endpoint order
is retained there too. Initial or zero diagrams, initial realizations, constant
diagrams satisfying the given Reedy tests, equal maps and constant homotopies
are admitted. No nonempty indexing, fibrancy, pointedness, additivity, field,
characteristic, Noetherian or finiteness assumptions occur. Empty schemes are
not an extra case of this abstract category statement. The simplex category is
small, simplicial sets are in the mapping-space universe v, and u and v remain
independent. Every binder and universe is explicit under autoImplicit false;
there is no hidden let, local notation, private notion or universe equality.

Independent searches (different queries from the first reader):

- LeanFinder via msearch: `coend realization Reedy cofibrant simplicial model
  category cylinder prism`. Eight hits, all generic Cylinder constructions and
  properties; no tensor-realization/prism theorem.
- Loogle via msearch: `CategoryTheory.SimplicialObject.Homotopy`. Twelve hits,
  including the exact existing Homotopy structure and its endpoint fields,
  reflexivity and pre/postcomposition, but no realization-transfer theorem.
- LeanSearch via msearch: `The realization of a Reedy cofibrant simplicial object
  in a simplicial model category is cofibrant and simplicial homotopies give
  cylinder homotopies`. Eight hits: generic cylinder/cofibrant-replacement and
  Kan-model facts. Cylinder.LeftHomotopy takes a cylinder as input and does not
  construct the specified tensor cylinder or realize combinatorial homotopies.
- Direct rg in Mathlib, upstream WeilConjectures, project lean/Sheaf, and
  dag/lean_names_upstream.json: `prismInclusion|reedy_realization_prism|realization.*
  [Cc]ofibrant|[Cc]ofibrant.*realization|[Pp]rism.*[Rr]ealization|[Rr]ealization.*
  [Pp]rism` (the actual regex is continuous). No name collision or exact match.
  Project hits included ReedyRealizationHomotopyInvariance and
  SimplicialRealizationExtraDegeneracy; I opened both. They state downstream
  weak-equivalence results and explicitly use this prism argument, not its
  conclusion as an existing declaration. Other hits were proof prose about
  topological realizations. Existing realization, realization-map and collapse
  constructions are reused, as required by H4.

Mismatches and repairs:

- No mismatch in objects, hypotheses, clauses, strength or quantifier order.
  The original Lean signature and the node's natural statement are unchanged.
- H8: the original four-step docstring compressed the node's eight steps and
  omitted the adjunction-of-lifting-squares argument, precise sequential-colimit
  closure, overlap gluing and generator checks. I replaced it with eight steps
  following the node, naming every proof dependency. The cylinder proof now
  follows the node's endpoint-horn/two-out-of-three argument explicitly.
- Proof imports: I added non-public imports of KanQuillenRightProper,
  RightPrismBoundary and SmallDirectColimitLifting, plus the Mathlib lifting-class
  closure and colimit modules, so available recorded proof dependencies are
  explicitly present. The skeletal-pushout node has no recorded declaration yet,
  so there is no module to import for it. It is a proof prerequisite only and
  is not needed to state the item. No downstream module was imported.
- There are no new definition nodes or dependency modules to audit under H12/H13.
  The worker's three added stmt_deps are already landed owning nodes for the
  actual constructions used above; all other non-Lean fields are unchanged.
- The helper's body is a real evaluation/conversion construction. There is only
  one postponed theorem, the item itself, with proof `sorry`; nothing is proved.

Validation: after these repairs, scompile.py N9 lem-coef-reedy-realization-prism
compiled the only delivered file separately in sandbox and actual library path
(1.6 s and 1.8 s), with no diagnostics. A direct text comparison confirms that
lean.statement is verbatim the theorem signature; all lines are at most 100
characters. The prescribed server preflight/delivery dry run follows below.
