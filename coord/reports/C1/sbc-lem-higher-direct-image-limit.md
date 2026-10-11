## Worker report

The module `Sheaf.AlgebraicGeometry.HigherDirectImageLimitSystem` states
`AlgebraicGeometry.Etale.isIso_higherDirectImage_limit_system`, with proof `sorry`.
It renders Stacks Lemma 59.51.7 (https://stacks.math.columbia.edu/tag/09Z1), which was
opened and read. No correction to the item's mathematical statement is necessary.
The upstream `Etale.higherDirectImage_limit` was read in full: it is only the case
of sheaves pulled back from one fixed sheaf, on stalks, so cannot be recorded as
an existing declaration for this general system statement.

Hypothesis and clause correspondence:

- `S : Scheme.{v}` is the arbitrary base scheme.
- `I : Type v`, `[Preorder I]`, `[IsDirected I (· ≤ ·)]`, `[Nonempty I]`
  give the nonempty directed index set of Stacks' inverse-system convention.
  The index lives in the schemes' universe.
- `D : Iᵒᵖ ⥤ Over S` gives the schemes X_i over S, their structure maps
  `(D.obj (op i)).hom`, their transition maps `(D.map f.op).left`, and
  all the over-S commutative triangles.
- The `IsAffineHom` binder is precisely affinity of every transition morphism.
- The two stagewise binders are quasi-compactness and quasi-separatedness of g_i.
- `c : Cone D` and `hc : IsLimit ((Over.forget S).mapCone c)` give the actual
  scheme limit X, with projection `(c.π.app (op i)).left` and structure map
  `c.pt.hom`. Its two property binders are precisely the qcqs assumptions on g.
- `F i : Sheaf (D.obj (op i)).left.smallEtaleTopology AddCommGrpCat.{v+1}`
  is an arbitrary abelian etale sheaf F_i, with no torsion condition.
- `φ f` has exactly type f_{ji}^{-1} F_i → F_j. `hφid` and `hφcomp`
  impose the identity and composition compatibility through the standard
  `upperStarId` and `upperStarComp` identifications. `HEq` only transports
  along the scheme-diagram functor's identity/composition equalities;
  the corresponding source objects are propositionally equal.
- `H`, `eH`, `hH` present the diagram f_i^{-1}F_i: `eH` identifies its objects
  and `hH` fixes each map to the pullback of φ, using the limit cone equation.
  `[HasColimit H]` selects its existing sheaf colimit; `colimit H` is F.
- `p : ℕ` ranges over exactly all p ≥ 0. Each higher direct image is written
  as degree-p homology of the recorded derived direct image of F_i[0].
- `K`, `eK`, `hK` present the diagram R^p g_{i,*}F_i, with its actual canonical
  maps (the new `abelianHigherDirectImageMap`, not unspecified transitions).
  `[HasColimit K]` selects the colimit in sheaves on S.
- `η` is the comparison cocone to R^p g_*(colimit H); `hη` fixes each leg
  to the canonical higher-direct-image map applied to the colimit inclusion,
  transported through `eH`. Thus it is not an arbitrary map hypothesis.
- `IsIso (colimit.desc K (Cocone.mk _ η))` says exactly that the canonical
  arrow colim_i R^p g_{i,*}F_i → R^p g_* F is an isomorphism of abelian sheaves.

The explicit diagram presentations `H`, `K`, `η` impose no extra mathematical
condition: for every compatible sheaf system their objects and maps are the
ones displayed, and the identity/composition and cocone laws follow from the
adjunction coherence and the compatibility of φ. They allow the statement to
use Mathlib's Functor and colimit API without new duplicate system definitions.
Similarly `HasColimit` is available for these directed diagrams in the
Grothendieck abelian sheaf categories. No tautological geometric assumption,
no arbitrary comparison map, and no fixed-origin restriction is used.

Dependency declarations read and used:

- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.lowerStar`, `upperStar`,
  `upperStarLowerStarAdjunction`, and `upperStarComp` (imported transitively).
- `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence`:
  `AlgebraicGeometry.Etale.rightDerivedLowerStarPlus`; the same recorded
  derived-direct-image functor is written with its generic `R+` notation.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence`:
  `AlgebraicGeometry.Etale.upperStarId`.
- `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs`:
  `AlgebraicGeometry.Etale.upperStarPlusComp`.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction`:
  `CategoryTheory.Adjunction.derivedPlus`, the bounded-below adjunction
  without extraneous monoidal hypotheses. The module-specific upstream
  `derivedUpperStarLowerStarAdjunctionPlus` unnecessarily requires monoidal
  coefficients; using this generic construction gives the same adjunction
  and works for abelian groups.
- The etale-sheaves dependency's recorded category is Mathlib's
  `CategoryTheory.Sheaf T.smallEtaleTopology AddCommGrpCat.{v+1}`; its additional
  constructible/set-valued predicates are not used here. The dependency module
  `Sheaf.AlgebraicGeometry.EtaleSheaves` and its docstrings were read.
- The scheme-conventions dependency defines no new declaration; its `Scheme`,
  `QuasiCompact`, `QuasiSeparated`, and `IsAffineHom` meanings are the Mathlib
  classes used here.

Edge cases checked before writing: p=0 gives ordinary direct image and filtered
colimits; a singleton index gives the identity comparison; all zero sheaves
produce zero on both sides; empty schemes remain admitted; transition φ may
be zero or noninvertible (there is no cartesian-sheaf assumption). An empty
index is excluded by the source's directed-system convention. No characteristic,
Noetherian, torsion, separation-of-the-base, or affine-stage restriction is added.

Searches made using `/home/ubuntu/weil-launcher/msearch.py`:

- LeanFinder, “Higher direct images commute with limits of schemes with affine
  transition maps for a compatible system of abelian etale sheaves”: eight
  affine-limit results, no higher-direct-image theorem.
- Loogle, `NatTrans.rightDerived, Functor.rightDerived`: zero hits, unknown
  identifier. The actual Mathlib right-derived API was subsequently read.
- Mathlib grep, `higherDirectImage.*limit|higher direct image.*limit`, in
  AlgebraicGeometry: zero hits.
- LeanSearch, “canonical transition map higher direct images abelian etale
  sheaves varying scheme”: unavailable (Internal Server Error), logged as such.
- LeanFinder, “canonical morphism between higher direct images of abelian
  sheaves induced by a commutative triangle of schemes and a map from inverse
  image”: eight underived pushforward results, no matching transition definition.
- Mathlib grep, `higherDirectImageTransition|higherDirectImageMap`: zero hits.
- `rg` in the upstream project found the already-read module-valued
  `higherDirectImageTransition` and its fixed-origin limit theorem; neither
  accepts abelian-group coefficients for this statement.
- `rg` in `lean/Sheaf` and `dag/lean_names_upstream.json` found no general
  abelian transition definition or theorem of this strength. DAG concept
  search via `tools/blueprint_refs.py search 'higher direct image transition'`
  returned zero nodes; broader search and grep were also inspected.

Both modules compile together on the server with no errors or warnings in
7.3 seconds. The sole theorem proof remains `sorry`; the new definition has
fully specified data and no `sorry`. No statement dispute was found.

## New nodes

`def-sbc-abelian-higher-direct-image-map` defines the canonical comparison
R^p h_*F → R^p h'_*F' attached to a commutative triangle and φ:a^{-1}F→F'.
Its module is `Sheaf.AlgebraicGeometry.AbelianHigherDirectImageMap`, declaration
`AlgebraicGeometry.Etale.abelianHigherDirectImageMap`. Source: Stacks Tag 09Z1,
canonical arrows in the directed system and its comparison to the limit.
The definition takes degree-p homology of the derived adjunction unit, the
pullback composition identification, the pullback of the derived counit,
the single-complex identification, and φ[0]. It uses the existing derived
pushforward and inverse image, without redefining either. The searches listed
above show no existing DAG notion or declaration for abelian coefficients;
the upstream analog is restricted to ModuleCat coefficients. Its naturality
proofs are not asserted in stage 2 and no proof data is postponed inside it.

## Second reading by C1

I independently compared the node with the source statement and the Lean signature.
The base scheme (S) is rendered by `{S : Scheme.{v}}`; the directed nonempty index
set is `{I : Type v}` with `[Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]`, and
its inverse diagram over (S) is `D : Iᵒᵖ ⥤ Over S`. Affine transitions are the
binder `∀ ... IsAffineHom (D.map f).left`; stagewise qc and qs are the two binders
on `(D.obj i).hom`, and the limit cone and its qcqs structure morphism are `c`,
`hc`, `[QuasiCompact c.pt.hom]`, and `[QuasiSeparated c.pt.hom]`.

The sheaf system is `F` together with `φ`; `hφid` and `hφcomp` render identity and
composition compatibility using `upperStarId` and `upperStarComp`. The projections
and colimit sheaf are rendered by `H`, `eH`, `hH`, `[HasColimit H]`, and `colimit H`.
For each `p : ℕ`, `K`, `eK`, and `hK` render the degree-(p) higher direct-image
system; its transition arrows are the canonical
`abelianHigherDirectImageMap` (the added dependency
`def-sbc-abelian-higher-direct-image-map`). Finally `η`, `hη`, and
`IsIso (colimit.desc K (Cocone.mk _ η))` render the canonical comparison and its
isomorphism. Every object, hypothesis, and conclusion clause of the node is present;
the explicit diagram presentations only expose the canonical data needed by the
Functor/colimit API and introduce no mathematical restriction.

Edge cases checked: `p = 0`, a singleton directed index, zero sheaves and zero
transition maps, empty schemes, and arbitrary characteristic are admitted; the
empty index is excluded by the source's nonempty directed-system convention. The
index universe is `Type v`, matching the scheme universe. No Noetherian, torsion,
affine-stage, or separation-of-base assumption was added.

Searches independently confirmed no matching general abelian higher-direct-image
transition or limit theorem in Mathlib, `WeilConjectures`, or `lean/Sheaf`; the
upstream fixed-origin module-valued theorem is a strictly narrower statement.
The only mismatch found was that the newly introduced transition-map notion was
not listed in the item's `stmt_deps`; I added
`def-sbc-abelian-higher-direct-image-map`. No Lean source change was needed.
