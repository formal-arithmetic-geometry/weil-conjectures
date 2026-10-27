## Worker report

The module `Sheaf.AlgebraicGeometry.DmLocallyQuasiFiniteAtlasTest` states
`CategoryTheory.locallyQuasiFinite_moduli_iff_etale_atlas`. Its only theorem proof
is `by sorry`; it introduces no definitions or axioms. The node statement and
proof are unchanged. Its `stmt_deps` gains the already landed definition node
`def-sfb-dm-stack-morphism-properties`, which owns the intrinsic predicate,
atlas predicate, diagonal and point-space vocabulary needed here. This addition
uses the brief's authorization to cite a landed definition instead of copying it.

Clause-by-clause correspondence:

- The base scheme is `{S : Scheme.{u}}`. All test schemes are `Over S`.
- The two DM stacks are `F : BasedCategory.{v₁, w₁} (Over S)` and
  `G : BasedCategory.{v₂, w₂} (Over S)` with exactly the hypotheses
  `hF : IsDeligneMumfordModuliStack F` and
  `hG : IsDeligneMumfordModuliStack G`. Their object and morphism universes
  are independent. The morphism over S is `f : BasedFunctor F G`.
- The initial stack, algebraic-space and 2-fibre-product conventions are the
  recorded `IsDeligneMumfordModuliStack`, `AlgebraicSpace`, `discreteModuli`,
  `BasedFunctor`, `ModuliTwoIso` and `moduliTwoFiberProduct` declarations.
  The stack fibre product is the actual iso-comma construction, retaining
  automorphisms; it is not an ordinary pullback of isomorphism classes.
- Clause (a) is the existing `IsLocallyQuasiFiniteModuliMap f`. Reading its
  full definition gives `IsLocallyFiniteTypeModuliMap f`,
  `ModuliSpaceTest @Scheme.Hom.IsLocallyQuasiFinite (moduliRelativeDiagonal f)`,
  and, for every field `K : Type u`, its S-structure `b`, field-valued target
  map `t` and fibre point `x`,
  `ModuliPointIsClosed (moduliTwoFiberProduct t f) ({x}ᶜ)`.
  The last clause says every singleton is open, exactly discreteness. Points
  are the existing quotient of field objects by field arrows and their
  equivalence closure; topology is detected by actual étale atlases.
  Local finite type is tested on étale atlases of every scheme base change,
  the equivalent DM presentation of the stated smooth-chart notion.
- Finite type and quasi-compactness in the opening paragraph are background
  conventions, not additional hypotheses or conclusions. The theorem does
  not require finite type, quasi-compactness, properness, separatedness or
  representability of f. It uses the library's intrinsic local-quasi-finite
  predicate without constructing another finite-type or point-space notion.
- Clause (b) is the universally quantified right side of the first `↔`:
  every `V`, every `v : discreteModuli (yoneda.obj V) → G`, every `U`,
  every `a : discreteModuli (yoneda.obj U) → moduliTwoFiberProduct v f`,
  and every compatible scheme map `p : U ⟶ V`. The notation here describes
  the `BasedFunctor` types spelled out in the file. `IsEtaleModuliMap a`
  is representability by algebraic spaces together with chartwise étaleness.
  There is no atlas or surjectivity hypothesis on a or v.
  The conclusion is the recorded Stacks-sense
  `Scheme.Hom.IsLocallyQuasiFinite p.left`.
- The compatibility hypothesis
  `Nonempty (ModuliTwoIso (a.comp (moduliTwoFiberFst v f))
    (discreteModuliMap (yoneda.map p)))`
  identifies p with the actual projection composite U → V. Quantification
  over all compatible p adds no mathematical assumption: Yoneda identifies
  the projection map into the discrete scheme groupoid with that scheme map.
- Clause (c) is the existential right side of the second `↔`, with the
  same V, v, U, a, p and actual projection comparison.
  `IsEtaleModuliAtlas v ∧ IsEtaleModuliAtlas a` requires both charts to be
  surjective. The final clause is again
  `Scheme.Hom.IsLocallyQuasiFinite p.left`.
- The conjunction `(a ↔ b) ∧ (a ↔ c)` expresses equivalence of all three
  conditions; it neither adds a fourth assertion nor drops an implication.

Dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `CategoryTheory.IsFibredInGroupoids`, `IsModuliStack`,
  `IsDeligneMumfordModuliStack`, `ModuliTwoIso`, `moduliTwoFiberProduct`,
  `moduliTwoFiberFst`, `discreteModuli`, `discreteModuliMap`,
  `HasSpaceBaseChange`, `IsRepresentableByAlgebraicSpaces`,
  `SpaceMapIsEtale`, `SpaceMapIsSurjective`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`:
  `AlgebraicGeometry.AlgebraicSpace`, its `IsEtale` and `IsSurjective`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType` and the recorded quasi-compactness
  convention; `Mathlib.AlgebraicGeometry.Morphisms.Etale`:
  `AlgebraicGeometry.Etale`; `Mathlib.AlgebraicGeometry.Morphisms.Smooth`:
  `AlgebraicGeometry.Smooth`, `SmoothOfRelativeDimension`.
- `WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism`:
  `AlgebraicGeometry.Scheme.Hom.IsQuasiFiniteAtPoint` and
  `IsLocallyQuasiFinite`. This includes finite type and is not replaced by
  Mathlib's weaker bare `LocallyQuasiFinite`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd` and
  `pullback.lift` for scheme fibre products in the proof plan.
- `Mathlib.Algebra.Field.Defs`: `Field`, the mathlib_match of `def-weil-field`.
- `Sheaf.AlgebraicGeometry.ModuliChartNormalization`:
  `CategoryTheory.IsEtaleModuliMap` and `IsSchemeModuliBaseChange`.
- `Sheaf.AlgebraicGeometry.DmStackMorphismProperties`:
  `CategoryTheory.IsLocallyQuasiFiniteModuliMap`,
  `IsLocallyFiniteTypeModuliMap`, `IsEtaleModuliAtlas`, `ModuliSpaceTest`,
  `moduliRelativeDiagonal`, `ModuliPoints`, `ModuliPointIsClosed`.

The file imports all presently recorded proof-dependency modules, as ordinary
imports: `StackChartwiseSmoothEtaleCalculus`,
`LocallyOfFiniteTypeOfIsLocallyQuasiFinite`, `QuasiFiniteAtPointIsolated`,
`IsolatedFiberPointQuasiFiniteAffinePairs`, `EtaleSpaceLocallyQuasiFinite`,
`SeparatedLqfBaseChange`, and `StackTopologyOpenSubstacks`. Their recorded
signatures and source docstrings were read. The currently unstated proof nodes
`lem-sfb-dm-etale-atlas-calculus`, `lem-sfb-stack-finite-type-calculus`,
`lem-sfb-dm-field-etale-chart-quasifinite`, and
`lem-sfb-dm-relative-diagonal-quasifinite` have no module to import; they are
retained in proof_deps and the theorem docstring, without assuming them as
hypotheses. No statement prerequisite is missing.

The theorem docstring carries all six proof steps, including the locally finite
 type check, isolation criterion, arbitrary nonsurjective charts, atlas choice,
relative-diagonal input, the projection-compatible three-base-change construction
of the field atlas, and descent of discreteness. Sources read locally:
`literature/stacks-project/stacks-morphisms.tex`, definitions and proofs at
Tags 06PU, 06UC and 06UF; the node's accepted DM specialization uses 06N3.

Edge cases checked before writing:

- Empty source and empty chart are allowed. The universal condition still
  includes all compatible maps, and no nonempty or inhabited hypothesis occurs.
- An empty target forces empty scheme charts in (c); no point is chosen.
- Disconnected and non-quasi-compact schemes and atlases are allowed; there
  is no finiteness bound on charts or components.
- A nonsurjective étale chart appears in (b) exactly as required; the two
  atlas surjectivity requirements occur only in (c).
- Positive-characteristic fields and arbitrary field extensions are allowed;
  no characteristic, perfection or algebraic-closedness assumption is added.
- Identity maps reduce to the usual local quasi-finiteness of étale charts.
  For the DM stack BG of an étale discrete group, stack automorphisms remain
  present; no representability of f is imposed. Positive-dimensional scheme
  maps over a field fail the discrete-fibre condition and the scheme chart test.
- A map U → V unrelated to the stack projection cannot be used, because both
  tests explicitly retain the projection 2-isomorphism.

Searches for an existing declaration (through the prescribed msearch wrapper):

- LeanFinder: "A morphism of Deligne Mumford stacks is locally quasi finite
  if and only if every etale scheme chart after scheme base change is locally
  quasi finite", and "Deligne Mumford stack locally quasi finite etale atlas
  criterion". The latter returned eight scheme-level hits, including
  `LocallyQuasiFinite`, `Scheme.Etale`, `Etale` and
  `LocallyOfFinitePresentation`; none states this DM stack equivalence.
- Loogle: "CategoryTheory.ModuliLocallyQuasiFinite,
  AlgebraicGeometry.LocallyQuasiFinite" returned zero hits and unknown
  identifier `CategoryTheory.ModuliLocallyQuasiFinite`.
- LeanSearch: "locally quasi finite morphism Deligne Mumford stack etale
  scheme presentation" returned eight scheme/ring-level hits including
  `LocallyQuasiFinite.mk` and `locallyQuasiFinite_iff`; no DM equivalence.
- Mathlib grep (CategoryTheory):
  `IsLocallyQuasiFiniteModuliMap|DeligneMumford|etale.*atlas.*quasi`
  returned zero hits.
- `rg` in `lean/WeilConjectures`, `lean/Sheaf` and
  `dag/lean_names_upstream.json` for the item id, the proposed theorem name
  and `IsLocallyQuasiFiniteModuliMap` found the intrinsic definition and
  downstream composition/coarse statements, but no existing atlas-test
  equivalence. This is why the existing predicate is reused and a new
  theorem statement is necessary.

Validation: prescribed `scompile.py Q01 lem-sfb-dm-lqf-atlas-test` compiled
both sandbox and library-path versions successfully (3.4 s and 3.3 s), without
errors or non-sorry warnings. `autoImplicit false` enforces explicit binders.
No statement correction, disputed statement, new node, or dependency module
was needed.

## Second reading by Q01

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
