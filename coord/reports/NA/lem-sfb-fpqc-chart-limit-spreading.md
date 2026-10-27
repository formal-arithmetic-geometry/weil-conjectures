## Worker report

The module `Sheaf.AlgebraicGeometry.FpqcChartLimitSpreading` states
`AlgebraicGeometry.exists_fpqc_chart_of_isLimit`, with one `sorry` and no new
definitions. The node is unchanged except for its `lean` record. No new nodes,
dependency repairs, or statement corrections are required. No statement dispute
was found.

Hypotheses and clauses, in their node order:

| Node text | Lean rendering |
| --- | --- |
| Affine schemes S and A | `S A : Scheme.{u}`, `[IsAffine S]`, `[IsAffine A]` |
| Flat, surjective, quasi-compact p : A → S | `p : A ⟶ S`, `[Flat p]`, `[Surjective p]`, `[QuasiCompact p]` |
| Contravariant set-valued functor on S-schemes | `F : (Over S)ᵒᵖ ⥤ Type (max u v)` |
| Covering equalizer condition for all fpqc coverings | `hF : Presheaf.IsSheaf (Scheme.fpqcTopology.over S) F` |
| F_A represented by an A-scheme P | `P : Over A`, `hP : Nonempty (((Over.map p).op ⋙ F).RepresentableBy P)` |
| P/A quasi-separated and locally of finite presentation | `[QuasiSeparated P.hom]`, `[LocallyOfFinitePresentation P.hom]` |
| Small nonempty directed set I | `I : Type u`, `[Preorder I]`, `[IsDirected I (· ≤ ·)]`, `[Nonempty I]` |
| Inverse system of affine S-schemes | `D : Iᵒᵖ ⥤ Over S`, `[∀ i : Iᵒᵖ, IsAffine (D.obj i).left]` |
| Its specified limit T and projections | `c : Cone D`, `hc : IsLimit c`; T is `c.pt.left`, its S-map is `c.pt.hom`, and projections are `(c.π.app (op i)).left` |
| F_T represented by Y, with its representation | `Y : Over c.pt.left`, `hY : ((Over.map c.pt.hom).op ⋙ F).RepresentableBy Y` |
| Specified open subscheme V of Y | `V : Over c.pt.left`, `j : V ⟶ Y`, `[IsOpenImmersion j.left]` |
| V/T of finite presentation | `[LocallyOfFinitePresentation V.hom]`, `[QuasiCompact V.hom]`, `[QuasiSeparated V.hom]` |
| Some stage i and T_i-scheme V_i | Existentials `i : I`, `Vi : Over (D.obj (op i)).left` |
| Map h_{V_i} → F_{T_i} | `α : uliftYoneda.{v}.obj Vi ⟶ (Over.map (D.obj (op i)).hom).op ⋙ F` |
| V_i/T_i of finite presentation | `LocallyOfFinitePresentation Vi.hom ∧ QuasiCompact Vi.hom ∧ QuasiSeparated Vi.hom` |
| Chart map representable by open immersions on every scheme test | `(MorphismProperty.over (@IsOpenImmersion)).relative uliftYoneda.{v} α` |
| Specified isomorphism V_i ×_{T_i} T ≅ V | `g` is an S-morphism from V to V_i and `IsPullback g.left V.hom Vi.hom (c.π.app (op i)).left` |
| Base-changed map is the specified inclusion | `F.map g.op (uliftYonedaEquiv.{v} (F := (Over.map (D.obj (op i)).hom).op ⋙ F) α) = hY.homEquiv j` |
| Quasi-affine choice when V is quasi-affine | `V.left.IsQuasiAffine → Vi.left.IsQuasiAffine` for the same witnesses |
| No representability of F_{T_i} | There is no such assumption or existential representation of that functor |

The cartesian-square encoding is equivalent to the required isomorphism over T,
including the map to V_i: V itself is the specified pullback object. Equality
of sections on V is equality of the natural transformations out of h_V by
Yoneda. Thus the last equality preserves the inclusion, rather than asserting
only an isomorphism of underlying schemes. The S-coordinate of g is part of
its `Over S` type, and its T_i-coordinate is imposed by the cartesian square.
The representation hY is explicit because the node refers to the specified
inclusion under that representation. Nonempty hP carries only the assumed
existence of a representation, since its choice is irrelevant to the conclusion.

The fpqc topology on `Over S` is Mathlib's induced topology. Its sheaf condition
is equivalent to the covering equalizer condition for the fpqc precoverage,
since schemes have pullbacks. The section-valued chart map is a map of fpqc
sheaves: representables are fpqc sheaves by subcanonicity, and restriction to
a slice preserves this covering equalizer condition. The full natural
transformation on underlying presheaves therefore encodes precisely that map.

The lifted Yoneda functor permits an independent value universe v while keeping
all scheme-test universes fixed at u. Enlarging the set universe to `max u v`
loses no set-valued functor (a smaller-valued one has its equivalent lifted
version), and `RepresentableBy` itself permits arbitrary value universes. The
index universe is u, as required for scheme limits in the project. A preorder
is the directed-set encoding used by the existing limit dependencies; no
linearity, countability, least element, or stage representability is imposed.

Dependency declarations used (read with their signatures and documentation):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.AffineScheme`: `AlgebraicGeometry.IsAffine`.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fpqcPrecoverage`,
  `Scheme.fpqcTopology`, `Scheme.Hom.singleton_mem_fpqcPrecoverage`, fpqc
  subcanonicity and covering stability instances.
- `Mathlib.CategoryTheory.Yoneda`: `Functor.RepresentableBy`, `uliftYoneda`,
  `uliftYonedaEquiv`. These are the recorded representability notion, its
  universe-lifted functor of points, and Yoneda's section correspondence.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`:
  `AlgebraicGeometry.QuasiCompact` (the quasi-compact clause of the recorded
  finite-type-morphism node).
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`:
  `AlgebraicGeometry.QuasiSeparated`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
- `Mathlib.CategoryTheory.Limits.HasLimits`: `Cone`, `IsLimit`, dual to the
  recorded colimit and cocone definitions.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback` and `.IsPullback`:
  `pullback`, its projections and universal property, and `IsPullback`.
- `Mathlib.CategoryTheory.Comma.Over.Basic` and `.Pullback`: `Over`, `Over.map`.
- `Mathlib.CategoryTheory.Sites.Over`: `GrothendieckTopology.over`.
- `Mathlib.CategoryTheory.MorphismProperty.Comma` and `.Representable`:
  `MorphismProperty.over`, `MorphismProperty.relative`, the existing general
  interface for representable scheme-test open immersions.
- `Mathlib.AlgebraicGeometry.QuasiAffine`: `Scheme.IsQuasiAffine`, which
  includes quasi-compactness and makes the canonical map to Spec Γ an open
  immersion; this is the node's quasi-compact quasi-affine convention.

The modules of stated proof dependencies are imported without `public`:
`WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit` for
`Scheme.exists_pullback_hom_of_isLimit` and
`Scheme.exists_pullback_fst_comp_eq_of_isLimit`;
`Sheaf.AlgebraicGeometry.OpenImmersionInverseLimitDescent` for
`IsOpenImmersion.eventually_of_inverseLimit`;
`WeilConjectures.AlgebraicGeometry.LimitFibreProducts` for
`limit_fibre_products_of_affine_transition`; and
`WeilConjectures.AlgebraicGeometry.FpqcOpenSubschemeDescent` for
`openSubscheme_existsUnique_of_fpqc`. Mathlib proof leaves are available through
these imports, including eventual quasi-affineness from its affine-transition
limit module and the affine/qcqs permanence and fpqc covering instances. The
proof-only node `lem-sfb-fpqc-form-qcqs-limit-continuity` has no recorded Lean
module in the read DAG, so there is no module to import for it. It remains an
explicit step in the full natural-language proof docstring, not a new premise.

Edge cases checked before writing:

- Empty V is allowed, as are empty schemes and the zero ring. No nonemptiness
  assumption is imposed on any scheme or on the chart; the empty chart is
  quasi-affine under Mathlib's convention.
- A singleton directed index works; no strict enlargement is required.
- An empty index is excluded exactly by the node's nonempty hypothesis.
- The whole open V = Y is included whenever V/T is finitely presented.
- Non-separated Y and non-quasi-compact P are allowed. Only the stated relative
  quasi-separatedness and local finite presentation of P are assumed.
- Non-quasi-affine V still gets a chart; the implication adds no condition in
  that case. When V is quasi-affine, it constrains those same chart witnesses.
- The stage restriction of F can remain nonrepresentable: representability is
  asserted only after pulling the chart back along each scheme test.
- Neither hY nor the identification of the inclusion is existentially forgotten;
  replacing hY changes the displayed section equality, as it should.

Searches performed with `msearch.py NA lem-sfb-fpqc-chart-limit-spreading`:

- `leanfinder`: “Open finitely presented scheme charts into an fpqc locally
  representable functor descend along inverse limits of affine schemes”. Eight
  hits: local finite presentation, scheme-target limit factorization, and local
  representability via Zariski gluing. None spreads an open chart into a functor
  whose stage restrictions need not be schemes.
- `loogle`: `AlgebraicGeometry.LocallyOfFinitePresentation,
  AlgebraicGeometry.IsOpenImmersion`. Three hits: local finite presentation of
  open immersions, the smooth-locus pullback, and flat monomorphisms. No match.
- `grep`: `fpqc.*limit|limit.*fpqc` in Mathlib `AlgebraicGeometry`: zero hits.
- `leansearch`: “Quasi-compact finitely presented open scheme charts of locally
  finitely presented fpqc sheaves descend along affine inverse limits”. Eight
  hits concerning morphism-property descent and module finite presentation;
  none is the required functor-valued chart-spreading statement.
- `rg` in both project source roots for fpqc forms, chart limit spreading and
  representable opens; no existing statement. The upstream representability
  interface is general local gluing and does not give this limit statement.
  The exact node-id search in `lean/WeilConjectures` had no match.
- `rg` in Mathlib's morphism-property files found `relative` and `over`, so no
  private definition of representable open immersion was introduced. Searching
  the proposed declaration and module names in the two project roots and
  `dag/lean_names_upstream.json` found no collision.

Sources read: the full node and its dependency records; Mathlib and project
signatures listed above; Stacks `limits.tex`, labels
`lemma-descend-finite-presentation`, `lemma-descend-open-immersion`, and
`lemma-limit-quasi-affine`; Raynaud's primary scan, Theorem 4.1 proof,
reductions 2--4, especially printed pp. 5-19--5-20:
https://www.numdam.org/item/SAC_1967-1968__2__A5_0.pdf .
The Lean docstring retains all seven proof steps and their named dependencies.

Validation uses only the authorized `scompile.py` and `deliver2.py` wrappers;
no global build, direct Git operation, or write to the read-only library.

## Second reading by NA

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
