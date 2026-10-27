## Worker report

The module `Sheaf.AlgebraicGeometry.ClosedSubcurveDualizingAdjunction` states
`AlgebraicGeometry.exists_closedSubcurveDualizingAdjunction`, with one postponed
proof and no new definitions. The node changes only in `lean`. There is no
statement correction, disputed statement, dependency repair, or new node.

Source read: `literature/stacks-project/curves.tex`,
`lemma-closed-immersion-dim-1-CM`, Tag 0E33, part (2), and its proof. It identifies
`i_* omega_Y` with `Hom_X(i_* O_Y, omega_X)`. Its proof explicitly writes the
structure morphism of Y as the composite of i and the structure morphism of X.
The ordinary representing-functor proof in this node realizes the same
isomorphism, and evaluation at 1 identifies the right side with the annihilator.
The source's module duality is Tag 0BS2(5), as supplied by the recorded dependency.

Hypothesis and clause correspondence:

- The field is `(k : Type u) [Field k]`.
- The schemes are `(X Y : Scheme.{u})`, with their k-structures expressed by
  `[X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]`.
- Properness is `[IsProper (X ↘ Spec (.of k))]` and the corresponding Y instance.
  The field, properness, reducedness, and closed-immersion notions are the recorded
  Mathlib interfaces, not local definitions.
- Reducedness is `[IsReduced X] [IsReduced Y]`; nonemptiness is `[Nonempty X]
  [Nonempty Y]`. Pure dimension one is exactly `hX : X.IsPureDimension 1` and
  `hY : Y.IsPureDimension 1`, using the recorded componentwise dimension definition.
- The closed immersion is `(i : Y ⟶ X) [IsClosedImmersion i]`.
  `[i.IsOver (Spec (.of k))]` makes it a morphism of the k-schemes, as in the
  source's identity g = f composed with i. It is not an extra geometric condition
  beyond the source setting.
- Its ideal sheaf is the actual `i.ker`, the declaration recorded by
  `def-sbc-closed-immersion-ideal-sheaf`. `i.ker.idealOfOpens V` is its existing
  extension to all opens, read in the upstream IdealSheaf.Module module. It is
  the kernel ideal on the open V, not an arbitrary ideal or annihilator parameter.
- The chosen dualizing modules and their natural representing isomorphisms are
  the actual `ReducedCurveDualizingPair k X` and `ReducedCurveDualizingPair k Y`.
  Their `omega`, `coherent`, `duality`, and `naturality` fields were read in the
  recorded dependency module. The theorem applies to every such choice.
- The displayed isomorphism is `e DX DY`, with source
  `(Scheme.Modules.pushforward i).obj DY.omega` and target the recorded
  `SheafOfModules.homObj (R := X.sheaf)` from the actual pushforward of
  `SheafOfModules.unit Y.ringCatSheaf` to `DX.omega`.
- The direct image is Mathlib's `Scheme.Modules.pushforward`. Its source defines
  its sections as sections on the inverse-image open, with scalars restricted
  along the scheme structure map. This is precisely the direct image specified
  in the node, with no replacement functor or independent action.
- Naturality under isomorphisms of chosen representing pairs is the first
  conjunct. The two premises say that `a` and `b` respect `duality` on every
  coherent test module. The equation says that pushing forward `b.hom` and then
  using `e DX' DY'` agrees with using `e DX DY` and postcomposition by `a.hom`
  in the actual sheaf Hom (`SheafOfModules.homObjMap`). This records the
  final sentence of proof step 5, not merely objectwise existence of isomorphisms.
- The second conjunct supplies an O_X-module morphism `ev` from that sheaf Hom
  into `DX.omega`. Its equation on every open U is
  `ev.val.app (op U) φ = φ.app (op (Over.mk (𝟙 U))) (1 : Γ(Y, i ⁻¹ᵁ U))`.
  The sheaf Hom section is a map on the localized category over U, so its
  component at the identity object evaluates the map on U itself. This is
  evaluation at the unit of the pushed-forward structure sheaf.
- `Function.Injective (ev.val.app (op U))` on every U makes this an inclusion.
  The range equivalence says exactly that w lies in the annihilator iff, on
  every smaller open V and for every j in `i.ker.idealOfOpens V`, multiplication
  of the restriction of w by j is zero. Testing every smaller open is essential:
  it states annihilation by the ideal *sheaf*, without assuming that ideal
  sections on U generate it. Since ev is a sheaf-module morphism and is injective
  on every open, this describes the displayed identification with the
  annihilator as an O_X-module sheaf, without introducing a duplicate notion.
- No connectedness, integrality, smoothness, geometric reducedness,
  invertibility of either dualizing module, or H^0(O) = k binder occurs.

Statement dependency declarations used (their signatures and docstrings read):

- `Field`, Mathlib.Algebra.Field.Defs (`def-weil-field`).
- `AlgebraicGeometry.IsProper`, Mathlib.AlgebraicGeometry.Morphisms.Proper
  (`def-weil-proper-morphism`).
- `AlgebraicGeometry.IsReduced`, Mathlib.AlgebraicGeometry.Properties
  (`def-pc-reduced-scheme`).
- `AlgebraicGeometry.Scheme.IsPureDimension`,
  Sheaf.AlgebraicGeometry.PureDimension (`def-weil-pure-dimension`).
- `AlgebraicGeometry.IsClosedImmersion`,
  Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
  (`def-weil-closed-immersion`).
- `AlgebraicGeometry.Scheme.Hom.ker`,
  Mathlib.AlgebraicGeometry.IdealSheaf.Basic
  (`def-sbc-closed-immersion-ideal-sheaf`); all-open ideals use the existing
  `Scheme.IdealSheafData.idealOfOpens` in
  WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module.
- `AlgebraicGeometry.ReducedCurveDualizingPair`, and the existence theorem
  `AlgebraicGeometry.exists_reducedCurveDualizingPair`,
  Sheaf.AlgebraicGeometry.ReducedCurveDualizingModule
  (`lem-sfb-reduced-curve-dualizing-module`).
- `SheafOfModules.homObj` and `SheafOfModules.homObjMap`,
  WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
  (`def-pur-sheaf-hom`). Their local-map representation was also read in
  WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHom.

The stated proof dependencies are imported directly:
WeilConjectures.AlgebraicGeometry.ClosedImmersionCoherentEquivalence,
WeilConjectures.AlgebraicGeometry.CoherentSheafHom,
WeilConjectures.AlgebraicGeometry.ZariskiModuleAbelianCohomologyAgree, and
WeilConjectures.Topology.ClosedImmersionPushforwardCohomology.
Their declarations and docstrings were read, including the coherent equivalence,
`Scheme.Modules.isCoherent_homObj`, `zariskiModuleAbelianCohomologyAgree`, and
`TopCat.cohomology_closed_immersion_pushforward`. The dualizing-module dependency
is already a public statement import. `lem-trf-proper-field-invertible-coherent`
has no Lean record or Mathlib match in the read DAG, so it has no module to import;
its statement is used only by the future proof and is described in the docstring.
No new notion is needed to state this item. The theorem docstring carries all
five proof steps, including local quotient lifts and gluing, factorization through
the annihilator, cohomology comparison, and uniqueness of representing objects.

Edge cases checked before writing and again against the final signature:

- Empty X or Y is excluded by the node itself; the vacuous pure-dimension
  condition on an empty scheme cannot accidentally satisfy nonemptiness.
- The identity immersion has zero ideal; evaluation at 1 identifies Hom(O,omega)
  with all of omega. Arbitrary choices of dualizing pairs are still covered.
- For a disconnected ambient curve and inclusion of a union of components,
  the pushed-forward module and annihilator vanish on the omitted components.
  No connectedness instance or identification of global functions with k occurs.
- A reduced subcurve of a singular, non-Gorenstein reduced curve is included;
  the statement uses coherent dualizing pairs, never an invertible-module class.
- On the empty open, the section modules are zero and the displayed evaluation,
  injectivity, and range criterion still have their correct meanings.
- Testing all smaller opens keeps the annihilator correct without assuming
  surjectivity of the structure map on sections of every arbitrary open.
- The field has arbitrary characteristic. All universes are explicit, using the
  same scheme/module/field size convention as the dependency. `autoImplicit` is
  disabled, and the final signature has no let, hidden show, or local notation.

Searches performed for an existing statement:

1. `msearch.py ... leanfinder`, query "dualizing module of a closed reduced
   subcurve is sheaf Hom from its structure sheaf to ambient dualizing module".
   Eight hits on ideal-sheaf data, subschemes, normalization, and reducedness;
   none gives this dualizing adjunction.
2. `msearch.py ... loogle`, query `SheafOfModules.homObj`.
   Zero hits: the service does not know this project declaration. The declaration
   is found and used directly from the recorded upstream source instead.
3. `msearch.py ... grep`, query `dualizing|annihilator` in AlgebraicGeometry.
   Four hits in Mathlib.AlgebraicGeometry.SpreadingOut, all elementary module
   annihilator calculations; no dualizing-module result.
4. `msearch.py ... leansearch`, query "dualizing module of a closed subcurve
   equals sheaf Hom from the pushed forward structure sheaf to the dualizing
   module of the ambient curve". Eight hits give ordinary module pushforward,
   pullback adjunctions and related functor instances, not duality on curves.
5. `rg` of `dualizing|dualising` in WeilConjectures finds six-functor and Weil
   dualizing complexes, not this coherent curve-module assertion. The exact
   node-id search in WeilConjectures has no hit. Searches in Sheaf find the
   recorded ReducedCurveDualizingModule dependency and unrelated curve results,
   no closed-subcurve dualizing adjunction. The proposed full declaration name
   has no hit in Mathlib, WeilConjectures, Sheaf, or dag/lean_names_upstream.json.
6. `rg` of annihilator/evaluation terms in the upstream module-sheaf and
   algebraic-geometry folders finds existing tensor/Hom evaluation infrastructure
   and closed-pushforward annihilation results. Their objects are reused; none
   states this item. No private copy of any searched notion is introduced.

Validation: every compile used the prescribed scompile.py wrapper. The first
compile exposed field-notation elaboration on the sheaf Hom evaluation morphism;
using its actual `val.app (op U)` components fixed it. The final sandbox and
library-name compiles both returned cleanly (22.4 s and 16.2 s), with no error
or warning. The node's `lean.statement` is extracted verbatim from the theorem
signature, JSON uses indent 1 and a final newline, and every Lean line has at
most 100 characters. The only theorem proof is the required `by sorry`.

## Second reading by Q85

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
