## Worker report

Stated all five clauses of `lem-wf-dense-open-pi1-surjective` in
`Sheaf.Paper.DenseOpenPiOneSurjective`, as eight named theorems with `sorry` proofs.
The module introduces no new mathematical definition. It uses the existing canonical
`Scheme.FiniteEtale.fiberAutBaseChange`, rather than introducing another fundamental-group
map. A dependency interface repair in `Sheaf.Paper.RealSheavesSetup` supplies the
characteristic of the datum's finite field and the coefficient-prime instance; the
consumer needs no additional characteristic hypothesis. No natural-language statement,
statement dependency, proof, or proof dependency was changed. No new nodes.

Sources read: the current main-20261015 lemma and its proof, paragraphs Step 0 and
(1)--(5); the item's current DAG statement and seven proof steps; all five statement
dependencies and their recorded declaration sources/docstrings; the example
CompactObject module and its node. The current statement explicitly retains the
compatible finite-level O_E-model convention in clause (3). The source module
`WeilConjectures.SixFunctors.ProEtale.Adic.Constructible`, lines 19--36 and 79--87,
explains its existing lisse Qbar_l encoding, including finite fields of definition.

Hypotheses and clauses:

1. `V : Scheme.{u}`, `[ConnectedSpace V]`, `[IsNoetherian V]`, and
   `hV : ∀ x, IsDomain (V.presheaf.stalk x) ∧ IsIntegrallyClosed ...` render connected,
   Noetherian, normal V. This is precisely the stalkwise convention in
   `regular_normal_and_normal_decomposition`, without replacing normality by regularity
   or assuming integrality separately. `j : U ⟶ V`, `[IsOpenImmersion j]`, and
   `hj : DenseRange j.base` render the dense open immersion. `s : Spec (.of Ω) ⟶ U`
   with `[Field Ω] [IsSepClosed Ω]` is its geometric base point. The theorem
   `fundamentalGroupMap_surjective_of_normal_dense_open` asserts
   `Function.Surjective (fiberAutBaseChange j s)`. Its groups are exactly the
   automorphism groups of the recorded fibre functors, not arbitrary group models.
   The separate `isConnected_pullback_of_normal_dense_open` states the equivalent
   connected-cover formulation for every `P : V.FiniteEtale` with `hP : IsConnected P`.
   No connectedness hypothesis on U is added: Step 0 derives it.
2. `k₀ : Type u`, `[Field k₀] [Finite k₀]`, and the structure map `p` specify the finite
   base field; `[IsSeparated p] [LocallyOfFiniteType p] [QuasiCompact p]` specify separated
   finite type. `[ConnectedSpace p.geometricFiber]` and stalkwise normality of
   `p.geometricFiber` are exactly the geometric hypotheses. The geometric fibre uses
   the canonical algebraic closure; changing the chosen closure identifies these fibre
   products by the usual algebra isomorphism. `pU` and `hp : j ≫ p = pU` specify the
   open over the same field. The dense open is `j`, `hj`, and its base point is `s`.
   `weilGroup_dense_open_surjective` supplies a group homomorphism rho whose underlying
   pair is exactly `(fiberAutBaseChange j s w.val.1, w.val.2)` for every w. This formula
   determines rho; it is not an unconstrained existence of a surjective homomorphism.
   The second conjunct is equality of degree maps, the third is surjectivity on their
   geometric kernels, and the fourth is `Function.Surjective rho`. The kernels are the
   geometric fundamental groups by the recorded exact sequence. The pair formula is
   the canonical restriction on those groups, so the kernel assertion is precisely the
   restriction of clause (1). The types are the bodies of the *existing*
   `Scheme.FiniteEtale.weilGroup` and `weilGroupDeg` abbreviations, namely
   `constantCoverAction.weilGroup geometricFrobenius` and its degree homomorphism.
   This uses the recorded constructions verbatim and avoids assuming geometric
   connectedness of the open, or connectedness of either arithmetic scheme, as extras.
3. `Etale.isIso_lisse_unit_of_normal_dense_open` retains the connected, normal,
   Noetherian, dense-open hypotheses, every finite commutative ring
   `Λ : Type (u+1)`, and every small-etale module sheaf N with
   `[Scheme.IsFiniteLocallyConstantSheaf N]`. Its conclusion is `IsIso` of the actual
   `upperStarLowerStarAdjunction ... j` unit applied to N. The algebraic l-adic
   assertion is `ProEtale.isIso_lisse_unit_of_normal_dense_open`, for the existing
   `AdicSheaf l V` and `IsAdicLisseSheaf N`, with the actual
   `adicUpperStarLowerStarAdjunction` unit. The existing pro-etale lisse convention
   realizes compatible finite O_E-models with E finite over Q_l and scalar extension
   to Qbar_l, as documented in its owning module. Its proof docstring records the
   compatible finite-level inverse maps, inverse limit, inversion of l, and extension
   of scalars. No regularity, smoothness, separatedness, or quasi-compactness hypothesis
   on j is added to either unit statement. The coefficient closure is the upstream
   canonical closure; a different chosen algebraic closure gives the same assertion
   by scalar transport, and no embedding into C occurs in this assertion.
4. Both curve theorems take `D : RealSheaves.Setup.{u,v}` and the exact recorded
   `hC : D.IsCurve C`, with `[Nonempty U]`, an open immersion j over D.k₀. Thus all
   chapter conditions are retained: p prime, positive a, q=p^a, the finite field and
   algebraic closure, l prime different from p, coefficient closure and embedding,
   nonempty separated smooth finite-type curve, pure dimension one, and connected
   geometric base change. The Weil-sheaf theorem states preservation of lisse objects,
   bijectivity of the pullback map on every Hom between lisse F and G (full
   faithfulness of the restriction to that full subcategory), and preservation of
   `WeilSheaf.IsIrreducibleLisse`. This existing predicate means lisse, nonzero, with
   every lisse monomorphism either zero or invertible; it does not mean simple among
   all constructible sheaves. The geometric theorem states the same three clauses for
   `AdicSheaf D.l (D.geometricCurve C)` and
   `IsIrreducibleAdicLocalSystem`. Its morphism is the explicit `pullback.map` of j
   with the identity of Spec D.k, so it uses D's chosen geometric curves and the
   canonical base-change morphism. Neither theorem assumes the open is dense or normal:
   these follow from hC and its nonemptiness. No separate coefficient-characteristic
   assumption is present after the dependency repair.
5. `Scheme.isConstructible_middleExtension_of_curve_lisse` takes the same D and exact
   hC, a nonempty open immersion j, every finite commutative Λ, and every finite locally
   constant module sheaf F on U. It asserts
   `Scheme.IsConstructibleEtaleModuleSheaf ((Etale.lowerStar ... j).obj F)`.
   This is the finite-constant-value constructibility predicate in the dependency,
   not merely finite generation of stalks. The ordinary lowerStar is exactly the
   finite-level middle extension specified by `def-wf-middle-extension`; there is no
   derived direct image or cohomological shift. Every finite level of a compatible
   lisse model is covered by quantification over Λ and F.

Statement dependency declarations used:

- `WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale`:
  `AlgebraicGeometry.Scheme.FiniteEtale.fiber` (finite geometric fibres).
- `WeilConjectures.AlgebraicGeometry.FundamentalGroup.WeilGroup`:
  `constantCoverAction`, `geometricFrobenius`, and the exact bodies of `weilGroup` and
  `weilGroupDeg`; the generic fibre-product/degree definitions are in
  `WeilConjectures.GroupTheory.WeilGroup`.
- `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`:
  the recorded constructible-complex convention reexports the underlying
  `Scheme.IsConstructibleEtaleModuleSheaf` used here; lisse finite-level sheaves use
  the existing `Scheme.IsFiniteLocallyConstantSheaf`.
- `Sheaf.Paper.CurveWeilMiddleExtension` (and publicly imported CurveMiddleExtension):
  `WeilSheaf.curveWeilMiddleExtension` is the existing ordinary Weil direct image;
  the definition node explicitly identifies its finite-level operation with
  `AlgebraicGeometry.Etale.lowerStar`, which is used in clause (5).
- `Sheaf.Paper.RealSheavesSetup`: `RealSheaves.Setup`, `Setup.IsCurve`, and
  `Setup.geometricCurve`, plus the characteristic interface repair below.

Additional reused constructions: `Scheme.FiniteEtale.fiberAutBaseChange` from
`Sheaf.AlgebraicGeometry.FundamentalGroup.FiniteEtaleWeilTransport` is the canonical
whiskering-and-conjugation map, read in full. There is no DAG dependency path from its
owning node back to this item. The existing `ProEtale.AdicSheaf`, `IsAdicLisseSheaf`,
`IsIrreducibleAdicLocalSystem`, and ordinary adic adjunction are publicly supplied by
`WeilConjectures.SixFunctors.ProEtale.Adic.DenseOpenUnit`. Every already stated proof
input is imported: GaloisLisseRepresentations, OpenSubgroups, EtaleNormalComponents,
NormalOpenLisseImage, GaloisTransitive, GeometricallyConnectedAlgebraicClosure,
RegularNormalDecomposition, FiberEquivalence, and the upstream fundamental-group,
Weil-group and smooth-normal infrastructure. The finite-field universally-open fact is
Mathlib infrastructure. Unstated proof nodes are not restated in this delivery.

Edge cases checked before and during writing:

- A geometric point excludes the empty open in (1); ConnectedSpace excludes the empty
  target. A connected finite-etale object is nonempty. An empty finite-etale cover is
  not silently treated as a connected Galois-category object.
- Singular normal schemes are included: all relevant normality hypotheses are normal
  domains in every stalk, with no regularity assumption.
- Identity immersions, rank-zero sheaves, zero finite coefficient rings, and arbitrary
  finite coefficient levels remain included. Irreducibility uses the conventional
  nonzero condition; zero sheaves still occur in all unit and Hom assertions.
- A nonempty chapter open is dense as a consequence; no properness or affineness is
  imposed. Arbitrary characteristic p and every prime l distinct from p are retained.
- The field exponent a is positive, so the characteristic comparison does not admit
  the false p^0=1 case. The Setup repair works for all universes u and v.
- Full automorphism groups can be larger than the scheme universe; no small-model
  assumption or universe equality is imposed. Finite-level module values retain the
  established u+1 convention. The embedding iota is unrestricted and unused, as in
  these conclusions.

Searches actually run (all msearch calls used group Q14 and this item):

- leanfinder: "A dense open immersion into a connected normal Noetherian scheme induces
  a surjective map of etale fundamental groups". Eight hits, about scheme-morphism
  surjectivity and affine spaces; no exact theorem.
- loogle: `fundamentalGroup, IsOpenImmersion, Surjective`. Zero hits; response says
  `unknown identifier 'fundamentalGroup'`, not evidence that all alternatives were
  searched successfully.
- grep: `fundamentalGroup|weilGroup`, Mathlib AlgebraicGeometry. Zero hits.
- leansearch: "Surjectivity of fundamental groups for a dense open immersion of a normal
  scheme". Eight hits, on surjectivity on stalks/open or closed immersions; no exact match.
- rg on upstream WeilConjectures, the side framework, lean/Sheaf, and
  dag/lean_names_upstream.json for the item id, dense-open/pi1/surjectivity phrases,
  and the proposed names. The upstream DenseOpen group theorem requires IsRegular
  and states only part (1) with that stronger hypothesis. The WeilSheaf.DenseOpen
  theorem states only irreducibility in (4). The old RealSheaves.Construction theorem
  is for smooth curves, not the normal arbitrary-dimensional clause (2).
  DenseOpenUnit has a regular-stalk hypothesis. Boundary's constructibility theorem
  has an additional finite-complement hypothesis and is only clause (5). None is an
  exact match to all five clauses, and the overly strong hypotheses are not copied.
- A later rg for `Aut (.*fiber`, `mapAut.*fiber`, and
  `autMulEquivOfIso.*pullbackFiberIso` found the existing canonical
  `fiberAutBaseChange` and the path-dependent `padicH1FundamentalMap`. Read both;
  used the former and removed the draft helper. This search prevented a duplicate
  definition. Searches for `Setup.ringChar_eq` and `coefficientCharFact` found no
  existing characteristic interface in the allowed sources.

## Dependency modules

`d-real-setup`: its existing module records p prime, a positive, card(k₀)=p^a, and l != p,
but does not expose the stated characteristic p. The existing WeilSheaf pullback API
requires `Fact (ringChar k₀ ≠ l)`. Requiring that as an extra consumer hypothesis would
fail to use the full datum. The delivery retains the entire original
`Sheaf.Paper.RealSheavesSetup` file and appends `Setup.ringChar_eq` (with a source/proof
docstring and sorry) and the real-data instance `Setup.coefficientCharFact`, obtained
from that named theorem and `l_ne_p`. The instance has no sorry in its data. The
node changes only in lean. Its original Setup, all field choices, curve predicate,
Frobenius, closed-point and affine-open interfaces are preserved. The added theorem
is exactly the characteristic clause of the dependency's own first paragraph.

## Second reading by Q14

The delivering worker reread the node, dependency records and complete modules under
the dispatcher's instruction not to start other agents; the maintainer supplies the
independent review. The rereading found and repaired three interface issues before
this delivery: the initial group-model interface had unnecessary connectedness
assumptions on the open, the initial canonical-map helper duplicated an existing
helper, and the Weil-sheaf API needed a characteristic instance not exposed by Setup.
The final group statements use existing full fibre-automorphism groups and their
canonical map; the Weil-group expression is the existing fibre-product expression;
the Setup repair supplies the characteristic instance instead of adding a hypothesis.
The rereading also made preservation of lisse objects explicit in both curve
statements, alongside Hom bijections and irreducibility. Each of the five numbered
clauses is matched above. All theorem proofs remain exactly sorry; the sole added
instance has real data. No disputed statement or source correction was found.

## Validation

Every delivered module is compiled separately in dependency order through scompile.py.
The final dry run and delivery use deliver2.py, including the server preflight and
per-file compilation. No global build or direct git command was run.
