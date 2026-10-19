## Worker report

The module `Sheaf.AlgebraicGeometry.FinitePushforwardTensorComparison` states
`AlgebraicGeometry.Etale.finitePushforward_tensorComparison`, with proof `sorry`.
Its four auxiliary definitions have real data: `finiteConstantExchange`,
`finiteConstantTensorReduction`, `finiteConstantTensorTargetReduction`, and
`finitePushforwardUntensoredComparison`. They name the particular arrows of this
node, assembled from existing exchange, projection, unit and adjunction maps.
No theorem is proved and no new independent notion or dependency repair is needed.

Hypothesis and object correspondence:

- The field is `{K : Type u} [Field K]`. The K-scheme structures of X and S' are
  `x : X ⟶ Spec (.of K)` and `s : S' ⟶ Spec (.of K)`.
- All schemes, including the four fibre products, have universe `Scheme.{u}`.
  `I`, `I'`, and `J` mean X_i, X'_i, and Y_i. Using arbitrary pullback witnesses
  rather than the chosen implementation of `pullback` retains exactly the
  universal fibre-product condition, with no geometric extra assumption.
- `p`, `f'`, `h`, `e`, and `g` are exactly the named projections and map in the
  node. `_sqBase : IsPullback p f' x s` and `sqG : IsPullback e h g f'`
  give X' = X ×_K S' and Y = X' ×_{S'} T with these projections.
- `[QuasiCompact g] [QuasiSeparated g]` are both assumptions on g.
- `π : I ⟶ X` with `[IsFinite π]` is the finite map, without flatness,
  finite-presentation, surjectivity, nonemptiness, or smoothness assumptions.
- `sqPi : IsPullback pI π' π p` specifies X'_i and both projections;
  `sqRho : IsPullback hI ρ π' h` specifies Y_i and both projections.
  Thus f'_i is π' followed by f', and e_i is ρ followed by e.
- `ℓ : ℕ`, `[Fact ℓ.Prime]`, and `_hℓ : IsUnit (ℓ : K)` render exactly the
  prime and invertibility assumptions. The coefficient ring is
  `ULift.{u+1} (ZMod ℓ)`, the prime field placed in the coefficient universe.
  The lift is a ring equivalence, not a restriction on the prime or field.
- F is a `Sheaf T.smallEtaleTopology (ModuleCat.{u+1} (ULift (ZMod ℓ)))`,
  inserted in degree zero by `DerivedCategory.singleFunctor _ 0`.

Each conclusion clause:

1. `IsIso (finiteConstantTensorReduction ... sqPi.toCommSq A)` gives the
   first canonical isomorphism. Here A is L(f')* Rg_* F. The arrow first applies
   finite exchange to p* Rπ_* k, then the canonical constant-unit pullback
   identification, then `rightDerivedLowerStarProjectionMap` for π', then
   `derivedTensorLeftUnitor` under Rπ'_*. Its target is Rπ'_* Lπ'* A.
2. `IsIso (finiteConstantTensorTargetReduction ... sqPi.toCommSq
   sqRho.toCommSq V)` gives the second canonical isomorphism, with V = Le*F.
   Its domain is Rh_* (Lh* Lp* Rπ_* k tensor V); its target is
   Rπ'_* Rh_i,* Lρ*V. The definition applies Lh* of the first constant exchange,
   the same finite projection construction for ρ, and the conjugate of
   `derivedSquareUpperStarIso` under the two composite adjunctions. The
   conjugate's inverse has the direction Rh_* Rρ_* → Rπ'_* Rh_i,*.
3. The third conjunct is α followed by that second arrow equals the first
   arrow followed by Rπ'_* of β. The formula for α is written directly in the
   signature: `derivedUpperStarLowerStarAdjunction ... h |>.homEquiv` applied
   to the pullback tensor comparison followed by tensoring the identity with
   `derivedSquareUpperStarIso ... sqG` and Le* of the g-counit. This is exactly
   the comparison adjoint to 1 tensor e⁻¹ ε_g. β is the named
   `finitePushforwardUntensoredComparison`: its h_i-transpose is the inverse
   square composition identification followed by Lρ* of the same δ. Thus it
   is precisely the comparison adjoint to e_i⁻¹ ε_g, with iterated inverse
   images representing (f'_i)⁻¹ and e_i⁻¹ through the canonical composition
   isomorphisms. No arbitrary comparison map or isomorphism is quantified.
4. The fourth conjunct says `IsIso β → IsIso α`, for exactly the same maps.

The equality is written in the unbounded derived categories through the fully
faithful inclusions of D⁺. All its objects are the included bounded-below objects:
F is in degree zero, inverse image is exact, right direct image preserves a lower
bound, and over the prime field the tensor of bounded-below complexes is bounded
below. For finite π, Rπ_* of the constant complex is canonically the degree-zero
sheaf M = π_* underline{k}; likewise Rπ'_* and Rρ_* are the termwise finite direct
images. Consequently these are the exact objects and arrows of the node under
the finite-exactness and inclusion identifications explicitly used in its proof.
Using Rπ_* here does not impose an acyclicity assumption or change M to an arbitrary
object. The unitor is the identification of tensor with the free rank-one
constant coefficient module. `constantComplex` is the existing constant sheaf in
degree zero, built from Mathlib's sheafified constant presheaf, not a new constant
sheaf definition.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, its
  projections and universal property; `IsPullback` states that property for
  the explicitly named projections.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`: `QuasiSeparated`.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `IsFinite`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `constantSheaf`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`: the existing six-functor
  encoding of `DerivedCategoryModule`, D⁺ and cohomology; current source read
  with `scompile.py --source` because it is absent in the older local checkout.
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`: `derivedTensor`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: `lowerStar`,
  `upperStar`, `upperStarLowerStarAdjunction` and their derived functors.
- Canonical constructions come from `BaseChange.DerivedUnbounded`
  (`derivedBaseChangeMap`, `derivedSquareUpperStarIso`),
  `Etale.Derived.LowerStarProjection` (`rightDerivedLowerStarProjectionMap`),
  `Etale.Derived.UpperStarMonoidal.Comparison` (`leftDerivedUpperStarUnitIso`,
  `leftDerivedUpperStarTensorComparison`), and `Etale.Derived.TensorStructure`
  (`derivedTensorLeftUnitor`). The composition comparison is constructed by
  `conjugateIsoEquiv` with `Adjunction.comp`.
- The modules recorded for the already stated proof dependencies are imported
  non-publicly. The theorem docstring follows all eight proof steps, including
  finite exactness and the two successive Hom transposes.

Edge cases checked before writing and on the final signature: π = identity gives
unit and composition normalizations; I empty makes both finite pushforwards zero;
X or T empty is admitted; F = 0 is admitted; the finite disjoint union X ⊔ X → X
is admitted and gives two summands; ramified and non-flat finite π are admitted
because the hypothesis is only `IsFinite π`. No assumption on the dimension,
Noetherianity or finite type of X or S' occurs. All prime characteristics allowed
by invertibility are retained. No independent smaller universe is used for test
schemes or coefficients. There are no auto-bound variables or file-local aliases.

Searches (2026-10-17):

- `msearch.py ... leanfinder "Finite pushforward of the constant sheaf reduces
  the derived tensor base change comparison to the untensored base change map"`:
  8 hits, including `SheafOfModules.pushforwardCongr` and unit/counit formulas;
  no derived étale finite-pushforward comparison theorem.
- `msearch.py ... loogle '"lowerStar", "tensor"'`: 0 hits.
- `msearch.py ... grep 'finite.*pushforward|projectionFormula|tensor.*baseChange'
  AlgebraicGeometry`: 0 hits.
- `msearch.py ... leansearch "Finite direct image of constant etale sheaves
  identifies tensor base change with the untensored comparison"`: 8 hits on
  ordinary scalar base change and constant sheaves, no matching theorem.
- `rg` in upstream WeilConjectures for the item id returned no result; searches
  for `finitePushforward`, `finite_pushforward`, and finite/tensor/base-change
  patterns found no statement of this result. `rg` in side `lean/Sheaf` found
  the parent `PunctualTensorBaseChange` and the untensored arbitrary-scheme node,
  neither of which states this reduction. The generic projection/base-change
  compatibility theorem in `LowerStarProjectionBaseChange` is infrastructure,
  not the finite constant-pushforward reduction or its two isomorphisms.
- Exact-name `rg` across Mathlib, upstream and side sources for all five names
  introduced here returned no collision.

No statement correction, disputed statement, new node or dependency module.
The Stacks intermediate calculation drops ρ_* in one displayed line; the DAG
already restores the correctly typed map, and this delivery follows that DAG.

## Second reading by Q125

Independent maintainer reading, 2026-10-17, of immutable delivery
`d5a72dd111f49795eeb5427372f792533470e75f`. This replaces the delivered
section that explicitly described an author self-check. The independent reviewer
read the item, all nine statement dependencies and their recorded interfaces,
Stacks `etale-cohomology.tex`, `lemma-punctual-base-change-upgrade`
(0F1J, lines 20706–20876), and the module itself. No Lean or node correction
was needed.

Objects and hypotheses checked individually:

- `{K : Type u} [Field K]`, `x`, and `s` give exactly the field and the
  two K-scheme structures. `_sqBase : IsPullback p f' x s` gives X'.
- `g` has both `QuasiCompact` and `QuasiSeparated`. `sqG` gives Y and
  its correctly oriented projections e and h. No hypothesis on X such as
  Noetherianity, affineness, separation or finite type was introduced.
- `π : I ⟶ X` has only `IsFinite`; `sqPi` and `sqRho` give X'_i and Y_i.
  The maps f'_i and e_i are represented by the indicated iterated pullbacks,
  using their canonical composition identifications. Finite presentation,
  flatness, étaleness, surjectivity and nonemptiness are not assumed.
- `ℓ`, `Fact ℓ.Prime` and `IsUnit (ℓ : K)` retain every allowed prime and
  characteristic. `ULift.{u+1} (ZMod ℓ)` is the same coefficient ring by
  its canonical ring equivalence. F ranges over all sheaves of modules in
  the established coefficient universe and is inserted in degree zero.

Conclusion checks:

1. `finiteConstantExchange` is `derivedBaseChangeMap` on the tensor unit
   followed by pushforward of `leftDerivedUpperStarUnitIso.hom`.
   `finiteConstantTensorReduction` then tensors this arrow with A, applies
   `rightDerivedLowerStarProjectionMap` at the unit and A, and applies the
   pushed-forward left unitor. Its `IsIso` is exactly the first reduction.
2. `finiteConstantTensorTargetReduction` applies h-pullback of constant
   exchange, the same reduction for the square `(hI,ρ,π',h)`, and the
   inverse of the conjugate square isomorphism. The inverse has direction
   Rh_* Rρ_* → Rπ'_* RhI_*; hence its `IsIso` is the second reduction.
3. The displayed α is the h-adjoint of the tensor pullback comparison
   followed by identity tensored with the square identification and e-pullback
   of the g-counit. β uses `derivedSquareUpperStarIso sqRho` inversely,
   followed by ρ-pullback of that same counit composite, then the hI Hom
   bijection. Thus β is precisely adjoint to e_i⁻¹ ε_g. The equality is
   α ≫ Ψ = φ ≫ Rπ'_*β, with the actual maps specified, not arbitrary maps.
4. The final implication is `IsIso β → IsIso α`, with the same α and β.

I checked the exact upstream declarations in `BaseChange/DerivedUnbounded`
(square isomorphism and mate), `Etale/Derived/LowerStarProjection` (projection
mate), `Etale/Derived/UpperStarMonoidal/Comparison` (tensor and unit maps),
`Etale/Derived/TensorStructure` (unitor), and Mathlib `Adjunction.comp` and
`conjugateIsoEquiv`. All four helpers contain real composite data. Their
coefficient-category assumptions are discharged by existing module-category
instances; none becomes an additional assumption of the theorem.

D⁺ is the full bounded-below subcategory of the same unbounded D. F starts in
nonnegative degrees; exact inverse images and right derived direct images
preserve a lower bound, and tensor over the prime field preserves boundedness
below. Finite exactness identifies Rπ_*k with M in degree zero and identifies
Rπ'_* and Rρ_* with their termwise functors. These identifications explain the
unbounded notation without strengthening or changing the node. The global
`derivedTensor`, `constantComplex`, `lowerStar` and `upperStar` are reused.

The proof docstring follows all eight DAG steps. Finite exchange and finite
exactness apply to arbitrary finite maps; 0F0G applies because finite maps are
proper and the coefficient ring is torsion. The two iterated transposes have
counit factors ε_ρ ∘ ρ⁻¹E and hI⁻¹ε_π', equal by the exchange mate identity.
This checks the omitted map compatibility, not merely the endpoint objects.
The missing ρ_* in an intermediate Stacks display is already repaired in the
unchanged DAG statement. There is no stage-2 statement correction or citer audit
to perform.

Edge cases checked: π = identity; empty I, X or T; F = 0; a two-component
finite disjoint union; ramified or non-flat finite π; and every characteristic
permitted by ℓ invertibility. Scheme universes are shared without imposing an
extra equality on the site object and morphism universes. The coefficient
universe is the existing six-functor convention, and no independent smaller
test universe appears.

Independent searches used LeanSearch for “finite direct image constant
coefficients projection formula compatibility with base change adjunction”
(8 hits, ordinary algebraic base change and finite-morphism stability),
LeanFinder for “canonical tensor exchange square finite pushforward constant
sheaf derived etale” (8 underived sheaf-module hits), and `rg` across pinned
Mathlib, upstream WeilConjectures, and the group's side sources for the five
introduced names and finite/tensor/comparison alternatives. No exact existing
statement or name collision was found. The generic projection/base-change
compatibility theorem and the parent punctual tensor theorem were opened;
neither duplicates this finite-constant reduction with both isomorphisms.

Compiler reproduction used the immutable file:

`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q125 lem-kun-0f1j-finite-pushforward-comparison snapshot/lean/Sheaf/AlgebraicGeometry/FinitePushforwardTensorComparison.lean`

Exit 0, no errors or warnings: sandbox `Sheaf/Stage2/Sandbox0.lean` 32.3 s,
library `Sheaf/AlgebraicGeometry/FinitePushforwardTensorComparison.lean` 30.4 s,
both under the wrapper's 60 s per-file limit. The installed wrapper currently
runs its side overlay on the server; it was used as prescribed, without direct
SSH, a global build or project-clone edits. `scompile.py --source
WeilConjectures.AlgebraicGeometry.DerivedCategories` also confirmed the exact
current recorded dependency source missing in the older checkout.

Mechanical checks: `lean.statement` equals the theorem signature verbatim;
all five declarations are listed; there is exactly one `sorry`, the theorem
body; every declaration has source/blueprint documentation; all Lean lines are
at most 100 characters; all variables and universes are bound. The only finding
was H11: the original second-reading section was an author self-check. This
complete report replacement supplies the independent reading. No module, node,
helper, universe or mathematical statement needed repair.
