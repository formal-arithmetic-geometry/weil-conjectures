## Worker report

The module `Sheaf.AlgebraicGeometry.FlatCurveLineDepth` states
`AlgebraicGeometry.flat_curve_line_depth`, with exactly one postponed proof (`sorry`).
No definitions, dependency repairs, new nodes, or statement corrections are needed.
The item's JSON changes only in `lean`.

Sources read: algebra.tex `lemma-apply-grothendieck` (Tag 0337),
`lemma-ideal-nonzerodivisor` (00LL); schemes.tex `lemma-local-ring-fibre`
(0HA1); morphisms.tex `lemma-finite-type-noetherian` (01T6). The six-step
assembly in the node is reproduced in the theorem docstring. These sources give
precisely the depth formula, nonzerodivisor argument, fibre quotient and
Noetherianity used in the node, without smoothness, normality or properness.

Hypothesis and conclusion correspondence:

| Node clause | Lean rendering |
| --- | --- |
| R a DVR | `R : Type u`, `[CommRing R] [IsDomain R] [IsDiscreteValuationRing R]` |
| uniformizer pi | `(π : R) (hπ : Irreducible π)`; `irreducible_iff_uniformizer` identifies this with the generator condition |
| fraction field K | `K : Type u`, `[Field K] [Algebra R K] [IsFractionRing R K]` |
| residue field k | canonical `IsLocalRing.ResidueField R`, with the ring map `IsLocalRing.residue R` |
| S = Spec R, f : X -> S | `(X : Scheme.{u}) (f : X ⟶ Spec (.of R))` |
| f flat, finite type | `[Flat f] [LocallyOfFiniteType f] [QuasiCompact f]` |
| special fibre | `pullback f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))` |
| reduced special fibre | `[IsReduced (pullback f ...)]` |
| pure dimension one | `hdim : (...).IsPureDimension 1` |
| invertible M | `(M : X.Modules) [M.IsInvertible]` with the recorded scheme-module class |
| X Noetherian, finite affine Noetherian cover | `IsNoetherian X`; Mathlib Noetherian.lean's `isNoetherian_iff_of_finite_iSup_eq_top` is the finite-affine-cover formulation |
| every m in N including zero | `∀ m : ℕ`, without a positivity hypothesis, using existing `M.tensorPow m` |
| pi multiplication injective on every stalk | first conjunct, `∀ x : X, Function.Injective ...`, acting by the germ of `f.appTop ((Scheme.ΓSpecIso (.of R)).inv π)` |
| restriction to generic fibre injective | second conjunct, `Function.Injective (pullbackΓ (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) (M.tensorPow m))` |
| every closed special-fibre point x | `∀ x : pullback (C := Scheme.{u}) f ..., IsClosed ({x} : Set _) → ...` |
| local ring depth at least two | first depth inequality uses `X.presheaf.stalk ((pullback.fst f ...) x)` as ring and module |
| tensor-power stalk depth at least two | second inequality uses exactly `TopCat.Presheaf.stalk (C := Ab.{u}) (X := X) (M.tensorPow m).val.presheaf` at the projected point |
| finite free rank-one stalk | its finiteness is supplied in the conclusion as `∃ hf : Module.Finite ...`; `@IsLocalRing.depth` explicitly receives that proof |

The displayed generic restriction has target sections of `j^*(M.tensorPow m)`,
where j is the actual fibre-product projection. This is the restricted module
written in the node as `(M_K)^{tensor m}`: the canonical monoidal pullback
comparison identifies these two module expressions, and postcomposition by
that isomorphism does not alter injectivity. This uses no arbitrary map or
choice of a trivialization. The existing upstream `Scheme.Modules.pullbackΓ`
is actually in namespace `AlgebraicGeometry` (despite the module name), as
confirmed by reading its full definition in Modules/PullbackUnit.lean.
`M.tensorPow 0` is definitionally the structure module, as read in
Modules/Invertible.lean. Thus the restriction includes its degree-zero case.

The stalk carrier is Mathlib's existing additive stalk with its canonical module
structure from Mathlib.Algebra.Category.ModuleCat.Stalk; using `.val.presheaf`
exposes this instance without manufacturing a new scalar action. The finite
witness is needed only because the recorded `IsLocalRing.depth` definition
requires finite generation; placing it in the conclusion adds no assumption.
There is no `let` binder or hidden chosen module instance in the statement.

Recorded statement dependencies used (signatures and docstrings read):

- Mathlib.RingTheory.DiscreteValuationRing.Basic: `IsDiscreteValuationRing`,
  `IsDiscreteValuationRing.irreducible_iff_uniformizer`.
- Mathlib.Algebra.Algebra.Defs: `Algebra`, inherited by the imported ring APIs.
- Mathlib.AlgebraicGeometry.Scheme: `Spec`, `Spec.map`.
- Mathlib.AlgebraicGeometry.Morphisms.Flat: `Flat` (its stalkwise equivalence is documented).
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType and Morphisms.QuasiCompact:
  `LocallyOfFiniteType`, `QuasiCompact`.
- Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback: `pullback`,
  `pullback.fst`, `pullback.snd`, inherited via scheme morphism modules.
- Mathlib.AlgebraicGeometry.Properties: `IsReduced`, inherited via Noetherian.
- Sheaf.AlgebraicGeometry.PureDimension: `Scheme.IsPureDimension`.
- WeilConjectures.AlgebraicGeometry.Modules.Invertible:
  `Scheme.Modules.IsInvertible`, `Scheme.Modules.tensorPow`.
- Mathlib.RingTheory.Noetherian.Defs: `IsNoetherianRing`, inherited via Noetherian.
- WeilConjectures.RingTheory.Depth: `Ideal.depth`, `IsLocalRing.depth`.

All recorded non-Mathlib proof modules are plain imports: GenericFibreAffineRingModels,
FibreStalkQuotient, EquidimensionalOpenLocalDimension, ClosedPointDimensionLocalRing,
NonzerodivisorIfMaximalNotAssociated, FlatLocalDepthFormula. Relevant Mathlib proof
inputs are directly or transitively imported, including affine Noetherianity,
localization, torsion-freeness and regular sequences. No import cycle was needed.

Edge cases checked before writing: X may be empty; then point clauses are vacuous
and generic restriction is between trivial section groups. The special fibre may
be empty even when X is not (a family supported over the generic point); then
there are no closed special points and uniformizer multiplication is invertible.
The generic fibre may be disconnected or reducible: nothing assumes integrality
of X. A reduced nodal fibre is allowed. A nonreduced special fibre is correctly
excluded only by the stated reducedness condition. m = 0 is included without
any bound, and the zero module on the empty scheme is not excluded. No
properness, separatedness, smoothness, normality, nodality, or characteristic
hypothesis was introduced. All scheme and field models use a common universe u,
as required by the scheme fibre-product API; no test objects are quantified over
in a smaller independent universe.

Searches actually run through msearch.py (NN, this item):

- LeanFinder: “Flat reduced curve families over a discrete valuation ring have
  depth two at closed special points and invertible sheaf sections inject into
  the generic fibre”: 8 hits, Weierstrass good/minimal reduction, valuative
  criterion and Flat. None states this combined result.
- Loogle: `"IsLocalRing.depth", "Flat"`: 0 hits.
- grep Mathlib AlgebraicGeometry: `depth|generic[Ff]iber|torsion[Ff]ree`: 1 hit,
  an unrelated recursion-depth comment in elliptic-curve point code.
- LeanSearch: “Depth two of invertible sheaves on flat reduced curve families
  over a DVR and generic fibre injectivity”: 8 hits, generating-section
  constructor injectivity, integral-scheme germ injectivity, stalkwise tests,
  and structure-sheaf localization. None states the node's theorem.
- rg of lean/WeilConjectures by the item id: no declaration.
- rg of lean/WeilConjectures and lean/Sheaf for `flat.*curve.*depth`,
  `depth.*curve`, `generic.*restrict.*inject`, `inject.*generic`, and searches
  for tensor powers, pullback sections, and stalk finiteness found the APIs
  listed above. NodalLogDualizingPullback and GeometricallyReducedEtaNormal
  contain related proof plans but different hypotheses and conclusions.

Validation: compiled through the prescribed scompile.py server wrapper in module
mode, both the sandbox check and named library module, with no errors or warnings.
The final declaration has its entire proof as `sorry`; there are no diagnostics
or probe declarations left in the file. Every variable and universe is explicit,
with both autoImplicit and relaxedAutoImplicit disabled. No node fault or
STATEMENT-DISPUTED issue was found.

## Second reading by NN

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
