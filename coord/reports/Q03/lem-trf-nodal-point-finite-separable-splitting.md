## Worker report

The module `Sheaf.AlgebraicGeometry.NodalPointFiniteSeparableSplitting` states
`AlgebraicGeometry.nodal_point_finite_separable_splitting`, with its sole proof `sorry`.
There are no definitions, new nodes, dependency repairs, or statement corrections.
The docstring contains all eight proof steps of the node, including the characteristic-two
quadratic calculation and the completion base-change argument.

Hypothesis and conclusion correspondence:

| Node clause | Lean rendering |
| --- | --- |
| k a field; C a k-scheme | `{k : Type u} [Field k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))` |
| finite type over k | `[LocallyOfFiniteType f] [QuasiCompact f]` |
| every algebraically closed extension Omega/k | `∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (ι : k →+* Ω)`; a field ring map is automatically injective, and need not be algebraic |
| geometric base change C_Omega | `pullback f (Spec.map (CommRingCat.ofHom ι))`, with structure map `pullback.snd` |
| empty or equidimensional of dimension one | `.IsPureDimension 1`; the recorded definition holds vacuously on the empty scheme, so this is precisely the stated alternative |
| every nonsmooth geometric point | `∀ y, (¬ ∃ U, y ∈ U ∧ Smooth (U.ι ≫ pullback.snd ...)) → ...` |
| geometric completed local ring Omega[[u,v]]/(uv) | `Nonempty (AdicCompletion (IsLocalRing.maximalIdeal (...presheaf.stalk y)) (...presheaf.stalk y) ≃+* Orgogozo.nodeRing Ω)`; ring isomorphism, without adding scalar compatibility to this hypothesis |
| any nonsmooth x in C | `(x : C) (hx : ¬ ∃ U : C.Opens, x ∈ U ∧ Smooth (U.ι ≫ f))` |
| x is closed | `x ∈ closedPoints C` |
| kappa(x)/k finite separable | `(f.residueFieldAlgebraMap x).Finite` and `@Algebra.IsSeparable ... (f.residueFieldAlgebraMap x).toAlgebra` |
| finite separable k'/k containing a chosen copy of kappa(x) | `∃ (K : Type u) (_ : Field K) (i : C.residueField x →+* K)`, with finiteness and separability for `i.comp (f.residueFieldAlgebraMap x)`; that composite defines the ground-field structure, so containment respects k |
| relative degree at most two | `@Module.finrank (C.residueField x) K _ _ i.toAlgebra.toModule ≤ 2` |
| x' in C_K above x | `∃ x' : pullback ...`, with `pullback.fst ... x' = x` |
| x' K-rational in the specified sense | `Function.Bijective (Scheme.Hom.residueFieldAlgebraMap (pullback.snd ...) x')`; a bijective field ring map is an isomorphism |
| completed split equation as K-algebras | `Orgogozo.IsOrdinaryDoublePoint (pullback.snd ...) x'`; its definition is an actual ring equivalence from the maximal-ideal completion to `nodeRing K`, agreeing with the structural K-map on every scalar |

No local-finite-presentation hypothesis was added. Smoothness at a point is expressed
using a smooth open neighbourhood, directly from the recorded `Smooth` definition.
This avoids requiring a separate derivable finite-presentation instance just to write
`smoothLocus`. It is the same local notion for these finite-type schemes over a field.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`, together
  with `QuasiCompact` from `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic` (available through the imported geometric
  data): `IsAlgClosed`. The dependency's `AlgebraicClosure` is not a restriction to
  algebraic extensions; the statement correctly uses arbitrary algebraically closed fields.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: the scheme-base-change
  convention is `Limits.pullback`, with `pullback.fst` and `pullback.snd`. Read the live
  source using `scompile.py --source`, since it is absent from the older local source tree.
- `Sheaf.AlgebraicGeometry.PureDimension`: `Scheme.IsPureDimension`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`.
- `Mathlib.RingTheory.AdicCompletion.Basic` and `.Algebra`: `AdicCompletion`,
  its ring structure and `AdicCompletion.of` used by the reused split-node predicate.
- `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries`, indexed by `Fin 2`,
  and the variables `MvPowerSeries.X`, as used in the existing `Orgogozo.nodeRing`.
- `Mathlib.Topology.JacobsonSpace`: `closedPoints`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`;
  `WeilConjectures.ZetaSeries`: `Scheme.Hom.residueFieldAlgebraMap`, the canonical
  structural embedding of the ground field, not an arbitrary algebra structure.
- `Mathlib.FieldTheory.Separable`: `Algebra.IsSeparable`, which includes algebraicity.
- `Mathlib.Algebra.Algebra.Defs`: field extensions as ring maps or algebra structures;
  `RingHom.toAlgebra` is used explicitly for each extension.
- `Sheaf.Paper.OrgogozoInductionData`: `Orgogozo.nodeRing`, `Orgogozo.localScalar`,
  `Orgogozo.IsOrdinaryDoublePoint`. The already landed node
  `def-trf-orgogozo-induction-data` is added to `stmt_deps`, as authorized for reuse of
  landed definitions. No new definition node or second split-node definition is needed.

The module imports all currently recorded non-Mathlib proof-dependency modules:
`FirstFittingSingularSubscheme`, `DimensionBaseChange`, `DimensionAffineOpenCover`,
`Dimension`, and `UnramifiedOverFieldLocalCriterion`. The remaining proof prerequisites
have no recorded Lean module at the time of this delivery; no statements are invented
for these proof-only inputs. Their uses remain named in the proof docstring.

Source checked: Stacks `curves.tex`, `remark-quadratic-extension` (0CBT),
`remark-trivial-quadratic-extension` (0CBU), `definition-split-node`, `lemma-split-node`
(0CBW), and the residue-field paragraph of the first proof of
`lemma-etale-local-structure-nodal-family` (0CBY). These distinguish the separable
quadratic branch algebra from the field needed to split it: the latter may have degree one.

Edge cases checked:

- The empty C has no x and satisfies the geometric condition vacuously.
- Disconnected curves are allowed; no connectedness or irreducibility is assumed.
- A smooth curve has no x satisfying hx. Generic smooth points are not accidentally included.
- Closedness is a conclusion, not a binder; all nonsmooth x are covered.
- The already split equation uv requires only degree one, allowed by the bound two.
- Over the reals u^2+v^2 splits over a quadratic separable extension.
- In characteristic two, u^2+uv+v^2 splits over the separable quadratic extension;
  neither the signature nor its proof plan divides by two.
- Cusps and double lines fail the geometric completed-equation hypothesis.
- The degree bound cannot be made vacuous by an infinite extension: the composite K/k
  is required finite, hence K/kappa(x) is finite as well. Degree one is not excluded.
- All fields, schemes, points, and universes are explicitly bound. The geometric-field
  quantifier uses the scheme universe, following the project's geometric-fibre convention;
  the finite extension sought in the conclusion has a model in that universe.

Searches performed using `msearch.py`:

- LeanFinder: "A nodal point on a finite type curve over a field becomes a rational split
  node over a finite separable extension of degree at most two over its residue field".
  Eight hits: elliptic-curve maps/reductions, polynomial splitting and the separability
  of unramified residue fields; no splitting-node theorem.
- Loogle: `Algebra.IsSeparable, Module.finrank`. Twelve hits about embeddings,
  separable degree, traces and discriminants; no geometric splitting theorem.
- Mathlib grep: `nodal|SplitNode|split_node|splitNode` in `AlgebraicGeometry`.
  Zero hits.
- LeanSearch: "nodal curve finite separable extension split node completed local ring".
  Eight hits about formal unramifiedness and separability, none asserting this theorem.
- Source `WeilConjectures` grep for nodal and split-node names: only contextual
  comments about singular duality/projection formula/Kunneth. Searching the node id
  finds no declaration.
- Project `lean/Sheaf` search found `Orgogozo.nodeRing` and
  `Orgogozo.IsOrdinaryDoublePoint`, which are reused, and the existing pure-dimension
  and geometric-nodal-fibre definitions. `HasNodalGeometricFibres` also imposes
  connectedness/nonemptiness and therefore is not substituted for hgeom.
- The proposed declaration name was searched in Mathlib/source/project names;
  no existing declaration was found.

Validation: `scompile.py Q03 lem-trf-nodal-point-finite-separable-splitting` compiled
both its sandbox pass and its library-path pass cleanly, with no errors or warnings.
The initial elaboration failures were repaired by specifying `C := Scheme.{u}` for
pullbacks in point-type positions and spelling out the residue-map function application.
No mathematical statement change was needed. Every line of the module is at most 100 characters.
No STATEMENT-DISPUTED issue was found.

## Second reading by Q03

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
