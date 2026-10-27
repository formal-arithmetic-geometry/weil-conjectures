## Worker report

The module `Sheaf.AlgebraicGeometry.DedekindActionBoundaryAmple` states
`AlgebraicGeometry.Scheme.Modules.isAmple_dual_cartierIdeal_of_affine_orbit_complement`.
Its only proof is `by sorry`; it introduces no definitions, assumptions in disguise,
or auxiliary theorems. The node is unchanged except for its `lean` record.

Source checked: BLR, Néron Models, §6.4 Proposition 2, printed pp.153–154,
PDF pp.159–160, in the primary scan at
https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf.
The source gives relative ampleness; the node uses the affine-base absolute form
(Stacks 01VK). The explicit separatedness and finite-type assumptions are retained
exactly as the assigned node states them. No statement correction is needed.

Hypotheses and clauses, individually:

| Node text | Lean rendering |
| --- | --- |
| D a domain | `(D : Type u) [CommRing D] [IsDomain D]` |
| Noetherian | `[IsNoetherianRing D]` |
| Integrally closed | `[IsIntegrallyClosed D]` |
| Krull dimension one | `(hdim : ringKrullDim D = 1)` |
| S = Spec D | The base of `H X : Over (Spec (CommRingCat.of D))` is literally this spectrum; no arbitrary base or unrecorded identification is used. |
| H a relative group scheme | `[GrpObj H]`: multiplication, identity, inverse in the cartesian category `Over S`, with all group diagrams. |
| H smooth | `[Smooth H.hom]` |
| H separated | `[IsSeparated H.hom]`; its definition is precisely the closed-immersion diagonal condition. |
| H finite type | `[LocallyOfFiniteType H.hom] [QuasiCompact H.hom]` |
| H geometrically connected fibres | `[GeometricallyConnected H.hom]`; the class quantifies over field-valued base changes and is equivalent to geometric connectedness of every fibre. |
| X smooth | `[Smooth X.hom]` |
| X separated | `[IsSeparated X.hom]` |
| X finite type | `[LocallyOfFiniteType X.hom] [QuasiCompact X.hom]` |
| a an S-action with unit and associativity | `[ModObj H X]`, whose action morphism is `(γ[H, X]).left`; both laws are fields of `ModObj`. |
| E an effective Cartier divisor | `J : X.left.IdealSheafData` and `hJ : J.IsInvertible`; the existing predicate says each point has an affine neighbourhood with a single non-zero-divisor generator. The corresponding closed subscheme is `J.subschemeι`. |
| A = X minus the support of E | `J.support.compl`; this is the complement of the existing ideal-sheaf support, not the support of its underlying invertible module. |
| A affine | `haffine : IsAffineOpen J.support.compl` |
| H ×_S A → X surjective on underlying points | `horbits : ∀ x : X.left, ∃ z : (H ⊗ X).left, (snd H X).left z ∈ J.support.compl ∧ (γ[H, X]).left z = x`. The chosen tensor in `Over S` is the scheme fibre product. Its open inverse image under the second projection is precisely H ×_S A, so this condition is exactly surjectivity of the restricted action. |
| O_X(E) = I_E dual | `J.toModulesᵛ`, using existing `IdealSheafData.toModules` and `Scheme.Modules.dual`. |
| Invertible | The instance argument is supplied by `hJ.isInvertible_dual_toModules`, a theorem of the recorded dependency, not an additional hypothesis. |
| Absolutely ample | `@IsAmple X.left J.toModulesᵛ hJ.isInvertible_dual_toModules`, the recorded absolute section-locus definition, including quasi-compactness. |
| No transitivity, properness, commutativity or Néron property assumed | There is no such binder or condition. In particular `horbits` is orbit coverage by A, not a transitivity condition. |

Dependencies read and used (declaration signatures and docstrings were opened):

- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Spec`.
- `def-pc-scheme`: the same module, `AlgebraicGeometry.Scheme` and its morphisms.
- `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, `AlgebraicGeometry.Smooth`.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`, and its quasi-compact component
  `AlgebraicGeometry.QuasiCompact` in `Morphisms.QuasiCompact`.
- `def-weil-connected-scheme`: `ConnectedSpace` in `Mathlib.Topology.Connected.Basic`.
  `Mathlib.AlgebraicGeometry.Geometrically.Connected` supplies the existing fibrewise
  form `AlgebraicGeometry.GeometricallyConnected`, using `ConnectedSpace` without
  defining connectedness again.
- `def-sc-group-scheme`: `Mathlib.CategoryTheory.Monoidal.Grp`, `CategoryTheory.GrpObj`,
  applied to the relative category rather than only a field base.
  The action is the existing `CategoryTheory.ModObj` of `Monoidal.Mod`.
- `def-weil-closed-immersion`: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion`, used through the exact definition of
  `IsSeparated` in `Morphisms.Separated`.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback` and its projections from
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`. The cartesian
  monoidal structure on `Over S` uses these chosen scheme pullbacks; its second
  projection is `CartesianMonoidalCategory.snd`.
- `def-nagata-effective-cartier-ideal`:
  `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible`,
  `AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible`.
- `def-pc-divisor-line-bundle`: `WeilConjectures.AlgebraicGeometry.EffectiveCartier`,
  `AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.isInvertible_dual_toModules`;
  its existing `IdealSheafData.toModules` and `Scheme.Modules.dual` supply the line.
- `def-sc-invertible-module`:
  `WeilConjectures.AlgebraicGeometry.Modules.Invertible`,
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`.
- `def-weil-pbc-ample-invertible-module`:
  `WeilConjectures.AlgebraicGeometry.Ample`,
  `AlgebraicGeometry.Scheme.Modules.IsAmple`.

The already recorded proof dependencies are imported privately:
`WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus` (canonical section),
`WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor`,
`Mathlib.AlgebraicGeometry.PullbackCarrier` (surjectivity base change),
`Mathlib.AlgebraicGeometry.Noetherian` (finite-presentation comparison),
and `Mathlib.AlgebraicGeometry.Morphisms.Proper` (proper/smooth base change).
Separated and finite-type base-change interfaces come from the public imports
already needed by the statement. The three proof-only nodes
`lem-sfb-dedekind-invariant-component-ample-test`,
`lem-sfb-dedekind-action-square-power`, and
`lem-sfb-square-action-affine-orbit-criterion` have no recorded Lean declarations
in the read DAG; they are named in the full proof docstring, with no guessed import
or restatement. They are not needed to type this statement.

Edge cases checked before writing:

- Empty X is allowed: no `Nonempty X` or surjectivity of X → S is introduced.
  The ideal and orbit conditions and the ample section-neighbourhood condition
  are vacuous there, and the empty scheme is quasi-compact and affine.
- Empty E is allowed (J the unit ideal). Then A = X, and the affine hypothesis
  asserts X affine; the structural line is ample on an affine scheme.
- If A is empty, `horbits` forces X empty. In a nonempty X the second projection
  of a witness cannot lie in the empty open.
- The zero ideal is not an effective Cartier ideal on a nonempty X, so the
  invertibility predicate excludes an accidental whole-scheme divisor.
- Fields and the zero ring are excluded exactly by the node's domain and
  dimension-one assumptions, not by an additional nonfield or locality binder.
- X need not have connected fibres or meet every base point. The pointwise group
  action on a fibre product includes all residue-field extensions; it does not
  replace scheme points by pairs or by rational points.
- The dimension and scheme universes are explicit; `autoImplicit false` ensures
  no accidental variable is inserted.

Searches for an existing declaration:

1. Prescribed `msearch.py` leanfinder query:
   `An effective Cartier divisor with affine complement meeting all group action orbits over a Dedekind scheme has ample associated invertible sheaf`.
   Result: 8 hits, all affine/basic-open and localization results, including
   `AlgebraicGeometry.exists_eq_pow_mul_of_isAffineOpen`,
   `AlgebraicGeometry.Proj.isAffineOpen_basicOpen`; none is this action-ampleness theorem.
2. Prescribed `msearch.py` loogle query: `"IsAmple", "ModObj"`.
   Result: successful search, 0 hits.
3. Prescribed `msearch.py` grep query:
   `boundary.*ample|ample.*orbit|Cartier.*ample`, subdirectory `AlgebraicGeometry`.
   Result: successful search, 0 hits.
4. `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for the node id,
   `boundary.*[Aa]mple|ample.*orbit`: only related `AmpleOrbitAffinePair` and
   `AmpleCurveTwoSectionPencil`, with different statements; no match for this node.
5. `rg` for `GrpObj`, `ModObj`, `GeometricallyConnected`, `ringKrullDim`,
   `support.compl` and the existing dual/invertibility declarations found all
   notions already present. `SquareActionProjImmersionLocusStable` demonstrates
   the same relative action and product interfaces.
6. Exact declaration-name search over Mathlib, both project roots, and
   `dag/lean_names_upstream.json`: no collision.

Validation: `scompile.py N8 lem-sfb-dedekind-action-boundary-ampleness` compiled
both the sandbox and the library module successfully (1.5 s and 1.6 s), with no
errors or warnings. The module has maximum line length 86. The JSON record
contains the exact signature, explicit declaration, date and file path.

No new nodes, dependency repairs, statement changes or disputed statements.

## Second reading by N8

A separate reread in this worker compared the finished signature to every clause
of the node; the maintainer supplies the independent review under the dispatch
brief. No other worker was spawned, and no independent-agent review is claimed.

The reread checked that finite type has both components for H and X, geometric
connectedness is on H only, the effective Cartier predicate is local regular
principality, and the affine open is the divisor support's complement. It checked
that the orbit witness is in the actual fibre product and is restricted by its
second projection, and that the conclusion uses the positive divisor line
`J.toModulesᵛ`, with its derived invertibility proof explicitly supplied. The
relative base is exactly Spec D, and the dimension is equality to one. No omitted
or extra hypothesis, clause, object, or edge case was found; no change was needed.
