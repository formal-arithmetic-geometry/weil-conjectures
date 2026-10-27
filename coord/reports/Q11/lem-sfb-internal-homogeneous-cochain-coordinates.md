## Worker report

The module `Sheaf.CategoryTheory.InternalHomogeneousCochainCoordinates` states
`CategoryTheory.CondensedBar.exists_internalHomogeneousCochainCoordinates` with `sorry`.
Its conclusion supplies simultaneous internal function/bar presentations and the
coordinate isomorphisms for every profinite group. Simultaneous presentation merely
packages the universal group-restriction naturality in the node; it puts no hypothesis
on a group or coefficient object. The ordinary derived isomorphism is included in the
conclusion and is fixed to be localization of the displayed cochain maps.

All other declarations are definitions or structures specifying exactly the complexes,
evaluations and maps in this node. They are local helpers of the owning mathematical
notion, publicly recorded in `lean.declarations`; no new independent notion or new DAG
node is needed. Their data are written in full. In particular, there is no choice of a
map or complex from a bare existence theorem. `coordinateLocalization` is literally
Mathlib's `DerivedCategory.Q` with `HasDerivedCategory.standard`.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node clause | Lean rendering |
| --- | --- |
| Arbitrary commutative condensed ring on the small coherent profinite site | `A : CondensedBar.Ring.{u}`, the existing `CommMon` of abelian sheaves on `coherentTopology Profinite.{u}`. Its underlying `A.toMon` is the recorded `Profinite.CondensedRing`. |
| Profinite group J, and every profinite group K in the restriction assertion | `J K : ProfiniteGrp.{u}`. This bundles all and only a profinite set, group, and continuous group operations. |
| Internal A-module with A-linear condensed J-action | `M : Equivariant A J`, exactly the existing `Profinite.CondensedAction.ActionModule A.toMon J`; no topological presentation of M. |
| Internal Hom from the free module A[P] | The existing `InternalFunctions A`, including its `internalHom : functor P ≅ Mod.ihom (freeParameter A P)`, and its natural, additive, scalar-linear evaluation equivalences. |
| Homogeneous degree n is the indicated submodule sheaf, including the condition after every base change | `InternalHomogeneousCochains.inclusion`, `injective`, and `image`. The image is exactly `IsHomogeneousSection`, quantified over `S T`, `f : T ⟶ S`, `a : C(T,J)` and the entire continuous tuple. The inclusion is an internal A-module morphism, so this specifies the precise subobject, up to its unique inclusion-preserving isomorphism. |
| Alternating deletion differential | `InternalHomogeneousCochains.differential`: sum over `i : Fin (n+2)` with integer signs `(-1)^i.val` and omission using `i.succAbove`. The complex field itself retains the square-zero equations. |
| Inhomogeneous cochains and the action-dependent bar differential | Existing `BarDiagram`, `cochains`, `BarDiagram.term`, `face`, `degeneracy`, and `maps`; the first face is the action face, interior faces multiply adjacent entries, and the last face drops the final entry. |
| Complexes zero in negative degrees | Both nonnegative complexes are extended using the existing `CondensedBar.extend`, namely `HomologicalComplex.extend` along `ComplexShape.embeddingUpNat`, in the derived field. |
| Internal linear cochain maps Phi and Psi, mutually inverse | `InternalCochainCoordinates.coordinates J` is a natural isomorphism between functors to `CochainComplex (Modules A) ℕ`. Its `.hom.app M` and `.inv.app M` are actual cochain maps. Iso identities give both inverse equations; the `Hom.comm` equations give both differential equations. |
| Phi evaluation at (1,g1,g1g2,...) | `InternalCochainCoordinates.phi` and `coordinatePrefixes`. A prefix is the ordered product of the first `i.val` entries of `List.ofFn g`; the zeroth prefix is the empty product 1. |
| Psi evaluation x0 c(x0^-1 x1,...,x(n-1)^-1 xn) | `InternalCochainCoordinates.psi` and `coordinateQuotients`, with the existing section action `M.act T (x 0)`. |
| Formulas over every test set and all its base changes | Both formulas quantify over `S T : Profinite.{u}` and every `f : T ⟶ S`; the inherited function evaluation is a natural family on the entire slice. |
| Naturality for all equivariant internal coefficient maps | `coordinates J` is a natural isomorphism in `Equivariant A J`. `InternalHomogeneousCochains.maps` fixes its homogeneous coefficient maps to postcomposition; `BarDiagram.maps` does the same on the inhomogeneous side. |
| Naturality under profinite base change | All cochain components and submodule inclusions are internal sheaf/module morphisms, hence commute with the sheaf restriction maps. `InternalFunctions.restriction` and `FunctionFamily.IsNatural` fix evaluation compatibility; the coordinate formulas retain arbitrary slice maps f. |
| Restriction along any continuous homomorphism u:K→J, with the restricted action | `homogeneousRestriction`, `inhomogeneousRestriction`, with the exact existing `Profinite.CondensedAction.inflate v`; both are natural transformations valued in cochain complexes. Their `_eval` fields fix both maps by tuple precomposition with `v.toContinuousMap`. |
| R Psi_J = Psi_K r and r Phi_J = Phi_K R | `restriction_psi` and `restriction_phi`. Category composition `≫` reads left-to-right, giving precisely the node's two squares. |
| Degree zero Phi_0 F=F(1) and Psi_0 m(x)=xm | `zero` identifies C^0 with M; `zero_eval` fixes that identification by empty-tuple evaluation on every slice. `phi_zero` and `psi_zero` state exactly the two requested formulas, the latter after every base change. |
| Isomorphism in the ordinary derived category represented by those maps | `InternalCochainCoordinates.derived` gives `e` in the codomain of `coordinateLocalization A`, explicitly equating `e.hom` and `e.inv` to Q applied to extension by zero of the two coordinate maps. |
| No injectivity, trivial action, rationality or representability assumption | The only theorem input is `A`. The quantified objects are every `Equivariant A J`; all the model and coordinate data occur in its conclusion, never as additional hypotheses. |

Dependency declarations read and used:

- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing` (through the public
  imports of the bar-data module); the bundled `CondensedBar.Ring` is its commutative form.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod`, `ModObj`, and their internal
  morphisms, through the recorded module/action declarations.
- `Sheaf.CategoryTheory.CondensedActionModule`: `Profinite.CondensedAction.ActionModule`,
  `Equivariant`, `inflate`, with its exact underlying unchanged module and section action.
- `Sheaf.CategoryTheory.CondensedEquivariantBarData`: `Ring`, `Modules`, `sections`,
  `sectionModule`, `InternalFunctions`, `FunctionFamily.IsNatural`, `power`, `tupleMap`,
  `freeParameter`, `BarDiagram`, `cochains`, `extend`. The full source signatures and
  docstrings were read, including the primary recorded `CondensedBar.Assertion`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory.standard`, `DerivedCategory.Q`; inherited through the public bar-data
  import. No extra derived-category existence hypothesis is imposed.
- `def-weil-size-convention` is explicitly a convention-only node: `u` fixes profinite
  test objects and groups; abelian section values live in `u+1`, internal module objects
  and the ordinary large localization in `u+2`, matching the recorded bar datum.
- `Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic`: `ProfiniteGrp`, supplying the
  already existing bundled form of a profinite group, rather than a new definition.

The three proof dependencies are already public statement dependencies of the bar-data
module or used directly here. No separate redundant proof import or import cycle is added.

Edge cases checked before and after writing:

- n=0: prefixes give the one-entry tuple (1); quotients are empty; the two deletion terms
  give F(g)-F(1), corresponding to gm-m. `zero_eval`, `phi_zero`, `psi_zero` retain the exact
  degree-zero normalization, not only a claim about positive degrees.
- n=1: prefixes (1,g), quotients x0^-1 x1. Deleting each position in the length-three
  homogeneous tuple yields action, multiplication, and final faces in exactly that order.
- Noncommutative J: `List.prod` uses increasing tuple order, and the quotient is
  left inverse times the next element; no reordering is used.
- Trivial J: degree maps have alternating sums (zero or identity according to parity),
  so the statement does not inadvertently claim all positive differentials vanish.
- Zero M and the zero coefficient ring: no faithfulness/nonzero assumptions exclude them.
- Empty profinite test sets: the formulas and slice quantifiers remain defined. No
  inhabitance of a test set is assumed. Every group itself is inhabited by its unit.
- Characteristic two: signs act by integer scalar multiplication in the section abelian
  group, so pair cancellation still works; no division by an integer occurs.
- All continuous homomorphisms, including the identity and the constant unit map, are
  allowed; no injectivity, surjectivity, finite-index or open-image hypothesis is present.
- Negative degrees are the canonical zero extension, not extra arbitrary degrees.

Searches made:

1. `msearch.py ... leanfinder "Internal condensed module homogeneous equivariant cochains
   are naturally isomorphic to inhomogeneous cochains by cumulative products"`: eight
   hits, headed by `groupCohomology.inhomogeneousCochainsIso`; all concern ordinary or
   topological coefficient representations rather than arbitrary internal condensed modules.
2. `msearch.py ... loogle '"homogeneous", "cochains"'`: twelve hits, including
   `TopRep.homogeneousCochains`, `groupCohomology.inhomogeneousCochainsIso`, and differential
   formulas. Neither category is the internal condensed-module category of this node.
3. `msearch.py ... grep 'homogeneous|inhomogeneous' RepresentationTheory/Homological`:
   25 hits in Mathlib continuous/ordinary group cohomology, with no internal condensed match.
4. `rg` of `lean/WeilConjectures` and `lean/Sheaf` for homogeneous/inhomogeneous cochains
   and coordinate names; also `grep -rn` for the exact node id in `lean/WeilConjectures`.
   Existing `HomogeneousInhomogeneousContinuousCohomology` and related modules use
   `TopRep`, not internal condensed coefficients. No duplicate of this statement was found.
5. Exact helper-name search in Mathlib, both source roots and `dag/lean_names_upstream.json`:
   no existing declaration has any of the new full names.
6. `tools/blueprint_refs.py search 'homogeneous cochain'` and reading the current blueprint
   direct-image proof, paragraph (3), as well as Stacks `etale-cohomology.tex`,
   `section-continuous-group-cohomology` (0DVG), including its n=0 differential. This node
   is the agent's explicit internal-sheaf adaptation, as its source field already says.

No statement correction, dependency repair, new node, or disputed mathematical assertion.
The accepted Q101 stage-1 statement, proof split and all other fields are preserved.
The inherited BLOCKED report concerned stage-1 re-splitting: `coord/brief-stage2.md` §0
expressly authorizes proceeding with this stage-2 handoff, and the live queue lists stage 2.
There is no released repair note for this item.

Validation: `scompile.py Q11 lem-sfb-internal-homogeneous-cochain-coordinates <module>`
checks the single file against the live published library, both under its sandbox and its
final module name. Only the final theorem is postponed; every helper has real data.
The maintainer supplies the independent delivery review under this dispatcher's brief.

## Second reading by Q11

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
