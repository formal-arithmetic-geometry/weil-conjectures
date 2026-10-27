## Worker report

Item: `lem-sfb-group-difference-diagonal-domain`.
Module: `Sheaf.AlgebraicGeometry.GroupDifferenceDiagonalDomain`.
Main declaration: `AlgebraicGeometry.group_difference_diagonal_domain`.
Helper: `AlgebraicGeometry.groupDifferenceOnOpen` is the actual multiplication/inverse
construction of the map φ already introduced by this node. It has real data and no sorry.
The sole postponed theorem is the item's theorem; its complete eight-step proof, with
all dependency identifiers, is in its docstring. No independent notion or dependency
module is added. The DAG copy changes only `lean`.

Source read: local `literature/milne-abelian-varieties_AV.pdf`, Chapter I, Lemma 3.3,
printed p.17, extracted with pdftotext. Its first paragraph constructs the difference by
multiplication and inverse, proves the two extension implications at the diagonal, and
identifies the diagonal value with e. The accepted DAG's scheme-theoretic argument
replaces the source's choice of a point u by flat density and fpqc descent. No statement
correction is needed. The previous BLOCKED ending concerned a stage-1 split already
merged from NR; the current node has no lean record and is explicitly in queue stage 2.

Every hypothesis and clause is rendered as follows:

| Node text | Lean rendering |
| --- | --- |
| k is a field | `(k : Type u) [Field k]` |
| X is a k-scheme | `X : Over (Spec (.of k))`; structure morphism `X.hom` |
| X nonempty and integral | `[IsIntegral X.left]`; its `nonempty` field includes nonemptiness |
| X separated | `[IsSeparated X.hom]` |
| X finite type | `[LocallyOfFiniteType X.hom] [QuasiCompact X.hom]` |
| X smooth over k | `[Smooth X.hom]` |
| G is a k-group scheme | `G : Over (Spec (.of k))` and `[GrpObj G]` |
| G smooth, connected, separated, finite type | `[Smooth G.hom] [ConnectedSpace G.left] [IsSeparated G.hom] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]` |
| Identity e | `(MonObj.one (X := G)).left : Spec (.of k) ⟶ G.left` |
| U dense open in X | `U : X.left.Opens`, `hU : Dense (U : Set X.left)` |
| f is a morphism over k | `f : U.toScheme ⟶ G.left`, `hf : f ≫ G.hom = U.ι ≫ X.hom` |
| X ×_k X and its diagonal | `pullback X.hom X.hom`, `pullback.diagonal X.hom` |
| Ω open containing the whole diagonal | `Ω` is an ambient open; `hΩ : (pullback.diagonal X.hom) ⁻¹ᵁ Ω = ⊤` |
| H = Ω ∩ (U ×_k U) | `hH` identifies H with Ω intersected with both projection inverse images of U |
| φ(x,y) = f(x)f(y)⁻¹ as a scheme morphism | `hφ` identifies φ with `groupDifferenceOnOpen`, which restricts both projections using `resLE`, composes with f and then inversion on the second factor, pairs by `pullback.lift`, and composes with `(MonObj.mul (X := G)).left` |
| D is the union of all local extensions | `hD` is exactly `D = sSup {V | ∃ F, F over k ∧ F agrees with f on V ⊓ U}` |
| B is the union of all difference extensions in Ω | `hB` is exactly `B = sSup {N | N ≤ Ω ∧ ∃ c, c over k ∧ c agrees with φ on N ⊓ H}` |
| There exists a unique k-morphism b on B | `∃! b : B.toScheme ⟶ G.left` with the base-commutation equation and universal local compatibility |
| b restricts to every b_N | The universal quantifiers over N, `hNB : N ≤ B`, and every c satisfying the two extension equations conclude `homOfLE hNB ≫ b = c` |
| Δ⁻¹(B) = D | The conclusion begins `∃ hδ : (pullback.diagonal X.hom) ⁻¹ᵁ B = D` |
| b composed with Δ on D equals e composed with the structure map | `(pullback.diagonal X.hom).resLE B D (le_of_eq hδ.symm) ≫ b = D.ι ≫ X.hom ≫ (MonObj.one (X := G)).left` |
| All scheme points; no rational-point or geometric-integrality assumption | The equality is in the lattice of all scheme opens, and the final equality is of scheme morphisms; there are no rational-point, algebraic-closure, or geometrically-integral hypotheses |

The equations `hH`, `hφ`, `hD`, `hB` are explicit presentations of the objects defined
in the node, rather than additional restrictions on its input. Each is always instantiable
by the displayed definition. In particular, the statement has no `let` binders and
all universes and variables are explicit (`set_option autoImplicit false`).

An open of Ω is represented as an ambient open N with `N ≤ Ω`, via the usual
inclusion of an open subscheme. Its structure map is the first projection followed
by `X.hom`, equal to the second projection followed by `X.hom`. Thus `hB` computes
the same union as the node's B, viewed in the product. Every extension open N in
`hB` satisfies `N ≤ B` by the defining supremum, so the universal compatibility clause
covers every b_N in the node. Conversely `hB` implies `B ≤ Ω`, hence every N with
`N ≤ B` lies in Ω. This change of representation neither adds nor removes an open.

The leading existential `hδ` asserts an equality of opens, not an extra data choice.
Its symmetric equality supplies the inclusion required by Mathlib's `resLE` for the
restricted diagonal. The uniqueness quantifier includes the diagonal identity in its
predicate. Uniqueness of compatible gluings itself follows already from the local
compatibility clause: the extension opens defining B cover B, so two compatible maps
agree on this cover. Thus including the identity does not drop the node's uniqueness
assertion for compatible morphisms.

Dependency declarations read and used:

- `def-weil-field`: Mathlib `Field`, in `Mathlib.Algebra.Field.Defs`, the commutative
  division-ring class. Nontriviality is inherited; the zero ring is excluded.
- `def-pc-integral-scheme`: `AlgebraicGeometry.IsIntegral`,
  `Mathlib.AlgebraicGeometry.Properties`; nonempty and domains on all nonempty opens.
- `def-weil-pbc-scheme-conventions`: its recorded convention deliberately has no
  declaration. Separated is `AlgebraicGeometry.IsSeparated`, finite type is
  `LocallyOfFiniteType` plus `QuasiCompact`, as in the convention record; these are
  read in `Mathlib.AlgebraicGeometry.Morphisms.Separated`, `.FiniteType`, `.QuasiCompact`.
- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth`,
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`; the recorded affine-local definition.
- `def-sc-group-scheme`: `CategoryTheory.GrpObj`,
  `Mathlib.CategoryTheory.Monoidal.Grp`, used on `Over (Spec (.of k))` exactly as its
  record specifies. `GrpObj.inv`, `MonObj.mul`, `MonObj.one` supply the actual maps;
  the interpretation and canonical over-category monoidal structure are exposed by
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`, whose docstring was read.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback`, `.fst`, `.snd`,
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, with `.lift` and
  `.diagonal`. `Scheme.Hom.resLE` and `Scheme.homOfLE`, in
  `Mathlib.AlgebraicGeometry.Restrict`, give actual canonical restrictions.

All stated proof-dependency modules are imported non-publicly: Noetherian,
SchemeTheoreticallyDominant (Mathlib and upstream), Smooth and Flat (already public
through the statement's Smooth import), Proper (which exposes the permanence modules),
UniversallyOpen, ModuleCat.Descent and Adjunction.Additive for scalar extension,
FpqcMorphismsDescend (which exposes Sites.Fpqc). These provide respectively the
Noetherian implication, reduced dense-image theorem, density and separated-target
rigidity, open/smooth/flat calculus, permanence, openness, scalar extension exactness,
and descent. The recorded upstream signatures `Scheme.Hom.ker_pullback_snd`,
`ext_of_isSchemeTheoreticallyDominant`, and `Scheme.fpqc_morphisms_descend` were read
with their docstrings. None is copied or replaced.

Edge cases checked before writing:

- U = X: f extends everywhere, so D = X; its difference extends throughout Ω,
  so B = Ω and the diagonal identity follows from g g⁻¹ = e.
- Constant f: the difference is identically e; again B = Ω and D = X.
- The identity/trivial group scheme, and empty local opens V or N: the definitions
  and compatibility equations still use actual morphisms; empty intersections impose
  the correct unique empty restriction.
- X = Spec L for a nontrivial finite separable L/k: X is integral and smooth but
  need not be geometrically integral and may have no k-point. The product can be
  disconnected. The statement allows this, an arbitrary Ω, and every scheme point.
- General U without k-points and nonclosed x: neither any construction nor any
  binder chooses a rational point. The docstring retains the residue-field/fpqc route.
- Noncommutative G: the inverse is on the second factor and multiplication order
  is exactly f(x)f(y)⁻¹. There is no `IsCommMonObj` assumption.
- Empty X is excluded by precisely the stated integrality/nonemptiness assumption;
  an empty U cannot be dense in this X. No extra nonemptiness binder is added.
- A single explicit universe u covers schemes and the field, with no quantification
  over a too-small independent test universe. No geometric-integrality condition is used.

Searches made with the prescribed msearch.py wrapper and direct rg:

- `grep` query `difference.*diagonal|diagonal.*difference|extensionDomain`: 0 hits; no hits.
- `loogle` query `"AlgebraicGeometry", "RationalMap"`: 12 hits; AlgebraicGeometry.Scheme.RationalMap, AlgebraicGeometry.Scheme.RationalMap.id, AlgebraicGeometry.Scheme.RationalMap.domain, AlgebraicGeometry.Scheme.Hom.toRationalMap.
- `leanfinder` query `The domain of extension of a group valued rational map equals the inverse image along the diagonal of the extension domain of its difference map`: 8 hits; AlgebraicGeometry.Scheme.RationalMap.domain, Function.extend_sub, AlgebraicGeometry.Scheme.PartialMap.le_domain_toRationalMap, AlgebraicGeometry.Scheme.RationalMap.mem_domain.
- `leansearch` query `A rational map to a group scheme extends at a point exactly when its difference map extends at the diagonal point`: 8 hits; AlgebraicGeometry.Scheme.RationalMap, AlgebraicGeometry.Scheme.PartialMap.noConfusionType, AlgebraicGeometry.Scheme.RationalMap.IsOver.exists_partialMap_over, AlgebraicGeometry.Scheme.RationalMap.ofFunctionField.

The LeanFinder/LeanSearch/Loogle hits are rational-map and partial-map APIs, not a
comparison of the difference extension domain with the diagonal preimage. Source was
opened at `Birational/RationalMap.lean`: a partial map records a dense domain and morphism,
and equivalence is agreement on a dense subopen. These are useful general notions but do
not state this lemma; the present statement uses the node's own explicit union formula.
Direct rg over `lean/WeilConjectures`, `lean/Sheaf`, Mathlib and the upstream name index
found neither new declaration name. Searches for `difference.*[Dd]iagonal`,
`[Dd]iagonal.*difference`, `extensionDomain`, and the exact node id found no existing
statement; the downstream divisorial-indeterminacy module only mentions this item in
its proof docstring. No private copy of any existing notion was introduced.

Validation: scompile.py compiled the delivered module separately in sandbox and library
module modes, 1.7 seconds each, with no errors or non-sorry warnings. No local Lake or
global build was run. There is no STATEMENT-DISPUTED finding and no node fault.

## Second reading by Q12

A fresh second pass in this worker reread the node, source paragraph, helper construction,
and full theorem signature. The dispatcher explicitly prohibits starting other agents;
this section records a second reading, not a claim of an independent worker review.
The maintainer independently reviews the delivered statement.

The reread checked every row of the mapping above against the actual signature. The
helper's first factor is f after the first restriction, its second factor is f followed
by inversion after the second restriction, and its last map is multiplication. The
pullback compatibility proof uses only the over equations and pullback condition.
The reading checked the `inf_le_left.trans inf_le_right` inclusion selects the first
projection's U condition in the left-associated threefold intersection, and the other
inclusion selects the second. No component-integrality assumption enters.

The D union uses agreement on V ∩ U; it does not require V to contain U. The B union
uses agreement on N ∩ H and N contained in Ω. The final local compatibility covers all
extensions contributing to B because every such N lies in B; conversely B lies in Ω.
The final map is the actual restricted diagonal via the asserted open equality, and
its right side is the structure morphism followed by the group identity section.
The universe and all scheme-property binders agree with the node. No mismatch was
found, so no mathematical statement or accepted stage-1 split was changed.
