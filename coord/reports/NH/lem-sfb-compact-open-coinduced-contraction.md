## Worker report

Item: `lem-sfb-compact-open-coinduced-contraction`, group NH, stage 2.

The module `Sheaf.RepresentationTheory.CompactOpenCoinducedContraction` states
`ContinuousCohomology.exists_compactOpenCoinducedContraction`, with one `sorry` as
its whole proof. Its docstring contains all seven steps of the DAG proof. The
statement is unchanged, as are its dependencies and every other existing node field
except `lean`. No new nodes or dependency repairs are needed.

The bundle `CompactOpenCoinducedContraction` specifies the objects uniquely up to
evaluation-preserving isomorphism, using the already landed coordinate dependency's
method. It does not select data from the existence theorem. The only helper definitions
construct the ordinary coefficient single complex and its degree-zero evaluation using
Mathlib's `HomologicalComplex.single` and `singleObjXSelf`, with actual data throughout.
The structure and helpers belong to this same contraction and are recorded in
`lean.declarations`.

Hypotheses and clauses, matched individually:

- Compact Hausdorff abelian additive group J: `(J : Type v) [AddCommGroup J]`
  `[TopologicalSpace J] [IsTopologicalAddGroup J] [CompactSpace J] [T2Space J]`.
- Topological field k: `(k : Type u) [Field k] [TopologicalSpace k]`
  `[IsTopologicalDivisionRing k]`.
- Hausdorff topological k-vector space with continuous vector operations:
  `(V : Type w) [AddCommGroup V] [Module k V] [TopologicalSpace V]`
  `[IsTopologicalAddGroup V] [ContinuousSMul k V] [T2Space V]`.
- R is exactly `C(J, V)`, Mathlib's continuous maps with compact-open topology;
  its vector and topological structures are Mathlib instances. It is never replaced
  by discrete maps, locally constant maps, or iterated cochains.
- Translation is the bundled `action`, fixed by `action_apply` to
  `action a f y = f (y + a.toAdd)`. `action_continuous` states joint continuity.
  `Multiplicative J` is Mathlib's type tag carrying the same topology and elements;
  multiplication is addition in J. This uses the existing multiplicative coordinate
  API without redefining any homogeneous or inhomogeneous cochain notion.
- The existing `JointContinuousCochainCoordinates k (Multiplicative J) C(J,V) action B C`
  is the field `coordinates`. Its `bRange`/`cRange` give exactly jointly continuous
  equivariant homogeneous cochains and jointly continuous inhomogeneous cochains,
  its differential fields give exactly the specified differentials, its `iso`, `phi`,
  and `psi` give the prescribed two coordinate formulas, and its negative fields
  extend both complexes by zero. Degree zero uses the continuous functions on the
  empty tuple, canonically equal to R, exactly as in the dependency's recorded API.
- D consists of the jointly continuous functions on `Fin (n+1) → J`:
  `eval` is linear and `injective`, and `range` says its image is *exactly* `Continuous f`.
  Consequently the abstract vector-space representation neither loses nor adds
  cochains, and its operations are the pointwise ones. `negative` specifies zero
  below zero. `delta` is the alternating omission formula, with `a.succAbove`
  deleting a coordinate and `(-1 : k)^a.val` its sign.
- The mutually inverse linear cochain maps Theta are the actual complex isomorphism
  `theta : B ≅ D`; `theta_apply` evaluates at zero and `theta_inv_apply` fixes its
  inverse to `phi(x_0+y,...,x_n+y)`. A complex isomorphism includes linearity,
  commutation with differentials and both inverse equations.
- The insertion maps in degree q≥1 are `h n`, with q=n+1. `h_apply` is precisely
  precomposition with `Fin.cons 0 x`. Each output belongs to D and hence is an actual
  continuous cochain by `range`; no assertion of operator continuity is added.
- V[0] is `compactOpenCoefficientSingle`, the ordinary integer-indexed single complex
  on `ULift V`. `compactOpenSingleEval` uses its canonical degree-zero isomorphism and
  `ULift.down`. The lift merely places V in the same category as function spaces;
  `ULift.moduleEquiv` is the canonical linear equivalence with V. Its carrier and
  universe are fully specified, not obtained from a sorry theorem.
- `i` and `p` are actual cochain maps; `i_apply` specifies the constant inclusion in
  degree zero, and `p_apply` specifies evaluation at the all-zero singleton tuple.
  Outside degree zero the single complex is zero, so their components there are the
  unique zero arrows. The field `pi : i ≫ p = 𝟙 _` is the node's pi=1, in Lean's
  left-to-right composition convention.
- `contraction : Homotopy (𝟙 D) (p ≫ i)` states `id = dh + hd + ip` using Mathlib's
  homotopy convention. `contraction_h` identifies its positive-degree components
  with insertion; `contraction_h0` sets h0 to zero. Components in negative degrees
  are uniquely zero because D vanishes there.
- `equiv : HomotopyEquiv C V[0]` is the asserted actual chain homotopy equivalence.
  `equiv_hom` is pT and `equiv_inv` is T-inverse i, with
  T=Theta Phi-inverse. `equiv_h` specifies its homotopy as the negative of
  T-inverse h T: Mathlib's equivalence homotopy is oriented IP to id, opposite to
  `contraction`, so this minus sign is necessary. It introduces no stronger condition.
- `derived` is an actual isomorphism `DerivedCategory.Q.obj C ≅ Q.obj V[0]`.
  `derived_hom` and `derived_inv` fix its representatives to the specified cochain
  maps. The abstract derived category and its localization functor are exactly
  Mathlib's recorded dependency.
- `primitive` says that for every n≥0 a closed cochain in degree n+1 is the
  differential of an element in degree n. The `cRange` field in `coordinates` ensures
  that both are actual continuous inhomogeneous cochains. The specified transported
  homotopy also supplies the node's explicit primitive formula.
- There are no discreteness, completeness, normability, finite-dimension, or
  local-compactness assumptions on V. No characteristic is restricted.
- `u`, `v`, `w`, `t`, `r` are explicitly bound independent universes. Function-space
  carriers lie in `max v w t`. `[HasDerivedCategory.{r} (ModuleCat.{max v w t} k)]`
  records the chosen size of localization morphisms, as required by the recorded
  abstract-derived-category interface. No equality of coefficient/group universes is
  imposed. Helpers have explicit universe applications to avoid max-universe ambiguity.

Dependencies read and used:

- `Sheaf.RepresentationTheory.TopologicalHomogeneousCochainCoordinates`:
  `ContinuousCohomology.JointContinuousCochainCoordinates` and
  `exists_jointContinuousCochainCoordinates`. Read the full structure and both
  theorem docstrings/signatures, including the naturality theorem. The structure is
  reused directly, not duplicated; its existence theorem is the proof input.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, and `DerivedCategory.Q` (the abstract derived-category node).
- Proof-only Mathlib leaves: `WeaklyLocallyCompactSpace.locallyCompactSpace` in
  `Mathlib.Topology.Separation.Basic`, with Hausdorffness supplying R1; and
  `ContinuousMap.curry`, `ContinuousMap.uncurry` in `Mathlib.Topology.CompactOpen`.
  Their full source signatures/docstrings were read. They are available through the
  imported Hausdorff and continuous-map modules. The proof docstring names both nodes.
- Mathlib `Homotopy`, `HomotopyEquiv` in `Algebra.Homology.Homotopy`,
  `HomologicalComplex.single`/`singleObjXSelf` in `Algebra.Homology.Single`, and
  the standard module instances on ULift are used directly.

Edge cases checked before writing: J is inhabited by zero, including the trivial group;
V may be the zero vector space; degree zero has differential phi(x1)-phi(x0), and
h1 delta gives phi(x)-phi(0), rather than phi(x). Empty inhomogeneous tuples correctly
model C0. Below zero all spaces are zero. The insertion cancellation remains valid in
characteristic two. All continuity arguments work for nondiscrete, incomplete V.
Compactness is used for compact-open evaluation and joint action, not to impose an
unmentioned finiteness condition on a cochain. Homotopy signs were checked against
Mathlib's exact `Homotopy.comm` convention.

Searches for an existing statement:

- `msearch.py ... leanfinder "Continuous coinduced functions compact open topology
  homogeneous evaluation at identity insertion contracting homotopy"`: 8 hits on
  loop insertion, condensed coinducing maps, and topological homotopies; no match.
- `msearch.py ... loogle "ContRepresentation.coind₁, ContinuousMap"`: 12 hits on
  continuous coinduction and its maps. Read `ContRepresentation.coind`, `coindV`,
  `coind₁` and the evaluation formula in `Mathlib.RepresentationTheory.Continuous.Basic`.
  `coind₁` uses the twisted action π(g)f(g-inverse x), not this specified positive
  right-translation contraction. None states Theta, its insertion contraction, or
  the derived conclusion for arbitrary V.
- `msearch.py ... grep "coind₁|coinduced|contract" RepresentationTheory/Continuous`:
  10 hits on coinduction in `Basic`/`TopRep`, no matching contraction.
- Local `rg` on `coinduced|Coinduced|insertion|Contraction` in the project's
  `lean/Sheaf/RepresentationTheory` and `lean/WeilConjectures/RepresentationTheory`,
  and broader `compact-open|coinduced.*contraction` searches in both roots:
  existing locally constant/discrete coefficient contractions and coordinate
  comparisons only. In particular the `CoinducedHomotopyContinuous` and
  `CoinducedContinuousAcyclic` APIs require discrete coefficients, so do not match.
- `rg` on the item id in `lean/WeilConjectures` and on the selected declaration
  names in both roots and `dag/lean_names_upstream.json`: no existing declaration.
  No new mathematical notion outside the item's explicit constructions was needed.

Sources: read the current `literature/blueprint/latest/.../` direct-image proof,
paragraph (3). It gives the open direct-image reduction; this analytic input is correctly
marked agent-written in the DAG. The Lean proof docstring preserves that attribution
and does not attribute the contraction itself to Stacks Tag 0DVG. No statement fault,
statement correction, or STATEMENT-DISPUTED issue was found. The historical example
`Sheaf/CategoryTheory/CompactObject.lean` is withdrawn; its node now records
`WeilConjectures.CategoryTheory.CompactObject`, whose live module was read instead.

Validation: the prescribed `scompile.py NH lem-sfb-compact-open-coinduced-contraction`
compiled this single file on the server as both sandbox and its actual library module,
with no errors or warnings. One initial universe-linter warning and unresolved ambient
universe constraint were repaired by giving the helper a single ambient lift universe
and explicitly supplying the structure universes. No global build or direct repository
write or git command was run. All authored files are in the assigned sandbox.

## Second reading by NH

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
