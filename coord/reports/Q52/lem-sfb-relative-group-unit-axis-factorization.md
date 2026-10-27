## Worker report

Item: `lem-sfb-relative-group-unit-axis-factorization`, group Q52, stage 2.
The module `Sheaf.AlgebraicGeometry.RelativeGroupUnitAxisFactorization` states
`AlgebraicGeometry.relative_group_unit_axis_factorization` with proof `sorry`.
It also constructs `groupIdentityAxis` and `groupPowerIdentitySection` by `Pi.lift`.
These are the canonical maps explicitly introduced in this node, not additional
hypotheses or new independent notions. They contain real data and no postponed proofs.
All three declarations are recorded in `lean.declarations`.

The node's statement, accepted split, statement dependencies and proof dependencies
are preserved verbatim. Only `lean` is changed. The previous worker's stage-1 refusal
is inapplicable: the stage handoff paragraph of `coord/brief-stage2.md` expressly
permits recording the statement of a previously reviewed split. There is no repair
note for this item in `coord/repair-notes`.

Sources read: the node's full statement, proof and source; Milne, Algebraic Groups
(2017), printed pp. 246–247, Proposition 12.48 and its proof, identity (79), and
Remark 12.50; Stacks `perfect.tex`, `lemma-proper-flat-geom-red-connected`, Tag 0E0L.
The relative theorem is the agent formulation already accepted in the node; the
module docstring follows all seven steps of that formulation. No source statement
correction or disputed statement is needed.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Scheme S | `{S : Scheme.{u}}`, with explicit universe `u` |
| Morphism p:G → S | `(G : Over S)`, underlying scheme `G.left`, structure map `G.hom` |
| Commutative group scheme, with addition, inverse and identity and all group laws | `[CommGrpObj G]`, Mathlib's abbreviation for `GrpObj G` and `IsCommMonObj G` |
| Smooth | `[Smooth G.hom]` |
| Separated, meaning closed diagonal | `[IsSeparated G.hom]` |
| Finite presentation | `[LocallyOfFinitePresentation G.hom] [QuasiCompact G.hom]`; quasi-separatedness is supplied by separatedness, so this is exactly finite presentation, not just its local version |
| Geometrically connected fibres | `[GeometricallyConnected G.hom]`; `GeometricallyConnected.iff_geometricallyConnected_fiber` identifies this with the stated fibre condition |
| Either p proper or S reduced | `(hbase : IsProper G.hom ∨ IsReduced S)`, an actual disjunction, with no reducedness assumed in the proper case |
| n ≥ 1 | `(n : ℕ) (hn : 1 ≤ n)` |
| P_n, the n-fold fibre product over S | `(∏ᶜ (fun _ : Fin n => G)).left`, the categorical product in `Over S` |
| Structure map p_n | `(∏ᶜ (fun _ : Fin n => G)).hom` |
| Projection pi_i | `(Pi.π (fun _ : Fin n => G) i).left` |
| a_i inserts its input in coordinate i and e elsewhere | `(groupIdentityAxis G n i).left`, whose definition is `Pi.lift (fun j => if j = i then 𝟙 G else (1 : G ⟶ G))` |
| All-identity section e_n | `(groupPowerIdentitySection G n).left`, defined by `Pi.lift (fun _ => (1 : Over.mk (𝟙 S) ⟶ G))` |
| Every invertible global regular function u | `(u : (Γ((∏ᶜ (fun _ : Fin n => G)).left, ⊤))ˣ)` |
| Star on functions is pullback along the indicated scheme morphism | `Scheme.Hom.appTop`; on units, `Units.map f.appTop.hom.toMonoidHom` |
| Base correction p_n^*((e_n^*u)^(1-n)) | `Units.map` of the structure map applied to the pullback of u along the all-identity section, raised to `(1 - (n : ℤ))` |
| Product of pi_i^*(a_i^*u) over all i | `∏ i : Fin n, Units.map` of the projection applied to the pullback of u along `groupIdentityAxis G n i` |
| Equality of regular functions on P_n | The first conjunct coerces u and the entire right-hand unit expression into `Γ(P_n, ⊤)` |
| In particular, all a_i^*u = 1 implies u = 1 | The second conjunct is exactly the implication from `∀ i : Fin n, (groupIdentityAxis G n i).left.appTop ↑u = 1` to `↑u = 1` |

The multiplicative notation for a commutative group object describes the same
commutative group structure called addition in the node. In the scoped Mathlib
Hom monoid, `1 : X ⟶ G` is the constant identity map (`MonObj.Hom.one_def`), whereas
`𝟙 G` is the identity morphism. Thus the axis definition has exactly one varying
coordinate, and the other coordinates are the composite of p with e. The source
of the all-identity section is `Over.mk (𝟙 S)`, whose underlying scheme is S.
There are no arbitrary choices of sections or products constrained only by existence:
`Pi.lift` supplies the unique maps into Mathlib's chosen product. All variables
and universes are bound explicitly; `set_option autoImplicit false` enforces this.

Dependency declarations read and used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme`, including the locally affine structure and
  morphisms of locally ringed spaces.
- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth`,
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`; its affine-local ring-map signature
  and docstring were read.
- `def-sbc-locally-finite-presentation`: `AlgebraicGeometry.LocallyOfFinitePresentation`,
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`, including its full affine
  `appLE` condition. Quasi-compactness is included to render finite presentation.
- `def-weil-proper-morphism`: `AlgebraicGeometry.IsProper` from
  `Mathlib.AlgebraicGeometry.Morphisms.Proper`, and `AlgebraicGeometry.IsSeparated`
  from `Mathlib.AlgebraicGeometry.Morphisms.Separated`. The former extends the
  separated, universally closed and locally finite type conditions; the latter
  requires the diagonal to be a closed immersion.
- `def-pc-reduced-scheme`: `AlgebraicGeometry.IsReduced` from
  `Mathlib.AlgebraicGeometry.Properties`, the sectionwise reducedness class and its
  equivalence to reduced stalks.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback`, `pullback.fst`,
  `pullback.snd` and `pullback.lift`,
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`.
  Finite powers use the existing `Pi.π`/`Pi.lift` product interface in
  `Mathlib.CategoryTheory.Limits.Shapes.Products`, with products in `Over S`
  constructed from fibre products by
  `Mathlib.CategoryTheory.Limits.Constructions.Over.Products`; scheme limits come
  from `Mathlib.AlgebraicGeometry.Limits`. This is the same fibre-product notion,
  with all factors and maps over S, rather than a product over an absolute base.
- `def-pc-geometrically-irreducible`: its recorded Mathlib match explicitly includes
  `AlgebraicGeometry.GeometricallyConnected` in
  `Mathlib.AlgebraicGeometry.Geometrically.Connected`. Both its class docstring and
  signature and the fibre equivalence at lines 111–113 were read. The integral
  class from the primary record is not incorrectly used for connectedness.

Additional existing interfaces: `CategoryTheory.CommGrpObj` from
`Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_`, `GrpObj` and its inverse laws,
`MonObj` and its identity/multiplication laws, `IsCommMonObj` and commutativity;
`Scheme.Hom.appTop` from `Mathlib.AlgebraicGeometry.Scheme`; and `Units.map`.
No private copies of these notions are introduced.

The stated proof dependencies are imported without `public`: the upstream smooth
geometric-reducedness module; `Sheaf.AlgebraicGeometry.ProperFlatGlobalSections`;
`Sheaf.RingTheory.SmoothAlgebraReduced`; the upstream
`WeilConjectures.AlgebraicGeometry.Morphisms.SmoothConnectedGenericGeometryCore`;
and the Mathlib finite-type, quasi-compactness, closed-immersion and residue-field
modules. Smoothness/base-change and separatedness dependencies are already public
statement imports or their public dependencies. Their recorded signatures were
inspected. `lem-sfb-rosenlicht-product-unit-factorization` currently has neither a
Lean record nor a Mathlib match, so it cannot yet be imported; its exact use is
retained in step 5 of the proof docstring. This is a proof-only dependency, not a
missing notion needed to state this item. The maintainer can add its import when
that separate statement lands, as required by stages/2-statements.md §3(7).

Edge cases checked mathematically before writing:

- n = 1: the sole axis is the identity under the canonical one-factor product
  isomorphism; the exponent is zero and the formula reduces to u = u.
- n = 2: the exponent is -1, giving exactly Milne's normalization by the value at
  the all-identity point. The use of integer subtraction avoids truncated natural
  subtraction, which would wrongly make this correction equal to one.
- n = 0 is expressly excluded by the node and by `hn`; the helper constructions
  themselves remain defined for the empty categorical product.
- Empty S: G is also empty, the section rings are zero rings, their unit groups
  are singleton, and both asserted equalities hold. No `Nonempty S` or nontrivial
  coefficient-ring assumption is imposed.
- Nonreduced S and proper p: the left branch of `hbase` is available independently
  of the reducedness class, as the universal proper-flat argument requires.
- Nonproper p and reduced S: the right branch is available without properness,
  Noetherianity, normality or a field structure on the base.
- No characteristic or algebraic-closedness condition is imposed on S; geometric
  fibres are used only in the proof. No affineness assumption is imposed on G.
- Identity group G = S: the exponent 1-n cancels n copies of the same pulled-back
  base unit, including on disconnected bases.

Searches actually made with the prescribed wrapper:

1. `leanfinder`: "An invertible regular function on a finite fibre product of smooth
   connected group schemes factors as the product of its restrictions to the
   identity axes". Eight hits, all scheme-pullback coordinate identities; none
   asserts unit factorization. Returned names included `Scheme.Pullback.t'_snd_fst_fst`,
   `Scheme.Pullback.t'_fst_snd` and `Scheme.Pullback.cocycle`.
2. `loogle`: `AlgebraicGeometry.Scheme, "unit"`. Twelve hits, including
   `Scheme.basicOpen_of_isUnit`, Gamma–Spec adjunction unit declarations and
   `exists_isUnit_germ_eq`; none is the relative unit-factorization theorem.
3. `leansearch`: "Invertible global regular functions on products of geometrically
   connected smooth group schemes factor through the identity axes". Eight hits,
   including `Scheme.Hom.inv_appTop`, `MulEquiv.piUnits`, pointwise inverse
   identities and trivial square-zero extension invertibility; none is this result.
4. `grep` wrapper: `rosenlicht|axis.*[Uu]nit|[Uu]nit.*axis` under
   `Mathlib/AlgebraicGeometry`: zero hits.
5. Direct `rg` over `lean/WeilConjectures` and `lean/Sheaf`, initially for group
   objects, group schemes, identity axes and Rosenlicht, found the existing group
   object interfaces but no unit-factorization theorem. A narrower
   `rosenlicht|unit.*axis|axis.*unit` search found only an unrelated identity-axis
   sentence in `GroupScheme/IdentityTangentAddition.lean`.
6. Direct item-id search in `lean/WeilConjectures`: no hits. Name search for
   `relativeGroupPower|relative_group_unit_axis` and then all three proposed
   declaration names over Mathlib, both project roots and
   `dag/lean_names_upstream.json`: no hits.

Validation: the prescribed `scompile.py Q52 lem-sfb-relative-group-unit-axis-factorization`
compiled both the sandbox view and the library module cleanly (2.6 s and 4.3 s,
respectively). Only this delivery's sandbox was written. No git command, global
build or local preflight was run by the worker. The delivery wrapper performs the
required independent server preflight and compile.

## Second reading by Q52

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
