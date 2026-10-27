## Worker report

Item: `det-cor-jacobian-torsion-pic`, group Q110, stage 2, 2026-10-22 UTC.

The delivery states `AlgebraicGeometry.Scheme.Hom.jacobian_torsion_pic` in
`Sheaf.AlgebraicGeometry.Curve.JacobianTorsionPic`. Its sole proof is `sorry`.
There are no new definitions, helper theorems, dependency repairs or node corrections.
The node changes only in `lean`. The statement signature is copied verbatim,
including line breaks, from the delivered module.

I read the item, all five statement-dependency statements and records, their
recorded source declarations and docstrings, the proof and proof-dependency
records, and the current blueprint source and proof at
`literature/blueprint/main-20261015/blueprint/sec-picard-framework/`:
`sk-cor-jacobian-torsion/det-cor-jacobian-torsion-pic.md` and
`det-cor-jacobian-torsion-pic.proof.md`. The `blueprint_update` entries of
`def-sc-picard-group` and `def-sc-pic0` were followed. No repair note exists
for this item.

Hypotheses and objects, matched individually:

- Algebraically closed field k: `{k : Type u} [Field k] [IsAlgClosed k]`.
- Curve C over k: `{C : Scheme.{u}} (f : C ⟶ Spec (.of k))`.
  The explicit f is needed by the recorded `IsConnectedCurve`, `picZero`
  and `picDegree` interfaces.
- Connected, nonempty curve of dimension exactly one:
  `[IsConnectedCurve f]`. Its superclass is the recorded `IsCurve`,
  including separatedness, finite type and dimension at most one.
- Smooth: `[Smooth f]`; proper: `[IsProper f]`.
- Genus g is the intrinsic `f.genus` already built into the dimension
  equality in `IsJacobian`. There is no independent g or restriction on g.
- The Jacobian J(C) is any `J : Over (Spec (.of k))` with `[GrpObj J]`
  and `[IsJacobian f J]`. This reuses the existing class, including its
  abelian-variety, genus-dimension and group-valued representability clauses.
  Its interface requires `[GeometricallyIntegral f]`. The theorem SUPPLIES
  this proof in its initial existential conclusion; it is not a hypothesis.
  Smooth connected curves over algebraically closed fields are geometrically
  integral: connectedness is geometric connectedness over a separably closed
  field, and smoothness then gives geometric irreducibility and reducedness.
  This is the same typing convention used by `genus_jacobian_invariant`.
- A choice of the group-valued representing identification is made explicit as
  `(r : (picardFunctorDegree f 0).obj.RepresentableBy J)` and
  `(_hr : IsPicardZeroMul f r)`. These are precisely the representation and
  group compatibility carried existentially by `IsJacobian.represents`, not
  an added existence condition. The result holds for every such choice.
  Rational points are `𝟙_ (Over (Spec (.of k))) ⟶ J`.

Each clause of the conclusion:

1. The inclusion `J(k) = Pic⁰(C) ⊆ Pic(C)` is a homomorphism
   `i : (𝟙_ (Over (Spec (.of k))) ⟶ J) →* C.Pic`, with
   `Function.Injective i` and `Set.range i = f.picZero`.
   It is not an arbitrary embedding: for every point a, the displayed
   sheafification/representation equation says that the class i(a), pulled
   back to C ×_k k, is the degree-zero Picard-functor section classified by a.
   The existential h is only its fibrewise-degree-zero membership proof.
   Since the Jacobian representation and the ordinary-to-relative Picard
   comparison at Spec k are bijective, this equation uniquely determines i.
2. For every n ≥ 1, multiplication by n on J(k) is surjective:
   `∀ (n : ℕ), 0 < n → Function.Surjective (fun a ↦ a ^ n)`.
   The library writes the group law multiplicatively. No condition on
   `(n : k)`, invertibility, or characteristic is imposed.
3. For every positive n, the first subset equality identifies
   `J[n](k)` and `J(k)[n]` inside Pic(C): `Set.range` of
   `fun a : 𝟙_ _ ⟶ torsionSubgroupScheme J n ↦
   i (a ≫ torsionSubgroupScheme.ι J n)` equals
   `i '' {a | a ^ n = 1}`. This uses the actual kernel scheme and its
   actual inclusion, not a separate abstract group with the right size.
4. The second equality is
   `i '' {a | a ^ n = 1} = {L : C.Pic | L ^ n = 1}`.
   Thus the *same inclusion* identifies this subgroup with all Picard
   n-torsion. Injectivity of i ensures the first equality also recovers the
   equality in J(k) itself.
5. The group quotient in the source is
   `C.Pic ⧸ (powMonoidHom n : C.Pic →* C.Pic).range`, and ℤ/nℤ is
   `Multiplicative (ZMod n)`. The existential `e` is a `MulEquiv`
   between them. Its value on EVERY representative is fixed by
   `e (QuotientGroup.mk L) =
   Multiplicative.ofAdd ((f.picDegree L : ℤ) : ZMod n)`.
   This records that degree induces the isomorphism, as the source requires;
   a bare `Nonempty` equivalence would not express that requirement.

Dependency declarations actually reused:

- `sk-def-curve`: `IsCurve`, `IsConnectedCurve`, `Scheme.Hom.genus`,
  `WeilConjectures.AlgebraicGeometry.Curve`, read lines 69–199.
  Its recorded module `Sheaf.AlgebraicGeometry.CurveGenus` is publicly
  imported; its source was read, including the final genus-invariance theorem.
- `sk-def-av-jacobian`: `AlgebraicGeometry.IsJacobian`,
  `WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian`, lines 57–88.
  The incomplete attachment names its declaration; its closed upstream audit
  supplies this module. Its field `represents` and the recorded
  `AlgebraicGeometry.IsPicardZeroMul` in
  `WeilConjectures.AlgebraicGeometry.Picard.Jacobian` (lines 482–504)
  give the representation used in the statement.
- `sk-def-av-mult-n`: the closed audit records
  `AlgebraicGeometry.torsionSubgroupScheme` in
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`, lines 181–198.
  I also read its inclusion, `torsionByPointsEquiv` and `torsionByEquiv`.
- `def-sc-picard-group`: `AlgebraicGeometry.Scheme.Pic`,
  `WeilConjectures.AlgebraicGeometry.PicardFunctor`, lines 159–169;
  group law `Scheme.Pic.instCommGroup` in
  `WeilConjectures.AlgebraicGeometry.Picard.Group`, lines 131–153.
- `def-sc-pic0`: `Scheme.Hom.picDegree` and `Scheme.Hom.picZero`,
  `WeilConjectures.AlgebraicGeometry.Curve`, lines 156–199. These are
  precisely the current blueprint's Euler-characteristic degree and its
  zero locus. No private degree or Pic-zero definition is introduced.

The proof-plan imports are `WeilConjectures.AlgebraicGeometry.Picard.Scheme`
(sk-thm-picard-main, with its Jacobian statement already publicly available
through the statement imports),
`WeilConjectures.AlgebraicGeometry.Curve.PicardDecomposition`
(lem-sc-pic-proper-decomposition), and
`WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny`
(lem-sc-isogeny-surjective). I read the latter two recorded signatures:
`Scheme.Hom.exists_mulEquiv_prod_picZero` uses exactly the connected smooth
proper curve hypotheses and specifies both degree and inclusion compatibility;
`surjective_npow_points` requires only n > 0 over the algebraically closed
field. The torsion-definition proof dependency is already a public import.
The module docstring gives the source; the theorem docstring expands all
five DAG proof steps and names these nodes. Nothing is proved in this stage.

Edge cases checked before writing:

- n = 1: the multiplication map is the identity, both torsion sets are
  singleton identity, and both quotients are trivial (`ZMod 1`).
- n = 0: deliberately excluded by the source's `0 < n`. If included,
  Pic-torsion would not lie in Pic-zero; there is no accidental n = 0 claim.
- Positive characteristic with p dividing n: fully included. Surjectivity
  uses rational points of a finite surjective map, not etaleness. No false
  assertion of n^(2g) distinct geometric torsion points appears.
- Genus zero: the Jacobian is trivial, Pic is ℤ, and the degree quotient
  is ℤ/nℤ. Both torsion equalities remain correct.
- Genus one: the statement is the usual divisibility of elliptic-curve
  points, including inseparable multiplication, and the Picard degree quotient.
- Empty C, Spec k, disconnected unions of curves: excluded exactly by the
  source's connected-curve notion, which requires nonemptiness and dimension
  one. No extra nonemptiness or chosen rational point is assumed.
- Universes: k and C lie in the scheme universe u; `C.Pic` lives in u+1,
  and the cross-universe homomorphism i handles that without shrinking the
  Picard group or restricting the curves. All variables and u are explicit;
  `autoImplicit` is false. No file-local notation or local instances are used.

Searches actually performed (2026-10-22; msearch queries are logged in the sandbox):

- LeanFinder via `msearch.py`: `Jacobian rational points divisible Picard
  group torsion degree modulo n`. Eight hits were Weierstrass Jacobian
  coordinates/point classes, elliptic class-group maps and
  `FunctionField.classNumber`; none is this general-curve statement.
- Loogle via `msearch.py`: `"Pic"`. Twelve substring hits concern
  pickling, Lean metavariable closure and PiBaseTopic; no Picard theorem.
- Grep via `msearch.py`: `Picard|picDegree|torsionSubgroupScheme` in
  Mathlib/AlgebraicGeometry. Three hits, all in EllipticCurve/Weierstrass,
  only mention schemes with trivial Picard group, so no match.
- LeanSearch via `msearch.py`: `Jacobian rational points divisible Picard
  group modulo n degree isomorphism`. Eight hits concern only Weierstrass
  Jacobian coordinates and their point group, not this statement.
- `rg` on both `lean/WeilConjectures` and `lean/Sheaf`, plus the upstream
  name index, for the exact node id and `jacobian_torsion_pic`: no match.
  Concept searches for torsion/Picard, degree/quotient and surjective powers
  located and led to reading the existing Curve/PicProperNTorsion*,
  Curve/RootsOfUnityTop, Curve/Jacobian, Curve/PicZeroJacobianPointComparison,
  AbelianVariety/Isogeny, AbelianVariety/Jacobian and Picard/Jacobian modules.
  PicProperNTorsionCoker requires `(n : k) ≠ 0` and omits the degree
  compatibility, so is not an exact existing statement. RootsOfUnityTop has
  useful component facts but neither both inclusion-based torsion equalities
  nor the complete theorem. The point-comparison theorem concerns extensions
  of fields, not this theorem. No notion was defined again.

Validation: the prescribed `scompile.py Q110 det-cor-jacobian-torsion-pic`
compiled both the sandbox probe and the actual named library module cleanly
(9.1 s and 15.6 s respectively), under the default 60-second limit.
All lines are at most 100 characters. The only `sorry` is the main theorem.
Initial syntax/scope diagnostics were repaired by opening the existing
`MonoidalCategory` and `MonObj` namespaces and correctly grouping the
sheafified representative; there are no remaining errors or warnings.

No STATEMENT-DISPUTED issue, source error, statement correction, new node,
or dependency repair was needed.

## Second reading by Q110

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
