## Worker report

The module `Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion` states
`AlgebraicGeometry.IsConnectedCurve.pic_proper_ntorsion`, with only a `sorry` proof.
It contains no new definitions or auxiliary theorems. Its docstring carries all four
steps of the node's natural-language proof and their cited node ids.

The hypotheses and clauses correspond as follows:

- Algebraically closed field k: `{k : Type u} [Field k] [IsAlgClosed k]`.
- Curve over k: `{C : Scheme.{u}} (f : C ⟶ Spec (.of k))` and `[IsConnectedCurve f]`.
  This class extends the recorded `IsCurve`, so supplies separatedness, finite type,
  dimension one, connectedness and nonemptiness.
- Proper and smooth: `[IsProper f] [Smooth f]`.
- Genus g: `f.genus`, using the recorded genus definition, without introducing a separate
  free g or an extra hypothesis. Its differential-form definition is the equivalent
  expression explicitly allowed by def-sc-genus, as documented in Curve.lean.
- n prime to char k: `(n : ℕ) (_hn : (n : k) ≠ 0)`. In positive characteristic p this is
  p not dividing n; in characteristic zero it is n positive. This is the source's
  positive-integer convention, already explained in proof step 2 of the node.
- Pic(C)[n] ≅ (Z/n)^(2g): the first `Nonempty` contains an additive group equivalence
  from `AddSubgroup.torsionBy (Additive C.Pic) (n : ℤ)` to
  `Fin (2 * f.genus) → ZMod n`. Mathlib's torsionBy is the subgroup killed by n.
- coker(n : Pic(C) → Pic(C)) ≅ Z/n: the second `Nonempty` contains an additive group
  equivalence from the quotient by the range of `nsmulAddMonoidHom` to `ZMod n`.
  This quotient is precisely the cokernel in abelian groups.
- Pic^0(C) is n-divisible: every `L ∈ f.picZero` has `M ∈ f.picZero` with `M ^ n = L`.
  Pic's group operation is tensor product, written multiplicatively upstream; powers
  therefore express the requested multiplication by n. The first two clauses use
  Mathlib's `Additive` wrapper for that same group, not a replacement Picard group.

Dependency declarations read and used:

- def-sc-curves: `WeilConjectures.AlgebraicGeometry.Curve`,
  `AlgebraicGeometry.IsCurve` and its `IsConnectedCurve` specialization.
- def-sc-picard-group: `WeilConjectures.AlgebraicGeometry.PicardFunctor`,
  `AlgebraicGeometry.Scheme.Pic`, imported through Curve; its commutative group instance
  is from `WeilConjectures.AlgebraicGeometry.Picard.Group`.
- def-sc-pic0: `WeilConjectures.AlgebraicGeometry.Curve`,
  `AlgebraicGeometry.Scheme.Hom.picZero`. This is a set of degree-zero classes, so the
  divisibility clause is expressed by membership rather than inventing a subgroup.
- def-sc-genus: `WeilConjectures.AlgebraicGeometry.Curve`,
  `AlgebraicGeometry.Scheme.Hom.genus`.

Edge cases: n = 0 is excluded by its nonzero field cast, including in characteristic zero;
n = 1 gives trivial torsion and cokernel and tautological divisibility. Genus zero gives
the trivial function group on `Fin 0`, with cokernel still Z/n. In characteristic p only
multiples of p are excluded. Empty curves and dimension-zero points are excluded precisely
by the dependency's connected-curve definition, not by extra binders. Universe u is explicit;
Pic naturally lies in Type (u+1), which is allowed by the group equivalences. Every variable
and universe is explicitly bound.

Searches for an existing statement:

- msearch leanfinder: “Picard group of a proper smooth connected curve n torsion rank 2g
  cokernel multiplication n and divisible degree zero”: eight hits on function-field
  class numbers and Weierstrass class-group maps; none state the lemma.
- msearch loogle: `AlgebraicGeometry.Scheme.Pic, AddMonoidHom.ker, ZMod`:
  no hits (unknown identifier AlgebraicGeometry.Scheme.Pic in the Mathlib index).
- msearch leansearch: “Picard group proper smooth curve n torsion cokernel degree zero
  divisible”: unavailable, Internal Server Error; no verdict inferred from that failure.
- msearch grep: `pic.*torsion|Pic.*torsion|pic.*divisible|Pic.*divisible` in Mathlib
  AlgebraicGeometry: two unrelated Weierstrass docstring hits about 12-torsion.
- rg of the same expression, plus the item id, in WeilConjectures and lean/Sheaf:
  nearby cohomology estimates, affine-curve divisibility and real-sheaf Jacobian comparison;
  no combined proper-curve Picard statement. Read Curve/Estimate.lean and Curve/Picard.lean:
  the former states cohomology conclusions and the latter a decomposition, neither this lemma.
- rg for `pic_proper_ntorsion|pic_torsion_and_cokernel` in dag/lean_names_upstream.json,
  WeilConjectures and lean/Sheaf: no name clashes.
- Read Mathlib Algebra/Module/Torsion/Basic.lean for AddSubgroup.torsionBy and
  Algebra/Group/Hom/Basic.lean for nsmulAddMonoidHom's generated signature.

No node correction, new node, dependency module, or disputed statement is needed.
The local literature payload is absent; the source statement and its four proof steps are
recorded verbatim in the DAG node, and the existing E1 report independently reads the source.
The raw GitHub source request also failed to fetch. No correction depends on an unread source.

## Second reading by J1

I read the node statement and the delivered module side by side. The node introduces an
algebraically closed field `k`, a proper smooth connected curve `C` over `k`, its genus `g`,
and a natural number `n` prime to `char k`. The Lean renders these as `{k : Type u}
[Field k] [IsAlgClosed k]`, `{C : Scheme.{u}}`, `(f : C ⟶ Spec (.of k))`,
`[IsConnectedCurve f] [Smooth f] [IsProper f]`, `f.genus`, and `(n : ℕ) (_hn :
(n : k) ≠ 0)`, respectively. `IsConnectedCurve` supplies the curve's separated,
finite-type, dimension-one, connected, and nonempty conditions; no stronger curve
hypothesis is introduced. The field and scheme share universe `u`, which permits the
node's cases without an artificial universe restriction.

The first conclusion clause, `Pic(C)[n] ≅ (Z/nZ)^(2g)`, is rendered as
`Nonempty (AddSubgroup.torsionBy (Additive C.Pic) (n : ℤ) ≃+
(Fin (2 * f.genus) → ZMod n))`. `Additive C.Pic` is the same Picard group with its
multiplicative tensor law expressed additively, and `torsionBy` is precisely the subgroup
killed by `n`; `Fin (2 * genus) → ZMod n` is the stated rank-
`2g` product, including genus zero. The second clause, the cokernel of multiplication by
`n`, is rendered as `Nonempty ((Additive C.Pic ⧸
(nsmulAddMonoidHom (α := Additive C.Pic) n).range) ≃+ ZMod n)`, which is the additive
cokernel quotient by the image of the multiplication map. The final clause is rendered as
`∀ L : C.Pic, L ∈ f.picZero → ∃ M : C.Pic, M ∈ f.picZero ∧ M ^ n = L`; this exactly
states n-divisibility of `Pic^0`, with Pic's tensor-product group law written by powers.
The conjunction and quantifier order agree with the node.

I checked edge cases: `n = 0` is excluded by `_hn`, `n = 1` gives trivial torsion and
cokernel and immediate divisibility, genus zero gives `Fin 0`, and positive-characteristic
prime-to-characteristic means exactly a nonzero field cast. The connected-curve class
excludes empty schemes and dimension-zero points as required by the source. The zero
Picard element is covered by the universal quantifiers.

I searched the project and source with `rg`, and used the recorded msearch LeanSearch,
LeanFinder/Loogle, and grep searches for Picard torsion, cokernels, and divisibility. No
existing declaration states this theorem, and the dependency declarations are the
recorded `IsConnectedCurve`, `Scheme.Pic`, `Scheme.Hom.picZero`, and `Scheme.Hom.genus`.
I also read their definitions: no dependency is a special case or an unusable notion.
The local Stacks literature payload is absent, so I checked the blueprint source place and
its proof steps recorded in the node. I found no mismatch and made no code or node change.
