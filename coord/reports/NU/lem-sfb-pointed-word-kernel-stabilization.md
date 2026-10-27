## Worker report

Stated `AlgebraicGeometry.pointedProductWordKernel_stabilization` in
`Sheaf.AlgebraicGeometry.PointedWordKernelStabilization`. Its proof is `sorry`.
The real auxiliary definitions `pointedProductWord` and `pointedProductWordKernel`
construct the ordered word morphism and take the kernel of its actual pullback.
They belong to this node's construction, are listed in `lean.declarations`, and
introduce no independent notion requiring a new DAG node. No statement correction,
new node, dependency repair, or disputed statement was needed. Only the item's
`lean` field changes.

Source read: Milne, Algebraic Groups (2017), Section 2h, printed pp.54–56
(PDF pages 66–68), especially the identity-appending maps and their coordinate
kernels, and Proposition 6.20(a), printed p.130 (PDF page 142). The node's seven
proof steps are reproduced in the theorem docstring, including the finite-dimension
argument in place of an assertion about arbitrary descending ideal chains.

Hypothesis and clause correspondence:

- Algebraically closed field: `(k : Type u) [Field k] [IsAlgClosed k]`.
- The two k-group schemes: `G J : Over (Spec (.of k))`, with `[GrpObj G]`
  and `[GrpObj J]`. The base, structural maps, group multiplication, inverse,
  and identity are those of the recorded group-object interface.
- Affineness: `[IsAffine G.left] [IsAffine J.left]`.
- Smoothness and connectedness of G: `[Smooth G.hom] [ConnectedSpace G.left]`.
  In particular connectedness includes nonemptiness.
- Finite type of G: smoothness implies locally of finite presentation, hence
  locally of finite type; affineness makes its structure map affine and
  quasi-compact. This hypothesis is mathematically redundant and inferred,
  rather than added as a hollow binder. A server-compiled module-mode probe
  checked `#synth LocallyOfFiniteType G.hom` and `#synth QuasiCompact G.hom`.
  The outputs were `instLocallyOfFiniteTypeOfLocallyOfFinitePresentation G.hom`
  and `instQuasiCompactOfIsAffineHom G.hom`.
- Finite type of J: `[LocallyOfFiniteType J.hom]`, together with quasi-compactness
  from affineness. The same probe checked `#synth QuasiCompact J.hom`, yielding
  `instQuasiCompactOfIsAffineHom J.hom`. No smoothness or reducedness of J is imposed.
- Positive arity: `(r : ℕ) (hr : 1 ≤ r)`.
- Arbitrary k-morphism from G^r: `φ : (∏ᶜ fun _ : Fin r ↦ G) ⟶ J` in the
  over category. There is no `IsMonHom φ` binder.
- Pointedness: `hφ` states that `Pi.lift` of the r identity sections composed
  with φ is `1`. The scoped Mathlib group on morphisms makes `1` the identity
  section from the terminal k-scheme; it is not the identity morphism of J.
- Powers are finite products in `Over (Spec (.of k))`, thus fibre products over k,
  not products over Spec Z. The domain of `pointedProductWord φ n` is `(G^r)^n`:
  it is G^(rn) with the specified blocks, canonically identified by the product
  universal property and the bijection of `Fin n × Fin r` with `Fin (r*n)`.
  This changes neither the domain's coordinates nor the map.
- The word w_n: `pointedProductWord` takes `List.ofFn` of the n maps
  `Pi.π ... i ≫ φ` and their ordered `List.prod`. The scoped Mathlib
  `Hom.group`/`Hom.monoid` multiplies two such maps by pairing followed by
  multiplication in J. The definition therefore gives exactly
  φ(x_1)⋯φ(x_n), with its stated order even for noncommutative J.
- I_n: `pointedProductWordKernel φ n` is `RingHom.ker` of
  `(pointedProductWord φ n).left.appTop.hom`, namely
  k[J] → k[(G^r)^n]. This is the actual coordinate pullback.
- Geometric integrality of every positive power:
  `∀ m : ℕ, 1 ≤ m → GeometricallyIntegral (∏ᶜ fun _ : Fin m ↦ G).hom`.
- Stabilization at a positive index: `∃ N : ℕ, 1 ≤ N ∧ ...`, with
  `∀ n : ℕ, N ≤ n → pointedProductWordKernel φ n = pointedProductWordKernel φ N`.
- Prime stabilized ideal: `(pointedProductWordKernel φ N).IsPrime`.
- Intersection of all positive kernels: the `iInf` indexed by
  `{n : ℕ // 1 ≤ n}` equals the kernel at N. No n=0 kernel enters this claim.
- Z is exactly the quotient spectrum:
  `Spec (.of (Γ(J.left, ⊤) ⧸ pointedProductWordKernel φ N))`.
  `IsIntegral` of this explicit scheme is a conjunct.
- Factorization: the existential v has source `(G^r)^N` and target that exact Z.
  Its composite with `Spec.map` of `Ideal.Quotient.mk`, followed by
  `J.left.isoSpec.inv`, equals `(pointedProductWord φ N).left`.
  Thus the closed inclusion Z → J is the canonical quotient inclusion, not
  a supplied arbitrary map. Equip Z with the k-structure obtained by composing
  that inclusion with J.hom; the factorization equality makes v a k-morphism
  as well. No extra over-base hypothesis on v is needed.
- Density and injective coordinate pullback: `DenseRange v.base` and
  `Function.Injective v.appTop`. The latter uses the canonical Γ(Spec C) ≅ C
  implicit in the usual coordinate-ring description, so it states precisely
  injectivity of the quotient coordinate map.

Dependency declarations read and used:

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs.
- `def-weil-algebraic-closure`: `IsAlgClosed` (the applicable clause of its
  `mathlib_match`), Mathlib.FieldTheory.IsAlgClosed.Basic. No algebraic extension
  of an additional base field is part of this statement.
- `def-sc-group-scheme`: `CategoryTheory.GrpObj`, Mathlib.CategoryTheory.Monoidal.Grp;
  its Cartesian morphism-group API is Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
  and .Mon. Read their class and the definitions of `Hom.group` and `Hom.monoid`,
  and the project group-scheme conventions in
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs. No replacement structure.
- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth`,
  Mathlib.AlgebraicGeometry.Morphisms.Smooth.
- `def-weil-connected-scheme`: `ConnectedSpace`, Mathlib.Topology.Connected.Basic.
- `def-weil-finite-type-morphism`: `LocallyOfFiniteType` and `QuasiCompact`,
  Mathlib.AlgebraicGeometry.Morphisms.FiniteType and .QuasiCompact.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback`,
  Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback; its finite-product
  incarnation in the over category uses `piObj`, `Pi.π`, and `Pi.lift`, with
  the scheme/over limits supplied by Mathlib.AlgebraicGeometry.Pullbacks.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map`,
  Mathlib.AlgebraicGeometry.Scheme; `Scheme.isoSpec`,
  Mathlib.AlgebraicGeometry.AffineScheme, identifies affine J with Spec k[J].
- `def-weil-pbc-algebra-hom-quotient`: Mathlib's ideal quotient and quotient map,
  imported via Mathlib.RingTheory.Ideal.Quotient.Operations. The ring-kernel
  formulation is the underlying ring map of the stated k-algebra map.
- `def-pc-geometrically-irreducible`: `AlgebraicGeometry.GeometricallyIntegral`,
  Mathlib.AlgebraicGeometry.Geometrically.Integral, whose class is exactly
  integrality after every field base change.
- `def-pc-integral-scheme`: `AlgebraicGeometry.IsIntegral`,
  Mathlib.AlgebraicGeometry.Properties, including nonemptiness.

Plain proof imports retain the recorded modules for
`lem-trf-connected-point-geometrically-connected`,
`lem-sc-geometrically-irreducible-product`,
`sbc-lem-smooth-geometrically-reduced`, `lem-kun-dimension-finite-type`,
`def-kun-dimension`/`def-kun-topological-krull-dimension`, and
`lem-pc-proper-base-change`. Their recorded declarations and source signatures
were read. Mathlib's `pullbackSpecIso` and `smooth_comp` are already available
from the public Pullbacks and Smooth imports. The proof prerequisite
`lem-trf-smooth-connected-fibre-normal-integrality` has no recorded module in
this checkout, so there is no module to import yet; it is a future proof input,
not a missing object needed to type this statement.

Edge cases checked mathematically: r=1 and N=1 are allowed. The trivial group
and constant identity-valued φ give the identity-point kernel and an integral
quotient Spec k. J may be nonreduced, such as α_p in characteristic p; no domain,
smoothness, or connectedness of J is assumed. Positive characteristic and
noncommutative J are allowed. Non-homomorphic pointed φ is allowed. Empty G is
excluded by connectedness (and also by its identity section). The geometric
integrality clause and intersection exclude the zero power. The auxiliary word
is nevertheless defined at n=0 by the empty product, the constant identity map;
this extends only a definition and adds no theorem clause. All universes and
variables are explicit, with `set_option autoImplicit false`. A single arbitrary
universe u permits any field and schemes after common universe enlargement.

Searches for an exact existing statement (all negative):

- msearch leansearch: `pointed product morphism affine group scheme kernels stabilize`:
  eight hits, including `AddMonoidHom.ker_prodMap`, `MonoidHom.ker_prod`, and
  `LinearMap.ker_prodMap`; none states a scheme word-kernel stabilization result.
- msearch leanfinder: `kernels of pointed product word maps from powers of a smooth
  connected affine group scheme stabilize at a prime ideal`: eight hits, including
  `Scheme.ker_toSpecΓ`, normalization kernels and ideal-sheaf kernel comparisons;
  none asserts stabilization, geometric integral powers, or this quotient conclusion.
- msearch loogle: `RingHom.ker, Ideal.IsPrime, Antitone`: zero hits.
- msearch grep: `wordMap|word_map|stabili.*image|image.*stabili` in AlgebraicGeometry:
  zero hits. `pointedProductWord|pointed.*word|word.*kernel` across Mathlib:
  four unrelated hits in probability, localization and Galois comments.
- rg for word-map/kernel names in lean/WeilConjectures and lean/Sheaf, and the
  item's id in lean/WeilConjectures and dag/lean_names_upstream.json: no existing
  declaration. The project citer SmoothConnectedDerivedSubgroup only mentions
  this node in its proof plan and has a different theorem.

Validation: the final delivered module compiled through scompile.py in both
sandbox and library module modes, with no errors or warnings. The finite-type
inference probe also compiled cleanly through scompile.py; it lives outside
lean/ and is not delivered. Every new definition has real data, the only
postponed proof is the main named theorem, and its source and complete proof
plan are in its docstring.

## Second reading by NU

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
