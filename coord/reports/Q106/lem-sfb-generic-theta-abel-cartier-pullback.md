## Worker report

The module `Sheaf.AlgebraicGeometry.GenericThetaAbelCartierPullback` states
`AlgebraicGeometry.exists_dense_open_genericThetaAbelCartierPullback`, with its sole
proof `sorry`. The node is unchanged except for `lean`. No statement correction,
new DAG node, or dependency repair is needed.

Two real-data helpers belong to this node and are listed in `lean.declarations`:
`IsPointedHilbertAbelMap` packages the family formula for the Abel maps already
specified in the dependency; `translatedNegativeThetaIdeal` constructs the
scheme-theoretic inverse image under x ↦ a-x using the actual group morphisms
and `IdealSheafData.comap`. Neither introduces an arbitrary morphism or a choice.

Hypotheses and clauses, in node order:

- Algebraically closed field: `{k : Type u} [Field k] [IsAlgClosed k]`.
- Smooth projective connected curve: `f : C ⟶ Spec (.of k)` with
  `[IsConnectedCurve f] [Smooth f] [IsHProjective f]`. Connectedness includes
  nonemptiness and dimension exactly one; projective is the recorded finite
  projective-space embedding convention.
- Genus g ≥ 1: `(g : ℕ) (hg : f.genus = g) (hgpos : 1 ≤ g)`.
- Rational base point: `(P : Spec (.of k) ⟶ C) (hP : P ≫ f = 𝟙 _)`.
- Fixed Jacobian and representing isomorphism: `J`, `[GrpObj J]`, `hJ : IsJacobian …`,
  `eJ : (picardFunctorDegree f 0).obj.RepresentableBy J`, and
  `heJ : IsPicardZeroMul f eJ`. The geometric-integrality argument is the existing
  `pointedAbelGeometricIntegrality f`, derived from the curve hypotheses.
- O(-P) is `N : C.Pic` with `hN`, its representative isomorphic to `P.ker.toModules`.
  This names the line class in the source formula; it adds no extra geometric
  hypothesis. `hfP` specifies fP(Q) as O(Q-P) on every test scheme, using the dual
  graph ideal and the pullback of N. This is exactly the formula in the recorded
  Abel-image-geometry theorem, not an arbitrary map on rational points.
- The two relevant members of C^(r) and fP^(r) are `H₀,e₀,a₀` at r=g-1 and
  `H,eH,aG` at r=g. `e₀,eH` represent the recorded Hilbert presheaves.
  `ha₀,haG : IsPointedHilbertAbelMap …` specify their Abel morphisms on every
  family by O(D) tensor O(-rP). They are the maps from the dependency, with
  no independently assumed dimension, birationality or Cartier property.
  The other r in the node only describe notation and do not occur in its conclusion.
- Theta=W_(g-1): `a₀.left.ker` is the ideal of the actual scheme-theoretic image.
  The helper's map is inversion after x ↦ x-a: its pullback ideal is precisely
  t_(-a)^*([-1]^*Theta), hence Theta^-+a with the source's sign convention.
- Dense open subscheme: `∃ U : J.left.Opens, Dense (U : Set J.left) ∧ …`.
  A rational point lies in it when `Set.range a.left ⊆ U`.
- Exactly one effective degree-g divisor maps to a: `∃! d, d ≫ aG = a`.
  Representability by `eH` identifies these rational Hilbert points with the
  effective degree-g divisors. The subsequent universal `d` clause applies
  to that unique divisor, independently of how its witness was selected.
- The divisor as a finite sum of closed points is `D : C.Divisor`, `0 ≤ D`,
  and `Scheme.Divisor.degree C D = (g : ℤ)`. Its ideal equals the ideal
  `(eH.homEquiv d).val` transported from C×_k Spec k along the inverse of
  `pullback.fst f (𝟙 _)`. This identifies D with the unique Hilbert divisor,
  rather than merely choosing a linearly equivalent divisor.
- Sum of g distinct points: `∃ p : Fin g → closedPoints C, Function.Injective p ∧
  D = ∑ i, Finsupp.single (p i) 1`. All these closed points are k-rational
  because C is of finite type over algebraically closed k.
- Theta^-+a is effective Cartier: `(translatedNegativeThetaIdeal …).IsInvertible`.
  This is the recorded ideal predicate for affine-local non-zero-divisor equations,
  not just invertibility of an abstract module.
- Its inverse image is effective Cartier: the same `IsInvertible` assertion on
  its `comap fP.left`.
- Equality as Cartier divisors: the exact equality of this comap with
  `D.prod (fun q n ↦ vanishingIdeal ⟨{q.val},q.prop⟩ ^ n.toNat)`.
  It is equality of the closed-subscheme ideals, preserving multiplicities.
- Associated invertible sheaves: `Nonempty ((tensorPullback fP.left).obj
  (translatedNegativeThetaIdeal …).toModulesᵛ ≅
  D.moduleOfSmoothConnectedCurve k C f)`. This uses the specified tensor
  pullback, the dual ideal definition of O_J(Theta^-+a), and the actual
  divisor-module definition O_C(D), rather than an arbitrary Picard class.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`; `Mathlib.FieldTheory.IsAlgClosed.Basic`:
  `IsAlgClosed` (the relevant clause of the algebraic-closure node).
- `WeilConjectures.AlgebraicGeometry.Curve`: `IsConnectedCurve`/`IsCurve`,
  `Scheme.Hom.genus`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`: `IsHProjective`.
- `WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian`: `IsJacobian`;
  its dimension and group-compatible Picard representation fields were read.
- `Sheaf.AlgebraicGeometry.SymmetricAbelImageGeometry`:
  `pointedAbelGeometricIntegrality`, `exists_pointedAbel_image_geometry`;
  the latter's entire family, Abel-map, Hilbert, image and Cartier signatures
  and proof docstring were read before stating this consumer.
- `WeilConjectures.AlgebraicGeometry.Hilbert.Defs` and `.Hilbert.Curve`:
  `hilbertPresheaf`, `IsHilbertSubscheme`, `hilbertPresheaf_curve_points`.
- `Sheaf.AlgebraicGeometry.DivisorModule`: `Scheme.Divisor.moduleOfSmoothConnectedCurve`;
  the existing divisors and degree come from `WeilConjectures.AlgebraicGeometry.Curve.Divisor`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`: `Scheme.Modules.IsInvertible`;
  `.Modules.Dual`: `Scheme.Modules.dual`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction` publicly exposes
  `Scheme.Modules.tensorPullback` from `WeilConjectures.AlgebraicGeometry.TensorPullback`;
  the normalized adjunction and actual tensor functor signatures were read.
- `WeilConjectures.AlgebraicGeometry.EffectiveCartier`:
  `IdealSheafData.IsInvertible.isInvertible_dual_toModules`;
  the effective-Cartier equivalence with invertible kernel ideals was also read.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Functorial`: `IdealSheafData.comap`
  is the kernel of the projection of the actual fibre product.

Every recorded proof-dependency module that is available is imported, including the
Mathlib matches (properness, flatness, universal openness, integral fibre products,
surjectivity, Jacobson spaces, closed-point residue fields, and function fields).
The ten-step docstring carries the complete node proof, including the finite-free
rank calculation, support calculation, multiplicities, and glued dual-basis comparison.

Edge cases checked before writing: g=1 uses the degree-zero Hilbert scheme and
W_0, not a nonexistent degree -1 scheme; `g-1` is natural subtraction with g≥1.
No characteristic restriction is imposed, including characteristics 2 and those
dividing g. Empty/disconnected/zero-dimensional curves are excluded by the source's
connected-curve assumption, not by a new hypothesis. No empty open is substituted
for the dense open. Nonreduced test schemes remain in both family formulas.
The pullback is not assumed flat. The inverse of `pullback.fst f (𝟙 _)` is a
canonical isomorphism, so the Hilbert fibre is compared on the actual curve C.
All variables and universes are explicitly bound with `autoImplicit false`.

Searches made:

- `msearch.py … leanfinder`: “For a curve of genus g the generic pullback of a
  translated negative theta divisor along the Abel map is the unique reduced
  effective divisor of degree g”. Eight results, all unrelated Weierstrass
  coordinate-ideal/class-group facts; none has this statement.
- `msearch.py … loogle`: `AlgebraicGeometry.IsJacobian, AlgebraicGeometry.hilbertPresheaf`.
  Zero results, unknown identifier IsJacobian in Mathlib's index.
- `msearch.py … grep`: `theta|Theta|generic.*Abel` in `AlgebraicGeometry`.
  Zero Mathlib results.
- `rg` of `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for the item id and generic theta / theta pullback names: no matching theorem;
  the existing SymmetricAbelImageGeometry supplies the prerequisites only.
- `rg` for all three chosen declaration names in Mathlib, WeilConjectures,
  Sheaf and the upstream name index: no collisions. Searches for named
  Abel-map/translation constructions found no existing helper for these two
  formula packages. Existing `comap`, group structure and Hilbert presheaf
  are reused in their definitions.

The source PDF was read locally with `pdftotext`, including the notation before
Theorem 6.6 and all of Lemma 6.7 on printed pp.105–106. No node fault or
STATEMENT-DISPUTED issue was found.

Validation: prescribed `scompile.py` compiled the sandbox and final module cleanly
in module mode after fixing Cartesian monoidal lifting and explicit divisor-degree
application. Only the expected postponed theorem remains.

## Second reading by Q106

I reread the node and the full module after elaboration. This is a separate self-review
pass; no second agent was started, as the dispatcher brief prohibits delegation.

The field, curve, genus, point, Jacobian and fixed representation hypotheses match.
The map hypotheses supply only the defining family formulas from the dependency;
no isomorphism locus, generic rank, reducedness or Cartier conclusion is assumed.
The image ideal is the kernel of a₀ itself, so it defines W_(g-1), not a chosen
support or a different theta. The translation composite evaluates to
-(x-a)=a-x; consequently its inverse image is the required negative-theta
translate, with no sign reversal. Representability and the transported ideal
identify the unique d and D as the same divisor. The distinct-point sum has
coefficient one; equality of ideal products retains multiplicities. Both
Cartier assertions use ideal invertibility. The final isomorphism has the
tensor pullback on its left and the recorded rational-function divisor module
on its right. The genus-one and arbitrary-characteristic cases remain present.
No mathematical mismatch was found or statement changed in this pass.
