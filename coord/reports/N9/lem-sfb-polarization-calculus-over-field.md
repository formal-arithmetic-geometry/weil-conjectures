## Worker report

Stage 2, N9, 2026-10-24. Delivered statement:
`AlgebraicGeometry.IsAbelianVariety.polarization_calculus_over_field` in
`Sheaf.AlgebraicGeometry.AbelianVariety.PolarizationCalculusOverField`.
It has one postponed theorem, with the node's ten-step proof in its docstring.
`RationalHom` supplies only real definitions and abbreviations; none contains sorry.
No statement correction, dependency replacement, or statement dispute is needed.
The previous BLOCKED referred to stage-1 deliver.py rejecting an already accepted split.
The current queue explicitly assigns stage 2 and the node has no lean record;
brief-stage2 section 0 explicitly distinguishes these situations.

Hypotheses and clause correspondence (in statement order):

- Any field: `{k : Type u} [Field k]`. There is no algebraic closedness,
  perfection, characteristic, or positive-dimension hypothesis on k or A.
- Abelian variety: `A : Over (Spec (.of k))`, `[GrpObj A] [IsAbelianVariety A]`.
  The latter is proper, smooth and connected, exactly the recorded definition.
- Integral Hom consists of group-scheme homomorphisms: `abelianHom B C` is
  `Additive (Grp.mk B ⟶ Grp.mk C)`. Bundled group-object arrows carry IsMonHom;
  pointwise multiplication becomes addition under the Additive type tag.
- Rational Hom is `abelianRationalHom B C = ℚ ⊗[ℤ] abelianHom B C`.
  This is the node's tensor product with its factors exchanged by
  `TensorProduct.comm`; it is not a field extension of k. Rationalization
  `abelianHomToRational` reuses `AddCommGroup.rationalizationMap`.
- Composition is the existential bilinear map `c B C E`. Its displayed equation
  on `r ⊗ f` and `s ⊗ g` fixes its value to `(r*s) ⊗ (f ≫ g)`.
  Pure tensors generate, so this specifies the unique ordinary rational
  composition, not a freely chosen multiplication. We use categorical order:
  `c f g` means g after f. The usual product vw is consequently `c w v`.
- The normalized dual exists: `∃ D : AbelianDualPoincareDatum A`. Its definition
  retains the Poincare sheaf, two identity axes, specified rigidification,
  fibrewise algebraic triviality, tensor law and universal property over all T.
- Every invertible N has a group homomorphism: dependent function
  `φ : (N : A.left.Modules) → N.IsInvertible → abelianHom A D.dual`.
  The first clause says `ClassifiesAbelianDifference D N f ↔ f = ...φ...`.
  Thus the map is determined by the existing normalized difference, and no
  arbitrary map can replace it. Proof arguments of invertibility do not change it.
- Geometric-point formula: for every algebraically closed Ω in the scheme
  universe, base map s and `x : Over.mk s ⟶ A`, the next isomorphism identifies
  the Poincare line at x followed by φ_N with translation pullback of N tensor
  its inverse. Translation is the actual scheme arrow
  `fst A T * (snd A T ≫ x)`, and N is first pulled to A × T.
  This treats extension-valued geometric points, not merely k-rational points.
  The isomorphism is on A × Spec Ω, the standard model of A_Ω.
- Tensor additivity is `φ (N ⊗ P) inferInstance = φ N hN + φ P hP`.
  The known tensor-invertibility instance supplies the proof; no extra
  invertibility hypothesis on the tensor product is imposed.
- Structure module: `φ (𝟙_ A.left.Modules) inferInstance = 0`.
- Duality is supplied on all Hom groups B → C and all normalized data DB, DC:
  `d B C DB DC : abelianHom B C →+ abelianHom DC.dual DB.dual`.
  Specializing B=C=A and DB=DC=D gives the stated b-dual. Its classifier clause
  reads `(b × 1)^* P_C ≅ (1 × bDual)^* P_B ↔ bDual = d(b)`.
  Both axis trivializations are those of the supplied normalized data.
  An isomorphism can be rescaled by a unit from the dual base to preserve the
  specified rigidification: proper geometrically connected A has only base
  global functions. Thus this iff formulation specifies the same normalized
  classifier, as in the already reviewed PolarizationCalculus dependency API;
  it does not choose a second rigidification or a second Poincare sheaf.
- The dual geometric-point clause explicitly identifies its Poincare fibre at q
  with the pullback along f × 1 of the Poincare fibre represented by q.
  Thus it says `[Q] ↦ [f^*Q]` over every geometric field, including for b.
- Additivity of duality is built into `→+`. The `→ₗ[ℚ]` map dQ and its pure
  tensor equation say that this extends Q-linearly to rational homomorphisms.
- Pullback formula is the clause ending
  `abelianHomComp (abelianHomComp b (φ N hN)) (d A A D D b)`.
  In categorical order this is exactly b followed by φ_N followed by b-dual.
  Upstream pullback of an invertible module is invertible, so the argument of
  φ for b-star N uses inferInstance, without a new assumption.
- For every ample invertible L, the statement gives invLambda in rational
  Hom(D,A), and a rational linear map dagger on rational End(A).
  The two c equations are the left and right inverse identities for φ_L.
- The equation for dagger reads, in categorical order, λ followed by v-dual
  followed by invLambda. This is exactly λ^{-1} v^vee λ in ordinary composition.
- `Function.Involutive dagger` supplies the involution law. The c equation
  reverses composition; `dagger (r • id) = r • id` fixes all rational scalars.
  Q-linearity is included in dagger's linear-map type.
- Symmetric kernel: the final universally quantified N is invertible;
  `Nonempty ((tensorPullback (ι[A]).left).obj N ≅ N)` is [-1]-symmetry;
  `abelianHomToRational (φ N hN) = 0` is precisely rational vanishing;
  `Nonempty (N.tensorPow 2 ≅ 𝟙_ A.left.Modules)` is the asserted square triviality.

Dependency declarations read and used:

- `Field`, Mathlib.Algebra.Field.Defs; `TensorProduct`, Mathlib.LinearAlgebra.TensorProduct.Defs,
  with its quotient construction, canonical bilinear map, lift and scalar extension.
- `IsAbelianVariety`, WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs;
  `IsAbelianVariety.isCommMonObj`, its Basic module (commutativity is inferred).
- `GrpObj`, `Grp.mk`, bundled homomorphisms, and Hom.commGroup,
  Mathlib.CategoryTheory.Monoidal.Grp and Monoidal.Cartesian.Grp.
- `Scheme.Modules.IsInvertible`, WeilConjectures.AlgebraicGeometry.Modules.Invertible;
  `Scheme.Modules.dual`, its Dual module; tensor-invertibility in ProjectionFormula.
- `Scheme.Modules.IsAmple`, WeilConjectures.AlgebraicGeometry.Ample.
- `Scheme.Modules.tensorPullbackSectionAdjunction` and `tensorPullback`,
  Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction / the public upstream
  TensorPullback import. The geometric-point and symmetry clauses use tensorPullback.
- `AbelianDualPoincareDatum`, `ClassifiesAbelianDifference`,
  `abelianNormalizedDifference`, Sheaf.AlgebraicGeometry.AbelianVariety.DualPoincareDatum.
  Its existing classifiers use `Scheme.Modules.pullback`, so the dual classifier
  and pullback-calculus clause retain that precise existing interface.
  This is the same inverse-image functor as tensorPullback up to its canonical
  adjunction comparison: both are left adjoint to the same pushforward.
  No separate module-pullback definition is introduced.
- `AddCommGroup.rationalizationMap`, Sheaf.GroupTheory.TorsionfreeRationalizationInjective;
  reused directly in the helper, including the tensor-factor order already used there.

All already stated proof dependencies are imported, either directly or through public
statement imports: the relative algebraic-space Poincare calculus, schemeSpace,
locally separated group-space representability, ordinary/etale invertible comparison,
module pullback/tensor and composition, and torsion-free rationalization.
The field-extension, ample-isogeny, simple-decomposition, biduality and finite-free-Hom
proof nodes currently have no Lean record; no import is invented for them.
They are proof prerequisites, not notions required to type this statement.

Edge cases checked: dim A=0 (zero Hom groups and id=zero cause no contradiction);
N=O_A; b=zero and b=id; r=0 and negative rationals; imperfect k; characteristic
2 (no division by 2 in k); nonsymmetric ample L (no extra symmetry assumption);
symmetric N whose image vanishes only after rationalization; geometric points over
extensions of k. Rational denominators occur in Q, never in k. Schemes and fields
share u as in the recorded datum; Ω is not quantified in a smaller universe.

Searches: actual wrapper logs are retained in searches.jsonl. LeanFinder query
"Polarization of an abelian variety Rosati involution rational endomorphisms symmetric
line bundles" returned eight root-system results, not abelian geometry. Loogle
`"Rosati", "AbelianVariety"` returned zero; Mathlib geometry grep
`Rosati|[Pp]olarization|Poincare` returned zero. LeanSearch for rational Hom tensor
integers/rationals returned generic tensor and scalar maps; LeanFinder for that
notion returned Weierstrass point maps and AddMonoidHom.toRatLinearMap, not the
scheme Hom rationalization. Loogle `"Grp.mk", "TensorProduct"` and grep
`abelianRationalHom|abelianHomToRational|Rosati` returned zero. The returned
AddMonoidHom and TensorProduct APIs are used rather than redefined.
Project rg searches for Rosati/polarization/Poincare and rational Hom, and the exact
item-id grep in WeilConjectures, found no theorem covering this item. The existing
Sheaf AbelianVariety.PolarizationCalculus theorem assumes IsAlgClosed k and has no
rational involution or symmetric-kernel conclusion; it is not an exact match.
DAG searches for rational Hom and `blueprint_refs.py search 'rational homomorphisms'`
found no definition node (zero blueprint matches); references to End tensor Q in
other statements do not define a reusable interface. The entire provided stage-2
brief, stage rules and error section H were read. Milne AV I Proposition 8.4,
Remark 8.5, the normalized difference, §9 and §14 opening were read from the local
PDF. The current latest blueprint unit was read; it is the six-functor stability
statement, not this auxiliary. No blueprint statement is changed.

## New nodes

`def-sfb-abelian-rational-hom`: defines the integral group-scheme Hom with additive
notation, rational Hom by the actual Mathlib tensor product, the existing canonical
rationalization, integral composition and identity. Source: Milne AV I §10 and §14
opening p.61. No theorem is postponed here. Its own module is RationalHom.lean.
The Mathlib pieces exist but no node or project declaration supplies this particular
scheme Hom tensor interface; the search records are copied without changing their
query/results from the actual wrapper log. It cites Field, abelian variety, group
scheme and tensor product, and the item cites it. The ancestor is null exactly as
`blueprint_refs.py ancestor` reports and as the parent auxiliary records.

Validation: both delivered files compiled separately through scompile.py in dependency
order, including module-mode library rechecks; only the item's expected sorry is left.
All binders and the universe u are explicit, autoImplicit and relaxedAutoImplicit are
false, and no local notation, local instance or private helper occurs. The helper is
an explicit construction; existential c, dQ and dagger occur inside the proposition,
where their displayed characterizations determine them, not as hollow chosen data.

## Second reading by N9

Self-check only; no independent second worker was started, in accordance with the
brief. The maintainer supplies independent review. On rereading the node and both
files I removed unnecessary proof binders for tensor/pullback invertibility in favor
of their existing instances, added the dual geometric-point formula explicitly, and
strengthened the classifier presentation to the existing iff-with-equality interface
so uniqueness does not depend on extra properties. Both composition identities and
the reversal clause were checked in categorical order. No mathematical hypothesis
or clause was dropped; no source or accepted split field is changed.
