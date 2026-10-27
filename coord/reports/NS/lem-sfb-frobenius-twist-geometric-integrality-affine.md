## Worker report

The module `Sheaf.AlgebraicGeometry.FrobeniusTwistGeometricIntegralityAffine` states
`AlgebraicGeometry.frobeniusTwist_geometricIntegrality_affine`. Its only postponed
proof is this theorem. Four real-data helpers package the existing Mathlib tensor
product, elementary tensors, and its two inclusions with an explicitly supplied
right scalar map; they introduce no new independent mathematical notion. All five
declarations are listed in `lean.declarations` and carry the owning blueprint tag.
No statement correction, new node, or dependency repair is needed.

Hypothesis and clause correspondence:

- The field is `(k : Type u) [Field k]`; positive prime characteristic is
  `(p : ℕ) (hp : p.Prime) [CharP k p]`. The equation passed to the recorded ring
  Frobenius is `CharP.cast_eq_zero k p`. No perfection, finiteness, smoothness,
  properness, or algebraic-closure assumption is made.
- The named structure morphism is `(X : Scheme.{u}) (s : X ⟶ Spec (.of k))`,
  and its geometric integrality is `[GeometricallyIntegral s]`.
- `(n : ℕ)` includes zero. The scalar power map is the dependency's
  `iterateFrobeniusOfPrime k hp (CharP.cast_eq_zero k p) n`.
- The scheme `X_n` is written literally as `pullback s (Spec.map ...φ_n...)`.
  Its first projection is `pullback.fst`, and its k-structure is `pullback.snd`.
- The existential `hX : (p : Γ(X, ⊤)) = 0` is a conclusion, derived from the
  structure map, not an additional hypothesis needed to invoke absolute Frobenius.
  The existential `F` has the two equations `F ≫ pullback.fst ... =
  X.iterateFrobenius hp hX n` and `F ≫ pullback.snd ... = s`. These uniquely
  determine the canonical pair map by pullback hom-extensionality; an arbitrary
  unconstrained map is not substituted for relative Frobenius.
- `GeometricallyIntegral (pullback.snd ...)` is precisely geometric integrality
  for the second-projection structure on `X_n`.
- `∀ (k' : Type u) [Field k'] (ι : k →+* k')` covers arbitrary field extensions
  in the ambient scheme universe; unital field homomorphisms are injective.
  The isomorphism `e` has target `pullback s (Spec.map (.ofHom (ι.comp φ_n)))`.
  Its two projection equations specify the canonical comparison, with first
  projection the composite of the two first projections and second projection
  the second projection to `Spec k'`. This uses no inverse Frobenius.
- The pointwise affine-cover clause is `∀ y : (X_n : Scheme.{u}), ∃ U :
  X.affineOpens, pullback.fst ... y ∈ U.1`. Thus the inverse images of all
  affine opens cover `X_n`.
- An affine open `U = Spec A ⊆ X` is represented by any `(A : Type u)
  [CommRing A] [Algebra k A] (i : Spec (.of A) ⟶ X) [IsOpenImmersion i]`
  satisfying `i ≫ s = Spec.map (.ofHom (algebraMap k A))`. This covers every
  affine open with its induced k-algebra structure and any affine presentation.
- `scalarTwistTensor k A φ_n` is Mathlib's actual `A ⊗[k] k`, with the
  right module and algebra explicitly taken from `φ_n.toAlgebra`. The explicit
  arguments are essential: Lean otherwise selects the ordinary self-module on k.
  Its commutative-ring data are `Algebra.TensorProduct.instCommRing`.
- `j : Spec (scalarTwistTensor k A φ_n) ⟶ X_n`, `IsOpenImmersion j`, its
  two projection equations with `scalarTwistTensorInl` and `scalarTwistTensorInr`,
  and `Set.range j = (pullback.fst ...) ⁻¹' Set.range i` identify the twist
  canonically with that tensor spectrum as an open in `X_n`. Along with the
  affine-cover clause these are precisely the covering twisted opens.
- `F ⁻¹' Set.range j = Set.range i` states `F⁻¹(U_n) = U`.
- The affine ring homomorphism is `H : scalarTwistTensor k A φ_n →+* A`.
  `H.comp (scalarTwistTensorInr k A φ_n) = algebraMap k A` is exactly
  k-linearity for the second-factor k-structure; a ring homomorphism commuting
  with those scalar maps is equivalently the asserted k-algebra homomorphism.
  `∀ a b, H (scalarTwistTensorTmul k A φ_n a b) =
  a ^ (p ^ n) * algebraMap k A b` states the full elementary-tensor formula.
  `Spec.map (.ofHom H) ≫ j = i ≫ F` identifies its spectrum map with the
  restriction of the very same `F`, using the open identifications already stated.
- At `n = 0`, `IsIso (pullback.fst ...)` specifies the canonical identity-base-change
  isomorphism, and `F ≫ pullback.fst ... = 𝟙 X` identifies `F` with the identity.
  The affine implication gives explicitly `H (a ⊗ b) = a * algebraMap k A b`.
  Its inverse is the first tensor inclusion, by identity-scalar balancing.

Dependency declarations read and used:

- `Field`, in `Mathlib.Algebra.Field.Defs`, and `CharP`/`CharP.cast_eq_zero`,
  in `Mathlib.Algebra.CharP.Defs`: the field and characteristic leaves.
- `AlgebraicGeometry.Scheme.Over`, in `Mathlib.AlgebraicGeometry.Over`: the
  structure-map notion; the node names s, so it is bound explicitly.
- `AlgebraicGeometry.GeometricallyIntegral`, in
  `Mathlib.AlgebraicGeometry.Geometrically.Integral`: its definition tests
  integral base changes at all field-valued points, exactly the recorded notion.
- `AlgebraicGeometry.baseChange_iterated` and the conventions of
  `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: scheme base
  change is `Limits.pullback` with second projection as structure morphism.
  `Scheme.Modules.moduleBaseChange` is the module-sheaf clause of that bundle,
  not the scheme construction used here; the record explicitly says this.
- `AlgebraicGeometry.Scheme.iterateFrobenius`, with its point and section
  formulas, in `WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius`.
- `iterateFrobeniusOfPrime`, with `iterateFrobeniusOfPrime_apply`, in
  `WeilConjectures.Mathlib.Algebra.CharP.Lemmas`; it permits zero section rings.
- `AlgebraicGeometry.Spec` and `Spec.map`, in
  `Mathlib.AlgebraicGeometry.Scheme`: the recorded spectrum definition.
- Proof imports include `Sheaf.AlgebraicGeometry.SchemeCharacteristic`
  (`Scheme.IsCharacteristic`), `Mathlib.AlgebraicGeometry.PullbackCarrier`
  (`Scheme.Pullback.range_map`), and `Mathlib.RingTheory.TensorProduct.Maps`
  (`Algebra.TensorProduct.productMap`). `Mathlib.AlgebraicGeometry.Pullbacks`
  supplies `Scheme.pullback_map_isOpenImmersion` and `pullbackSpecIso`, with
  its projection formulas. `pullback`, its projections, `pullback.lift`, and
  hom-extensionality come from the recorded fibre-product Mathlib interface.

Sources checked: Stacks varieties.tex, `definition-relative-frobenius` (0CC9),
`remark-n-fold-relative-frobenius` (0CCG), and `definition-geometrically-integral`
clause (3). The remark starts at n ≥ 1; the node explicitly extends to n=0
by its fifth proof step, carried verbatim in the theorem docstring. The five
proof steps also record the open-fibre-product, affine-product, and tensor
universal-property arguments with their dependency ids. All theorem proofs
remain `sorry`.

Edge cases checked mathematically before writing: n=0; X=Spec k; affine opens
with A the zero ring (the empty open); nonperfect k=F_p(t), where φ_n need not
be surjective; the affine line over that field; and arbitrary extensions ι,
including the identity. The empty X is excluded by geometric integrality
itself, not by an extra assumption. The ring/tensor helpers still make sense
for empty opens, and the recorded Frobenius API also supports their zero ring.
The universal universe u can be instantiated at any ambient size; test fields
and affine rings use this same ambient universe and are not quantified in an
independent potentially smaller universe.

Searches for an existing complete statement:

- `msearch.py ... leanfinder "Geometrically integral schemes remain geometrically
  integral under Frobenius twist and affine relative Frobenius is a tensor product
  map"`: eight results, concerning integral morphisms or geometrically reduced
  algebras; none includes the twist, all compatibility clauses, and the affine map.
- `msearch.py ... loogle '"frobenius", "pullback"'`: one unrelated result,
  `CategoryTheory.Regular.frobeniusMorphism_isPullback`.
- `msearch.py ... grep
  "relativeFrobenius|relative_frobenius|frobeniusTwist|GeometricallyIntegral"
  AlgebraicGeometry`: nine results, mainly the existing geometric-integrality
  definition and instances, with no complete matching statement.
- `rg` of the project and upstream Lean trees for relative Frobenius, twists,
  and the exact node id found the general relative pair-map interface and
  finite-field/curve results, but no statement of this node. In particular,
  `WeilConjectures.AlgebraicGeometry.RelativeFrobenius` gives the generic pair
  with reversed pullback order and an affine formula for compatible arbitrary
  endomorphisms; it does not assert this node's geometric-integrality and affine
  open clauses. The existing smooth-proper-curve relative-degree theorem is
  restricted to algebraically closed fields and smooth proper curves.
- `rg` for `scalarTwistTensor|frobeniusTwist_geometricIntegrality_affine` in
  Mathlib, upstream, and project sources found no name collisions. The helpers
  reuse `TensorProduct`, `TensorProduct.tmul`, and Mathlib's two inclusions,
  rather than defining another tensor product.

Validation: the module is checked by the prescribed per-file `scompile.py`
against the published live build. The delivery dry run and final wrapper are
also run, with any findings repaired before delivery.

## Second reading by NS

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
