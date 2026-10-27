module

public import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Universal density of separable points in their reduced closure

Source: Bosch–Lütkebohmert–Raynaud, Néron Models, 3.3 Lemma 4, printed p.67;
coefficient-basis and finite-product extension used in 7.1 Lemma 4
(blueprint: lem-sfb-separable-point-closure-universal-density).

The reduced induced closure is specified by its reduced closed immersion and its image,
as characterized by `Scheme.IdealSheafData.reduced_induced_closed_subscheme`.
Products in `Over (Spec E)` are fibre products over `E`. Their rational points are
identified with induced tuples by their coordinate composites into the ambient scheme.
Vanishing is tested in residue fields; these embed into the rational point's field,
so this is exactly vanishing under rational-point evaluation.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The reduced closure of a Galois-stable family of separable points is geometrically
reduced, and its positive finite powers are schematically detected by those tuples,
including after arbitrary extensions of the separable closure.

Source: BLR, Néron Models, 3.3 Lemma 4, printed p.67; coefficient and product extension
used in 7.1 Lemma 4 (blueprint: lem-sfb-separable-point-closure-universal-density).

Proof:
1. Every point factors through the reduced induced closed subscheme, by
   `lem-weil-pbc-reduced-induced-closed-subscheme`. On each affine open of that
   subscheme the family is topologically dense. A section vanishing at its points
   belongs to the nilradical by `lem-weil-pbc-affine-open-section-vanishing-prime`
   and `lem-weil-pbc-zero-locus-eq-iff-radical-eq`; it is zero by reducedness and
   `lem-weil-pbc-affine-scheme-reduced-iff`. Thus evaluation B → K^T is injective.
2. The kernel of B tensor_k K → K^T is a K-linear subspace stable under Galois:
   evaluating sigma(f) at t gives sigma(f(sigma^{-1}(t))). The separable closure is
   Galois by `lem-weil-pbc-separable-closure-exists-galois`. Apply
   `lem-sfb-galois-stable-subspace-descent`: the kernel descends to the zero kernel
   from step 1, hence is zero.
3. For any E/K, expand the finitely many coefficients of a tensor in a K-basis of E,
   using `lem-weil-pbc-vector-space-basis-through-vector`. Independence and step 2
   show evaluation remains injective. Tensor and tower identifications are
   `def-weil-vector-space-scalar-extension`.
4. In a common algebraically closed overfield Omega of K and L, the preceding injection
   makes B tensor_k Omega reduced. Faithful scalar extension embeds B tensor_k L
   into it. By `lem-weil-pbc-fibre-product-affine-spectra`,
   `lem-weil-pbc-open-fibre-product` and `lem-weil-pbc-affine-scheme-reduced-iff`,
   these reduced affine charts cover Y_L, proving reducedness.
5. Induct on the positive number of factors. Expand a tensor in a basis of the last
   affine coordinate ring. Evaluating at a tuple in the preceding factors leaves
   an element detected by the last factor. Independence kills its coefficients;
   induction kills the original tensor. Apply step 3 to extend this to every E/K.
6. This gives injectivity on products of affine charts. For a principal open D(g),
   a section b/g^r vanishing at its family has gb evaluating to zero everywhere,
   so gb = 0 and b/g^r = 0. The principal-open basis and localization descriptions
   (`lem-weil-pbc-spec-localization-away-basic-open` and
   `lem-weil-pbc-affine-open-section-vanishing-prime`) and the sheaf axiom give
   the claimed test on every affine open of the product.
7. Empty T has empty reduced closure. All field base changes and positive powers
   are empty, and their section rings are zero rings. Empty affine factors and
   empty restricted families are included in the same injectivity arguments. -/
theorem separable_point_closure_universal_density
    {k K : Type u} [Field k] [Field K] [Algebra k K] [IsSepClosure k K]
    (Z : Over (Spec (.of k))) [LocallyOfFiniteType Z.hom]
    (T : Set (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ Z))
    (hstable : ∀ (σ : K ≃ₐ[k] K) (t :
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ Z),
      t ∈ T → ∃ t' ∈ T, t'.left = Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ t.left)
    (Y : Scheme.{u}) (i : Y ⟶ Z.left) [IsClosedImmersion i] [IsReduced Y]
    (hclosure : Set.range i = closure (Set.range (fun t : T ↦
      t.val.left (IsLocalRing.closedPoint K)))) :
    (∀ (L : Type u) [Field L] [Algebra k L]
      (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra k Ω] [Algebra K Ω] [Algebra L Ω]
      [IsScalarTower k K Ω] [IsScalarTower k L Ω],
      IsReduced (pullback (i ≫ Z.hom) (Spec.map (CommRingCat.ofHom (algebraMap k L))))) ∧
    (∀ (E : Type u) [Field E] [Algebra K E] [Algebra k E] [IsScalarTower k K E]
      (m : ℕ), 1 ≤ m →
      ∀ (U : (∏ᶜ (fun _ : Fin m ↦ Over.mk (pullback.snd (i ≫ Z.hom)
          (Spec.map (CommRingCat.ofHom (algebraMap k E)))))).left.affineOpens)
        (s : (∏ᶜ (fun _ : Fin m ↦ Over.mk (pullback.snd (i ≫ Z.hom)
          (Spec.map (CommRingCat.ofHom (algebraMap k E)))))).left.presheaf.obj
            (Opposite.op U.1)),
        (∀ (x : Over.mk (𝟙 (Spec (.of E))) ⟶
            ∏ᶜ (fun _ : Fin m ↦ Over.mk (pullback.snd (i ≫ Z.hom)
              (Spec.map (CommRingCat.ofHom (algebraMap k E)))))),
          (∀ j : Fin m, ∃ t ∈ T,
            x.left ≫ (Pi.π (fun _ : Fin m ↦ Over.mk (pullback.snd (i ≫ Z.hom)
              (Spec.map (CommRingCat.ofHom (algebraMap k E))))) j).left ≫
              pullback.fst (i ≫ Z.hom) (Spec.map (CommRingCat.ofHom (algebraMap k E))) ≫ i =
                Spec.map (CommRingCat.ofHom (algebraMap K E)) ≫ t.left) →
          ∀ hx : x.left (IsLocalRing.closedPoint E) ∈ U.1,
            Scheme.evaluation _ U.1 (x.left (IsLocalRing.closedPoint E)) hx s = 0) → s = 0) := by
  sorry

end AlgebraicGeometry
