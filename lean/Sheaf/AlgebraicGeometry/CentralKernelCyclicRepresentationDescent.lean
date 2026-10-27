module

public import Sheaf.RingTheory.HopfActionModuleData
public import Sheaf.AlgebraicGeometry.HopfCoactionLinearization
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Mathlib.RingTheory.RingHom.FaithfullyFlat

import WeilConjectures.RingTheory.FaithfullyFlat.Amitsur
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Descent of the cyclic representation of a kernel-fixed vector

Source: Milne, Algebraic Groups (2017), Lemma 5.15 and Theorem 5.13, pp.101--102.
(blueprint: lem-sfb-central-kernel-cyclic-representation-descent)
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry.RationalRepresentation

/-- The canonical coordinate pullback of a morphism of affine schemes over the field.
It is obtained from the fully faithful affine Spec functor using the canonical affine
identifications, so no coordinate map is chosen as extra data.
Source: Milne, Theorem 5.13, p.101, affine coordinates.
(blueprint: lem-sfb-central-kernel-cyclic-representation-descent). -/
def coordinatePullback {F : Type u} [Field F]
    {H G : Scheme.{u}} [H.Over (Spec (.of F))] [G.Over (Spec (.of F))]
    [GrpObj (H.asOver (Spec (.of F)))] [GrpObj (G.asOver (Spec (.of F)))]
    [IsAffine H] [IsAffine G]
    (q : H.asOver (Spec (.of F)) ⟶ G.asOver (Spec (.of F))) :
    Γ(G, ⊤) →ₐ[F] Γ(H, ⊤) :=
  ((Spec.mapMulEquiv (R := F) (S := Γ(G, ⊤)) (T := Γ(H, ⊤))).invFun
    ((H.isoSpec.inv.asOver (Spec (.of F))) ≫ q ≫
      G.isoSpec.hom.asOver (Spec (.of F)))).ofConv

/-- The actual intersection of all subcomodules containing the vector. A subspace is
stable precisely when the coaction lands in the image of its tensor inclusion.
Source: Milne, Lemma 5.15, p.102; the minimum-dimension intersection argument in the node.
(blueprint: lem-sfb-central-kernel-cyclic-representation-descent). -/
def cyclicSubspace {F : Type u} [Field F]
    {H : Scheme.{u}} [H.Over (Spec (.of F))]
    [GrpObj (H.asOver (Spec (.of F)))] [IsAffine H]
    {V : Type u} [AddCommGroup V] [Module F V]
    (ρ : {c : V →ₗ[F] V ⊗[F] Γ(H, ⊤) //
      HopfAction.Coassociative F Γ(H, ⊤) V c ∧ HopfAction.Counital F Γ(H, ⊤) V c})
    (v : V) : Submodule F V :=
  sInf {U : Submodule F V | v ∈ U ∧
    ∀ x : U, ρ.val x ∈ LinearMap.range (U.subtype.rTensor Γ(H, ⊤))}

/-- The finite cyclic subcomodule of a kernel-fixed nonzero vector has trivial kernel
coaction and a unique descended coaction, whose coordinate pullback is exactly its
original coaction.
Source: Milne, Lemma 5.15 and Theorem 5.13, pp.101--102.
(blueprint: lem-sfb-central-kernel-cyclic-representation-descent).

Proof: (1) Split kernels and images of linear maps using bases
(lem-weil-pbc-vector-space-free, def-weil-pbc-free-module). Tensor the split decompositions
and inverse maps using def-weil-pbc-module-tensor-product: tensoring preserves kernels,
injections and binary intersections over F.
(2) Among subcomodules containing v choose one of minimum dimension. Its intersection
with any other member has the same dimension, hence equals it. Thus the displayed
intersection is a subcomodule. It is finite-dimensional, and v remains nonzero in it
(def-weil-finite-dimensional-subspace).
(3) The K-fixed subspace is the kernel of the restricted coaction minus x tensor 1.
By (1), its scalar extensions are the corresponding kernels. Evaluation at K-points
identifies these kernels with invariants; the universal K-point proves the converse
(def-weil-pbc-module-tensor-product, lem-weil-pbc-algebra-tensor-pushout-universal-property).
(4) K is normal as a scheme-theoretic kernel (def-sc-group-scheme). The identity
k(hw)=h(h⁻¹kh)w after every algebra extension shows that the invariant subspace is
H-stable. Evaluation at the universal H-point gives a subcomodule containing v,
so the cyclic subcomodule is contained in it. Its restricted K-coaction is trivial.
(5) Put A=F[G], B=F[H]. The two points of H(B tensor_A B) have the same G-image,
so their quotient belongs to K. Triviality on the cyclic submodule says its matrix
coefficients b satisfy b tensor 1 = 1 tensor b. Augmented Amitsur exactness
(lem-pc-cech-exact), with the tensor algebra of
lem-weil-pbc-algebra-tensor-pushout-universal-property, descends each coefficient uniquely
to A. Define the descended linear map on a basis by these coefficients.
(6) Pull back its coassociativity identity along 1 tensor q* tensor q*: it becomes
coassociativity of the given H-coaction. This pullback is injective by (1) and (5).
Counitality follows from compatibility of q* with the counits. The same injectivity
proves uniqueness. No finite-type, reducedness or centrality assumption is used. -/
theorem centralKernel_cyclic_representation_descent
    {F : Type u} [Field F] (H G : Scheme.{u})
    [H.Over (Spec (.of F))] [G.Over (Spec (.of F))]
    [GrpObj (H.asOver (Spec (.of F)))] [GrpObj (G.asOver (Spec (.of F)))]
    [IsAffine H] [IsAffine G]
    (q : H.asOver (Spec (.of F)) ⟶ G.asOver (Spec (.of F))) [IsMonHom q]
    (hq : (coordinatePullback q).toRingHom.FaithfullyFlat)
    (V : Type u) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (ρ : {c : V →ₗ[F] V ⊗[F] Γ(H, ⊤) //
      HopfAction.Coassociative F Γ(H, ⊤) V c ∧ HopfAction.Counital F Γ(H, ⊤) V c})
    (v : V) (hv : v ≠ 0)
    (hKv : ∀ (R : Type u) [CommRing R] [Algebra F R] (x : Γ(H, ⊤) →ₐ[F] R),
      x.comp (coordinatePullback q) =
          (Algebra.ofId F R).comp (Bialgebra.counitAlgHom F Γ(G, ⊤)) →
        x.toLinearMap.lTensor V (ρ.val v) = v ⊗ₜ[F] (1 : R)) :
    FiniteDimensional F (cyclicSubspace ρ v) ∧
      (∃ w : cyclicSubspace ρ v, (w : V) = v ∧ w ≠ 0) ∧
      ∃ ρW : {c : cyclicSubspace ρ v →ₗ[F] (cyclicSubspace ρ v) ⊗[F] Γ(H, ⊤) //
          HopfAction.Coassociative F Γ(H, ⊤) (cyclicSubspace ρ v) c ∧
            HopfAction.Counital F Γ(H, ⊤) (cyclicSubspace ρ v) c},
        (cyclicSubspace ρ v).subtype.rTensor Γ(H, ⊤) ∘ₗ ρW.val =
          ρ.val ∘ₗ (cyclicSubspace ρ v).subtype ∧
        (∀ (R : Type u) [CommRing R] [Algebra F R] (x : Γ(H, ⊤) →ₐ[F] R),
          x.comp (coordinatePullback q) =
              (Algebra.ofId F R).comp (Bialgebra.counitAlgHom F Γ(G, ⊤)) →
            ∀ w : cyclicSubspace ρ v,
              x.toLinearMap.lTensor (cyclicSubspace ρ v) (ρW.val w) =
                w ⊗ₜ[F] (1 : R)) ∧
        ∃! ρG : {c : cyclicSubspace ρ v →ₗ[F] (cyclicSubspace ρ v) ⊗[F] Γ(G, ⊤) //
            HopfAction.Coassociative F Γ(G, ⊤) (cyclicSubspace ρ v) c ∧
              HopfAction.Counital F Γ(G, ⊤) (cyclicSubspace ρ v) c},
          (coordinatePullback q).toLinearMap.lTensor (cyclicSubspace ρ v) ∘ₗ ρG.val =
            ρW.val := by
  sorry

end AlgebraicGeometry.RationalRepresentation
