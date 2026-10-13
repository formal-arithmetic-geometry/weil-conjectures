/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.EtaleAffineSingletonTensorDegreeHomNormalization

/-! # EtaleSingletonTensorNormalizedRestriction
Source: Stacks Project, Tags 03P2 and 03DR.
(blueprint: lem-sc-singleton-tensor-normalized-restriction)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme
noncomputable section

/-- The evaluated normalized pure sections agree after omitting a factor.
Source: Stacks Project, Tag 03P2 (tensor Čech identification), Tag 03DR.
(blueprint: lem-sc-singleton-tensor-normalized-restriction)

Proof: apply hf to evaluate the input section as the product of pulled-back
functions times the restriction of m from U. Semilinearity of
etaleTensorSectionsRestriction moves that scalar product outside restriction.
A ring homomorphism preserves finite products. For each k, the product map
omitting j followed by the k-th projection is the j.succAbove(k)-th projection,
by Pi.lift_π. Functoriality of appTop therefore identifies each pulled-back
scalar with the corresponding retained projection function on the larger
product. Composition of etaleTensorSectionsRestriction and the over-U
triangle identify the restricted coefficient with direct restriction from U.
Apply hf' to evaluate the inserted-unit pure section. Its j-th scalar factor
is the pullback of one and equals one. Fin.prod_univ_succAbove, together with
insertNth at j and at j.succAbove(k), identifies its remaining factors with
those just computed. Thus the evaluated sections agree. This argument has
no Čech coface and no injectivity assertion. It works in degree zero, for
both possible omitted factors, and for zero modules and empty schemes.
-/
theorem singletonTensor_normalized_restriction
    (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent]
    (U W : X.Etale) (g : W ⟶ U) (n : ℕ) (j : Fin (n + 2))
    (f : (singletonTensorAmitsur X F U W g).X n ⟶
      (singletonTensorCech X F U W g).X n)
    (f' : (singletonTensorAmitsur X F U W g).X (n + 1) ⟶
      (singletonTensorCech X F U W g).X (n + 1))
    (hf : IsSingletonTensorDegreeComparisonHom X F U W g n f)
    (hf' : IsSingletonTensorDegreeComparisonHom X F U W g (n + 1) f')
    (m : Γ((Modules.tensorPullback U.hom).obj F, ⊤))
    (b : Fin (n + 1) → Γ(W.left, ⊤)) :
    letI : Algebra Γ(U.left, ⊤) Γ(W.left, ⊤) := g.left.appTop.hom.toAlgebra
    Modules.etaleTensorSectionsRestriction F (Pi.lift (fun k : Fin (n + 1) ↦
      Pi.π (fun _ : Fin (n + 2) ↦ Over.mk g) (j.succAbove k))).left
      (((Pi.π (fun _ : Fin (n + 1) → Fin 1 ↦
      AddCommGrpCat.of (ULift.{u + 1}
        Γ((Modules.tensorPullback
          (∏ᶜ (fun _ : Fin (n + 1) ↦ Over.mk g)).left.hom).obj F, ⊤)))
      (fun _ ↦ 0)) (f (ULift.up (m ⊗ₜ[Γ(U.left, ⊤)] PiTensorProduct.tprod Γ(U.left, ⊤) b)))).down) =
    ((Pi.π (fun _ : Fin (n + 2) → Fin 1 ↦
      AddCommGrpCat.of (ULift.{u + 1}
        Γ((Modules.tensorPullback
          (∏ᶜ (fun _ : Fin (n + 2) ↦ Over.mk g)).left.hom).obj F, ⊤)))
      (fun _ ↦ 0)) (f' (ULift.up (m ⊗ₜ[Γ(U.left, ⊤)]
        PiTensorProduct.tprod Γ(U.left, ⊤) (j.insertNth 1 b))))).down := by sorry

end
end AlgebraicGeometry.Scheme
