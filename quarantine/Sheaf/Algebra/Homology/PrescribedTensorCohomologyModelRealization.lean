/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModel
public import WeilConjectures.Algebra.Homology.RingTensorCohomology

import WeilConjectures.Algebra.Homology.KFlatScalarExtensionCounit
import WeilConjectures.Algebra.Homology.MixedTensorKFlatQuasiIso
import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModelMap
import WeilConjectures.Algebra.Homology.BaseTensorOrdinaryIso
import WeilConjectures.Algebra.Homology.FlatScalarExtensionHomologyAdjunct

/-! # Realization of prescribed tensor cohomology on a K-flat resolution

Source: Stacks Project, Tags 06Y6, 064L, 065Z and 00HD.
(blueprint: lem-pc-prescribed-tensor-cohomology-model-realization). -/

@[expose] public section

set_option autoImplicit false

universe u w v z

open CategoryTheory
open scoped TensorProduct

namespace RingTensorCohomology

/-- Realize prescribed lifts and their comparison on any functorial K-flat replacement.
Source: Stacks Project, Tags 06Y6 and 064L (K-flat replacements), 065Z
(the canonical comparison), and 00HD (exact flat extension).
(blueprint: lem-pc-prescribed-tensor-cohomology-model-realization)

Proof: put V=resolution_R(restrict_R(Q)). Its augmentation is a quasi-isomorphism,
and V is R-K-flat. For each supplied L(M), the universal counit is invertible on
V(M); derived extension of the augmentation consequently identifies L(M)'s derived
cohomology of Q(M) with the ordinary extension of V(M). Applying resolution_R to
restrict_R(pi) gives a quasi-isomorphism between R-K-flat complexes, which remains
so after extension to B: apply clause (i) of
[lem-pc-mixed-tensor-kflat-quasi-iso] with the B-complex B[0]; the natural
single-complex tensor and unit isomorphisms identify the induced mixed tensor map
with scalar extension of this resolution map. Thus this cohomology is naturally
source(U). Conjugate by
eS and L.cohomologyIso to obtain sigma. Naturality for multiplication by a and hS
show that sigma commutes with a tensor 1. It is B-linear already, so tensor
induction upgrades it to a tensor-algebra-linear isomorphism.
For the target use the common span resolution_A(Q) to Q and resolution_A(U),
whose arrows are augmentation_A(Q) and resolution_A(pi). Both are
quasi-isomorphisms between A-K-flat complexes and remain so after extension to
A tensor_R B: apply clause (i) of
[lem-pc-mixed-tensor-kflat-quasi-iso] with the C-complex C[0]; the natural
single-complex tensor and unit isomorphisms identify the induced mixed tensor maps
with scalar extension of the two span maps. Ordinary tensor associativity and eT
identify target(U) with
cohomology of the latter complex. The equation hT upgrades this identification
to tensor-algebra-linearity. The span identifies it with ordinary tensor cohomology
of Q. Flat extension to D commutes with cohomology; its canonical homology adjunct
and tensor associativity give gamma. Every map in these spans is natural, giving
gamma's naturality. For each g, use the unique counit-compatible isomorphism
between L(M).derived and L(N).derived. Under sigma, S.map g is cohomology of
L(M).derived applied to Q.map g followed by that isomorphism, giving the stated
model-map equation. Finally hc identifies c with the comparison computed on the
common R-K-flat span, and comparison_eq identifies L.comparison with its counit.
Extend this comparison to D and compose with the same canonical homology adjunct
used in gamma. Scalar-extension adjunction and localized_eq identify the result
with L.localizedComparison, proving the final equation. No localization or comparison
between different base rings
is asserted here. The zero replacement and identity replacement satisfy the same
construction, and no boundedness or flatness of B over R is used. -/
theorem prescribedTensorCohomology_model_realization
    (R A B D : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing D]
    [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) D]
    [Algebra A D] [IsScalarTower A (A ⊗[R] B) D]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} B)]
    (E : Type v) [Category.{z} E]
    (U Q : E ⥤ CochainComplex (ModuleCat.{u} A) ℤ)
    (pi : Q ⟶ U) (hpi : ∀ M, QuasiIso (pi.app M))
    (hQ : ∀ M, (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat (Q.obj M))
    (i : ℤ)
    (S T : E ⥤ ModuleCat.{u} (A ⊗[R] B))
    (eS : S ⋙ ModuleCat.restrictScalars Algebra.TensorProduct.includeRight.toRingHom ≅
      U ⋙ source R A B i)
    (eT : T ⋙ ModuleCat.restrictScalars Algebra.TensorProduct.includeRight.toRingHom ≅
      U ⋙ target R A B i)
    (c : S ⟶ T)
    (hS : ∀ (M : E) (a : A) (x : S.obj M),
      eS.hom.app M ((Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) • x) =
        (source R A B i).map (a • 𝟙 (U.obj M)) (eS.hom.app M x))
    (hT : ∀ (M : E) (a : A) (x : T.obj M),
      eT.hom.app M ((Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) • x) =
        (target R A B i).map (a • 𝟙 (U.obj M)) (eT.hom.app M x))
    (hc : Functor.whiskerRight c
        (ModuleCat.restrictScalars Algebra.TensorProduct.includeRight.toRingHom) ≫ eT.hom =
      eS.hom ≫ Functor.whiskerLeft U (comparison R A B i))
    (hf : (algebraMap (A ⊗[R] B) D).Flat)
    (L : ∀ M : E, ModuleCat.BaseDerivedTensorCohomologyModel R A B (Q.obj M) D) :
    ∃ (sigma : ∀ M : E, S.obj M ≅ (L M).cohomology i)
      (gamma : ∀ M : E,
        (ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)).obj (T.obj M) ≅
          (((ModuleCat.extendScalars ((algebraMap (A ⊗[R] B) D).comp
            (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex (.up ℤ)).obj
              (Q.obj M)).homology i),
      (∀ (M N : E) (g : M ⟶ N),
        (ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)).map (T.map g) ≫
            (gamma N).hom =
          (gamma M).hom ≫ HomologicalComplex.homologyMap
            (((ModuleCat.extendScalars ((algebraMap (A ⊗[R] B) D).comp
              (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex (.up ℤ)).map (Q.map g)) i) ∧
      (∀ (M N : E) (g : M ⟶ N),
        ∃ delta : (L M).derived ⟶ (L N).derived,
          Functor.whiskerLeft (DerivedCategory.Qh (C := ModuleCat.{u} R)) delta ≫
              (L N).counit = (L M).counit ∧
          (ModuleCat.restrictScalars Algebra.TensorProduct.includeRight.toRingHom).map
              ((sigma M).inv ≫ S.map g ≫ (sigma N).hom) ≫ ((L N).cohomologyIso i).hom =
            ((L M).cohomologyIso i).hom ≫
              (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map
                ((L M).derived.map (DerivedCategory.Qh.map
                  ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).map
                    ((restrict R A).map (Q.map g))))) ≫
              (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map
                (delta.app (DerivedCategory.Qh.obj
                  ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).obj
                    ((restrict R A).obj (Q.obj N)))))) ∧
      (∀ M : E,
        (ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)).map (c.app M) ≫ (gamma M).hom =
          (ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)).map (sigma M).hom ≫
            (L M).localizedComparison i) := by sorry

end RingTensorCohomology
