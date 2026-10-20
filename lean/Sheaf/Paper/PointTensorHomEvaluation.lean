/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A8
-/
module

public import Sheaf.Paper.PointDerivedHomModels
import Sheaf.Paper.PointSheafHomMaps
import Sheaf.Paper.ModuleHomSignedEvaluation

/-! # Signed tensor-Hom evaluation at a point

Source: Stacks Project, Tags 0A8X and 08J7.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe t u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open scoped TensorProduct

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

namespace WeilConjectures.PointDerivedHom

variable (k : Type t) [Field k]
  {R : CommRingCat.{max u (t + 1)}}
  (B : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{max u (t + 1)})
  (α : constantRing.{t, u} k R ⟶ B)
  (L : ModuleCat.{max u (t + 1)} R ⥤ Modules.{t, u} k B)
  (hobj : ∀ M : ModuleCat.{max u (t + 1)} R,
    L.obj M = extensionObject.{t, u} k B α M)
  (adj : L ⊣ sections.{t, u} k B α)
  (c : CochainComplex (ModuleCat.{max u (t + 1)} R) ℤ)

/-- The normalized Hom comparison intertwines ordinary signed evaluation.
Source: Stacks Project, Tags 0A8X and 08J7, the tensor-Hom counit
(blueprint: lem-pod-point-tensor-hom-evaluation).

Proof: in each bidegree (p,j), evaluate a section of Hom on its argument and
multiply by (-1)^(pj). This is bilinear and respects restriction, so the presheaf
tensor universal property, associated-module sheafification and the coproduct
universal property give eB. The Hom differential and tensor differential make it
a chain map: the two terms containing h(dy) cancel, leaving d_I(h(y)). The same
construction with module linear maps gives eR. For beta, use the adjunction unit
x ↦ 1 tensor x, tensor with the section h, and insert into the (p,j) total summand.
Scalar balancing holds through the constant-value map. Naturality of the unit,
the specified action of L on morphisms, and naturality of tensor give the chain
identity. These constructions do not commute sections with any coproduct.
Finally both composites on x tensor h equal (-1)^(pj) h(1 tensor x), by the
normalization of q. Pure tensors generate each module tensor summand; coproduct
extensionality proves equality of the chain maps. This argument uses neither
K-flatness nor a K-injective target: those are only needed to interpret the maps
in the derived category. The sign calculation is valid in every integer degree. -/
theorem point_tensor_hom_evaluation
    (hex : ExplicitAdjunction.{t, u} k B α L hobj adj)
    (I : CochainComplex (Modules.{t, u} k B) ℤ)
    (q : (sectionComplex.{t, u} k B α).obj
      (sheafHom.{t, u} k B ((extensionComplex.{t, u} k B α L adj).obj c) I) ≅
        CochainComplex.moduleHomComplex c ((sectionComplex.{t, u} k B α).obj I))
    (hq : IsComparison.{t, u} k B α L hobj adj c I q) :
    EvaluationCompatible.{t, u} k B α L hobj adj c I q := by
  obtain ⟨eB, beta, heB, hbeta⟩ := point_sheaf_hom_maps k B α L hobj adj c hex I
  obtain ⟨eR, heR⟩ := CochainComplex.module_hom_signed_evaluation c
    ((sectionComplex k B α).obj I)
  refine ⟨eB, beta, eR, heB, hbeta, heR, ?_⟩
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p j hpj
  change p + j = n at hpj
  subst n
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x h
  have ht := congrArg (fun f ↦ f.hom (x ⊗ₜ[R] h))
    (HomologicalComplex.ι_mapBifunctorMap (𝟙 c) q.hom (curriedTensor _)
      (.up ℤ) p j (p + j) rfl)
  change ((((curriedTensor (ModuleCat R)).map₂CochainComplex.obj c).map q.hom).f
    (p + j)).hom (moduleTotalElement c _ p j x h) =
      moduleTotalElement c _ p j x ((q.hom.f j).hom h) at ht
  change (((sectionComplex k B α).map eB).f (p + j)).hom
    ((beta.f (p + j)).hom (moduleTotalElement c _ p j x h)) =
      (eR.f (p + j)).hom
        (((((curriedTensor (ModuleCat R)).map₂CochainComplex.obj c).map q.hom).f
          (p + j)).hom (moduleTotalElement c _ p j x h))
  rw [hbeta, ht]
  have hr := heR p j x ((q.hom.f j).hom h)
  change (eR.f (p + j)).hom (moduleTotalElement c _ p j x
    ((q.hom.f j).hom h)) = _ at hr
  erw [hr, hq]
  exact heB p j (op (finalObject k)) _ h

end WeilConjectures.PointDerivedHom
