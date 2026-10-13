/- Copyright (c) 2026 The SHEAF contributors. -/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule

/-! # Vanishing of the completion of a coherent kernel's ideal product

Source: Stacks Project, Tags 088A, 087W and 00MB.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- An affine limit-kernel annihilator makes every reduction of the coherent
ideal product with the original kernel zero.
Source: Stacks Project, Tag 088A, second application of Remark 0888;
Tag 087W and Algebra, Tag 00MB (exactness of finite-module completion).
(blueprint: lem-weil-pbc-coherent-kernel-ideal-product-completion-zero).

Proof:
1. The kernel of a map between coherent modules on a Noetherian scheme is coherent.
The ideal power is quasi-coherent and locally finitely generated. Its product with
this kernel is quasi-coherent and a submodule of a coherent module, hence coherent.
2. On an affine open U, exact affine sections identify the sheaf kernel with the
kernel of the section map and the ideal product with K(U)^t times that kernel.
Finite-module completion is tensoring with the flat completed ring. It therefore
identifies the completion of this kernel with the kernel of the completed map,
and the completion of its ideal product with the image of the completed ideal action.
3. The natural quotient and inverse-limit comparisons identify the completed map
with the inverse limit of the section maps of the quotient system. The stated
annihilator bound makes the image from step 2 zero. Thus the completion of the
ideal product is zero on every affine open.
4. Each positive quotient is a quotient of that finite-module completion, so it
is zero on each affine open. The affine opens form a basis, and sheaf separatedness
makes each quotient zero globally. This includes t = 0, the empty affine, and the
unit completion ideal; no faithfulness of affine completion is used.
-/
theorem coherentKernel_idealProduct_completion_zero
    {X : Scheme.{u}} [IsNoetherian X] (I K : X.IdealSheafData)
    (F G : CoherentModules X) (a : F ⟶ G) (t : ℕ)
    (h : ∀ U : X.affineOpens,
      K.ideal U ^ t ≤ Module.annihilator Γ(X, U.1) (LinearMap.ker
        (lim.map (Functor.whiskerRight ((completion X I).map a).hom
          (SheafOfModules.evaluation X.ringCatSheaf (op U.1)))).hom)) :
    RingedSpace.IsCoherent X.toRingedSpace
      (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι t).2
        (kernel a.hom)) ∧
    ∀ n : ℕ, IsZero (formalModuleQuotient I (n + 1)
      (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι t).2
        (kernel a.hom))) := by sorry

end AlgebraicGeometry
