/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.CanonicalPullbackTensorComparison
import Sheaf.Algebra.Homology.KFlat
import Sheaf.Algebra.Homology.KFlatPullback
import Sheaf.Algebra.Homology.KFlatResolution
import Sheaf.AlgebraicGeometry.DerivedPullback
import Sheaf.AlgebraicGeometry.DerivedPullbackTensorProduct
import Sheaf.AlgebraicGeometry.DerivedTensorStructure
import Sheaf.AlgebraicGeometry.ModulePullbackTensor
import Sheaf.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition

/-! # Tensor pullback counit in one K-flat coordinate

Source: Stacks Project, cohomology.tex, Tag 079U; perfect.tex, Tag 0DJA(1).
(blueprint: lem-pc-tensor-counit-one-kflat-coordinates).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
noncomputable section
namespace AlgebraicGeometry

/-- With one K-flat tensor factor, the total-complex counit and the derived
 tensor comparison agree up to the canonical representative isomorphisms.

Source: Stacks Project, cohomology.tex, Tag 079U; perfect.tex, Tag 0DJA(1).
Proof: the localization tensor map Q(P) tensor Q(G) -> Q(Tot(P tensor G))
is invertible because P is K-flat; let a be its associated isomorphism.
Termwise module tensor pullback commutes with sums and has its canonical
tensor isomorphism, so it gives a chain isomorphism from the pullback of the total
complex to Tot(g^*P tensor g^*G). Pullback preserves K-flatness of P; hence the
localization tensor map at g^*P and g^*G is invertible. The universal counit at P
is invertible as well. Compose these isomorphisms to obtain b.
For K-flat G the required equation is the characterizing coordinate equation of
hτ, after canceling the counit at P and the target localization tensor map.
For general G take a K-flat resolution
N -> G. Tensoring it with P preserves quasi-isomorphisms. Naturality
of the universal counits, the localization tensor maps, and the termwise tensor
pullback comparison gives the same equation after precomposing with the induced
isomorphism on derived tensor products. Cancel that isomorphism. This proves the
equation for arbitrary G, without imposing flatness over X or any base scheme.
(blueprint: lem-pc-tensor-counit-one-kflat-coordinates). -/
theorem tensorCounit_oneKFlat_coordinates
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X T : Scheme.{u}} (k : T ⟶ X)
    [@MonoidalPreadditive _ _ _ (SheafOfModules.monoidalCategory X.sheaf)]
    (P G : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hP : CochainComplex.IsKFlat (R := X.sheaf) P)
    (τ : ∀ A B : schemeDerivedCategory X,
      (derivedPullback k).obj (A ⊗ B) ⟶
        (derivedPullback k).obj A ⊗ (derivedPullback k).obj B)
    (hτ : IsCanonicalPullbackTensorComparison k τ) :
    ∃ a : DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj G ≅
        DerivedCategory.Q.obj (CochainComplex.mapBifunctor P G
          (@curriedTensor _ _ (SheafOfModules.monoidalCategory X.sheaf))),
      ∃ b : (DerivedCategory.Q
          (C := SheafOfModules.{u} (moduleRings T.toRingedSpace))).obj
          (((Scheme.Modules.tensorPullback k).mapHomologicalComplex (.up ℤ)).obj
            (CochainComplex.mapBifunctor P G
              (@curriedTensor _ _ (SheafOfModules.monoidalCategory X.sheaf)))) ≅
        (derivedPullback k).obj (DerivedCategory.Q.obj P) ⊗ (DerivedCategory.Q
          (C := SheafOfModules.{u} (moduleRings T.toRingedSpace))).obj
          (((Scheme.Modules.tensorPullback k).mapHomologicalComplex (.up ℤ)).obj G),
        (derivedPullback k).map a.hom ≫
          (SingleComplexBaseChange.counit k).app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj (CochainComplex.mapBifunctor P G
              (@curriedTensor _ _ (SheafOfModules.monoidalCategory X.sheaf)))) ≫ b.hom =
          τ (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj G) ≫
            (derivedPullback k).obj (DerivedCategory.Q.obj P) ◁
            (SingleComplexBaseChange.counit k).app
              ((HomotopyCategory.quotient _ (.up ℤ)).obj G) := by sorry

end AlgebraicGeometry
