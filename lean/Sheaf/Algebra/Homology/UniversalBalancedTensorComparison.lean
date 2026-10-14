/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N2
-/
module

public import Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModel
public import Sheaf.Algebra.Homology.RingTensorCohomology
import Sheaf.Algebra.Homology.KFlatScalarExtensionCounit

/-! # Universal scalar extension computed by a fixed second-factor resolution

Source: Stacks Project, Tags 064L and 06Y6.
(blueprint: new-lem-pc-universal-balanced-tensor-comparison).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory
open scoped TensorProduct ChangeOfRings

namespace RingTensorCohomology

/-- Natural additive comparisons for universal scalar extension and a fixed K-flat
second factor. Source: Stacks Project, Tags 064L and 06Y6.
(blueprint: new-lem-pc-universal-balanced-tensor-comparison).

Proof: use the functorial R-K-flat resolution P(X) -> X. Tensoring its augmentation
with F is a quasi-isomorphism because F is K-flat. Tensoring F -> B[0] with P(X)
is a quasi-isomorphism because P(X) is K-flat. Identify P(X) tensor B[0] with
restriction of the ordinary extension of P(X) to B, on pure tensors by
x tensor b -> b tensor x. The universal scalar-extension counit at P(X) is
invertible by scalarExtensionCounit_isIso_of_kFlat. Its composite with the inverse
of the derived image of P(X) -> X therefore compares the given universal functor
with this span. Take homology and forget to additive groups to obtain e.
Naturality of the resolution augmentation, tensoring, the counit and the homology
comparison proves the first equation. The defining counit equation for the unique
isomorphism between two universal left derived functors proves the second equation
at P(X); naturality for P(X) -> X then proves it at X. The two quasi-isomorphism
inverses cancel in both equations. There are no boundedness or flatness assumptions
on B or X; zero complexes and zero rings are included. -/
theorem exists_universalBalancedTensorComparison
    (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} B)]
    (i : ℤ) (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (f : F ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj
      (ModuleCat.of R B)) (hf : QuasiIso f)
    (hF : (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat F) :
    let V := HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ) ⋙ DerivedCategory.Qh
    let H := DerivedCategory.homologyFunctor (ModuleCat.{u} B) i
    let T := (MonoidalCategory.curriedTensor (ModuleCat.{u} R)).map₂CochainComplex
    let W := HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ)
    ∃ e : ∀ (L : DerivedCategory (ModuleCat.{u} R) ⥤
        DerivedCategory (ModuleCat.{u} B))
      (ε : DerivedCategory.Qh ⋙ L ⟶
        (ModuleCat.extendScalars (algebraMap R B)).mapHomotopyCategory (.up ℤ) ⋙
          DerivedCategory.Qh),
      L.IsLeftDerivedFunctor ε W → ∀ X : CochainComplex (ModuleCat.{u} R) ℤ,
        H.obj (L.obj (V.obj X)) ≃+ (((T.obj X).obj F).homology i),
      (∀ L ε hL X Y (g : X ⟶ Y) x,
        e L ε hL Y (H.map (L.map (V.map g)) x) =
          HomologicalComplex.homologyMap ((T.map g).app F) i (e L ε hL X x)) ∧
      (∀ (L : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} B))
        (ε : DerivedCategory.Qh ⋙ L ⟶
          (ModuleCat.extendScalars (algebraMap R B)).mapHomotopyCategory (.up ℤ) ⋙
            DerivedCategory.Qh) (hL : L.IsLeftDerivedFunctor ε W)
        (K : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} B))
        (δ : DerivedCategory.Qh ⋙ K ⟶
          (ModuleCat.extendScalars (algebraMap R B)).mapHomotopyCategory (.up ℤ) ⋙
            DerivedCategory.Qh) (hK : K.IsLeftDerivedFunctor δ W) X x,
        letI := hL
        letI := hK
        let ζ := Functor.leftDerivedNatIso L K ε δ W (Iso.refl _)
        e K δ hK X (H.map (ζ.hom.app (V.obj X)) x) = e L ε hL X x) := by sorry

end RingTensorCohomology
