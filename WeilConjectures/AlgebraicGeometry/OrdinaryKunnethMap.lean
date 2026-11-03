/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary
public import WeilConjectures.AlgebraicGeometry.Etale.Constant.EtaleConstantProjectionMap

/-!
# The absolute ordinary Künneth map

The constant-complex adjunct definitions of blueprint
`lem-pur-ordinary-kunneth-finite-ring`, separated from its coefficient theorem.
(blueprint: def-pur-ordinary-kunneth-absolute-map).
-/

@[expose] public section

universe u uA uC vC uB vB

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

section AbsoluteMap

variable (A : Type uA) [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- The canonical comparison from a constant derived complex on the source to the pullback
of its constant derived complex on the target. It is the inverse of the ordinary
constant-sheaf comparison, derived and then split by the exact-functor composition iso.
Source: blueprint order 1740, terminal-topos specialization
(blueprint: def-pur-ordinary-kunneth-absolute-map). -/
noncomputable def derivedConstantPullbackIso {X Z : Scheme.{u}} (p : Z ⟶ X) :
    (constantSheaf Z.smallEtaleTopology A).leftDerivedFunctor ≅
      (constantSheaf X.smallEtaleTopology A).leftDerivedFunctor ⋙
        L((p)^*[A]) :=
  (Functor.leftDerivedFunctorNatIso (constantSheaf Z.smallEtaleTopology A)
    (Scheme.upperStarConstantSheafIso A p).symm) ≪≫
      Functor.leftDerivedFunctorCompIso (constantSheaf X.smallEtaleTopology A) (upperStar A p)

/-- Pull the global-sections counit back to `Z`, identifying the pulled-back constant
complex with the constant complex on `Z` by `derivedConstantPullbackIso`.
Source: blueprint order 1740, terminal-topos specialization
(blueprint: def-pur-ordinary-kunneth-absolute-map). -/
noncomputable def ordinaryKunnethPulledCounit {X Z : Scheme.{u}} (p : Z ⟶ X)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (constantSheaf Z.smallEtaleTopology A).leftDerivedFunctor.obj
      ((rightDerivedGlobalSections A X).obj K) ⟶
        (L((p)^*[A])).obj K :=
  (derivedConstantPullbackIso A p).hom.app _ ≫
    (L((p)^*[A])).map
      ((derivedConstantGlobalSectionsAdjunction A X).counit.app K)

/-- The tensor-of-counits adjunct construction, with its categories left abstract.
Source: blueprint order 1740, the displayed adjunct formula
(blueprint: def-pur-ordinary-kunneth-absolute-map). This helper keeps the same tensor structures as
explicit parameters when specializing to the terminal geometric morphism. -/
noncomputable def ordinaryKunnethTensorMate
    {C : Type uC} [Category.{vC} C] {B : Type uB} [Category.{vB} B]
    (T : C ⥤ C ⥤ C) (T' : B ⥤ B ⥤ B)
    (F : C ⥤ B) (G : B ⥤ C) (adj : F ⊣ G)
    (δ : (Functor.postcompose₂.obj F).obj T ⟶
      (((Functor.whiskeringLeft₂ B).obj F).obj F).obj T')
    {P Q : C} {V W : B} (a : F.obj P ⟶ V) (b : F.obj Q ⟶ W) :
    (T.obj P).obj Q ⟶ G.obj ((T'.obj V).obj W) :=
  adj.homEquiv _ _ ((δ.app P).app Q ≫ (T'.map a).app _ ≫ (T'.obj _).map b)

/-- The absolute exterior-product arrow in the derived category of modules, adjoint to
the derived constant-sheaf tensor comparison followed by the tensor of the two
pulled-back global-sections counits. Its target is the derived sections of the ordinary
uncompleted derived external tensor product.
Source: blueprint order 1740 and Stacks Tag 0F1E (blueprint: def-pur-ordinary-kunneth-absolute-map).
This is the terminal-topos form of the upstream `kunnethMap`, using the constant-complex
versus sections adjunction. No equivalence for the etale point is chosen. -/
noncomputable def ordinaryGlobalKunnethMap {X Y Z : Scheme.{u}}
    (p : Z ⟶ X) (q : Z ⟶ Y)
    [(constantSheaf Z.smallEtaleTopology A).Monoidal]
    [(constantSheaf Z.smallEtaleTopology A).PreservesFlat]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (M : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    (rightDerivedGlobalSections A X).obj K ⊗
        (rightDerivedGlobalSections A Y).obj M ⟶
      (rightDerivedGlobalSections A Z).obj
        (((curriedTensor (DerivedCategory (Sheaf Z.smallEtaleTopology A))).obj
          ((L((p)^*[A])).obj K)).obj
            ((L((q)^*[A])).obj M)) :=
  ordinaryKunnethTensorMate (curriedTensor (DerivedCategory A))
    (curriedTensor (DerivedCategory (Sheaf Z.smallEtaleTopology A)))
    (constantSheaf Z.smallEtaleTopology A).leftDerivedFunctor
    (rightDerivedGlobalSections A Z) (derivedConstantGlobalSectionsAdjunction A Z)
    (constantSheaf Z.smallEtaleTopology A).leftDerivedTensorComparison
    (ordinaryKunnethPulledCounit A p K) (ordinaryKunnethPulledCounit A q M)


end AbsoluteMap

end AlgebraicGeometry.Etale
