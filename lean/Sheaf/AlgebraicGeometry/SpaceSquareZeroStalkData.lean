/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q10
-/
module

public import Sheaf.AlgebraicGeometry.SpacePointedStalkData
public import Sheaf.AlgebraicGeometry.SpaceSquareZeroExtensionData
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Mathlib.RingTheory.Ideal.Maps

/-! # Normalized square-zero stalk-comparison data

Source: Stacks Project, Properties of Spaces, Tags 04K2, 04K5 and 05VQ;
Modules on Sites, Tags 04EQ and 05V5; Morphisms of Spaces, Tag 03MB;
More on Morphisms of Spaces, Tag 05ZS
(blueprint: def-sfb-space-square-zero-stalk-data).

These structures record normalized presentations of the objects used in the
geometric stalk calculation. Their defining equations prescribe the comparisons
on germs. This definition module makes no existence assertion.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.AlgebraicSpace

/-- squareZeroThickenedStructure: normalized data used by the geometric stalk calculation.
Source: Stacks, Tags 04K2, 04K5, 03MB and 05V5
(blueprint: def-sfb-space-square-zero-stalk-data). -/
def squareZeroThickenedStructure {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    {i : X ⟶ X'} (T : ThickeningSiteModel i) : X.EtaleSiteᵒᵖ ⥤ CommRingCat.{u} :=
  (T.equivalence.inverse ⋙ X'.etaleForget).op ⋙ Scheme.Γ

/-- SquareZeroIdeal: normalized data used by the geometric stalk calculation.
Source: Stacks, Tags 04K2, 04K5, 03MB and 05V5
(blueprint: def-sfb-space-square-zero-stalk-data). -/
structure SquareZeroIdeal {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    {i : X ⟶ X'} (T : ThickeningSiteModel i) where
  obj : X.Modules
  inclusion (U : X.EtaleSite) : obj.val.obj (op U) →+ T.rings.obj (op U)
  naturality {U V : X.EtaleSite} (f : U ⟶ V) (m : obj.val.obj (op V)) :
    T.rings.map f.op (inclusion V m) = inclusion U (obj.val.map f.op m)
  injective (U : X.EtaleSite) : Function.Injective (inclusion U)
  kernel (U : X.EtaleSite) (a : T.rings.obj (op U)) :
    T.quotient.app (op U) a = 0 ↔ ∃ m, inclusion U m = a
  scalar (U : X.EtaleSite) (a : T.rings.obj (op U)) (m : obj.val.obj (op U)) :
    inclusion U (T.quotient.app (op U) a • m) = a * inclusion U m
  square_zero (U : X.EtaleSite) (m n : obj.val.obj (op U)) :
    inclusion U m * inclusion U n = 0
  locally_surjective (U : X.EtaleSite) (a : X.structurePresheaf.obj (op U)) :
    ∃ R : Sieve U, R ∈ X.etaleTopology U ∧
      ∀ (V : X.EtaleSite) (v : V ⟶ U), R v →
        ∃ a' : T.rings.obj (op V), T.quotient.app (op V) a' =
          X.structurePresheaf.map v.op a

/-- squareZeroTensor: normalized data used by the geometric stalk calculation.
Source: Stacks, Tags 04K2, 04K5, 03MB and 05V5
(blueprint: def-sfb-space-square-zero-stalk-data). -/
abbrev squareZeroTensor {A B : CommRingCat.{u}} (β : A →+* B) (I : ModuleCat.{u} A) :=
  @TensorProduct A _ I B _ _ inferInstance β.toAlgebra.toModule

/-- squareZeroTmul: normalized data used by the geometric stalk calculation.
Source: Stacks, Tags 04K2, 04K5, 03MB and 05V5
(blueprint: def-sfb-space-square-zero-stalk-data). -/
def squareZeroTmul {A B : CommRingCat.{u}} (β : A →+* B) (I : ModuleCat.{u} A)
    (i : I) (b : B) : squareZeroTensor β I :=
  @TensorProduct.tmul A _ I B _ _ inferInstance β.toAlgebra.toModule i b

/-- Scalar multiplication by the right tensor factor, using the tensor symmetry.
Source: Stacks, Tags 04K2, 04K5, 03MB and 05V5
(blueprint: def-sfb-space-square-zero-stalk-data). -/
def squareZeroTensorScale {A B : CommRingCat.{u}} (β : A →+* B)
    (I : ModuleCat.{u} A) (b : B) (t : squareZeroTensor β I) : squareZeroTensor β I := by
  letI : Algebra A B := β.toAlgebra
  exact TensorProduct.comm A B I (b • (TensorProduct.comm A I B t))

/-- A stalk ring map prescribed on every compatible pair of pointed charts.
Source: Stacks, Tags 04K2, 04K5, 03MB and 05V5
(blueprint: def-sfb-space-square-zero-stalk-data). -/
def SquareZeroRingMap {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {p : SquareZeroPoint X} {q : SquareZeroPoint Y}
    (hpq : p.left = q.left)
    {R : X.EtaleSiteᵒᵖ ⥤ CommRingCat.{u}} {D : Y.EtaleSiteᵒᵖ ⥤ CommRingCat.{u}}
    (s : SquareZeroStalk p R) (t : SquareZeroStalk q D)
    (c : ∀ (U : X.EtaleSite) (V : Y.EtaleSite) (a : U.obj.left ⟶ V.obj.left),
      U.obj.hom ≫ f.hom.hom = yoneda.map a ≫ V.obj.hom →
        D.obj (op V) → R.obj (op U)) (φ : t.ring →+* s.ring) : Prop :=
  ∀ (n : SquareZeroNeighborhood p) (m : SquareZeroNeighborhood q)
    (a : n.right.obj.left ⟶ m.right.obj.left)
    (ha : n.right.obj.hom ≫ f.hom.hom = yoneda.map a ≫ m.right.obj.hom),
    n.hom.left ≫ a = eqToHom hpq ≫ m.hom.left →
    ∀ b : D.obj (op m.right),
      φ (t.ringGerms.app (op m) b) = s.ringGerms.app (op n) (c _ _ a ha b)

/-- The canonical map from `X` to the sheaf fibre product `Y ×_{Y'} X'`
(def-sfb-space-sheaf-fibre-product), the actual `pullback.lift` of the square.
Source: Stacks, Tags 04K2, 04K5, 03MB and 05V5
(blueprint: def-sfb-space-square-zero-stalk-data). -/
def squareZeroPullbackMap {S : Scheme.{u}} {X Y X' Y' : AlgebraicSpace S}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (i : X ⟶ X') (j : Y ⟶ Y')
    (h : f ≫ j = i ≫ f') : X ⟶ enlargedFibreProduct j f' :=
  ObjectProperty.homMk (pullback.lift f.hom i.hom (congrArg (fun a ↦ a.hom) h))

/-- The image ideal is the kernel of the actual pullback closed subspace at the point.
Source: Stacks, Tags 04K2, 04K5, 03MB and 05V5
(blueprint: def-sfb-space-square-zero-stalk-data). -/
structure SquareZeroFibreProductIdeal {S : Scheme.{u}} {X Y X' Y' : AlgebraicSpace S}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (i : X ⟶ X') (j : Y ⟶ Y')
    (h : f ≫ j = i ≫ f') (T : ThickeningSiteModel i) (p : SquareZeroPoint X)
    (sx' : SquareZeroStalk p (squareZeroThickenedStructure T)) where
  target : SquareZeroStalk
    ((CostructuredArrow.map (squareZeroPullbackMap f f' i j h).hom.hom).obj p)
    (squareZeroStructure (enlargedFibreProduct j f'))
  restriction : sx'.ring →+* target.ring
  normalization (n : SquareZeroNeighborhood p)
    (m : SquareZeroNeighborhood
      ((CostructuredArrow.map (squareZeroPullbackMap f f' i j h).hom.hom).obj p))
    (a : m.right.obj.left ⟶ (T.equivalence.inverse.obj n.right).obj.left)
    (ha : m.right.obj.hom ≫ (pullback.snd j.hom f'.hom).hom =
      yoneda.map a ≫ (T.equivalence.inverse.obj n.right).obj.hom)
    (hp : m.hom.left ≫ a = n.hom.left ≫ T.reduction.app n.right)
    (b : (squareZeroThickenedStructure T).obj (op n.right)) :
    restriction (sx'.ringGerms.app (op n) b) =
      target.ringGerms.app (op m) (Scheme.Γ.map a.left.op b)

end AlgebraicGeometry.AlgebraicSpace
