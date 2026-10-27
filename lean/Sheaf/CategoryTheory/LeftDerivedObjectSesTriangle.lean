module

public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.CategoryTheory.Functor.KanExtension.Basic
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import WeilConjectures.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem

import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedExactOfLocalization
import WeilConjectures.CategoryTheory.RightKanExtensionCoherentShift

/-! # The total left derived triangle of a short exact sequence of objects

Source: Stacks Project, Derived Categories, Tag 015D, proof, dualized;
Tags 014X, 05RT, 05S9, 05SA, 05SE, 05SU and 0152
(blueprint: lem-trf-total-left-derived-object-ses-triangle).
-/

@[expose] public section

set_option autoImplicit false

universe uA vA wA uB vB wB

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.Functor

/-- An everywhere-defined total left derived functor has its canonical exact shift
structure and carries the canonical single-complex triangle of any short exact
sequence to the displayed distinguished triangle. Compatibility with the specified
counit characterizes the shift comparison, so the last map is the image of the
canonical connecting map followed by that comparison. No object is assumed acyclic.

`hLV` records that `(LV, ε)` is the total derived pair, by its right Kan universal
property. `hdefined` is the essentially constant denominator-diagram condition of
Definition 05S9(2), expanded from `IsTriangulatedLeftDerivedDefinedAt` so that no
additional choice of a proof of saturation occurs in the signature.

Source: Stacks Project, Derived Categories, Tag 015D, proof, dualized;
Tags 014X, 05RT, 05S9, 05SA, 05SE, 05SU and 0152.
(blueprint: lem-trf-total-left-derived-object-ses-triangle)

Proof:
1. By lem-trf-additive-homotopy-triangulated, applying V termwise on the homotopy
category is exact. By lem-pur-quasi-isos-saturated-triangulated, Qh for B is exact,
so their composite F is exact, and quasi-isomorphisms for A form the required
saturated triangulated multiplicative system.
2. The essentially constant denominator cones yield pointwise right Kan limits by
lem-pur-left-derived-defined-pointwise-kan-bridge. At an inverse denominator their
legs are LV(Qh(s)) inverse followed by ε. Every structured arrow is represented
by a right fraction, so naturality identifies the induced cones with these limit
cones. Essential surjectivity of Qh then gives the right Kan universal property
of the canonical pair; this is the interface recorded by hLV.
3. Apply lem-pur-left-derived-exact-chosen-localization to F, LV, ε and hdefined.
It gives an exact shift structure. The coherent comparisons furnished by
lem-pur-right-kan-extension-coherent-shift are compatible with ε and agree with
this structure: for each n, shifting by -n and the Kan property identify
Nat(G, LV[n]) with Nat(Qh G, F[n]). Two shift comparisons compatible with ε
have the same image under this bijection and therefore coincide.
4. By lem-sf-derived-ses-triangle, hS.singleTriangle is distinguished. Its objects
are the degree-zero single complexes of S.X₁, S.X₂, S.X₃, its first two maps
are the images of S.f and S.g, and its third map is the canonical hS.singleδ.
5. Exactness of LV sends this triangle to a distinguished triangle. By the
definition of mapTriangle, the first two arrows are their LV-images and the
third is LV.map hS.singleδ followed by the degree-one shift comparison at
the single complex of S.X₁. This is precisely the stated triangle; invertibility
of the counit on the three objects was never used. -/
theorem leftDerived_object_ses_triangle
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
    [EnoughProjectives A] (V : A ⥤ B) [V.Additive] [PreservesFiniteColimits V]
    (LV : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Qh ⋙ LV ⟶
      V.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (hLV : LV.IsRightKanExtension ε)
    (hdefined : ∀ X : HomotopyCategory A (ComplexShape.up ℤ),
      ∃ Y : DerivedCategory B,
        IsEssentiallyConstantProDiagram
          (MorphismProperty.Over.forget (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ⊤ X ⋙
            Over.forget X ⋙ V.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) Y)
    (S : ShortComplex A) (hS : S.ShortExact) :
    ∃ (_ : LV.CommShift ℤ), NatTrans.CommShift ε ℤ ∧ LV.IsTriangulated ∧
      Triangle.mk
          (LV.map ((DerivedCategory.singleFunctor A 0).map S.f))
          (LV.map ((DerivedCategory.singleFunctor A 0).map S.g))
          (LV.map hS.singleδ ≫
            (LV.commShiftIso (1 : ℤ)).hom.app ((DerivedCategory.singleFunctor A 0).obj S.X₁)) ∈
        distTriang (DerivedCategory B) := by
  sorry

end CategoryTheory.Functor
