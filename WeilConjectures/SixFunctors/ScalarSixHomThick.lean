/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ScalarSixTensorComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.Retract
import Mathlib.CategoryTheory.MorphismProperty.Retract
import WeilConjectures.CategoryTheory.DerivedCategory.NativeInternalHomExact
import Mathlib.CategoryTheory.Triangulated.Adjunction
import Mathlib.CategoryTheory.Triangulated.Opposite.Functor

/-! # The native scalar Hom comparison has a thick invertibility locus

Source: current blueprint det-prop-scalar-six-tensor-hom.proof.md, Reduction;
Stacks Project, Tags 08J9 and 08JC
(blueprint: lem-sfb-native-scalar-hom-thick).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open scoped CategoryTheory.Obj CategoryTheory.Functor
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated.Opposite
namespace AlgebraicGeometry.ProEtale.CondensedRing

private def nativeScalarHomNatTrans {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    (X : Scheme.{u})
    (M : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X)) :
    (derivedHom Λ.X X).flip.obj M ⋙ scalarSixChange a X ⟶
      (scalarSixChange a X).op ⋙
        (derivedHom Λ'.X X).flip.obj ((scalarSixChange a X).obj M) where
  app K := (Functor.LaxMonoidal.ihomComparison (scalarSixChange a X) K.unop).natTrans.app M
  naturality _ _ f :=
    Functor.LaxMonoidal.map_pre_app_comp_ihomComparison_app (scalarSixChange a X) f.unop M

/-- Both native contravariant scalar Hom rows are exact, even for nonflat maps.
Source: blueprint det-prop-scalar-six-tensor-hom, Reduction; Stacks 08JC
(blueprint: lem-sfb-native-scalar-hom-thick).

Proof: restriction of scalars is exact, so its derived functor is triangulated.
The derived extension/restriction adjunction equips scalar extension with an
exact shift structure. Native internal Hom into either fixed target is exact
contravariantly. Compose those structures, using the triangulated opposite for
the second row. This assertion does not assert compatibility of the comparison
with these shifts; that is the remaining calculation. -/
theorem scalarSixHom_rows_exact {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    (X : Scheme.{u})
    (M : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X)) :
    let B := (derivedHom Λ.X X).flip.obj M ⋙ scalarSixChange a X
    let E := (scalarSixChange a X).op ⋙
      (derivedHom Λ'.X X).flip.obj ((scalarSixChange a X).obj M)
    ∃ (sB : B.CommShift ℤ) (sE : E.CommShift ℤ),
      (fun [_bshift : B.CommShift ℤ] [_eshift : E.CommShift ℤ] ↦
        B.IsTriangulated ∧ E.IsTriangulated) (_bshift := sB)
          (_eshift := sE) := by
  let F := scalarSixChange a X
  let adj : F ⊣ (Mod.comap
      (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X)).mapDerivedCategory :=
    Mod.derivedExtendMapDerivedCategoryAdjunction
      (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X)
  let : F.CommShift ℤ := adj.leftAdjointCommShift ℤ
  have : adj.CommShift ℤ := adj.commShift_of_rightAdjoint ℤ
  have : F.IsTriangulated := adj.isTriangulated_leftAdjoint
  obtain ⟨sH, hH⟩ := DerivedCategory.nativeInternalHom_contravariant_exact
    (ModuleRingedComparison.internalModules Λ.X X) M
  let : ((derivedHom Λ.X X).flip.obj M).CommShift ℤ := sH
  have : ((derivedHom Λ.X X).flip.obj M).IsTriangulated := hH
  obtain ⟨sJ, hJ⟩ := DerivedCategory.nativeInternalHom_contravariant_exact
    (ModuleRingedComparison.internalModules Λ'.X X) (F.obj M)
  let : ((derivedHom Λ'.X X).flip.obj (F.obj M)).CommShift ℤ := sJ
  have : ((derivedHom Λ'.X X).flip.obj (F.obj M)).IsTriangulated := hJ
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

/-- The invertibility locus of the actual native evaluation mate is triangulated.
Source: blueprint det-prop-scalar-six-tensor-hom, Reduction; Stacks 08J9, 08JC
(blueprint: lem-sfb-native-scalar-hom-thick).

Proof: compute scalar extension with the K-flat universal counit and native Hom
with a K-injective representative of M. The canonical scalar tensor comparison
commutes with shifts in each input: on K-flat representatives its square is the
ordinary tensor shift square, and localization gives the square on all objects.
Taking mates gives the source-shift square for the evaluation transpose. The two
native opposite-Hom shifts both have the scalar (-1)^(n*(n+1)/2), so the signed
square commutes as well. Native signed Hom exactness and exactness of derived
scalar extension make this a transformation between exact contravariant functors.
Apply contravariantComparison_isoLocus to get closure under zero, integer shifts
and finite extensions. Naturality carries the same property along derived
isomorphisms. This calculation uses no flatness of the coefficient map, no
constructibility, and no field or scheme dimension bound. -/
theorem scalarSixHom_isTriangulated {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    (X : Scheme.{u})
    (M : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X)) :
    let P : ObjectProperty
        (DerivedCategory (ModuleRingedComparison.internalModules Λ.X X)) :=
      fun K ↦ IsIso
        ((Functor.LaxMonoidal.ihomComparison (scalarSixChange a X) K).natTrans.app M)
    P.IsTriangulated := by sorry

/-- Naturality alone proves retract closure; exactness supplies the triangulated clause.
Source: blueprint det-prop-scalar-six-tensor-hom, Reduction
(blueprint: lem-sfb-native-scalar-hom-thick). -/
theorem scalarSixHom_isoLocus {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    (X : Scheme.{u})
    (M : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X)) :
    let P : ObjectProperty
        (DerivedCategory (ModuleRingedComparison.internalModules Λ.X X)) :=
      fun K ↦ IsIso
        ((Functor.LaxMonoidal.ihomComparison (scalarSixChange a X) K).natTrans.app M)
    P.IsTriangulated ∧ P.IsStableUnderRetracts := by
  refine ⟨scalarSixHom_isTriangulated a X M, ⟨fun r h ↦ ?_⟩⟩
  exact MorphismProperty.of_retract (P := MorphismProperty.isomorphisms _)
    ((nativeScalarHomNatTrans a X M).retractArrowApp r.op) h

end AlgebraicGeometry.ProEtale.CondensedRing
