/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q81
-/
module

public import Sheaf.Algebra.Homology.RingHomExtensionDefs
public import Sheaf.Algebra.Homology.RingedInternalHomSignedCalculus
public import Sheaf.Paper.CoefficientHomRepresentativeEvaluation
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Sheaf.Algebra.Homology.TotalTensorHomotopyConeSigns
public import Sheaf.Algebra.Homology.SignedDoubleHomCone
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-! # Exact tensor and two-target double Hom with specified signs

Source: Stacks Project, More on Algebra, Tag 064J; Cohomology on Sites, Tag 08JC,
with the explicit component calculation in the DAG proof
(blueprint: lem-trf-tensor-double-hom-exact-comparisons).

The functors are written directly using the recorded Hom and tensor, so this
module has no import of the downstream evaluation-map theorem. The representative
maps are fixed by the ordinary Hom augmentation and the localization tensor map.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open DerivedCategory

namespace DerivedCategory

/-- Exactness and the fully normalized shift and cone comparisons for fixed tensor
and two successive contravariant Homs, with independently chosen targets.
Source: Stacks 064J and 08JC, explicit signed expansion
(blueprint: lem-trf-tensor-double-hom-exact-comparisons).

Proof:
1. On the one-object identity-covering site use K-injective representatives J,I
(prop-pur-kinjective-resolutions-exist). Hom(J,I) represents RHom(L,M), and
Hom(Hom(U,J),I) represents the double Hom: only its outer target must be
K-injective (def-pur-derived-internal-hom). Resolve Hom(J,I) by a flat-term
K-flat B (lem-pc-kflat-resolution). Fixed tensor by B is exact
(lem-weil-pbc-kflat-fixed-tensor-triangulated), and tensoring B -> Hom(J,I)
with any K-flat P is a quasi-isomorphism
(lem-weil-pbc-total-tensor-homotopy-cone-signs).
2. The coherent second-factor tensor shifts have sign (-1)^(m*a)
(lem-weil-pbc-total-tensor-integer-shifts). The tensor cone map has signs 1
and (-1)^a on the unshifted and shifted summands. Its inclusion and projection
identities also respect the negative connecting projection. The same cone
criterion (lem-pur-quasi-iso-cone-acyclic) proves that cones of K-flat complexes
are K-flat; shifts preserve K-flatness as well.
3. In Hom degree q, signed reindexing s multiplies by (-1)^(m*q). Both sides
of the chain-map equation are (-1)^(m*q+m)d_V f - (-1)^(m*q+q)f d_U.
The inverse has the same sign and precomposition proves naturality. Compose
Hom(s,I) inverse with s at (Hom(P,J),-m), and multiply by (-1)^m. On an outer
map of degree n tested in inner degree c the resulting sign is (-1)^(m*(n+c)).
This proves zero and additive shift coherence, including negative shifts.
4. Apply lem-sf-double-hom-cone-comparison to target J plus I. Finite biproduct
Hom decomposes into four blocks; all maps preserve those blocks since their
signs depend only on degrees. Restrict to the (J,I) block. The cone comparison
is (alpha,beta) -> (alpha,(-1)^(p+r)*beta); it respects the inclusion.
5. The negative connecting projection restricts to minus beta; the signed
comparison takes it to minus gamma. Thus both contravariant triangle reversals
give exactly the comparison with its leading (-1)^m, not an unsigned reversal.
6. Hom into either K-injective target inverts quasi-isomorphisms
(lem-pur-rhom-well-defined). Descend the comparisons and use the cone-triangle
presentation of def-weil-abstract-derived-category. The fixed augmentations
identify the resulting comparisons with the canonical derived representatives.
No boundedness or equality between the two targets is used. -/
theorem tensor_double_hom_exact_comparisons
    (R : Type u) [CommRing R] [HasDerivedCategory.{u} (RingSiteModules R)] :
    (∀ L M : DerivedCategory (RingSiteModules R),
      (tensorLeft ((SignedRingedHom.hom.{u} ⊥ (CochainComplex.onePointRingSheaf R) L).obj
        M)).IsTriangulated ∧
      ∃ _s : (((Functor.curry.obj (SignedRingedHom.homFunctor.{u} ⊥
        (CochainComplex.onePointRingSheaf R))).flip.obj L).rightOp ⋙ (Functor.curry.obj
        (SignedRingedHom.homFunctor.{u} ⊥ (CochainComplex.onePointRingSheaf R))).flip.obj
        M).CommShift ℤ,
        (((Functor.curry.obj (SignedRingedHom.homFunctor.{u} ⊥ (CochainComplex.onePointRingSheaf
          R))).flip.obj L).rightOp ⋙ (Functor.curry.obj (SignedRingedHom.homFunctor.{u} ⊥
          (CochainComplex.onePointRingSheaf R))).flip.obj M).IsTriangulated ∧
        ∀ (K : DerivedCategory (RingSiteModules R)) (m : ℤ),
          ((((Functor.curry.obj (SignedRingedHom.homFunctor.{u} ⊥
            (CochainComplex.onePointRingSheaf R))).flip.obj L).rightOp ⋙ (Functor.curry.obj
            (SignedRingedHom.homFunctor.{u} ⊥ (CochainComplex.onePointRingSheaf R))).flip.obj
            M).commShiftIso m).hom.app K =
            (m.negOnePow • (
          (((Functor.curry.obj (SignedRingedHom.homFunctor.{u} ⊥ (CochainComplex.onePointRingSheaf
            R))).flip.obj M).mapIso
            (((SignedRingedHom.sourceShift.{u} ⊥
              (CochainComplex.onePointRingSheaf R) K m).app L).op)).inv ≫
          ((SignedRingedHom.sourceShift.{u} ⊥ (CochainComplex.onePointRingSheaf R)
            ((SignedRingedHom.homFunctor.{u} ⊥ (CochainComplex.onePointRingSheaf R)).obj (op K,
              L)) (-m)).app M).hom ≫
          eqToHom (congrArg (fun n : ℤ ↦ ((SignedRingedHom.homFunctor.{u} ⊥
            (CochainComplex.onePointRingSheaf R)).obj
            (op ((SignedRingedHom.homFunctor.{u} ⊥ (CochainComplex.onePointRingSheaf R)).obj (op
              K, L)), M))⟦n⟧) (neg_neg m))))) ∧
    ∀ (J I : CochainComplex (RingSiteModules R) ℤ)
      [J.IsKInjective] [I.IsKInjective],
    ∃ _s : (((Functor.curry.obj (SignedRingedHom.homFunctor.{u} ⊥
      (CochainComplex.onePointRingSheaf R))).flip.obj (Q.obj J)).rightOp ⋙ (Functor.curry.obj
      (SignedRingedHom.homFunctor.{u} ⊥ (CochainComplex.onePointRingSheaf R))).flip.obj (Q.obj
      I)).CommShift ℤ,
    ∃ s : ∀ (U V : CochainComplex (RingSiteModules R) ℤ) (m : ℤ),
      homComplex.{u, u, u, u} (R := CochainComplex.onePointRingSheaf R) (U⟦m⟧) V ≅
        (homComplex.{u, u, u, u} (R := CochainComplex.onePointRingSheaf R) U V)⟦-m⟧,
    ∃ repJ : ∀ U : CochainComplex (RingSiteModules R) ℤ,
      Q.obj (homComplex.{u, u, u, u} (R := CochainComplex.onePointRingSheaf R) U J) ≅
        (SignedRingedHom.homFunctor.{u} ⊥ (CochainComplex.onePointRingSheaf R)).obj
          (op (Q.obj U), Q.obj J),
    ∃ repI : ∀ U : CochainComplex (RingSiteModules R) ℤ,
      Q.obj (homComplex.{u, u, u, u} (R := CochainComplex.onePointRingSheaf R) U I) ≅
        (SignedRingedHom.homFunctor.{u} ⊥ (CochainComplex.onePointRingSheaf R)).obj
          (op (Q.obj U), Q.obj I),
    ∃ tensorRep : ∀ (P : CochainComplex (RingSiteModules R) ℤ),
      CochainComplex.IsKFlatIndependentCoefficients P →
      (Q.obj (((SheafOfModules.TotalTensorSigns.total
        (CochainComplex.onePointRingSheaf R)).obj (homComplex.{u, u, u, u} (R :=
          CochainComplex.onePointRingSheaf R) J I)).obj P) ≅
          (tensorLeft ((SignedRingedHom.hom.{u} ⊥ (CochainComplex.onePointRingSheaf R) (Q.obj
            J)).obj (Q.obj I))).obj (Q.obj P)),
    ∃ homRep : ∀ P : CochainComplex (RingSiteModules R) ℤ,
      Q.obj (homComplex.{u, u, u, u} (R := CochainComplex.onePointRingSheaf R) (homComplex.{u, u,
        u, u} (R :=
        CochainComplex.onePointRingSheaf R) P J) I) ≅
        (((Functor.curry.obj (SignedRingedHom.homFunctor.{u} ⊥ (CochainComplex.onePointRingSheaf
          R))).flip.obj (Q.obj J)).rightOp ⋙ (Functor.curry.obj (SignedRingedHom.homFunctor.{u} ⊥
          (CochainComplex.onePointRingSheaf R))).flip.obj (Q.obj I)).obj (Q.obj P),
    ∃ chi : ∀ (P : CochainComplex (RingSiteModules R) ℤ) (m : ℤ),
      homComplex.{u, u, u, u} (R := CochainComplex.onePointRingSheaf R) (homComplex.{u, u, u, u}
        (R :=
        CochainComplex.onePointRingSheaf R) (P⟦m⟧) J) I ≅
        (homComplex.{u, u, u, u} (R := CochainComplex.onePointRingSheaf R) (homComplex.{u, u, u,
          u} (R :=
          CochainComplex.onePointRingSheaf R) P J) I)⟦m⟧,
    (((Functor.curry.obj (SignedRingedHom.homFunctor.{u} ⊥ (CochainComplex.onePointRingSheaf
      R))).flip.obj (Q.obj J)).rightOp ⋙ (Functor.curry.obj (SignedRingedHom.homFunctor.{u} ⊥
      (CochainComplex.onePointRingSheaf R))).flip.obj (Q.obj I)).IsTriangulated ∧
    (∀ (K : DerivedCategory (RingSiteModules R)) (m : ℤ),
      ((((Functor.curry.obj (SignedRingedHom.homFunctor.{u} ⊥ (CochainComplex.onePointRingSheaf
        R))).flip.obj (Q.obj J)).rightOp ⋙ (Functor.curry.obj (SignedRingedHom.homFunctor.{u} ⊥
        (CochainComplex.onePointRingSheaf R))).flip.obj (Q.obj I)).commShiftIso m).hom.app K =
        (m.negOnePow • (
          (((Functor.curry.obj (SignedRingedHom.homFunctor.{u} ⊥ (CochainComplex.onePointRingSheaf
            R))).flip.obj (Q.obj I)).mapIso
            (((SignedRingedHom.sourceShift.{u} ⊥
              (CochainComplex.onePointRingSheaf R) K m).app (Q.obj J)).op)).inv ≫
          ((SignedRingedHom.sourceShift.{u} ⊥ (CochainComplex.onePointRingSheaf R)
            ((SignedRingedHom.homFunctor.{u} ⊥ (CochainComplex.onePointRingSheaf R)).obj (op K,
              (Q.obj J))) (-m)).app (Q.obj I)).hom ≫
          eqToHom (congrArg (fun n : ℤ ↦ ((SignedRingedHom.homFunctor.{u} ⊥
            (CochainComplex.onePointRingSheaf R)).obj
            (op ((SignedRingedHom.homFunctor.{u} ⊥ (CochainComplex.onePointRingSheaf R)).obj (op
              K, (Q.obj J))), (Q.obj I)))⟦n⟧) (neg_neg m))))) ∧
    (∀ (U V : CochainComplex (RingSiteModules R) ℤ) (m q a : ℤ),
      (s U V m).hom.f q ≫
          ((homComplex.{u, u, u, u} (R := CochainComplex.onePointRingSheaf R) U
            V).shiftFunctorObjXIso (-m) q
            (q - m) (by omega)).hom ≫
          homComplexπ.{u, u, u, u} (R := CochainComplex.onePointRingSheaf R) U V (q - m) (a + m)
            (a + q) (by
            omega) =
        (m * q).negOnePow • (homComplexπ.{u, u, u, u} (R := CochainComplex.onePointRingSheaf R)
          (U⟦m⟧) V q a (a
          + q) rfl ≫
          SheafOfModules.homObjMap.{u, u, u, u} (U.shiftFunctorObjXIso m a (a + m) rfl).inv (𝟙
            _))) ∧
    (∀ U : CochainComplex (RingSiteModules R) ℤ,
      (repJ U).hom = Q.map (((homComplexFunctor.{u, u, u, u}
        (R := CochainComplex.onePointRingSheaf R)).obj (op U)).map
          ((CochainComplex.toKInjectiveResolution.{u} (RingSiteModules R)).app J)) ≫
        (WeilConjectures.coefficientHomResolutionIso.{u, u, u, u} ⊥
          (CochainComplex.onePointRingSheaf R) U J).inv ∧
      (repI U).hom = Q.map (((homComplexFunctor.{u, u, u, u}
        (R := CochainComplex.onePointRingSheaf R)).obj (op U)).map
          ((CochainComplex.toKInjectiveResolution.{u} (RingSiteModules R)).app I)) ≫
        (WeilConjectures.coefficientHomResolutionIso.{u, u, u, u} ⊥
          (CochainComplex.onePointRingSheaf R) U I).inv) ∧
    (∀ (P : CochainComplex (RingSiteModules R) ℤ)
        (hP : CochainComplex.IsKFlatIndependentCoefficients P),
      Functor.LaxMonoidal.μ Q (homComplex.{u, u, u, u} (R := CochainComplex.onePointRingSheaf R) J
        I) P ≫
        (tensorRep P hP).hom =
        (repI J).hom ⊗ₘ 𝟙 (Q.obj P)) ∧
    (∀ P : CochainComplex (RingSiteModules R) ℤ,
      (homRep P).hom = (repI (homComplex.{u, u, u, u} (R := CochainComplex.onePointRingSheaf R) P
        J)).hom ≫
        (SignedRingedHom.homFunctor.{u} ⊥ (CochainComplex.onePointRingSheaf R)).map
          ((repJ P).inv.op, 𝟙 (Q.obj I))) ∧
    (∀ (P : CochainComplex (RingSiteModules R) ℤ) (m : ℤ),
      (chi P m).hom = m.negOnePow •
        ((CategoryTheory.SignedDoubleHomCone.dual
          (R := CochainComplex.onePointRingSheaf R) I).map (s P J m).inv.op ≫
          (s (homComplex.{u, u, u, u} (R := CochainComplex.onePointRingSheaf R) P J) I (-m)).hom ≫
          eqToHom (congrArg (fun n : ℤ ↦ (homComplex.{u, u, u, u} (R :=
            CochainComplex.onePointRingSheaf R)
            (homComplex.{u, u, u, u} (R := CochainComplex.onePointRingSheaf R) P J) I)⟦n⟧)
            (neg_neg m)))) ∧
    (∀ (P : CochainComplex (RingSiteModules R) ℤ)
        (hP : CochainComplex.IsKFlatIndependentCoefficients P) (m : ℤ)
        (hmP : CochainComplex.IsKFlatIndependentCoefficients (P⟦m⟧)),
      Q.map (SheafOfModules.TotalTensorSigns.shiftLeft
          (CochainComplex.onePointRingSheaf R) (homComplex.{u, u, u, u} (R :=
            CochainComplex.onePointRingSheaf
            R) J I) P m).hom ≫
          (Q.commShiftIso m).hom.app
            (((SheafOfModules.TotalTensorSigns.total
              (CochainComplex.onePointRingSheaf R)).obj (homComplex.{u, u, u, u} (R :=
                CochainComplex.onePointRingSheaf R) J I)).obj P) ≫
          (tensorRep P hP).hom⟦m⟧' =
        (tensorRep (P⟦m⟧) hmP).hom ≫
          (tensorLeft ((SignedRingedHom.hom.{u} ⊥ (CochainComplex.onePointRingSheaf R) (Q.obj
            J)).obj (Q.obj I))).map
            ((Q.commShiftIso m).hom.app P) ≫
          ((tensorLeft ((SignedRingedHom.hom.{u} ⊥ (CochainComplex.onePointRingSheaf R) (Q.obj
            J)).obj (Q.obj I))).commShiftIso m).hom.app
            (Q.obj P)) ∧
    (∀ (P : CochainComplex (RingSiteModules R) ℤ) (m : ℤ),
      Q.map (chi P m).hom ≫
          (Q.commShiftIso m).hom.app (homComplex.{u, u, u, u} (R :=
            CochainComplex.onePointRingSheaf R)
            (homComplex.{u, u, u, u} (R := CochainComplex.onePointRingSheaf R) P J) I) ≫
          (homRep P).hom⟦m⟧' =
        (homRep (P⟦m⟧)).hom ≫
          (((Functor.curry.obj (SignedRingedHom.homFunctor.{u} ⊥ (CochainComplex.onePointRingSheaf
            R))).flip.obj (Q.obj J)).rightOp ⋙ (Functor.curry.obj (SignedRingedHom.homFunctor.{u}
            ⊥ (CochainComplex.onePointRingSheaf R))).flip.obj (Q.obj I)).map
            ((Q.commShiftIso m).hom.app P) ≫
          ((((Functor.curry.obj (SignedRingedHom.homFunctor.{u} ⊥
            (CochainComplex.onePointRingSheaf R))).flip.obj (Q.obj J)).rightOp ⋙
            (Functor.curry.obj (SignedRingedHom.homFunctor.{u} ⊥ (CochainComplex.onePointRingSheaf
            R))).flip.obj (Q.obj I)).commShiftIso m).hom.app
            (Q.obj P)) ∧
    ∀ (P₁ P₂ : CochainComplex (RingSiteModules R) ℤ)
      (_hP₁ : CochainComplex.IsKFlatIndependentCoefficients P₁)
      (_hP₂ : CochainComplex.IsKFlatIndependentCoefficients P₂) (f : P₁ ⟶ P₂),
      (((SheafOfModules.TotalTensorSigns.total
          (CochainComplex.onePointRingSheaf R)).obj (homComplex.{u, u, u, u} (R :=
            CochainComplex.onePointRingSheaf R) J I)).map
          (CochainComplex.mappingCone.inr f) ≫
          (SheafOfModules.TotalTensorSigns.coneLeft
            (CochainComplex.onePointRingSheaf R) (homComplex.{u, u, u, u} (R :=
              CochainComplex.onePointRingSheaf R) J I) f).hom =
        CochainComplex.mappingCone.inr
          (((SheafOfModules.TotalTensorSigns.total
            (CochainComplex.onePointRingSheaf R)).obj (homComplex.{u, u, u, u} (R :=
              CochainComplex.onePointRingSheaf R) J I)).map f)) ∧
      (∀ (a b n : ℤ) (hab : a + b = n),
        ((homComplex.{u, u, u, u} (R := CochainComplex.onePointRingSheaf R) J I).X a ◁
          (CochainComplex.mappingCone.inl f).v
            (b + 1) b (by omega) ≫
          SheafOfModules.TotalTensorSigns.ι (CochainComplex.onePointRingSheaf R)
            (homComplex.{u, u, u, u} (R := CochainComplex.onePointRingSheaf R) J I)
              (CochainComplex.mappingCone
              f) a b n hab ≫
          (SheafOfModules.TotalTensorSigns.coneLeft
            (CochainComplex.onePointRingSheaf R) (homComplex.{u, u, u, u} (R :=
              CochainComplex.onePointRingSheaf R) J I) f).hom.f n =
        a.negOnePow •
          (SheafOfModules.TotalTensorSigns.ι (CochainComplex.onePointRingSheaf R)
            (homComplex.{u, u, u, u} (R := CochainComplex.onePointRingSheaf R) J I) P₁ a (b + 1)
              (n + 1) (by
              omega) ≫
            (CochainComplex.mappingCone.inl
              (((SheafOfModules.TotalTensorSigns.total
                (CochainComplex.onePointRingSheaf R)).obj (homComplex.{u, u, u, u} (R :=
                  CochainComplex.onePointRingSheaf R) J I)).map f)).v
                  (n + 1) n (by omega)))) ∧
      ((SheafOfModules.TotalTensorSigns.coneLeft
          (CochainComplex.onePointRingSheaf R) (homComplex.{u, u, u, u} (R :=
            CochainComplex.onePointRingSheaf
            R) J I) f).hom ≫
          (CochainComplex.mappingCone.triangle
            (((SheafOfModules.TotalTensorSigns.total
              (CochainComplex.onePointRingSheaf R)).obj (homComplex.{u, u, u, u} (R :=
                CochainComplex.onePointRingSheaf R) J I)).map f)).mor₃ =
        ((SheafOfModules.TotalTensorSigns.total
          (CochainComplex.onePointRingSheaf R)).obj (homComplex.{u, u, u, u} (R :=
            CochainComplex.onePointRingSheaf R) J I)).map
            (CochainComplex.mappingCone.triangle f).mor₃ ≫
          (SheafOfModules.TotalTensorSigns.shiftLeft
            (CochainComplex.onePointRingSheaf R) (homComplex.{u, u, u, u} (R :=
              CochainComplex.onePointRingSheaf R) J I) P₁ 1).hom) := by
  sorry

end DerivedCategory
