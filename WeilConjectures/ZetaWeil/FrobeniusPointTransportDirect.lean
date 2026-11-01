/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.ZetaWeil.FrobeniusPointTransport
public import WeilConjectures.WeilSheaf.CondensedModule.CondensedModuleLocalFrobenius
public import WeilConjectures.AlgebraicGeometry.CondensedGeometricPoint.CondensedCoefficientPoint
public import WeilConjectures.AlgebraicGeometry.GeometricFieldProEtaleEvaluation
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOrdinaryCompactCohomology
public import Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.SepClosedProjective
public import Mathlib.CategoryTheory.Abelian.Projective.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.SixFunctors.PointProEtaleSectionsExactOfUniverses
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CohomologyTransport.CondensedIsomorphismCohomologyTransport
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.AlgebraicGeometry.Iso.IsoSectionwiseInverseImage
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.WeilObject.Sheaf.StalkUnit
import WeilConjectures.AlgebraicGeometry.ProEtaleObjectPullbackRestriction

/-!
# Direct condensed Frobenius point transport

This module states the direct point-fibre transport for geometric Frobenius.  The
construction uses the native sheafified-Kan upper-star and its unit-normalized
comparison with the identity.  At a representative `Q(C)`, the named
termwise-formula theorem below records the restriction `M(r)`, the normalized
inverse-image comparison `e_M⁻¹`, the module insertion `j_M(x)=1⊗x`, and the
finite-coefficient insertion normalization.

Source: Deligne, *La conjecture de Weil II*, (1.1.7), pp. 150--151;
(blueprint: def-weil-frobenius-point-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local instance 20000] HasDerivedCategory.ofIsGrothendieckAbelian
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open Opposite
open scoped CategoryTheory.Obj
namespace WeilConjectures

/-- The terminal profinite object and the singleton test object are identified by their
canonical terminal structures.  This is the object-level transport used in the point-unit map.
Source: Bhatt--Scholze, Example 4.1.10; (blueprint: def-weil-frobenius-point-transport). -/
noncomputable def directFrobeniusTopToSingleton :
    (⊤_ Profinite.{u}) ≅ Profinite.of (ULift.{u, 0} PUnit.{1}) := by
  let S := Profinite.of (ULift.{u, 0} PUnit.{1})
  let hS : IsTerminal S :=
    IsTerminal.ofUniqueHom
      (fun _ ↦ ConcreteCategory.ofHom
        ⟨fun _ ↦ default, continuous_const⟩)
      (fun _ _ ↦ by ext)
  let q : (⊤_ Profinite.{u}) ⟶ S := hS.from _
  let q' : S ⟶ (⊤_ Profinite.{u}) := terminal.from S
  refine { hom := q, inv := q', hom_inv_id := ?_, inv_hom_id := ?_ }
  · apply terminal.hom_ext
  · apply hS.hom_ext

/-- The module category on the small pro-etale site of `Spec k`.

Source: `def-weil-pbc-proetale-site` and `det-def-sfb-condensed-ring`;
(blueprint: def-weil-frobenius-point-transport). -/
abbrev directFrobeniusModule
    (D : FiniteFieldDatum.{u})
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] :=
  Mod (Sheaf (Scheme.ProEt.topology (Spec (.of D.k))) Ab.{u + 1})
    (condensedRingObj Λ (Spec (.of D.k)))

/-- The normalized inverse-image comparison followed by restriction on the identity
pro-etale object.

Source: `lem-route-exists-unique-pro-etale-iso-inverse-image-identification`;
(blueprint: def-weil-frobenius-point-transport).  This is the actual section map
`e_M⁻¹ ∘ M(r)`; it is kept separate from the derived transport so that the
representative formula is explicit. -/
def directFrobeniusSigmaSections (D : FiniteFieldDatum.{u})
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (M : directFrobeniusModule D Λ) :
    ((Mod.forget (condensedRingObj Λ (Spec (.of D.k)))).obj M).obj.obj
        (op (ProEt.mk (𝟙 (Spec (.of D.k))))) ⟶
      (((frobeniusPointIso D).hom)^*[Ab.{u + 1}].obj
        ((Mod.forget (condensedRingObj Λ (Spec (.of D.k)))).obj M)).obj.obj
        (op (ProEt.mk (𝟙 (Spec (.of D.k))))) := by
  let e := AlgebraicGeometry.Scheme.proEtaleIsoInverseImageIdentification
    (frobeniusPointIso D).hom Ab.{u + 1}
  exact
    ((Mod.forget (condensedRingObj Λ (Spec (.of D.k)))).obj M).obj.map
        (frobeniusPointRestriction D).op ≫
      (e.inv.app ((Mod.forget (condensedRingObj Λ (Spec (.of D.k)))).obj M)).app
        (op (ProEt.mk (𝟙 (Spec (.of D.k)))))

/-- The tensor-unit insertion `j_M(x)=1⊗x`, evaluated on the identity object.

Source: `det-def-sfb-module-pushforward-pullback`; (blueprint:
def-weil-frobenius-point-transport). -/
def directFrobeniusInsertionSections (D : FiniteFieldDatum.{u})
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (M : directFrobeniusModule D Λ) :
    (((frobeniusPointIso D).hom)^*[Ab.{u + 1}].obj
        ((Mod.forget (condensedRingObj Λ (Spec (.of D.k)))).obj M)).obj.obj
        (op (ProEt.mk (𝟙 (Spec (.of D.k))))) ⟶
      ((Mod.forget (condensedRingObj Λ (Spec (.of D.k)))).obj
        ((AlgebraicGeometry.ProEtale.CondensedRing.upperStar Λ
          (frobeniusPointIso D).hom).obj M)).obj.obj
        (op (ProEt.mk (𝟙 (Spec (.of D.k))))) := by
  let N := (((frobeniusPointIso D).hom)^*[Ab.{u + 1}].mapMod
      (condensedRingObj Λ (Spec (.of D.k)))).obj M
  exact
    (Mod.extendUnitHom (condensedPullbackHom Λ (frobeniusPointIso D).hom) N).hom.app
      (op (ProEt.mk (𝟙 (Spec (.of D.k)))))

/-- The underived chain-level point map `i_C=Γ(j_C)∘σ_C`, before localization.

Source: the displayed formula in `def-weil-frobenius-point-transport`; (blueprint:
def-weil-frobenius-point-transport). -/
def directFrobeniusTermwiseSections (D : FiniteFieldDatum.{u})
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (M : directFrobeniusModule D Λ) :
    ((Mod.forget (condensedRingObj Λ (Spec (.of D.k)))).obj M).obj.obj
        (op (ProEt.mk (𝟙 (Spec (.of D.k))))) ⟶
      ((Mod.forget (condensedRingObj Λ (Spec (.of D.k)))).obj
        ((AlgebraicGeometry.ProEtale.CondensedRing.upperStar Λ
          (frobeniusPointIso D).hom).obj M)).obj.obj
        (op (ProEt.mk (𝟙 (Spec (.of D.k))))) :=
  directFrobeniusSigmaSections D Λ M ≫ directFrobeniusInsertionSections D Λ M

/-- The scalar sections functor used for the termwise formula.

Source: the canonical scalar-sections construction in
`lem-weil-condensed-isomorphism-cohomology-transport`; (blueprint:
def-weil-frobenius-point-transport). -/
abbrev directFrobeniusSections (D : FiniteFieldDatum.{u})
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] :
    directFrobeniusModule D Λ ⥤ ModuleCat.{u + 1} (condensedScalarRing Λ) :=
  CondensedRing.CohomologyTransport.sections Λ (Spec (.of D.k))

end WeilConjectures
