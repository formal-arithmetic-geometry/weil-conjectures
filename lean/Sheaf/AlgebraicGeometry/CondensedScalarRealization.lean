/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q20
-/
module

public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import Mathlib.CategoryTheory.Sites.ConstantSheaf

/-! # Scalar realization for an arbitrary commutative condensed ring

Source: Hemo--Richarz--Scholbach, Constructible sheaves on schemes, Definition 3.5
and formula (3.1) (blueprint: def-zl-condensed-scalar-realization).
The scalar map is the constant-sheaf adjunction counit on the point. Derived extension
uses the universal K-flat construction, then the section-module equivalence and p_X^*.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The reconstructed ring sheaf has the original sections, restrictions and multiplication.
Source: HRS, Definition 3.5 (blueprint: def-zl-condensed-scalar-realization). -/
abbrev condensedSectionRing :=
  InternalAbelianSheafModule.sectionRingSheaf (coherentTopology Profinite.{u}) Λ

/-- The underlying scalar ring Γ(*,Λ), with the multiplication inherited from Λ.
Source: HRS, Definition 3.5 (blueprint: def-zl-condensed-scalar-realization). -/
abbrev condensedScalarRing : CommRingCat.{u + 1} :=
  (condensedSectionRing Λ).obj.obj (op (⊤_ Profinite.{u}))

/-- The canonical constant-section map, the counit of constant sheaf versus sections at *.
Source: HRS, Definition 3.5 (blueprint: def-zl-condensed-scalar-realization). -/
def condensedScalarMap :
    realizationRing (coherentTopology Profinite.{u}) (condensedScalarRing Λ) ⟶
      condensedSectionRing Λ :=
  (constantSheafAdj (coherentTopology Profinite.{u}) CommRingCat.{u + 1}
    terminalIsTerminal).counit.app (condensedSectionRing Λ)

/-- The standard localization size for constant scalar module sheaves.
Source: Stacks 05RU (blueprint: def-zl-condensed-scalar-realization). -/
instance condensedScalarConstantHasDerived :
    HasDerivedCategory.{u + 2}
      (realizationModules (coherentTopology Profinite.{u}) (condensedScalarRing Λ)) :=
  HasDerivedCategory.standard _

/-- The standard localization size for sectionwise condensed module sheaves.
Source: Stacks 05RU (blueprint: def-zl-condensed-scalar-realization). -/
instance condensedScalarSectionHasDerived :
    HasDerivedCategory.{u + 2} (SheafOfModules.{u + 1}
      ((sheafCompose (coherentTopology Profinite.{u})
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (condensedSectionRing Λ))) :=
  HasDerivedCategory.standard _

/-- The derived coefficient extension, fixed by its universal counit and K-flat computation.
Its universal property determines the selected object up to counit-compatible isomorphism.
Source: HRS, formula (3.1), and Stacks 06YY
(blueprint: def-zl-condensed-scalar-realization). -/
def condensedScalarExtensionModel :
    SheafOfModules.DerivedChangeOfRingsCochainModel.{u + 1, u, u + 1, u + 2, u + 2}
      (condensedScalarMap Λ) :=
  Classical.choice (SheafOfModules.nonempty_derivedChangeOfRingsCochainModel
    (condensedScalarMap Λ))

/-- Scalar extension of constant complexes on the point, followed by the existing
sectionwise/internal module equivalence and inverse image to X. These exact transports
preserve quasi-isomorphisms. The only derived nonexact operation is coefficient extension.
Source: HRS, Definition 3.5 and formula (3.1)
(blueprint: def-zl-condensed-scalar-realization). -/
def condensedScalarRealization (X : Scheme.{u}) :
    DerivedCategory (ModuleCat.{u + 1} (condensedScalarRing Λ)) ⥤
      DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X)) :=
  let e := InternalAbelianSheafModule.sectionModuleEquivalence
    (coherentTopology Profinite.{u}) Λ
  letI := Functor.additive_of_preserves_binary_products e.inverse
  letI : PreservesFiniteLimits (upperStarFromPoint X) := by
    unfold upperStarFromPoint pointUpperStar
    infer_instance
  letI : PreservesFiniteColimits (upperStarFromPoint X) := by
    let : pointUpperStar.{u}.IsLeftAdjoint :=
      pointUpperStarLowerStarAdjunction.isLeftAdjoint
    unfold upperStarFromPoint
    infer_instance
  let F := (upperStarFromPoint X).mapMod Λ
  letI := Functor.additive_of_preserves_binary_products F
  commutativeSiteDerivedConstantModuleFunctor (coherentTopology Profinite.{u})
      (condensedScalarRing Λ) ⋙
    (condensedScalarExtensionModel Λ).T ⋙ e.inverse.mapDerivedCategory ⋙ F.mapDerivedCategory

end AlgebraicGeometry.ProEtale
