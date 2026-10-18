/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N4
-/
module

public import Sheaf.AlgebraicGeometry.StrictTowerOpenExtension
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Sheaf.Paper.CompactSupportComparisonPullbackCoherence
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
public import Sheaf.Paper.EtaleOriginWitness
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction

/-!
# Normalized finite coefficient and etale-origin transport

Source: Stacks Project, Tags 0F7B, 0F7C, 0F7D, 0F7F, 07A7 and 09AE, and the explicit
strict-tower refinement in the blueprint (blueprint: def-cbc-finite-constant-coefficient-transport).

The index `n : ℕ` denotes positive level `n+1`. All derived categories below localize
complexes of strict towers, rather than forming towers in separate derived categories.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite

namespace AlgebraicGeometry.ProEtale.StrictTower

variable (B : Type (u + 1)) [CommRing B]

/-- Forgetting commutativity commutes with sheafification at the original site universes.
Source: Stacks, Tags 00W1 and 03DA
(blueprint: def-cbc-finite-constant-coefficient-transport).
Proof: the plus construction uses limits of matching families and filtered colimits
of coverings. Forgetting commutativity creates these limits and preserves these
filtered colimits. Apply the construction twice and its universal property to
identify ring sheafification with forgotten commutative-ring sheafification.
The resulting comparison preserves the sheafification unit. -/
@[instance]
theorem constantRingForget_preservesSheafification (X : Scheme.{u}) :
    (Scheme.ProEt.topology X).PreservesSheafification
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) := by
  sorry

/-- The canonical coefficient map sends a scalar to its constant function after φ.
Source: Stacks, Tags 03DA and 099R
(blueprint: def-cbc-finite-constant-coefficient-transport). -/
noncomputable def finiteScalarMap (X : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    (sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (coefficients B X) ⟶
        finiteCoefficientRingSheaf X Λ :=
  (constantCommuteCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).hom.app (CommRingCat.of B) ≫
  (constantSheaf (Scheme.ProEt.topology X) RingCat.{u + 1}).map (RingCat.ofHom φ) ≫
  ((sheafificationAdjunction (Scheme.ProEt.topology X) RingCat.{u + 1}).homEquiv
    _ _).symm (finiteCoefficientScalarMap X Λ)

/-- Actual restriction of module scalars along the specified constant-section map.
Source: Stacks, Tag 03DA
(blueprint: def-cbc-finite-constant-coefficient-transport). -/
noncomputable def finiteRestriction (X : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    FiniteCoefficientModules X Λ ⥤ Modules B X :=
  SheafOfModules.restrictScalars (finiteScalarMap B X Λ φ)

/-- Restriction of scalars is exact; no flatness of φ is required.
Source: Stacks, Tag 03DA
(blueprint: def-cbc-finite-constant-coefficient-transport).
Proof: restriction leaves the underlying additive sheaf, restrictions and maps
unchanged. Kernels and sheafified cokernels have the same restricted scalar action,
so both finite-limit and finite-colimit comparisons are isomorphisms. -/
theorem finiteRestriction_exact (X : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    (finiteRestriction B X Λ φ).Additive ∧
      PreservesFiniteLimits (finiteRestriction B X Λ φ) ∧
        PreservesFiniteColimits (finiteRestriction B X Λ φ) := by
  sorry

/-- Additivity of scalar restriction. Source: Stacks, Tag 03DA
(blueprint: def-cbc-finite-constant-coefficient-transport). -/
noncomputable instance finiteRestriction_additive (X : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    (finiteRestriction B X Λ φ).Additive := (finiteRestriction_exact B X Λ φ).1

/-- Left exactness of scalar restriction. Source: Stacks, Tag 03DA
(blueprint: def-cbc-finite-constant-coefficient-transport). -/
noncomputable instance finiteRestriction_finiteLimits (X : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    PreservesFiniteLimits (finiteRestriction B X Λ φ) := (finiteRestriction_exact B X Λ φ).2.1

/-- Right exactness of scalar restriction. Source: Stacks, Tag 03DA
(blueprint: def-cbc-finite-constant-coefficient-transport). -/
noncomputable instance finiteRestriction_finiteColimits (X : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    PreservesFiniteColimits (finiteRestriction B X Λ φ) := (finiteRestriction_exact B X Λ φ).2.2

/-- A level may have its own finite coefficient ring and its own lower bound. The
etale witness is exactly the recorded dependency's witness, followed by actual
restriction of scalars. Source: blueprint finite-origin hypothesis
(blueprint: def-cbc-finite-constant-coefficient-transport). -/
structure ScalarEtaleOrigin (X : Scheme.{u}) (K : DerivedCategory (Modules B X)) where
  Λ : Type (u + 1)
  [ring : CommRing Λ]
  [finite : Finite Λ]
  [topology : TopologicalSpace Λ]
  [discrete : DiscreteTopology Λ]
  φ : B →+* Λ
  F : FiniteCoefficientDerivedCategoryPlus X Λ
  origin : EtaleOriginWitness X Λ F
  iso : (finiteRestriction B X Λ φ).mapDerivedCategory.obj F.obj ≅ K

attribute [instance] ScalarEtaleOrigin.ring ScalarEtaleOrigin.finite
  ScalarEtaleOrigin.topology ScalarEtaleOrigin.discrete


/-- Realize finite fixed-ring sheaves, then restrict the specified scalar action.
Source: Stacks, Tags 03DA and 099R
(blueprint: def-cbc-finite-constant-coefficient-transport). -/
noncomputable def C (X : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ) ⥤ Modules B X :=
  finiteCoefficientRealization X Λ ⋙ finiteRestriction B X Λ φ

/-- The realization comparison is uniquely normalized on the sheafification unit.
Source: Stacks, Tag 03DA
(blueprint: def-cbc-finite-constant-coefficient-transport).
Proof: module sheafification has the sheafification of the underlying additive
presheaf as its underlying sheaf. The counit to the original additive sheaf is
an isomorphism and sends each unit section to itself. Local surjectivity of the
unit gives uniqueness. Scalar restriction leaves all these sections unchanged. -/
theorem cUnderlying_existsUnique (X : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    ∃! e : C B X Λ φ ⋙ SheafOfModules.toSheaf _ ≅
        sheafCompose (Scheme.ProEt.topology X) (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat),
      ∀ (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))
        (U : X.ProEtᵒᵖ) (m : F.obj.obj U),
        (e.hom.app F).hom.app U
          ((toSheafify (Scheme.ProEt.topology X)
            ((finiteCoefficientModulePresheaf X.ProEt Λ).obj F.obj).presheaf).app U m) = m := by
  sorry

/-- The specified underlying-sheaf identification, fixed on all unit sections.
Source: Stacks, Tag 03DA
(blueprint: def-cbc-finite-constant-coefficient-transport). -/
noncomputable def cUnderlying (X : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    C B X Λ φ ⋙ SheafOfModules.toSheaf _ ≅
      sheafCompose (Scheme.ProEt.topology X) (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat) :=
  Classical.choose (cUnderlying_existsUnique B X Λ φ)

/-- Direct image commutes with this scalar realization by identity on sections.
Source: Stacks, Tag 0D6E
(blueprint: def-cbc-finite-constant-coefficient-transport).
Proof: after the underlying-sheaf identifications both sides have sections of F
on U ×_Y X. Identity on these sections is B-linear because both coefficient maps
send b to the constant value φ(b). It is natural and invertible. Faithfulness of
underlying additive sheaves proves uniqueness. -/
theorem cDirect_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    ∃! e : ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f ⋙ C B Y Λ φ ≅
        C B X Λ φ ⋙ moduleDirectImage B f,
      ∀ (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))
        (U : Y.ProEtᵒᵖ)
        (m : ((C B Y Λ φ).obj
          ((ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f).obj F)).val.obj U),
        ((cUnderlying B X Λ φ).hom.app F).hom.app
            ((Scheme.proEtaleBaseChange f).op.obj U) ((e.hom.app F).val.app U m) =
          ((cUnderlying B Y Λ φ).hom.app
            ((ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f).obj F)).hom.app U m := by
  sorry

/-- The canonical sectionwise scalar/direct-image comparison.
Source: Stacks, Tag 0D6E
(blueprint: def-cbc-finite-constant-coefficient-transport). -/
noncomputable def cDirect {X Y : Scheme.{u}} (f : X ⟶ Y) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f ⋙ C B Y Λ φ ≅
      C B X Λ φ ⋙ moduleDirectImage B f :=
  Classical.choose (cDirect_existsUnique B f Λ φ)

/-- The actual etale-to-pro-etale comparison followed by scalar realization.
Source: Stacks, Tag 099R
(blueprint: def-cbc-finite-constant-coefficient-transport). -/
noncomputable def H (X : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⥤ Modules B X :=
  comparisonUpperStar (ModuleCat.{u + 1} Λ) X ⋙ C B X Λ φ

/-- The canonical inverse-image-square mate, followed by identity on scalar sections.
Source: Stacks, Tags 099R, 0D6E and 07A7
(blueprint: def-cbc-finite-constant-coefficient-transport). -/
noncomputable def hDirect {X Y : Scheme.{u}} (f : X ⟶ Y) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    Etale.lowerStar (ModuleCat.{u + 1} Λ) f ⋙ H B Y Λ φ ⟶
      H B X Λ φ ⋙ moduleDirectImage B f :=
  (Functor.associator _ _ _).inv ≫
  Functor.whiskerRight
    (mateEquiv (cbcEtaleComparisonAdjunction (ModuleCat.{u + 1} Λ) f)
      (cbcProEtaleComparisonAdjunction (ModuleCat.{u + 1} Λ) f)
      (cbcComparisonCoefficientPullbackIso (ModuleCat.{u + 1} Λ) f).inv) (C B Y Λ φ) ≫
  (Functor.associator _ _ _).hom ≫
  Functor.whiskerLeft (comparisonUpperStar (ModuleCat.{u + 1} Λ) X)
    (cDirect B f Λ φ).hom ≫ (Functor.associator _ _ _).inv

/-- The inverse-image comparison is precisely the inverse mate of hDirect.
Source: Stacks, Tags 03EK and 07A7
(blueprint: def-cbc-finite-constant-coefficient-transport). -/
noncomputable def hPullbackInv {X Y : Scheme.{u}} (f : X ⟶ Y) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    H B Y Λ φ ⋙ modulePullback B f ⟶
      Etale.upperStar (ModuleCat.{u + 1} Λ) f ⋙ H B X Λ φ :=
  (mateEquiv (cbcEtaleComparisonAdjunction (ModuleCat.{u + 1} Λ) f)
    (Scheme.proEtaleRingModuleAdjunction f (coefficients B Y)
      (coefficients B X) (constantRingIso B f))).symm (hDirect B f Λ φ)

/-- The specified coefficient/site pullback comparison is invertible.
Source: Stacks, Tags 03EK and 099R
(blueprint: def-cbc-finite-constant-coefficient-transport).
Proof: separate site inverse image from scalar restriction. The former has the
canonical inverse-image comparison; the latter keeps the inverse-image additive
sheaf and restricts its action. On constant scalars the two actions coincide.
The unit-section normalization identifies their composite with this inverse mate.
No flatness and no preservation of injectives by scalar restriction is used. -/
theorem hPullbackInv_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    IsIso (hPullbackInv B f Λ φ) := by
  sorry

/-- The inverse open comparison is the open-adjunction inverse mate of pullback.
Source: Stacks, Tag 09AF
(blueprint: def-cbc-finite-constant-coefficient-transport). -/
noncomputable def hOpenInv {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    H B U Λ φ ⋙ moduleJ B j ⟶
      Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j ⋙ H B X Λ φ :=
  ((mateEquiv (Etale.openImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} Λ) j) (moduleJAdj B j)).symm
    (@inv _ _ _ _ (hPullbackInv B j Λ φ) (hPullbackInv_isIso B j Λ φ))).natTrans

/-- The specified inverse open comparison is invertible.
Source: Stacks, Tag 09AF
(blueprint: def-cbc-finite-constant-coefficient-transport).
Proof: extension by zero has the original module on the open and zero off it.
Site comparison and scalar restriction retain these sections. The open-unit
transpose of their sectionwise identification is the displayed mate. The inverse
sectionwise identification has the inverse transpose, proving invertibility. -/
theorem hOpenInv_isIso {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    IsIso (hOpenInv B j Λ φ) := by
  sorry

/-- The forward open comparison is the inverse of the specified open-adjunction mate.
Source: Stacks, Tag 09AF
(blueprint: def-cbc-finite-constant-coefficient-transport). -/
noncomputable def hOpen {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j ⋙ H B X Λ φ ⟶
      H B U Λ φ ⋙ moduleJ B j :=
  (@asIso _ _ _ _ (hOpenInv B j Λ φ) (hOpenInv_isIso B j Λ φ)).inv

/-- The normalized forward open comparison is invertible.
Source: Stacks, Tag 09AF
(blueprint: def-cbc-finite-constant-coefficient-transport).
Proof: this is the inverse of the invertible unit-normalized inverse comparison,
so the two inverse identities give invertibility of the forward arrow. -/
theorem hOpen_isIso {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    IsIso (hOpen B j Λ φ) := by
  sorry

/-- The comparison functor is additive and exact.
Source: Stacks, Tags 03DA and 099R
(blueprint: def-cbc-finite-constant-coefficient-transport).
Proof: comparison inverse image, finite realization and scalar restriction are
additive and exact. Their composite therefore preserves finite limits and colimits. -/
theorem h_exact (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    (H B X Λ φ).Additive ∧ PreservesFiniteLimits (H B X Λ φ) ∧
      PreservesFiniteColimits (H B X Λ φ) := by
  sorry

/-- Additivity of H. Source: Stacks, Tag 099R
(blueprint: def-cbc-finite-constant-coefficient-transport). -/
noncomputable instance h_additive (X : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    (H B X Λ φ).Additive := (h_exact B X Λ φ).1

/-- Left exactness of H. Source: Stacks, Tag 099R
(blueprint: def-cbc-finite-constant-coefficient-transport). -/
noncomputable instance h_finiteLimits (X : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    PreservesFiniteLimits (H B X Λ φ) := (h_exact B X Λ φ).2.1

/-- Right exactness of H. Source: Stacks, Tag 099R
(blueprint: def-cbc-finite-constant-coefficient-transport). -/
noncomputable instance h_finiteColimits (X : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    PreservesFiniteColimits (H B X Λ φ) := (h_exact B X Λ φ).2.2

/-- The bounded-below comparison included into the unbounded target.
Source: Stacks, Tags 099R and 05RU
(blueprint: def-cbc-finite-constant-coefficient-transport). -/
noncomputable def HD (X : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory (Modules B X) :=
  (H B X Λ φ).mapDerivedCategoryPlus ⋙ DerivedCategory.Plus.ι

/-- Canonical derived direct-image comparison; its unit normalization is built into
rightDerivedFunctorPlusBaseChange. Source: Stacks, Tags 099R and 0B65
(blueprint: def-cbc-finite-constant-coefficient-transport). -/
noncomputable def hR {U X : Scheme.{u}} (f : U ⟶ X) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) f ⋙ HD B X Λ φ ⟶
      HD B U Λ φ ⋙ (moduleDirectImage B f).rightDerivedFunctor :=
  (Functor.associator _ _ _).inv ≫
  Functor.whiskerRight (Functor.rightDerivedFunctorPlusBaseChange (hDirect B f Λ φ))
    DerivedCategory.Plus.ι ≫
  (Functor.associator _ _ _).hom ≫
  Functor.whiskerLeft (H B U Λ φ).mapDerivedCategoryPlus
    (moduleDirectImage B f).rightDerivedFunctorPlusCompatibility.hom ≫
  (Functor.associator _ _ _).inv

/-- This particular direct-image comparison is an isomorphism for qcqs maps.
Source: Stacks, Tag 099R
(blueprint: def-cbc-finite-constant-coefficient-transport).
Proof: factor hDirect into the canonical etale/pro-etale mate and the sectionwise
scalar comparison. On bounded-below etale origins the former is invertible by
the cohomology-continuity comparison. The scalar-change derived-adjunction theorem
identifies the latter with restriction of the original derived direct image.
The unit factorizations show this is the specified hR. Both factors are invertible;
no flatness assumption or preservation of K-injectives by restriction is required. -/
theorem hR_isIso {U X : Scheme.{u}} (f : U ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    IsIso (hR B f Λ φ) := by
  sorry

/-- Derived open comparison with the same open-unit normalization.
Source: Stacks, Tag 09AF
(blueprint: def-cbc-finite-constant-coefficient-transport). -/
noncomputable def hJ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategoryPlus ⋙
        HD B X Λ φ ≅ HD B U Λ φ ⋙ (moduleJ B j).mapDerivedCategory :=
  (Functor.associator _ _ _).symm ≪≫
  isoWhiskerRight
    ((Functor.mapDerivedCategoryPlusCompIso _ _).symm ≪≫
      Functor.mapDerivedCategoryPlusNatIso
        (@asIso _ _ _ _ (hOpen B j Λ φ) (hOpen_isIso B j Λ φ)) ≪≫
      Functor.mapDerivedCategoryPlusCompIso _ _) DerivedCategory.Plus.ι ≪≫
  Functor.associator _ _ _ ≪≫
  isoWhiskerLeft (H B U Λ φ).mapDerivedCategoryPlus
    (moduleJ B j).mapDerivedCategoryPlusCompatibility ≪≫
  (Functor.associator _ _ _).symm

/-- The canonical comparison from H of the etale origin to its scalar-restricted
finite-coefficient realization. Source: blueprint finite-origin hypothesis
(blueprint: def-cbc-finite-constant-coefficient-transport). -/
noncomputable def originIso {X : Scheme.{u}} {K : DerivedCategory (Modules B X)}
    (w : ScalarEtaleOrigin B X K) : (HD B X w.Λ w.φ).obj w.origin.L ≅ K :=
  (isoWhiskerRight
    (Functor.mapDerivedCategoryPlusCompIso
      (finiteCoefficientComparison X w.Λ) (finiteRestriction B X w.Λ w.φ))
    DerivedCategory.Plus.ι ≪≫ Functor.associator _ _ _ ≪≫
    isoWhiskerLeft (finiteCoefficientComparison X w.Λ).mapDerivedCategoryPlus
      (finiteRestriction B X w.Λ w.φ).mapDerivedCategoryPlusCompatibility ≪≫
    (Functor.associator _ _ _).symm).app w.origin.L ≪≫
  (finiteRestriction B X w.Λ w.φ).mapDerivedCategory.mapIso
    (DerivedCategory.Plus.ι.mapIso w.origin.alpha) ≪≫ w.iso

end AlgebraicGeometry.ProEtale.StrictTower
