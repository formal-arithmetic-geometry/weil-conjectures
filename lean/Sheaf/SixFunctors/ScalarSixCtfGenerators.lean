/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.LocallyPerfectScalarModel
public import Sheaf.SixFunctors.ListedScalarCoefficientMaps
public import Sheaf.Paper.ConstantModelTorAmplitude
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.Shift
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral

/-! # The canonical locally closed scalar-perfect generators

These are the unchanged definitions used in scalar-six-ctf, factored out so their
coefficient-presentation comparisons do not depend on the assembly theorem.
Source: blueprint scalar-six-ctf (1) (blueprint: def-sfb-scalar-perfect-generators).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  Functor.leftDerivedFunctor HasDerivedCategory.ofHasKInjectiveResolutions
  HasDerivedCategory.standard

/-- Extension through the scheme-theoretic closure is exactly i_* u_!: exact open
extension followed by the ordinary derived module pushforward, whose action is
restriction along the published coefficient adjunct. No extension functor is chosen.
Source: blueprint scalar-six-ctf, final paragraph
(blueprint: def-sfb-scalar-perfect-generators). -/
def sfbLocallyClosedDerivedExtension (Λ : ScalarSixRing.{u})
    {k : Type u} [Field k] {X : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    {S : Scheme.{u}} (a : S ⟶ X.left) (ha : IsImmersion a) :
    DerivedCategory (ModuleRingedComparison.internalModules Λ.X S) ⥤
      DerivedCategory (ModuleRingedComparison.internalModules Λ.X X.left) :=
  letI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  letI : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  letI : IsNoetherian X.left := {}
  letI : IsImmersion a := ha
  letI : TopologicalSpace.NoetherianSpace S := a.isEmbedding.isInducing.noetherianSpace
  (openImmersionLowerShriek Λ.X a.toImage).mapDerivedCategory ⋙
    (lowerStar Λ.X a.imageι).rightDerivedFunctor

/-- The generators a_!P with locally perfect scalar models, up to derived isomorphism.
Source: blueprint scalar-six-ctf (1)
(blueprint: def-sfb-scalar-perfect-generators). -/
def sfbPerfectScalarGenerator (Λ : ScalarSixRing.{u}) {k : Type u} [Field k]
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] :
    ObjectProperty (DerivedCategory (ModuleRingedComparison.internalModules Λ.X X.left)) :=
  fun K ↦ ∃ (S : Scheme.{u}) (a : S ⟶ X.left) (ha : IsImmersion a)
    (P : DerivedCategory (ModuleRingedComparison.internalModules Λ.X S)),
    IsLocallyPerfectScalarModel Λ.X S P ∧
      Nonempty (K ≅ (sfbLocallyClosedDerivedExtension Λ a ha).obj P)

end AlgebraicGeometry.ProEtale.CondensedRing
