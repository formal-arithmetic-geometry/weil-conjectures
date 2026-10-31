/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GaloisLisseCorrespondenceData

/-! # The underlying linear scalar comparison -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme

/-- The underlying module comparison, oriented from the extended lisse representation
back to extension of the original representation. Source: Stacks 0DV5 (3), base change
of coefficients in `cor-galois-lisse-representations`.
(blueprint: new-w8-galois-scalar-underlying).

It is the composite of the fibre normalization, the underlying sheaf comparison, the
inverse scalar-stalk comparison, and scalar extension of the inverse normalization.
All four factors are natural isomorphisms. -/
noncomputable def galoisFiniteScalarUnderlying
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {y : Spec (.of Ω) ⟶ Y} {G : Type u} [Group G] [TopologicalSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    (d : GaloisLisseFiniteData y G)
    (R S : Type (u + 1)) [Ring R] [Finite R] [Ring S] [Finite S]
    (f : R →+* S)
    (B : LisseModuleSheafCategory Y R ⥤ LisseModuleSheafCategory Y S)
    (α : B ⋙ ObjectProperty.ι _ ≅ ObjectProperty.ι _ ⋙
      Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology f) :
    letI : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} R) :=
      ModuleCat.hasLimitsOfSize.{u, u, u + 1, u + 1}
    letI : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} S) :=
      ModuleCat.hasLimitsOfSize.{u, u, u + 1, u + 1}
    ((pointSmallEtale y).sheafFiber (A := ModuleCat.{u + 1} R) ⋙
      ModuleCat.ringExtendScalars.{u + 1, u + 1} f ≅
      Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology f ⋙
        (pointSmallEtale y).sheafFiber (A := ModuleCat.{u + 1} S)) →
    (B ⋙ (d.e S).functor ⋙ ObjectProperty.ι _ ⋙ forget₂ (Rep.{u + 1} S G) (ModuleCat S) ≅
      (d.e R).functor ⋙ ObjectProperty.ι _ ⋙ (Rep.repIsoAction R G).functor ⋙
        (ModuleCat.ringExtendScalars.{u + 1, u + 1} f).mapAction G ⋙
        (Rep.repIsoAction S G).inverse ⋙ forget₂ (Rep.{u + 1} S G) (ModuleCat S)) := by
  letI : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} R) :=
    ModuleCat.hasLimitsOfSize.{u, u, u + 1, u + 1}
  letI : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} S) :=
    ModuleCat.hasLimitsOfSize.{u, u, u + 1, u + 1}
  intro σ
  exact Functor.isoWhiskerLeft B (d.τ S) ≪≫
    Functor.isoWhiskerRight α ((pointSmallEtale y).sheafFiber (A := ModuleCat.{u + 1} S)) ≪≫
    Functor.isoWhiskerLeft (ObjectProperty.ι _) σ.symm ≪≫
    Functor.isoWhiskerRight (d.τ R).symm (ModuleCat.ringExtendScalars.{u + 1, u + 1} f)

end AlgebraicGeometry.Scheme
