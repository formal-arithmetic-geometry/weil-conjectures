/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AlternatingCechSheafConstruction
public import WeilConjectures.AlgebraicGeometry.AffineAlternatingCechModel
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.AlgebraicGeometry.AlternatingCechSheafAffineSections
import WeilConjectures.AlgebraicGeometry.AlternatingCechSheafAffineQuasicoherent

/-! # Affine direct image of the increasing-tuple sheaf complex

Source: Stacks Project, Tags 02KG and 02KH, comparison of affine Čech complexes;
Tag 01FM, signed increasing tuples.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- Direct image identifies the constructed sheaf complex with the affine section model.
Source: Stacks Project, Tag 02KG (affine module comparison), Tag 02KH, separated-case
proof before taking cohomology, and Tag 01FM (signed faces). -/
theorem alternatingCechSheafComplex_affineComparison
    {A : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec A) [IsSeparated f]
    {r : ℕ} (U : Fin r → X.Opens) (haffine : ∀ i, IsAffineOpen (U i))
    (G : X.Modules) [SheafOfModules.IsQuasicoherent.{u} G] :
    Nonempty (((Scheme.Modules.pushforward f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj
        ((alternatingCechSheafComplex U G).extend ComplexShape.embeddingUpNat) ≅
          affineAlternatingCechModel f U G) := by
  let : (moduleSpecΓFunctor (R := A)).Additive := ⟨by intros; rfl⟩
  let L := ((Scheme.Modules.pushforward f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    ((alternatingCechSheafComplex U G).extend ComplexShape.embeddingUpNat)
  obtain ⟨e⟩ := alternatingCechSheafComplex_affineSections f U G
  let (i : ℤ) : SheafOfModules.IsQuasicoherent.{u} (L.X i) :=
    alternatingCechSheafComplex_affineQuasicoherent f U haffine G i
  let c : ((tilde.functor A).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((moduleSpecΓFunctor (R := A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj L) ≅ L :=
    HomologicalComplex.Hom.isoOfComponents
      (fun i ↦ asIso (L.X i).fromTildeΓ)
      (fun i j _ ↦ (Scheme.Modules.fromTildeΓNatTrans.naturality (L.d i j)).symm)
  exact ⟨c.symm ≪≫ ((tilde.functor A).mapHomologicalComplex
    (ComplexShape.up ℤ)).mapIso e ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl
      (ModuleCat.restrictScalars (((Scheme.ΓSpecIso A).inv ≫ f.appTop).hom) ⋙
        tilde.functor A)) (ComplexShape.up ℤ)).app
      ((alternatingCechComplex U G.presheafModuleCat).extend
        ComplexShape.embeddingUpNat)⟩

end AlgebraicGeometry
