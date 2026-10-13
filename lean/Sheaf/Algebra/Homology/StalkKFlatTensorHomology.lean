/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.Paper.DerivedHomMayerVietoris
public import Sheaf.Algebra.Homology.KFlat
public import Sheaf.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.Single

/-! # K-flat tensor homology at a stalk, with transported scalars

(blueprint: lem-pc-stalk-kflat-tensor-homology).
-/

@[expose] public section

universe u v
open CategoryTheory CategoryTheory.Limits TopologicalSpace
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry

/-- A K-flat sheaf complex computes tensor homology after transporting its stalk ring.
Source: Stacks Project, Cohomology of Sheaves, Tags 06YB, 08CG and 09U9;
Modules Tag 01AG.
Proof: the stalk criterion makes the stalk of P K-flat. Restriction along the ring
isomorphism e is an exact tensor equivalence, so it preserves K-flatness. Stalks
commute with the direct sums and tensor differentials in the total complex and
with the degree-zero single complex. Exactness of stalks and scalar restriction
identifies homology with homology of this transported total tensor. The K-flat
comparison for derived tensor identifies Q of that tensor with Q of the transported
stalk of P tensor Q of the single transported stalk of F. The latter Q-single is
the derived single functor. Apply degree-i homology and forget scalars. No replacement
of P or choice of a module is made: the module is the image of F under S.
The argument applies to zero rings, zero modules and unbounded complexes.
(blueprint: lem-pc-stalk-kflat-tensor-homology). -/
theorem stalk_kFlat_tensor_homology_iso
    (Z : RingedSpace.{u}) (x : Z) (A : CommRingCat.{u})
    (e : A ≅ Z.presheaf.stalk x)
    [HasDerivedCategory.{v} (ModuleCat.{u} A)]
    (P : CochainComplex (SheafOfModules.{u} (moduleRings Z)) ℤ)
    (hP : CochainComplex.IsKFlat (R := Z.sheaf) P) :
    let S := RingedSpace.moduleStalkFunctor Z x ⋙ ModuleCat.restrictScalars e.hom.hom
    ∀ (F : SheafOfModules.{u} (moduleRings Z)) (i : ℤ),
      Nonempty ((TopCat.Sheaf.forget AddCommGrpCat.{u} Z.carrier ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj
          ((SheafOfModules.toSheaf _).obj
            ((CochainComplex.mapBifunctor P
              ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F)
              (@MonoidalCategory.curriedTensor _ _
                (SheafOfModules.monoidalCategory Z.sheaf))).homology i)) ≅
        (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).obj
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
            (DerivedCategory.Q.obj ((S.mapHomologicalComplex (.up ℤ)).obj P) ⊗
              (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (S.obj F)))) := by
  sorry
