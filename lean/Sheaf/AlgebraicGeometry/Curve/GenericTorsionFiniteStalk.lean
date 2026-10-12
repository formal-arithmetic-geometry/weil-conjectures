module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleTorsion
public import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

@[expose] public section
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme
/-- Finite-stalk torsion approximation of a torsion generic sheaf.
Source: blueprint `lem-sc-affine-generic-second`, finite stable subgroup construction.
(blueprint: lem-sc-generic-torsion-finite-stalk-colimit-finite)
The finite stable subgroups of the corresponding discrete continuous Galois module form a
filtered poset and transport through the sheaf/module equivalence to the asserted cocone.
-/
theorem exists_generic_torsion_finite_stalk_colimit
    (X : Scheme.{u}) [IsIntegral X] [CompactSpace X] [QuasiSeparatedSpace X]
    (M : Sheaf (Spec X.functionField).smallEtaleTopology AddCommGrpCat.{u + 1})
    (hM : M.IsTorsion) :
    ∃ (I : Type (u + 1)) (_ : SmallCategory I) (_ : IsFiltered I)
      (F : I ⥤ Sheaf (Spec X.functionField).smallEtaleTopology AddCommGrpCat.{u + 1})
      (ι : F ⟶ (Functor.const I).obj M),
      (∀ i, (F.obj i).IsTorsion) ∧
      (∀ i, Finite (((pointSmallEtale
        (Spec.map (CommRingCat.ofHom
          (algebraMap X.functionField (AlgebraicClosure X.functionField))))).sheafFiber
            (A := AddCommGrpCat.{u + 1})).obj (F.obj i))) ∧
      Nonempty (IsColimit (Cocone.mk M ι)) := by
  sorry
end AlgebraicGeometry.Scheme
