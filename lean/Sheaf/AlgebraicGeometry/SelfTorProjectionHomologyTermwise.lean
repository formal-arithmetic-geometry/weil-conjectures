module

public import Sheaf.Algebra.Homology.KFlat
public import Sheaf.AlgebraicGeometry.TensorPullback
public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry

/--
The projection-formula and representative-comparison argument produces an
invertible comparison arrow between the two displayed homology objects.  This
is the intermediate arrow-level form used below; its proof is the combination
of the qcqs derived projection formula, identification of the K-flat derived
pullback with the termwise tensor pullback, and exactness of pushforward along a
closed immersion.
(blueprint: lem-pc-self-tor-projection-homology-termwise-arrow)
-/
theorem exists_selfTor_projection_homology_termwise_arrow
    {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [IsClosedImmersion i] [(Scheme.Modules.tensorPullback i).Additive]
    (P : CochainComplex Y.Modules ℤ)
    (a : P ⟶ (HomologicalComplex.single Y.Modules (.up ℤ) 0).obj
      ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)))
    (hP : CochainComplex.IsKFlatResolution (R := Y.sheaf) a)
    (k : ℤ) :
    let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
    let S := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
    let T := ((Scheme.Modules.tensorPullback i).mapHomologicalComplex (.up ℤ)).obj P
    ∃ f : ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) k).obj (S.obj B ⊗ S.obj B)) ⟶
      (Scheme.Modules.pushforward i).obj (T.homology k), IsIso f := by
  sorry

/-- The termwise representative form of the self-Tor projection computation.

This is the derived projection-formula computation followed by comparison with the
specified K-flat resolution and exact closed-immersion pushforward.  It is separated
from representative transport so that an arbitrary isomorphic complex can be handled
functorially in the parent theorem.
(blueprint: lem-pc-self-tor-projection-homology-termwise).
-/
theorem nonempty_selfTor_projection_homology_termwise
    {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [IsClosedImmersion i] [(Scheme.Modules.tensorPullback i).Additive]
    (P : CochainComplex Y.Modules ℤ)
    (a : P ⟶ (HomologicalComplex.single Y.Modules (.up ℤ) 0).obj
      ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)))
    (hP : CochainComplex.IsKFlatResolution (R := Y.sheaf) a)
    (k : ℤ) :
    let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
    let S := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
    let T := ((Scheme.Modules.tensorPullback i).mapHomologicalComplex (.up ℤ)).obj P
    Nonempty (((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) k).obj (S.obj B ⊗ S.obj B)) ≅
      (Scheme.Modules.pushforward i).obj (T.homology k)) := by
  dsimp
  obtain ⟨f, hf⟩ := exists_selfTor_projection_homology_termwise_arrow i P a hP k
  let _ : IsIso f := hf
  exact ⟨asIso f⟩

end AlgebraicGeometry
