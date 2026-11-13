/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.PerfectMorphism
public import WeilConjectures.Algebra.Homology.KFlat
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.Single
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Sheaves.Abelian
import WeilConjectures.AlgebraicGeometry.StalkTorDimensionLocallyUniform
import WeilConjectures.AlgebraicGeometry.StrictlyPerfectRelativeTensorStalkBound
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-! # Local relative Tor bounds for perfect complexes

## References

* Stacks Project, Tags 069C and 0B6G.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

/-- Any K-flat model of the scalar restriction of a perfect complex has relative
Tor bounds uniform on a neighbourhood of each point. No compactness is assumed.
(Stacks, Tags 069C, 0B6G) -/
theorem perfect_relativeTensor_locally_bounded
    {X Y : Scheme.{u}} [IsNoetherian Y]
    (f : X ⟶ Y) [LocallyOfFiniteType f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (hperfect : HasStalkwiseFiniteTorDimension f)
    (E : schemeDerivedCategory X) (hE : IsPerfect X E)
    (K : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (e : Nonempty (DerivedCategory.Q.obj K ≅ E))
    (P : CochainComplex (SheafOfModules.{u} ((sheafCompose
      (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (TopCat.Sheaf.inverseImageRing f.base Y.sheaf))) ℤ)
    (hP : CochainComplex.IsKFlatTensor (R := TopCat.Sheaf.inverseImageRing f.base Y.sheaf) P)
    (q : P ⟶ ((SheafOfModules.restrictScalars
      ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{u} RingCat.{u})).map
          (Modules.tensorPullbackRingMap f))).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) (hq : QuasiIso q) :
    ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∃ a b : ℤ, a ≤ b ∧
      ∀ F : SheafOfModules.{u} ((sheafCompose
          (Opens.grothendieckTopology X)
          (forget₂ CommRingCat.{u} RingCat.{u})).obj
            (TopCat.Sheaf.inverseImageRing f.base Y.sheaf)),
        ∀ i : ℤ, i < a ∨ b < i → ∀ y : X, y ∈ U →
          IsZero ((TopCat.Sheaf.forget AddCommGrpCat.{u} X.carrier ⋙
            TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).obj
              ((SheafOfModules.toSheaf _).obj
                ((CochainComplex.mapBifunctor P
                  ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F)
                  (@MonoidalCategory.curriedTensor _ _ (SheafOfModules.monoidalCategory
                    (TopCat.Sheaf.inverseImageRing f.base Y.sheaf)))).homology i))) := by
  intro x
  obtain ⟨U, hxU, d, hU⟩ := stalkTorDimension_locally_uniform f hperfect x
  obtain ⟨V, hxV, L, hL, ⟨eL⟩⟩ := hE x
  obtain ⟨r, s, hdegrees⟩ := hL.1
  obtain ⟨eK⟩ := e
  have eKL : Nonempty ((SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) V).mapDerivedCategory.obj
        (DerivedCategory.Q.obj K) ≅ DerivedCategory.Q.obj L) :=
    ⟨((SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) V).mapDerivedCategory.mapIso eK) ≪≫ eL⟩
  refine ⟨U ⊓ V, ⟨hxU, hxV⟩, min (r - (d : ℤ)) s, s, min_le_right _ _, ?_⟩
  intro F i hi y hy
  apply strictlyPerfect_relativeTensor_stalk_bound f K V L hL eKL r s hdegrees
    y hy.2 d (hU y hy.1) P hP q hq F i
  rcases hi with hi | hi
  · exact Or.inl (lt_of_lt_of_le hi (min_le_left _ _))
  · exact Or.inr hi


end AlgebraicGeometry.Scheme
