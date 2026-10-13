module

public import Sheaf.Algebra.Homology.KFlat
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Sheaf.AlgebraicGeometry.TensorPullback
public import Sheaf.Algebra.Homology.DerivedInternalHom
public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

import Sheaf.Algebra.Homology.KFlatResolution
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions
import Sheaf.AlgebraicGeometry.DerivedInternalHomPullbackAdjunction
import Sheaf.AlgebraicGeometry.QCqsDerivedProjectionIsoUniverses
import Sheaf.Topology.ClosedImmersionPushforwardExact
import Sheaf.AlgebraicGeometry.ClosedImmersionPushforwardFullyFaithful

/-! # Resolutions and global self-Ext/self-Tor identifications

Source: Stacks Project, Tags 06YS, 079P, 08DH, 08I3, 08KS, 08EU and 068G.
(blueprint: new-j3-self-ext-tor-core). -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry

/-- Choose augmented resolutions and identify their global self-Ext/self-Tor homology.

Source: Stacks Project, Tag 06YS (K-flat resolutions), Tag 079P (K-injective resolutions),
Tags 08DH and 08I3 (internal Hom adjunction), Tag 08KS (closed-immersion equivalence),
Tag 08EU (projection formula) and Tag 068G (tensor computation).
(blueprint: new-j3-self-ext-tor-core).

Proof: Choose a K-flat resolution P of the single complex B, with flat terms and
quasi-isomorphism a, and a K-injective resolution J of the single complex O_Z, with
quasi-isomorphism b. The tensor pullback is additive by its adjunction with pushforward;
apply it termwise to P to form T. This is a representative of Li*B. The augmentation b
identifies the zeroth homology of J with O_Z and makes its other homology zero.
Test RHom_Y(B,i_*O_Z) against an arbitrary derived object A. Tensor-Hom adjunction,
derived pullback/direct-image adjunction, and the pullback tensor comparison identify
maps from A into this object with maps from A into Ri_*RHom_Z(Li*B,O_Z). Naturality
and Yoneda give the internal-Hom isomorphism. Since J is K-injective, Hom(T,J)
computes the latter internal Hom. Closed-immersion pushforward is exact, so homology
commutes with it; its fully faithful adjunction has invertible pullback counit. Apply
homology in degree n and this counit to obtain eG. The qcqs projection formula with
O_Z and B identifies B tensor^L B with i_*Li*B: B is quasi-coherent and a closed
immersion is affine, quasi-compact and quasi-separated. Exact pushforward followed by
the same counit in degree -n gives eQ. Carry these representative computations through
the localization comparisons into the supplied derived category on Y; the resolution
maps a and b and the formula T = i*P are retained for the local chart theorem. -/
theorem exists_selfExt_tor_resolution_core
    {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [IsClosedImmersion i] (n : ℕ) :
    let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
    let S := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
    let H := derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf
    let G := (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (n : ℤ)).obj
        (H.obj (op (S.obj B), S.obj B))
    let Q := (Scheme.Modules.tensorPullback i).obj
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (-(n : ℤ))).obj
          (S.obj B ⊗ S.obj B))
    ∃ (_add : (Scheme.Modules.tensorPullback i).Additive)
      (P : CochainComplex Y.Modules ℤ) (J : CochainComplex Z.Modules ℤ)
      (a : P ⟶ (HomologicalComplex.single Y.Modules (.up ℤ) 0).obj B)
      (b : (HomologicalComplex.single Z.Modules (.up ℤ) 0).obj
        (SheafOfModules.unit Z.ringCatSheaf) ⟶ J),
      CochainComplex.IsKFlatResolution (R := Y.sheaf) a ∧
      (∀ k : ℤ, SheafOfModules.IsFlat (P.X k)) ∧
      QuasiIso b ∧ J.IsKInjective ∧
      let T := ((Scheme.Modules.tensorPullback i).mapHomologicalComplex (.up ℤ)).obj P
      ∃ (hJ : ∀ k : ℤ, k ≠ 0 → IsZero (J.homology k))
      (e0 : J.homology 0 ≅ SheafOfModules.unit Z.ringCatSheaf)
      (eG : (Scheme.Modules.tensorPullback i).obj G ≅
        (homComplex (R := Z.sheaf) T J).homology (n : ℤ))
      (eQ : Q ≅ T.homology (-(n : ℤ))), True := by
  sorry

end AlgebraicGeometry
