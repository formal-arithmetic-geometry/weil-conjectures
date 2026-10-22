module

public import Sheaf.Algebra.Homology.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Algebra.Homology.KFlatResolution
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions
import Sheaf.AlgebraicGeometry.SelfExtPushforwardHomology
import Sheaf.AlgebraicGeometry.SelfTorPushforwardHomology
import WeilConjectures.AlgebraicGeometry.ClosedImmersionPushforwardFullyFaithful

/-! # Resolutions and global self-Ext/self-Tor identifications

Source: Stacks Project, Tags 06YS, 079P, 08DH, 08I3, 08KS, 08EU and 068G.
(blueprint: new-j3-self-ext-tor-core). -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry

set_option linter.unusedVariables false in
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
  classical
  dsimp
  let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
  obtain ⟨adj⟩ := Scheme.Modules.nonempty_tensorPullbackAdjunction i
  have hAdd : (Scheme.Modules.tensorPullback i).Additive := adj.left_adjoint_additive
  obtain ⟨P, a, hP, hflat, ha, _⟩ := CochainComplex.exists_isKFlatResolution
    (R := Y.sheaf) ((HomologicalComplex.single Y.Modules (.up ℤ) 0).obj B)
  obtain ⟨_, _, I, η, hI⟩ :=
    SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutions
      (Opens.grothendieckTopology Z) Z.sheaf
  let O := (HomologicalComplex.single Z.Modules (.up ℤ) 0).obj
    (SheafOfModules.unit Z.ringCatSheaf)
  let J := I.obj O
  let b := η.app O
  obtain ⟨hb, hKI, _⟩ := hI O
  have : QuasiIso b := hb
  have hJ : ∀ k : ℤ, k ≠ 0 → IsZero (J.homology k) := by
    intro k hk
    exact (HomologicalComplex.isZero_single_obj_homology (.up ℤ) 0
      (SheafOfModules.unit Z.ringCatSheaf) k hk).of_iso
        (isoOfQuasiIsoAt b k).symm
  let e0 : J.homology 0 ≅ SheafOfModules.unit Z.ringCatSheaf :=
    (isoOfQuasiIsoAt b 0).symm ≪≫
      HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 _
  refine ⟨hAdd, P, J, a, b, ⟨ha, hP⟩, hflat, hb, hKI, hJ, e0, ?_⟩
  let T := ((Scheme.Modules.tensorPullback i).mapHomologicalComplex (.up ℤ)).obj P
  obtain ⟨g⟩ := nonempty_selfExt_pushforward_homology i P J a b ⟨ha, hP⟩ hb hKI (n : ℤ)
  obtain ⟨q⟩ := nonempty_selfTor_pushforward_homology i P a ⟨ha, hP⟩ (-(n : ℤ))
  let e : Scheme.Modules.tensorPullback i ⊣ Scheme.Modules.pushforward i :=
    Classical.choice (Scheme.Modules.nonempty_tensorPullbackAdjunction i)
  have hc : ∀ N : Z.Modules, IsIso (e.counit.app N) :=
    (closedImmersion_pushforward_fullyFaithful i).1
  let eG := (Scheme.Modules.tensorPullback i).mapIso g ≪≫
    asIso (e.counit.app ((homComplex (R := Z.sheaf) T J).homology (n : ℤ)))
  let eQ := (Scheme.Modules.tensorPullback i).mapIso q ≪≫
    asIso (e.counit.app (T.homology (-(n : ℤ))))
  exact ⟨eG, eQ, trivial⟩

end AlgebraicGeometry
