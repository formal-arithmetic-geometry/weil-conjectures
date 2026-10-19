/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P2
-/
module

public import Sheaf.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.AlgebraicGeometry.AffineFreeKernelRankLocus
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Sheaf.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

/-! # Closed lowest-cohomology loci for an affine finite-free complex

Source: Stacks Project, Tag 0BDL, local matrix calculation, and Tag 0EWY.
(blueprint: lem-sc-affine-free-lowest-matrix-locus).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private theorem pullback_Q_iso {X Y : Scheme.{u}} (g : X ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (P : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (hP : CochainComplex.IsAcyclicTensorKFlat (R := Y.sheaf) P) :
    Nonempty ((derivedPullback g).obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj (((Modules.pullback g).mapHomologicalComplex (.up ℤ)).obj P)) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    obtain ⟨I, hI, hImap, hIadd, hIlim, hIcolim, hIres,
      F, hF, hFmap, hFadd, ε, hL, htri, hK⟩ :=
      (derivedPullback_spec g)
    have h : F = Modules.tensorPullback g := CategoryTheory.Functor.ext hF (fun _ _ a ↦ hFmap a)
    subst F
    have : (Modules.tensorPullback g).Additive := hFadd
    have : IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) := hK P hP
    let η := (Modules.nonempty_tensorPullbackAdjunction g).some.leftAdjointUniq
      (Modules.pullbackPushforwardAdjunction g)
    exact ⟨(derivedPullback g).mapIso ((DerivedCategory.quotientCompQhIso _).app P).symm ≪≫
      asIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≪≫
      DerivedCategory.Qh.mapIso
        (((Modules.tensorPullback g).mapHomotopyCategoryFactors (.up ℤ)).app P) ≪≫
      (DerivedCategory.quotientCompQhIso _).app _ ≪≫
      DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex η (.up ℤ)).app P)⟩

private theorem free_flat (X : Scheme.{u}) (n : ℕ) :
    SheafOfModules.IsFlat (SheafOfModules.free
      (R := moduleRings X.toRingedSpace) (ULift.{u} (Fin n))) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    let := SheafOfModules.monoidalCategory X.sheaf
    let := SheafOfModules.symmetricCategory X.sheaf
    obtain ⟨⟨mp⟩, ⟨mc⟩, _⟩ := SheafOfModules.tensorClosed X.sheaf
    let := mp
    let := mc
    have := SheafOfModules.isGrothendieckAbelian (moduleRings X.toRingedSpace)
    exact (ObjectProperty.flat_coproduct _ (fun _ ↦ ObjectProperty.prop_unit _)).2


private theorem lowest_pullback_iso
    [∀ T : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toRingedSpace))]
    (X T : Scheme.{u}) (h : T ⟶ X)
    (K : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (a : ℤ)
    (hbounded : ∃ c : ℤ, ∀ j : ℤ, c < j → IsZero (K.X j))
    (hlower : ∀ j : ℤ, j < a → IsZero (K.X j))
    (hfree : ∀ j : ℤ, ∃ n : ℕ, Nonempty (K.X j ≅ SheafOfModules.free
      (R := moduleRings X.toRingedSpace) (ULift.{u} (Fin n)))) :
    Nonempty (((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings T.toRingedSpace)) a).obj
        ((derivedPullback h).obj (DerivedCategory.Q.obj K))) ≅
      kernel ((Modules.pullback h).map (K.d a (a + 1)))) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    have hflat : ∀ j : ℤ, SheafOfModules.IsFlat (K.X j) := by
      intro j
      obtain ⟨n, ⟨e⟩⟩ := hfree j
      let := SheafOfModules.monoidalCategory X.sheaf
      exact (exactFunctor _ _).prop_of_iso
        ((MonoidalCategory.curriedTensor _).flip.mapIso e.symm) (free_flat X n)
    obtain ⟨e⟩ := pullback_Q_iso h K
      (CochainComplex.isKFlat_of_boundedAbove_flat_ringedSpace
        X.toRingedSpace K hbounded hflat)
    let F := Modules.pullback h
    have : F.Additive := Modules.instAdditivePullback h
    let P := (F.mapHomologicalComplex (.up ℤ)).obj K
    have hz : P.d (a - 1) a = 0 := by
      exact (F.map_isZero (hlower (a - 1) (by omega))).eq_of_src _ _
    let eH := (DerivedCategory.homologyFunctor.{w} (SheafOfModules.{u}
      (moduleRings T.toRingedSpace)) a).mapIso e ≪≫
      (DerivedCategory.homologyFunctorFactors.{w} (SheafOfModules.{u}
        (moduleRings T.toRingedSpace)) a).app P
    let eC := (P.isoHomologyπ (a - 1) a (by simp) hz).symm
    let eK := (P.cyclesIsKernel a (a + 1) (by simp)).conePointUniqueUpToIso
      (kernelIsKernel (P.d a (a + 1)))
    exact ⟨eH ≪≫ eC ≪≫ eK⟩


/-- A bounded-above finite-free complex starting in degree a on an affine scheme
has a closed rank-r lowest-cohomology locus when its first term has rank s <= r.
This assertion concerns a supplied complex, with no perfectness, Tor-amplitude,
Betti function, point, or choice of open neighbourhood in its statement.
Source: Stacks Project, Tag 0BDL, local matrix calculation, and Tag 0EWY.
(blueprint: lem-sc-affine-free-lowest-matrix-locus).

Proof: Every term is free, hence flat. Bounded-above flat complexes compute derived
pullback termwise (06YD). Since all terms below a vanish, after any pullback the
lowest cohomology is the kernel of the outgoing differential. Choose free frames
in degrees a and a+1 and express that differential by its finite matrix of global
sections on the affine X. If s=r, let Z be the closed subscheme cut out by these
entries. Its quotient ideal is finitely generated, so its closed immersion is
locally of finite presentation. A morphism into X factors through Z precisely
when all pulled-back entries vanish. This implies its kernel is free of rank r.
Conversely, trivialize a rank-r kernel on affine source neighbourhoods. Its
inclusion into the degree-a term is a square injective map. By 0EWY the dual of
its cokernel is zero. Each coordinate of the outgoing map factors through that
cokernel and is zero. The matrix therefore vanishes locally and globally; the
local factors through Z agree because a closed immersion is a monomorphism.
If s<r, take the empty closed subscheme. A rank-r free kernel on any nonempty
affine source chart injects into the rank-s first term. Pad the target with r-s
zero coordinates. The resulting square injection has injective transpose by
0EWY, but its transpose kills a nonzero padded basis vector, a contradiction.
Thus the source is empty. Conversely both predicates hold on the empty source.
The empty immersion is locally of finite presentation. For s=r=0 the first term
and matrix are zero and Z=X. Empty X and all zero rings obey the same argument. -/
theorem exists_affineFreeLowestMatrixLocus
    [∀ T : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toRingedSpace))]
    (X : Scheme.{u}) [IsAffine X]
    (K : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (a : ℤ) (s r : ℕ) (hsr : s ≤ r)
    (hbounded : ∃ c : ℤ, ∀ j : ℤ, c < j → IsZero (K.X j))
    (hlower : ∀ j : ℤ, j < a → IsZero (K.X j))
    (hfree : ∀ j : ℤ, ∃ n : ℕ, Nonempty (K.X j ≅ SheafOfModules.free
      (R := moduleRings X.toRingedSpace) (ULift.{u} (Fin n))))
    (ha : Nonempty (K.X a ≅ SheafOfModules.free
      (R := moduleRings X.toRingedSpace) (ULift.{u} (Fin s)))) :
    ∃ (Z : Scheme.{u}) (i : Z ⟶ X),
      IsClosedImmersion i ∧ LocallyOfFinitePresentation i ∧
      (∀ (T : Scheme.{u}) (h : T ⟶ X),
        (∃ g : T ⟶ Z, g ≫ i = h) ↔
          SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
            ((DerivedCategory.homologyFunctor
              (SheafOfModules.{u} (moduleRings T.toRingedSpace)) a).obj
                ((derivedPullback h).obj (DerivedCategory.Q.obj K))) r) := by
  obtain ⟨n, hn⟩ := hfree (a + 1)
  obtain ⟨Z, i, hi, hfp, hZ⟩ := exists_affineFreeKernelRankLocus X
    (K.X a) (K.X (a + 1)) (K.d a (a + 1)) s n r hsr ha hn
  refine ⟨Z, i, hi, hfp, ?_⟩
  intro T h
  obtain ⟨e⟩ := lowest_pullback_iso X T h K a hbounded hlower hfree
  rw [hZ T h]
  constructor
  · intro hk
    have := hk
    exact SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso e.symm
  · intro hh
    have := hh
    exact SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso e

end AlgebraicGeometry.Scheme
