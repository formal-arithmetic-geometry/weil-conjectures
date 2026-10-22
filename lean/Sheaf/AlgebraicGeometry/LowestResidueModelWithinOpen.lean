/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups P2 and P3
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import WeilConjectures.AlgebraicGeometry.DerivedFiberBetti
public import Sheaf.AlgebraicGeometry.DerivedTensorCohomologyVanishes
public import Mathlib.AlgebraicGeometry.AffineScheme
import Sheaf.AlgebraicGeometry.ResidueBettiZeroOfTensorVanishing
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Restricting a residue model to a prescribed open

Source: Stacks Project, Tags 0BDL and 0BCD.
(blueprint: lem-sc-lowest-residue-model-within-open).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

-- Use the shared SheafOfModules category instances, rather than Scheme.Modules instances.
private noncomputable def openRestrict {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] :
    SheafOfModules.{u} (moduleRings Y.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings X.toRingedSpace) := Modules.restrictFunctor f

private local instance openRestrict_additive {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] : (openRestrict f).Additive :=
  inferInstanceAs (Modules.restrictFunctor f).Additive

private local instance openRestrict_limits {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] : PreservesFiniteLimits (openRestrict f) :=
  inferInstanceAs (PreservesFiniteLimits (Modules.restrictFunctor f))

private local instance openRestrict_colimits {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] : PreservesFiniteColimits (openRestrict f) :=
  inferInstanceAs (PreservesFiniteColimits (Modules.restrictFunctor f))

private theorem derivedOpen_iso_restrict
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (E : schemeDerivedCategory Y) :
    let R : SheafOfModules.{u} (moduleRings Y.toRingedSpace) ⥤
        SheafOfModules.{u} (moduleRings X.toRingedSpace) := openRestrict f
    Nonempty ((derivedPullback f).obj E ≅ R.mapDerivedCategory.obj E) := by
  classical
  dsimp only
  let R : SheafOfModules.{u} (moduleRings Y.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings X.toRingedSpace) := openRestrict f
  let A := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  let B := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  obtain ⟨I, hI, hImap, hIadd, hIlim, hIcolim, hIres,
    F, hF, hFmap, hFadd, ε, hL, htri, hK⟩ :=
    (derivedPullback_spec f)
  have h : F = Modules.tensorPullback f :=
    CategoryTheory.Functor.ext hF (fun M N a ↦ hFmap a)
  subst F
  let η : Modules.tensorPullback f ≅ Modules.restrictFunctor f :=
    (Modules.nonempty_tensorPullbackAdjunction f).some.leftAdjointUniq
      (Modules.restrictAdjunction f)
  have : (Modules.tensorPullback f).Additive := hFadd
  let G := DerivedCategory.Q.objPreimage E
  obtain ⟨P, s, hP, _, hs, _⟩ := CochainComplex.exists_isKFlatResolution (R := Y.sheaf) G
  have : QuasiIso s := hs
  have : IsIso (ε.app ((HomotopyCategory.quotient A (.up ℤ)).obj P)) := hK P hP
  let eP : DerivedCategory.Q.obj P ≅ E :=
    asIso (DerivedCategory.Q.map s) ≪≫ DerivedCategory.Q.objObjPreimageIso E
  let e : (derivedPullback f).obj E ≅
      DerivedCategory.Q.obj
        (((Modules.tensorPullback f).mapHomologicalComplex (.up ℤ)).obj P) :=
    (derivedPullback f).mapIso eP.symm ≪≫
      (derivedPullback f).mapIso ((DerivedCategory.quotientCompQhIso A).app P).symm ≪≫
      asIso (ε.app ((HomotopyCategory.quotient A (.up ℤ)).obj P)) ≪≫
      DerivedCategory.Qh.mapIso ((Modules.tensorPullback f).mapHomotopyCategoryFactors
        (.up ℤ) |>.app P) ≪≫
      (DerivedCategory.quotientCompQhIso B).app _
  exact ⟨e ≪≫ DerivedCategory.Q.mapIso
    ((NatIso.mapHomologicalComplex η (.up ℤ)).app P) ≪≫
      (R.mapDerivedCategoryFactors.app P).symm ≪≫
      R.mapDerivedCategory.mapIso eP⟩

/-- A supplied residue model can be restricted inside a prescribed open and has no
terms below the lower Tor bound. This constructs no representing closed subscheme.
Source: Stacks Project, Tag 0BDL, affine model paragraph, and Tag 0BCD.
(blueprint: lem-sc-lowest-residue-model-within-open).

Proof: Tor amplitude implies that the derived residue fibre at U.ι x has zero
cohomology below a: use the stalk tensor criterion for Tor amplitude and tensor
with its residue field. Thus every Betti number in those degrees is zero. In the
supplied model P its term in each such degree is isomorphic to the free sheaf on
the empty indexing type, hence is zero. Choose an affine neighbourhood of U.ι x
inside O intersect U using the affine basis. Regard it as V inside U. Restrict P
to this neighbourhood and transport it from the over-site to V.toScheme by the
module equivalence. Restriction and this equivalence are exact and preserve free
sheaves with the same indexing types, and hence preserve the upper bound and
all prescribed ranks. Their termwise localization comparisons and the exact-open
comparison with derived pullback give the displayed derived isomorphism. The
first rank is the original degree-a Betti number, not a rank at a different point.
No assumption a <= b is necessary; when a > b all fibre ranks vanish. An empty U
has no x to consider, and zero ranks give actual zero free terms. -/
theorem lowestResidueModel_withinOpen
    [∀ T : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toRingedSpace))]
    (S : Scheme.{u})
    [∀ O : S.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over O))]
    (E : schemeDerivedCategory S) (a b : ℤ)
    (hamp : ∀ F : SheafOfModules.{u} (moduleRings S.toRingedSpace),
      ∀ j : ℤ, j < a ∨ b < j → schemeDerivedTensorCohomologyVanishes S E F j)
    (U : S.Opens) (x : U.toScheme) (O : S.Opens)
    (hxO : U.ι x ∈ O) (hO : IsAffineOpen O)
    (P : CochainComplex (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over O)) ℤ)
    (hbounded : ∃ c d : ℤ, ∀ j : ℤ, j < c ∨ d < j → IsZero (P.X j))
    (hrank : ∀ j : ℤ, Nonempty (P.X j ≅ SheafOfModules.free
      (R := (moduleRings S.toRingedSpace).over O)
        (ULift.{u} (Fin (derivedFiberBetti S E j (U.ι x))))))
    (e : (SheafOfModules.overFunctor.{u}
      (moduleRings S.toRingedSpace) O).mapDerivedCategory.obj E ≅ DerivedCategory.Q.obj P) :
    ∃ V : U.toScheme.Opens, x ∈ V ∧ IsAffine V.toScheme ∧
      ∃ K : CochainComplex
          (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace)) ℤ,
        (∃ c : ℤ, ∀ j : ℤ, c < j → IsZero (K.X j)) ∧
        (∀ j : ℤ, j < a → IsZero (K.X j)) ∧
        (∀ j : ℤ, Nonempty (K.X j ≅ SheafOfModules.free
          (R := moduleRings V.toScheme.toRingedSpace)
            (ULift.{u} (Fin (derivedFiberBetti S E j (U.ι x)))))) ∧
        Nonempty ((derivedPullback (V.ι ≫ U.ι)).obj E ≅
          DerivedCategory.Q.obj K) := by
  classical
  have _hO := hO
  have hbetti (j : ℤ) (hj : j < a) : derivedFiberBetti S E j (U.ι x) = 0 :=
    derivedFiberBetti_eq_zero_of_tensor_vanishes S E j (U.ι x)
      (fun F ↦ hamp F j (Or.inl hj))
  obtain ⟨V, hV, hxV, hsub⟩ :=
    exists_isAffineOpen_mem_and_subset (U := U.ι ⁻¹ᵁ O) hxO
  let f := V.ι ≫ U.ι
  have hf : Set.range f ⊆ Set.range O.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    exact hsub z.property
  let k := IsOpenImmersion.lift O.ι f hf
  have hk : k ≫ O.ι = f := IsOpenImmersion.lift_fac _ _ _
  have : IsOpenImmersion k := by
    apply IsOpenImmersion.of_comp k O.ι
  let A : SheafOfModules.{u} ((moduleRings S.toRingedSpace).over O) ⥤
      SheafOfModules.{u} (moduleRings O.toScheme.toRingedSpace) :=
    (Modules.overEquiv O).functor
  let R : SheafOfModules.{u} (moduleRings O.toScheme.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace) := openRestrict k
  let F := A ⋙ R
  let G := SheafOfModules.overFunctor.{u} (moduleRings S.toRingedSpace) O
  let K := (F.mapHomologicalComplex (.up ℤ)).obj P
  let Rf : SheafOfModules.{u} (moduleRings S.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace) := openRestrict f
  let θ : G ⋙ F ≅ Rf :=
    (Functor.associator G A R).symm ≪≫
      Functor.isoWhiskerRight (Modules.overFunctorEquiv O) R ≪≫
      (Modules.restrictFunctorComp k O.ι).symm ≪≫ Modules.restrictFunctorCongr hk
  obtain ⟨ef⟩ := derivedOpen_iso_restrict f E
  let ek : (derivedPullback f).obj E ≅ DerivedCategory.Q.obj K :=
    ef ≪≫ (Functor.mapDerivedCategoryNatIso θ).symm.app E ≪≫
      (Functor.mapDerivedCategoryCompIso G F).app E ≪≫
      F.mapDerivedCategory.mapIso e ≪≫ F.mapDerivedCategoryFactors.app P
  refine ⟨V, hxV, hV, K, ?_, ?_, ?_, ⟨ek⟩⟩
  · obtain ⟨c, d, hb⟩ := hbounded
    exact ⟨d, fun j hj ↦ F.map_isZero (hb j (Or.inr hj))⟩
  · intro j hj
    obtain ⟨ej⟩ := hrank j
    have hz : IsZero (SheafOfModules.free
        (R := (moduleRings S.toRingedSpace).over O)
          (ULift.{u} (Fin (derivedFiberBetti S E j (U.ι x))))) := by
      rw [hbetti j hj, IsZero.iff_id_eq_zero]
      apply (SheafOfModules.freeHomEquiv _).injective
      ext z
      exact Fin.elim0 z.down
    exact F.map_isZero (hz.of_iso ej)
  · intro j
    exact ⟨F.mapIso (hrank j).some ≪≫ R.mapIso
      (SheafOfModules.mapFreeIso A _ (Modules.overEquivFunctorObjUnitIso O)).symm ≪≫
        Modules.restrictFreeIso k _⟩

end AlgebraicGeometry.Scheme
