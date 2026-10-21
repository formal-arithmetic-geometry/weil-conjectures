/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q34
-/
module

public import Sheaf.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
public import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated
import Sheaf.AlgebraicGeometry.CoefficientTorFlatModel
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients

/-!
# Tensor cohomology segments and Tor intervals on the pro-etale site

Source: Stacks Project, Cohomology on Sites, Tag 08G2, lemma-cone-tor-amplitude (2),
and Tag 08FZ, definition-tor-amplitude.
(blueprint: lem-weil-proetale-tor-interval-triangle).

We use the recorded coefficient-sized model of the small pro-etale site, its ordinary
constant ring sheaf, and the existing K-flat derived tensor. Exactness of the two
cohomology maps is expressed by exactness of their short complex.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.Scheme

/-- The canonical module-sheaf abelian structure with all universe arguments fixed.
This only specializes Mathlib's existing instance and the published sheafification
instance, avoiding inference through an older successor-universe interface.
Source: Stacks Tags 03DA and 08G2
(blueprint: lem-weil-proetale-tor-interval-triangle). -/
instance coefficientProEtaleTorModulesAbelian (Y : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] :
    Abelian (ConstantCompletion.Mod.{max v (u + 1)}
      (ConstantCompletion.constant.{max v (u + 1)}
        (coefficientProEtaleModelTopology.{u, v} Y) A)) :=
  @SheafOfModules.instAbelian.{max v (u + 1), max v (u + 1),
    max v (u + 1), max v (u + 1)} _ _ _ _
    (coefficientModelAdditiveSheafify.{u, v} Y) inferInstance

/-- The published derived tensor with an arbitrary module sheaf in degree zero.
This is the existing K-flat tensor on the same small site as the Tor predicate;
it uses the standard derived localization, with no new choice of resolutions.
Source: Stacks Tags 06YU and 08G2
(blueprint: lem-weil-proetale-tor-interval-triangle). -/
def coefficientProEtaleTorTensor (Y : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A]
    (N : ConstantCompletion.Mod.{max v (u + 1)}
      (ConstantCompletion.constant.{max v (u + 1)}
        (coefficientProEtaleModelTopology.{u, v} Y) A)) :
    ConstantCompletion.D.{max v (u + 1)}
      (ConstantCompletion.constant.{max v (u + 1)}
        (coefficientProEtaleModelTopology.{u, v} Y) A) ⥤
    ConstantCompletion.D.{max v (u + 1)}
      (ConstantCompletion.constant.{max v (u + 1)}
        (coefficientProEtaleModelTopology.{u, v} Y) A) :=
  let R := ConstantCompletion.constant.{max v (u + 1)} (coefficientProEtaleModelTopology.{u, v} Y) A
  letI := HasDerivedCategory.standard (ConstantCompletion.Mod.{max v (u + 1)} R)
  (Functor.curry.obj
    (SheafOfModules.siteDerivedTensorIndependentCoefficients.{max v (u + 1),
      max v (u + 1), max v (u + 1), (max v (u + 1)) + 1} _ R)).flip.obj
    ((DerivedCategory.singleFunctor (ConstantCompletion.Mod.{max v (u + 1)} R) 0).obj N)

/-- Tensor cohomology is exact at the middle vertex, and Tor intervals of the two
outside vertices give their minimum/maximum interval for the middle vertex.
The last clause spells out the common-interval specialization; it does not assert
optimality of the endpoints.

Source: Stacks Tag 08G2, lemma-cone-tor-amplitude (2), and Tag 08FZ
(blueprint: lem-weil-proetale-tor-interval-triangle).

Proof plan:
1. Fix a module sheaf N. By lem-pc-kflat-resolution choose a flat-term K-flat
   resolution P of N[0]. By lem-weil-pbc-kflat-fixed-tensor-triangulated, tensoring
   with P descends to an exact functor, with its signed shift comparison. For each
   complex K choose a flat-term K-flat resolution P_K. The two quasi-isomorphisms
   from P_K tensor P to P_K tensor N[0] and to K tensor P identify this functor
   with the recorded derived tensor; lem-weil-derived-tensor-resolution-independent
   makes the identification independent of the resolution. Thus it sends the given
   distinguished triangle to a distinguished triangle, including its last arrow.
2. Apply lem-sf-derived-homology-long-exact to that tensor triangle. Its degree-i
   segment is exact, meaning that the image subobject of the first map equals the
   kernel subobject of the second map. These are the cohomology sheaves of
   def-weil-derived-cohomology-sheaves, computed by the standard homology functor.
3. Put c = min(a_U,a_W) and d = max(b_U,b_W). The ordered outside intervals give
   c <= d. For i < c or d < i, both outside cohomology sheaves vanish by
   def-weil-proetale-tor-amplitude, for every N. Exactness forces the middle sheaf
   to vanish as well. This is precisely Tor amplitude in [c,d].
4. Set a_U = a_W = a and b_U = b_W = b. The minimum and maximum are a and b,
   respectively, giving the last clause. No finiteness or constructibility is used.
-/
theorem coefficientProEtale_tor_interval_triangle (Y : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A]
    (T : Triangle (ConstantCompletion.D.{max v (u + 1)}
      (ConstantCompletion.constant.{max v (u + 1)}
        (coefficientProEtaleModelTopology.{u, v} Y) A)))
    (hT : T ∈ distTriang (ConstantCompletion.D.{max v (u + 1)}
      (ConstantCompletion.constant.{max v (u + 1)}
        (coefficientProEtaleModelTopology.{u, v} Y) A))) :
    (∀ (N : ConstantCompletion.Mod.{max v (u + 1)}
        (ConstantCompletion.constant.{max v (u + 1)}
        (coefficientProEtaleModelTopology.{u, v} Y) A))
      (i : ℤ),
      ∃ h : (((coefficientProEtaleTorTensor Y A N) ⋙
          coefficientModelCohomology.{max v (u + 1)}
            (ConstantCompletion.constant.{max v (u + 1)}
              (coefficientProEtaleModelTopology.{u, v} Y) A) i).map T.mor₁) ≫
          (((coefficientProEtaleTorTensor Y A N) ⋙
            coefficientModelCohomology.{max v (u + 1)}
              (ConstantCompletion.constant.{max v (u + 1)}
                (coefficientProEtaleModelTopology.{u, v} Y) A) i).map T.mor₂) = 0,
        (ShortComplex.mk
          (((coefficientProEtaleTorTensor Y A N) ⋙
            coefficientModelCohomology.{max v (u + 1)}
              (ConstantCompletion.constant.{max v (u + 1)}
                (coefficientProEtaleModelTopology.{u, v} Y) A) i).map T.mor₁)
          (((coefficientProEtaleTorTensor Y A N) ⋙
            coefficientModelCohomology.{max v (u + 1)}
              (ConstantCompletion.constant.{max v (u + 1)}
                (coefficientProEtaleModelTopology.{u, v} Y) A) i).map T.mor₂) h).Exact) ∧
    (∀ (aU bU aW bW : ℤ), aU ≤ bU → aW ≤ bW →
      HasCoefficientProEtaleTorAmplitude Y A T.obj₁ aU bU →
      HasCoefficientProEtaleTorAmplitude Y A T.obj₃ aW bW →
      HasCoefficientProEtaleTorAmplitude Y A T.obj₂ (min aU aW) (max bU bW)) ∧
    (∀ (a b : ℤ), a ≤ b →
      HasCoefficientProEtaleTorAmplitude Y A T.obj₁ a b →
      HasCoefficientProEtaleTorAmplitude Y A T.obj₃ a b →
      HasCoefficientProEtaleTorAmplitude Y A T.obj₂ a b) := by
  let R := ConstantCompletion.constant.{max v (u + 1)}
    (coefficientProEtaleModelTopology.{u, v} Y) A
  let M := ConstantCompletion.Mod.{max v (u + 1)} R
  let := HasDerivedCategory.standard M
  let B := SheafOfModules.KFlatFixedTensor.derivedTensor.{max v (u + 1),
    max v (u + 1), max v (u + 1), (max v (u + 1)) + 1} R
  obtain ⟨s, hs⟩ := SheafOfModules.KFlatFixedTensor.kFlat_fixed_tensor_triangulated.{max v (u + 1),
    max v (u + 1), max v (u + 1), (max v (u + 1)) + 1} R
  let : B.CommShift₂Int := s
  let F (N : M) := B.flip.obj ((DerivedCategory.singleFunctor M 0).obj N)
  have flatSite (S : ConstantCompletion.Cx R)
      (hf : ∀ n, SheafOfModules.IsFlat (R := R) (S.X n)) :
      ∀ n, SheafOfModules.IsFlatOnSite (J := coefficientProEtaleModelTopology.{u, v} Y)
        (R := R) (S.X n) := by
    intro n
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R (S.X n)).symm (hf n)
  have htri (N : M) : (F N).IsTriangulated := by
    obtain ⟨P, hp, hf, ⟨e⟩⟩ := exists_coefficientModelFlatKFlatRepresentative R
      ((DerivedCategory.singleFunctor M 0).obj N)
    have := (hs P hp (flatSite P hf)).2.2.1.2
    have : NatTrans.CommShift (B.flip.mapIso e).hom ℤ := by
      change NatTrans.CommShift (B.flip.map e.hom) ℤ
      exact Functor.CommShift₂.commShift_flip_map e.hom
    exact Functor.isTriangulated_of_iso (B.flip.mapIso e)
  have htest (K : ConstantCompletion.D R) (S : ConstantCompletion.Cx R)
      (hk : S.IsKFlatIndependentCoefficients)
      (hf : ∀ n, SheafOfModules.IsFlat (R := R) (S.X n))
      (e : (ConstantCompletion.Q R).obj S ≅ K) (N : M) (i : ℤ) :
      Nonempty (((F N) ⋙ coefficientModelCohomology.{max v (u + 1)} R i).obj K ≅
        coefficientModelTensorTest R S N i) := by
    obtain ⟨c, _, _⟩ := (hs S hk (flatSite S hf)).2.2.2.1
    let d : (F N).obj K ≅
        (ConstantCompletion.Q R).obj
          (((ringedKoszulTensor R).obj S).obj
            ((HomologicalComplex.single M (.up ℤ) 0).obj N)) :=
      (B.flip.obj ((DerivedCategory.singleFunctor M 0).obj N)).mapIso e.symm ≪≫
        (B.obj ((ConstantCompletion.Q R).obj S)).mapIso
          ((DerivedCategory.singleFunctorIsoCompQ M 0).app N) ≪≫
        (c.app ((HomologicalComplex.single M (.up ℤ) 0).obj N)).symm
    exact ⟨(coefficientModelCohomology.{max v (u + 1)} R i).mapIso d ≪≫
      (DerivedCategory.homologyFunctorFactors M i).app _⟩
  have hamp (K : ConstantCompletion.D R) (a b : ℤ) :
      HasCoefficientModelTorAmplitude R K a b ↔
        a ≤ b ∧ ∀ (N : M) (i : ℤ), i < a ∨ b < i →
          IsZero (((F N) ⋙
            coefficientModelCohomology.{max v (u + 1)} R i).obj K) := by
    constructor
    · intro h
      refine ⟨h.1, ?_⟩
      intro N i hi
      obtain ⟨S, hk, hf, ⟨e⟩⟩ := exists_coefficientModelFlatKFlatRepresentative R K
      obtain ⟨d⟩ := htest K S hk hf e N i
      exact (h.2 S hk ⟨e⟩ N i hi).of_iso d
    · rintro ⟨hab, h⟩
      refine ⟨hab, ?_⟩
      intro P hp ⟨eP⟩ N i hi
      obtain ⟨S, hk, hf, ⟨eS⟩⟩ := exists_coefficientModelFlatKFlatRepresentative R K
      obtain ⟨d⟩ := htest K S hk hf eS N i
      obtain ⟨c⟩ := coefficientModelTensorTest_iso R P S hp hk (eP ≪≫ eS.symm) N i
      exact ((h N i hi).of_iso d.symm).of_iso c
  have hexact (N : M) (i : ℤ) :
      ∃ h : (((F N) ⋙ coefficientModelCohomology.{max v (u + 1)} R i).map
          T.mor₁) ≫
          (((F N) ⋙ coefficientModelCohomology.{max v (u + 1)} R i).map
            T.mor₂) = 0,
        (ShortComplex.mk _ _ h).Exact := by
    have := htri N
    have hFT := (F N).map_distinguished T hT
    refine ⟨?_, DerivedCategory.HomologySequence.exact₂ ((F N).mapTriangle.obj T) hFT i⟩
    let H := DerivedCategory.homologyFunctor M i
    let U := (F N).mapTriangle.obj T
    change H.map U.mor₁ ≫ H.map U.mor₂ = 0
    exact (H.map_comp U.mor₁ U.mor₂).symm.trans
      ((congrArg H.map (comp_distTriang_mor_zero₁₂ U hFT)).trans (H.map_zero _ _))
  have hinterval (aU bU aW bW : ℤ) (hU : aU ≤ bU) (_hW : aW ≤ bW)
      (hTU : HasCoefficientProEtaleTorAmplitude Y A T.obj₁ aU bU)
      (hTW : HasCoefficientProEtaleTorAmplitude Y A T.obj₃ aW bW) :
      HasCoefficientProEtaleTorAmplitude Y A T.obj₂ (min aU aW) (max bU bW) := by
    apply (hamp _ _ _).2
    refine ⟨le_trans (min_le_left _ _) (le_trans hU (le_max_left _ _)), ?_⟩
    intro N i hi
    have hiU : i < aU ∨ bU < i := by omega
    have hiW : i < aW ∨ bW < i := by omega
    have hzU := ((hamp _ _ _).1 hTU).2 N i hiU
    have hzW := ((hamp _ _ _).1 hTW).2 N i hiW
    obtain ⟨h, he⟩ := hexact N i
    exact he.isZero_X₂ (hzU.eq_of_src _ _) (hzW.eq_of_tgt _ _)
  exact ⟨hexact, hinterval, fun a b hab hU hW ↦ by
    simpa only [min_self, max_self] using hinterval a b a b hab hab hU hW⟩

end AlgebraicGeometry.Scheme
