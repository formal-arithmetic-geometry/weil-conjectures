/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBase
public import Sheaf.AlgebraicGeometry.TensorPullback
import Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties
import Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBaseUnionPreimage
import Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Sheaf.AlgebraicGeometry.ModuleSupportProperOverBase
import Sheaf.AlgebraicGeometry.GrothendieckExistenceSupportedHom
import Sheaf.AlgebraicGeometry.GrothendieckExistenceSystemSupport
import Sheaf.AlgebraicGeometry.GrothendieckExistenceSupportedSystem
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.Curve.DivisorIdealSheaf

/-!
# Grothendieck existence with proper support

Source: Stacks Project, Cohomology of Schemes, Theorem 088E and Remark 088F,
with indices shifted by one (blueprint: prop-weil-pbc-grothendieck-existence).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Full faithfulness and algebraization for coherent modules with proper support.
Source: Stacks Project, Tags 088E and 088F.
The two projection equations specify the canonical transition immersion `i n` uniquely.
The comparison `c n` is the chosen composition comparison of tensor pullback, transported
along `hi n`; it is natural in the module. No independent comparison data is assumed.

Proof plan (Stacks 088E, in the form 088F):
1. X is Noetherian by pqf-lem-locnoeth-lft since it is finite type over Noetherian A.
   Use lem-weil-pbc-thickening-systems-dictionary to translate systems, morphisms and
   algebraizations into formal coherent modules and completion.
2. Full faithfulness: place both modules on a common closed subscheme proper over A by
   lem-weil-pbc-module-support-proper-over-base and the closed-immersion equivalence.
   Apply lem-weil-pbc-formal-completion-fully-faithful-proper on that subscheme.
3. Existence reduces to supporting the system on a closed subscheme proper over A;
   then prop-weil-pbc-grothendieck-existence-proper and the same equivalence algebraize it.
4. The empty scheme has only the zero system, which is algebraized by the zero module.
   Otherwise, by lem-weil-pbc-noetherian-acc-quasi-coherent choose a maximal failing
   annihilator and replace X by its closed subscheme. Every nonzero ideal then satisfies
   the claim.
5. Use lem-weil-pbc-chow-noetherian and lem-chow-closed-model for a proper modification Y,
   an isomorphism over a dense open U, and a projective compactification Y'.
6. Pull back and extend the system using lem-weil-pbc-formal-systems-pullback,
   lem-weil-pbc-support-pullback-finite-type and lem-weil-pbc-pushforward-coherent-on-open.
   Supports equal that of the first term, so the extension remains coherent on Y'.
7. Apply lem-weil-pbc-grothendieck-existence-projective. Its algebraization is supported
   inside Y: otherwise its proper image has a nonempty closed subset avoiding V(I),
   contradicting lem-weil-pbc-adic-complete-jacobson-radical. Restrict to Y.
8. Use lem-weil-pbc-reduced-induced-closed-subscheme on X minus U and
   lem-weil-pbc-formal-systems-push-pull to compare with the coherent proper pushforward.
   Kernel and cokernel are annihilated by a power of the complement ideal; they exist by
   lem-weil-pbc-coherent-formal-modules-abelian.
9. The pushforward has support in the proper image of the support on Y by
   lem-weil-pbc-closed-subset-proper-over-base-properties and
   lem-weil-pbc-closed-subset-proper-over-base-union-preimage.
10. The complement ideal has nonzero powers since its vanishing locus misses the dense U.
    Induction supports the kernel and cokernel on proper closed subschemes. Conclude for
    the system by lem-weil-pbc-formal-systems-proper-support-serre.
(blueprint: prop-weil-pbc-grothendieck-existence). -/
theorem grothendieck_existence
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) [IsAdicComplete I A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (i : ∀ n : ℕ, pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))) ⟶
      pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))
    (hi : ∀ n : ℕ, i n ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n
      + 1 + 1))))) = pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n +
      1))))))
    (hp : ∀ n : ℕ, i n ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n
      + 1 + 1))))) = pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n +
      1))))) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.pow_le_pow_right (I :=
      I) (Nat.le_succ (n + 1))))))
    (c : ∀ n : ℕ, Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (I ^ (n + 1 + 1)))))) ⋙ Scheme.Modules.tensorPullback (i n) ≅
      Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (I ^ (n + 1)))))))
    (hc : ∀ n : ℕ, c n = (Classical.choice (Scheme.Modules.nonempty_tensorPullbackComp (i n)
      (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 +
      1)))))))).symm ≪≫ eqToIso (congrArg Scheme.Modules.tensorPullback (hi n))) :
    (∀ (F G : X.Modules),
    RingedSpace.IsCoherent X.toRingedSpace F →
    RingedSpace.IsCoherent X.toRingedSpace G →
    Scheme.Modules.HasSupportProperOver f F →
    Scheme.Modules.HasSupportProperOver f G →
    ∀ (v : ∀ n : ℕ, (Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (I ^ (n + 1))))))).obj G ⟶ (Scheme.Modules.tensorPullback (pullback.fst
      f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))).obj F),
    (∀ n : ℕ, (c n).hom.app G ≫ v n = (Scheme.Modules.tensorPullback (i n)).map (v (n + 1)) ≫ (c
      n).hom.app F) →
    ∃! w : G ⟶ F, ∀ n : ℕ, (Scheme.Modules.tensorPullback (pullback.fst f (Spec.map
      (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))).map w = v n) ∧
    (∀ (F : ∀ n : ℕ, (pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n +
      1)))))).Modules)
    (φ : ∀ n : ℕ, (Scheme.Modules.tensorPullback (i n)).obj (F (n + 1)) ≅ F n),
    (∀ n : ℕ, RingedSpace.IsCoherent (pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
      (I ^ (n + 1)))))).toRingedSpace (F n)) →
    Scheme.Modules.HasSupportProperOver (pullback.snd f (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (I ^ (0 + 1)))))) (F 0) →
    ∃ G : X.Modules, RingedSpace.IsCoherent X.toRingedSpace G ∧
    Scheme.Modules.HasSupportProperOver f G ∧
    ∃ ψ : ∀ n : ℕ, (Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (I ^ (n + 1))))))).obj G ≅ F n,
    ∀ n : ℕ, (Scheme.Modules.tensorPullback (i n)).map (ψ (n + 1)).hom ≫ (φ n).hom = (c
      n).hom.app G ≫ (ψ n).hom) := by
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
  constructor
  · intro F G hF hG hproperF hproperG v hv
    obtain ⟨hFqc, hFft⟩ :=
      (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X F).mp hF
    obtain ⟨hGqc, hGft⟩ :=
      (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X G).mp hG
    let := hFqc
    let := hFft
    let := hGqc
    let := hGft
    obtain ⟨ZF, jF, hjF, hpF, hkF, _⟩ :=
      (Scheme.Modules.module_support_proper_over_base f F).2.1.mp hproperF
    obtain ⟨ZG, jG, hjG, hpG, hkG, _⟩ :=
      (Scheme.Modules.module_support_proper_over_base f G).2.1.mp hproperG
    let := hjF
    let := hjG
    let := hpF
    let := hpG
    have hclosedF : IsClosed (Set.range jF) := jF.isClosedMap.isClosed_range
    have hclosedG : IsClosed (Set.range jG) := jG.isClosedMap.isClosed_range
    have hrF : Set.range jF.base = (jF.ker.support : Set X) := by
      rw [jF.support_ker, hclosedF.closure_eq]
    have hrG : Set.range jG.base = (jG.ker.support : Set X) := by
      rw [jG.support_ker, hclosedG.closure_eq]
    have hsF : Scheme.IsClosedSubsetProperOver f jF.ker.support :=
      (Scheme.closed_subset_proper_over_base_properties f jF.ker.support).1.mpr
        ⟨ZF, jF, hjF, hrF, hpF⟩
    have hsG : Scheme.IsClosedSubsetProperOver f jG.ker.support :=
      (Scheme.closed_subset_proper_over_base_properties f jG.ker.support).1.mpr
        ⟨ZG, jG, hjG, hrG, hpG⟩
    have hsup : Scheme.IsClosedSubsetProperOver f (jF.ker.support ⊔ jG.ker.support) := by
      let Z : Fin 2 → TopologicalSpace.Closeds X :=
        fun n ↦ Fin.cases jF.ker.support (fun _ ↦ jG.ker.support) n
      have h := (Scheme.isClosedSubsetProperOver_union_preimage f).1 2 Z (by
          intro n
          fin_cases n
          · exact hsF
          · exact hsG)
      have heq : ⨆ n, Z n = jF.ker.support ⊔ jG.ker.support := by
        apply le_antisymm
        · apply iSup_le
          intro n
          fin_cases n
          · exact le_sup_left
          · exact le_sup_right
        · apply sup_le
          · exact le_iSup Z 0
          · exact le_iSup Z 1
      rw [← heq]
      exact h
    let K : X.IdealSheafData := jF.ker * jG.ker
    have hproperK : Scheme.IsClosedSubsetProperOver f K.support := by
      simpa [K, Scheme.IdealSheafData.support_mul] using hsup
    have hpK : IsProper (K.subschemeι ≫ f) :=
      (Scheme.closed_subset_proper_over_base_properties f K.support).2.1.mp
        hproperK K.subscheme K.subschemeι (Scheme.IdealSheafData.range_subschemeι K)
    have : IsProper (K.subschemeι ≫ f) := hpK
    have hleF : K ≤ jF.ker := by
      intro U
      exact Ideal.mul_le_left
    have hleG : K ≤ jG.ker := by
      intro U
      exact Ideal.mul_le_right
    have hkKF : ∀ (V : X.Opens) (a : Γ(X, V)),
        a ∈ K.subschemeι.ker.idealOfOpens V → ∀ t : Γ(F, V), a • t = 0 := by
      intro V a ha t
      have hmem : a ∈ K.idealOfOpens V := by simpa using ha
      exact hkF V a (Scheme.IdealSheafData.idealOfOpens_mono hleF V hmem) t
    have hkKG : ∀ (V : X.Opens) (a : Γ(X, V)),
        a ∈ K.subschemeι.ker.idealOfOpens V → ∀ t : Γ(G, V), a • t = 0 := by
      intro V a ha t
      have hmem : a ∈ K.idealOfOpens V := by simpa using ha
      exact hkG V a (Scheme.IdealSheafData.idealOfOpens_mono hleG V hmem) t
    have hb := grothendieckExistence_supported_hom A I f i hi hp c hc
      F G hF hG K.subscheme K.subschemeι hkKF hkKG
    obtain ⟨w, hw⟩ := hb.surjective ⟨v, hv⟩
    refine ⟨w, ?_, ?_⟩
    · intro n
      exact congrArg (fun t ↦ t.val n) hw
    · intro w' hw'
      apply hb.injective
      apply Subtype.ext
      funext n
      exact (hw' n).trans (congrArg (fun t ↦ t.val n) hw).symm
  · intro F φ hF hproper
    obtain ⟨Z, j, hj, hpj, hkill⟩ :=
      grothendieckExistence_system_support A I f i hi hp F φ hF hproper
    let := hj
    let := hpj
    exact grothendieckExistence_supported_system A I f i hi hp c hc F φ hF Z j hkill

end AlgebraicGeometry
