/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase
public import WeilConjectures.AlgebraicGeometry.TensorPullback
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseUnionPreimage
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.ModuleSupportProperOverBase
import WeilConjectures.AlgebraicGeometry.GrothendieckExistenceSupportedHom
import WeilConjectures.AlgebraicGeometry.GrothendieckExistenceSystemSupport
import WeilConjectures.AlgebraicGeometry.GrothendieckExistenceSupportedSystem
import WeilConjectures.AlgebraicGeometry.Curve.DivisorIdealSheaf
import WeilConjectures.AlgebraicGeometry.ThickeningSystemsDictionary

/-!
# Grothendieck existence with proper support

## Implementation details

Indices are shifted by one relative to the Stacks Project.

## References

* [Stacks Project, Cohomology of Schemes, Tags 088E, 088F]
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A map out of a composite left adjoint is determined by the composite of the two units
followed by an isomorphism of the right adjoints and the map. -/
private theorem eq_of_comp_unit_eq {C D E : Type*} [Category C] [Category D] [Category E]
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} (a₁ : L₁ ⊣ R₁) {L₂ : D ⥤ E} {R₂ : E ⥤ D} (a₂ : L₂ ⊣ R₂)
    {R : E ⥤ C} (e : R₂ ⋙ R₁ ≅ R) (G : C) {H : E} (x y : L₂.obj (L₁.obj G) ⟶ H)
    (h : a₁.unit.app G ≫ R₁.map (a₂.unit.app (L₁.obj G)) ≫ e.hom.app _ ≫ R.map x =
      a₁.unit.app G ≫ R₁.map (a₂.unit.app (L₁.obj G)) ≫ e.hom.app _ ≫ R.map y) : x = y := by
  rw [← e.hom.naturality x, ← e.hom.naturality y] at h
  simp only [← Category.assoc] at h
  have h' := (cancel_mono (e.hom.app H)).1 h
  apply ((a₁.comp a₂).homEquiv _ _).injective
  simpa only [Adjunction.homEquiv_unit, Adjunction.comp_unit_app, Functor.comp_map,
    Category.assoc] using h'


/-- Full faithfulness in Grothendieck existence: for any comparison `c` of the iterated and the
direct pullbacks to the thickenings, a family of maps on the thickenings compatible with `c`
between coherent modules with proper support comes from a unique map of modules.
(Stacks, Tags 088E and 088F) -/
theorem grothendieck_existence_fullyFaithful
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
      (Ideal.Quotient.mk (I ^ (n + 1))))))) :
    ∀ (F G : X.Modules),
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
      (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))).map w = v n := by
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
  intro F G hF hG hproperF hproperG v hv
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
  have hb := grothendieckExistence_supported_hom A I f i hi hp c
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

/-- Full faithfulness and algebraization for coherent modules with proper support.
The two projection equations specify the canonical transition immersion `i n` uniquely.
The adjunctions `ai n`, `aj n` are choices of the tensor-pullback adjunctions; the comparison
`c n` is the one they determine by its unit equation (part of the conclusion), and both
halves of the theorem are stated for it. No independent comparison data is assumed.
(Stacks, Tags 088E and 088F) -/
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
    (ai : ∀ n : ℕ, Scheme.Modules.tensorPullback (i n) ⊣ Scheme.Modules.pushforward (i n))
    (aj : ∀ n : ℕ, Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (I ^ (n + 1)))))) ⊣
      Scheme.Modules.pushforward (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (I ^ (n + 1))))))) :
    ∃ c : ∀ n : ℕ, Scheme.Modules.tensorPullback (pullback.fst f (Spec.map
        (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1)))))) ⋙
        Scheme.Modules.tensorPullback (i n) ≅
      Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (I ^ (n + 1)))))),
    (∀ (G : X.Modules) (n : ℕ),
      (aj (n + 1)).unit.app G ≫
        (Scheme.Modules.pushforward (pullback.fst f (Spec.map (CommRingCat.ofHom
            (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))).map
          ((ai n).unit.app
            ((Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
                (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))).obj G)) ≫
        (Scheme.Modules.pushforwardComp (i n) (pullback.fst f (Spec.map (CommRingCat.ofHom
            (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))).hom.app
          ((Scheme.Modules.tensorPullback (i n)).obj
            ((Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
                (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))).obj G)) ≫
        (Scheme.Modules.pushforwardCongr (hi n)).hom.app
          ((Scheme.Modules.tensorPullback (i n)).obj
            ((Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
                (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))).obj G)) ≫
        (Scheme.Modules.pushforward (pullback.fst f (Spec.map (CommRingCat.ofHom
            (Ideal.Quotient.mk (I ^ (n + 1))))))).map ((c n).hom.app G) =
      (aj n).unit.app G) ∧
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
  obtain ⟨_, _, _, _, _, _, c, _, _, _, hcu, -⟩ := thickeningSystems_dictionary f I i hi hp ai aj
  refine ⟨c, hcu, grothendieck_existence_fullyFaithful A I f i hi hp c, ?_⟩
  intro F φ hF hproper
  obtain ⟨Z, j, hj, hpj, hkill⟩ :=
    grothendieckExistence_system_support A I f i hi hp F φ hF hproper
  let := hj
  let := hpj
  obtain ⟨c', hc', G, hG, hpG, ψ, hψ⟩ :=
    grothendieckExistence_supported_system A I f i hi hp ai aj F φ hF Z j hkill
  obtain rfl : c' = c := funext fun n ↦ Iso.ext <| NatTrans.ext <| funext fun M ↦
    eq_of_comp_unit_eq (aj (n + 1)) (ai n)
      (Scheme.Modules.pushforwardComp (i n) _ ≪≫ Scheme.Modules.pushforwardCongr (hi n)) M _ _
      (by simpa only [Iso.trans_hom, NatTrans.comp_app, Category.assoc] using
        (hc' M n).trans (hcu M n).symm)
  exact ⟨G, hG, hpG, ψ, hψ⟩

end AlgebraicGeometry
