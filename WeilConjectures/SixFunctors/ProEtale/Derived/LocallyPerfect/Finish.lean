/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Flat.EquationalCriterion
public import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.SixFunctors.ProEtale.Derived.LocallyPerfect.Defs

/-!
# A complex with a deep perfect top part and finite Tor amplitude is perfect

This is the last step of Stacks, Tag 0FPV, in the form used for `D(Y_proét, Λ)` (compare
Stacks, Tag 08G7). Let `K ≅ Q(M)` have Tor amplitude in `[a, b]`, and let `j : P₀ ⟶ M` be a
degreewise monomorphism from the constant complex `P₀ = c(E₀)` attached to a bounded complex
`E₀` of finite free modules vanishing below `m`, which is an isomorphism in degrees `≥ m`, where
`m + 2 ≤ a`. The cokernel of `j` vanishes in degrees `≥ m`, so the derived tensor product with
any sheaf `F` shows that `H^{m+1}(P₀ ⊗ F)` injects into `H^{m+1}(K ⊗ᴸ F) = 0`. By the Tor
criterion `CategoryTheory.ObjectProperty.flat_opcycles_of_exactAt`, the cokernel `B` of
`P₀^{m+1} ⟶ P₀^{m+2}` is flat. Since `K` vanishes below `m + 2`, it is represented by the
truncation `τ^{≥ m+2} P₀`, whose terms are `B` and the finite free sheaves `P₀^i` for
`i > m + 2`. Finally `B = c(coker d)` is the constant sheaf of a finitely presented module, which
is flat (`AlgebraicGeometry.ProEtale.flat_of_flat_constantSheaf`), hence projective, so `B` is
dualizable.

## Main results

- `AlgebraicGeometry.ProEtale.flat_of_flat_constantSheaf`: over a nonempty scheme, a module
  whose constant sheaf is flat is flat.
- `AlgebraicGeometry.ProEtale.exists_iso_Q_obj_of_hasPerfectTop`: the step described above.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite MonoidalCategory Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open _root_.AlgebraicGeometry.Scheme

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- Over a nonempty scheme, the constant sheaf functor is faithful. -/
lemma faithful_constantSheaf (Y : Scheme.{u}) [Nonempty Y] :
    (constantSheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)).Faithful :=
  ⟨fun h ↦ constantSheaf_map_injective h⟩

/-- Over a nonempty scheme, a `Λ`-module whose constant pro-étale sheaf is flat is flat: the
constant sheaf functor is monoidal, exact and faithful. -/
lemma flat_of_flat_constantSheaf {Y : Scheme.{u}} [Nonempty Y] (B : ModuleCat.{u + 1} Λ)
    (h : ObjectProperty.flat ((constantSheaf (Scheme.ProEt.topology Y)
      (ModuleCat.{u + 1} Λ)).obj B)) : Module.Flat Λ B := by
  let c := constantSheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)
  have := faithful_constantSheaf (Λ := Λ) Y
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap'.{u + 1}]
  intro N N' _ _ _ _ f hf
  let f' : ModuleCat.of Λ N ⟶ ModuleCat.of Λ N' := ModuleCat.ofHom f
  have : Mono f' := (ModuleCat.mono_iff_injective _).2 hf
  have : Mono (c.obj B ◁ c.map f') := h.tensorLeft.1.preservesMonomorphisms.map_mono _
  have : Mono (c.map (B ◁ f')) := by
    rw [Functor.Monoidal.map_whiskerLeft]
    infer_instance
  have : Mono (B ◁ f') := c.mono_of_mono_map this
  exact (ModuleCat.mono_iff_injective _).1 this

/-- A zero sheaf is dualizable. -/
lemma isDualizable_of_isZero {Y : Scheme.{u}}
    {F : Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)} (hF : IsZero F) :
    IsDualizable F :=
  have h : IsZero ((constantSheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)).obj
      (ModuleCat.of Λ PUnit)) :=
    (constantSheaf _ _).map_isZero (ModuleCat.isZero_of_subsingleton _)
  (isDualizable_constantSheaf_obj (ModuleCat.of Λ PUnit)).of_iso (h.iso hF)

open _root_.DerivedCategory in
/-- **The last step of Stacks, Tag 0FPV.** Let `Λ` be Noetherian and `Y` nonempty. If
`K ∈ D(Y_proét, Λ)` has Tor amplitude in `[a, b]` and a perfect top part in degrees `≥ m`, with
`m + 2 ≤ a`, then `K` is represented by a bounded complex of dualizable sheaves. -/
theorem exists_iso_Q_obj_of_hasPerfectTop [IsNoetherianRing Λ] {Y : Scheme.{u}} [Nonempty Y]
    {a b m : ℤ}
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))}
    (hK : torAmplitudeIn (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)) a b K)
    (h : HasPerfectTop K m) (hm : m + 2 ≤ a) :
    ∃ (P : CochainComplex (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)) ℤ) (a' b' : ℤ),
      P.IsStrictlyGE a' ∧ P.IsStrictlyLE b' ∧ (∀ n, IsDualizable (P.X n)) ∧
        Nonempty (K ≅ Q.obj P) := by
  obtain ⟨M, E₀, j, B, ⟨e⟩, hj, hj', hE, hE', hfree⟩ := h
  let C := Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)
  let c := constantSheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)
  let P₀ := (c.mapHomologicalComplex (.up ℤ)).obj E₀
  have hP₀ (i : ℤ) : IsDualizable (P₀.X i) := by
    obtain ⟨_, _⟩ := hfree i
    exact isDualizable_constantSheaf_obj _
  have hP₀flat (i : ℤ) : ObjectProperty.flat (P₀.X i) := ObjectProperty.flat_of_isDualizable (hP₀ i)
  have : P₀.IsStrictlyGE m := by
    rw [CochainComplex.isStrictlyGE_iff]
    exact fun i hi ↦ c.map_isZero (E₀.isZero_of_isStrictlyGE m i hi)
  have : P₀.IsStrictlyLE B := by
    rw [CochainComplex.isStrictlyLE_iff]
    exact fun i hi ↦ c.map_isZero (E₀.isZero_of_isStrictlyLE B i hi)
  have hPk := CochainComplex.kFlat_of_bounded_of_flat P₀ m B hP₀flat
  have hKGE : K.IsGE a := (homologyConcentratedIn_of_torAmplitudeIn hK).1
  -- the cokernel of `j` vanishes in degrees `≥ m`
  have : Mono j := HomologicalComplex.mono_of_mono_f _ hj
  have hS : (ShortComplex.mk j (cokernel.π j) (cokernel.condition j)).ShortExact :=
    { exact := ShortComplex.exact_cokernel j }
  have hCok : (cokernel j).IsStrictlyLE (m - 1) := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    have : IsIso (j.f i) := hj' i (by lia)
    exact (isZero_cokernel_of_epi (j.f i)).of_iso
      (PreservesCokernel.iso (HomologicalComplex.eval _ (.up ℤ) i) j)
  -- `H^{m+1}(P₀ ⊗ F)` injects into `H^{m+1}(K ⊗ᴸ F) = 0`
  have hex (F : C) :
      (((tensorRight F).mapHomologicalComplex (.up ℤ)).obj P₀).ExactAt (m + 2 - 1) := by
    obtain hm' : m + 2 - 1 = m + 1 := by lia
    rw [hm']
    let T := ((curriedTensor (DerivedCategory C)).flip.obj
      ((singleFunctor C 0).obj F)).mapTriangle.obj (triangleOfSES hS)
    have hT : T ∈ distTriang _ := Functor.map_distinguished _ _ (triangleOfSES_distinguished hS)
    let H := homologyFunctor C 0
    have hδ : H.homologySequenceδ T m (m + 1) rfl = 0 := by
      have : (Q.obj (cokernel j) ⊗ (singleFunctor C 0).obj F).IsLE (m - 1 + 0) :=
        isLE_tensor _ _ _ _
      exact IsZero.eq_of_src ((Q.obj (cokernel j) ⊗ (singleFunctor C 0).obj F).isZero_of_isLE
        (m - 1 + 0) m (by lia)) _ _
    have hmono := (H.homologySequence_mono_shift_map_mor₁_iff T hT m (m + 1) rfl).2 hδ
    have h₂ : IsZero ((H.shift (m + 1)).obj T.obj₂) := by
      have := (hK F).1
      have : (Q.obj M ⊗ (singleFunctor C 0).obj F).IsGE a :=
        TStructure.t.isGE_of_iso (whiskerRightIso e _) a
      exact (Q.obj M ⊗ (singleFunctor C 0).obj F).isZero_of_isGE a (m + 1) (by lia)
    have h₁ : IsZero ((H.shift (m + 1)).obj T.obj₁) := IsZero.of_mono _ h₂
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact h₁.of_iso ((homologyFunctor C (m + 1)).mapIso
      (QObjTensorSingleFunctorObjIso P₀ hPk F).symm ≪≫
        (homologyFunctorFactors C (m + 1)).app _).symm
  have hop := ObjectProperty.flat_opcycles_of_exactAt P₀ (m + 2) (hP₀flat _) (hP₀flat _) hex
  -- the opcycles in degree `m + 2` are dualizable
  have hB : IsDualizable (P₀.opcycles (m + 2)) := by
    let e₁ : P₀.opcycles (m + 2) ≅ c.obj (E₀.opcycles (m + 2)) :=
      (E₀.sc (m + 2)).mapOpcyclesIso c
    have : Module.Flat Λ (E₀.opcycles (m + 2)) :=
      flat_of_flat_constantSheaf _ (ObjectProperty.prop_of_iso _ e₁ hop)
    have := (hfree (m + 2)).2
    have : Module.Finite Λ (E₀.opcycles (m + 2)) :=
      Module.Finite.of_surjective (E₀.pOpcycles (m + 2)).hom
        ((ModuleCat.epi_iff_surjective _).1 inferInstance)
    have : Module.Projective Λ (E₀.opcycles (m + 2)) :=
      Module.Flat.projective_of_finitePresentation
    exact (isDualizable_constantSheaf_obj _).of_iso e₁.symm
  -- `K` is represented by the truncation `τ^{≥ m+2} P₀`
  have : M.IsGE (m + 2) := by
    rw [← isGE_Q_obj_iff]
    have : (Q.obj M).IsGE a := TStructure.t.isGE_of_iso e a
    exact TStructure.t.isGE_of_ge _ (m + 2) a hm
  have : QuasiIso (CochainComplex.truncGEMap j (m + 2)) := by
    rw [CochainComplex.quasiIso_truncGEMap_iff]
    intro i hi
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact HomologicalComplex.isIso_homologyMap_of_epi_of_isIso_of_mono j
      (CochainComplex.prev ℤ i) (CochainComplex.next ℤ i)
      (have := hj' (i - 1) (by lia); inferInstance) (hj' i (by lia)) (hj _)
  have : IsIso (Q.map (CochainComplex.truncGEMap j (m + 2))) := by
    rw [isIso_Q_map_iff_quasiIso (C := C)]
    infer_instance
  refine ⟨P₀.truncGE (m + 2), m + 2, B, inferInstance, ?_, fun n ↦ ?_,
    ⟨e ≪≫ asIso (Q.map (M.πTruncGE (m + 2))) ≪≫
      (asIso (Q.map (CochainComplex.truncGEMap j (m + 2)))).symm⟩⟩
  · rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    obtain hi' | rfl | hi' := lt_trichotomy i (m + 2)
    · exact CochainComplex.isZero_of_isStrictlyGE _ (m + 2) i hi'
    · exact (P₀.truncGEXIsoOpcycles i).isZero_iff.2
        (IsZero.of_epi (P₀.pOpcycles i) (P₀.isZero_of_isStrictlyLE B i hi))
    · exact (P₀.truncGEXIso (m + 2) i hi').isZero_iff.2 (P₀.isZero_of_isStrictlyLE B i hi)
  · obtain hn | rfl | hn := lt_trichotomy n (m + 2)
    · exact isDualizable_of_isZero (CochainComplex.isZero_of_isStrictlyGE _ (m + 2) n hn)
    · exact hB.of_iso (P₀.truncGEXIsoOpcycles n).symm
    · exact (hP₀ n).of_iso (P₀.truncGEXIso (m + 2) n hn).symm

end AlgebraicGeometry.ProEtale
