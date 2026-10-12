/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective

/-!
# Right derived functors of finite cohomological dimension on unbounded complexes

Let `F : C ⥤ D` be a left exact additive functor between abelian categories, where `C` has
enough injectives, with `R^q F = 0` for `q > N` (`Functor.HasRightCohomologicalDimensionLE`).
By dimension shifting along the short exact sequences of cycles, `F` sends a complex of
`F`-acyclic objects which is exact in degrees `> m` to a complex which is exact in degrees
`> m + N`, without any boundedness assumption
(`Functor.HasRightCohomologicalDimensionLE.exactAt_map_of_rightAcyclic`). In particular `F`
sends acyclic complexes of `F`-acyclic objects to acyclic complexes.

Consequently, on the unbounded derived category of a Grothendieck abelian category `C`:

* the unbounded right derived functor `R(F)` is computed by applying `F` termwise to any complex
  of `F`-acyclic objects (`Functor.isIso_rightDerivedFunctorUnit_app_of_rightAcyclic`);
* `R(F)` has cohomological amplitude at most `N`: it sends `D^{≤ m}` into `D^{≤ m + N}`
  (`Functor.HasRightCohomologicalDimensionLE.isLE_rightDerivedFunctor_obj`);
* if `F` commutes with coproducts and coproducts of injective objects are `F`-acyclic, then
  `R(F)` commutes with coproducts
  (`Functor.preservesColimitsOfShape_discrete_rightDerivedFunctor`).

The hypothesis on acyclic complexes is isolated as
`Functor.PreservesAcyclicityOfRightAcyclic`, since in geometric applications it is checked
locally on the target, where the cohomological dimension is finite.
-/

@[expose] public section

namespace CategoryTheory

open Limits ZeroObject

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [HasInjectiveResolutions C]
  [Abelian D]

namespace Functor

variable (F : C ⥤ D) [F.Additive]

/-- `F` has *right cohomological dimension at most `N`*: `R^q F X = 0` for every object `X` and
every `q > N`. -/
def HasRightCohomologicalDimensionLE (N : ℕ) : Prop :=
  ∀ (q : ℕ) (X : C), N < q → IsZero ((F.rightDerived q).obj X)

/-- `F` *preserves acyclicity of complexes of `F`-acyclic objects*: `F` sends every acyclic
cochain complex all of whose terms are `F`-acyclic to an acyclic complex. This holds for
bounded below complexes in general (`HomologicalComplex.Acyclic.map_of_rightAcyclic`), and for
unbounded ones if `F` has finite cohomological dimension
(`Functor.HasRightCohomologicalDimensionLE.preservesAcyclicityOfRightAcyclic`). -/
def PreservesAcyclicityOfRightAcyclic : Prop :=
  ∀ K : CochainComplex C ℤ, K.Acyclic → (∀ n, F.rightAcyclic (K.X n)) →
    ((F.mapHomologicalComplex _).obj K).Acyclic

variable {F}

/-- **Dimension shifting on unbounded complexes.** Let `F` be left exact of right cohomological
dimension at most `N`, and let `K` be a cochain complex of `F`-acyclic objects which is exact in
all degrees `> m`. Then `F(K)` is exact in all degrees `> m + N`.

For `n ≥ m` the sequences `0 ⟶ Zⁿ ⟶ Kⁿ ⟶ Zⁿ⁺¹ ⟶ 0` of cycles are short exact, so that
`R^{q+1} F Zⁿ⁺¹ ↪ R^{q+2} F Zⁿ`; hence `R^{q+1} F Zⁿ ↪ R^{q+1+N} F Z^{n-N} = 0` for
`n ≥ m + N`, and `F` keeps the sequences of cycles short exact from there on. -/
theorem HasRightCohomologicalDimensionLE.exactAt_map_of_rightAcyclic [PreservesFiniteLimits F]
    {N : ℕ} (hF : F.HasRightCohomologicalDimensionLE N) {K : CochainComplex C ℤ} (m : ℤ)
    (hK : ∀ n, m < n → K.ExactAt n) (hK' : ∀ n, F.rightAcyclic (K.X n)) (n : ℤ)
    (hn : m + N < n) :
    ((F.mapHomologicalComplex _).obj K).ExactAt n := by
  have hS (n : ℤ) (hn : m ≤ n) :=
    (hK (n + 1) (by lia)).shortExact_cyclesShortComplex (i := n) (by simp)
  -- `R^{q+1} F Zⁿ = 0` as soon as `n ≥ m + k` and `q + k ≥ N`
  have hZ (k : ℕ) : ∀ (n : ℤ), m + k ≤ n → ∀ q : ℕ, N ≤ q + k →
      IsZero ((F.rightDerived (q + 1)).obj (K.cycles n)) := by
    induction k with
    | zero => exact fun n _ q hq ↦ hF _ _ (by lia)
    | succ k ih =>
      intro n hn q hq
      obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by lia⟩
      obtain ⟨δ, w₁, w₂, h₁, h₂⟩ := (hS n (by lia)).exists_rightDerived_δ_exact F (q + 1)
      exact h₁.isZero_of_both_zeros ((hK' n q).eq_of_src _ _)
        ((ih n (by lia) (q + 1) (by lia)).eq_of_tgt _ _)
  have hZ' (n : ℤ) (hn : m + N ≤ n) : F.rightAcyclic (K.cycles n) :=
    fun q ↦ hZ N n hn q (by lia)
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by lia⟩
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp; lia)]
  let T := ShortComplex.mk (F.map (K.iCycles (n + 1))) (F.map (K.d (n + 1) (n + 2)))
    (by rw [← F.map_comp, K.iCycles_d, F.map_zero])
  have hT : IsLimit (KernelFork.ofι T.f T.zero) :=
    isLimitForkMapOfIsLimit' F _ (K.cyclesIsKernel (n + 1) (n + 2) (by simp; lia))
  have : Epi (F.map (K.toCycles n (n + 1))) :=
    ((hS n (by lia)).map_of_rightAcyclic (hZ' n (by lia))).epi_g
  let φ : ((F.mapHomologicalComplex _).obj K).sc' n (n + 1) (n + 2) ⟶ T :=
    { τ₁ := F.map (K.toCycles n (n + 1))
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by
        change F.map (K.toCycles n (n + 1)) ≫ F.map (K.iCycles (n + 1)) =
          F.map (K.d n (n + 1)) ≫ 𝟙 _
        rw [Category.comp_id, ← F.map_comp, K.toCycles_i]
      comm₂₃ := by
        change 𝟙 _ ≫ F.map (K.d (n + 1) (n + 2)) = F.map (K.d (n + 1) (n + 2)) ≫ 𝟙 _
        rw [Category.comp_id, Category.id_comp] }
  have : Epi φ.τ₁ := this
  have : IsIso φ.τ₂ := inferInstanceAs (IsIso (𝟙 _))
  have : Mono φ.τ₃ := inferInstanceAs (Mono (𝟙 _))
  rw [ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ]
  exact ShortComplex.exact_of_f_is_kernel _ hT

/-- A left exact functor of finite right cohomological dimension sends acyclic complexes of
`F`-acyclic objects to acyclic complexes. -/
theorem HasRightCohomologicalDimensionLE.preservesAcyclicityOfRightAcyclic
    [PreservesFiniteLimits F] {N : ℕ} (hF : F.HasRightCohomologicalDimensionLE N) :
    F.PreservesAcyclicityOfRightAcyclic := fun K hK hK' n ↦
  hF.exactAt_map_of_rightAcyclic (n - N - 1) (fun n _ ↦ hK n) hK' n (by lia)

/-- **Acyclic complexes compute `F` on unbounded complexes, up to quasi-isomorphism.** If `F`
preserves acyclicity of complexes of `F`-acyclic objects, it sends a quasi-isomorphism between
complexes of `F`-acyclic objects to a quasi-isomorphism: apply the hypothesis to the mapping
cone. -/
theorem PreservesAcyclicityOfRightAcyclic.quasiIso_map
    (hF : F.PreservesAcyclicityOfRightAcyclic) {K L : CochainComplex C ℤ} (φ : K ⟶ L)
    [QuasiIso φ] (hK : ∀ n, F.rightAcyclic (K.X n)) (hL : ∀ n, F.rightAcyclic (L.X n)) :
    QuasiIso ((F.mapHomologicalComplex _).map φ) := by
  have hφ := (CochainComplex.mappingCone.quasiIso_iff_acyclic φ).1 ‹_›
  rw [CochainComplex.mappingCone.quasiIso_iff_acyclic]
  refine HomologicalComplex.Acyclic.of_iso ?_
    (CochainComplex.mappingCone.mapHomologicalComplexIso φ F)
  refine hF _ hφ fun n ↦ ?_
  exact F.rightAcyclic.prop_of_iso
    (HomologicalComplex.homotopyCofiber.XIsoBiprod φ n (n + 1) rfl).symm
    (rightAcyclic_biprod (hK (n + 1)) (hL n))

end Functor

end CategoryTheory

universe w

namespace DerivedCategory

open CategoryTheory

variable {C : Type*} [Category* C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  [HasDerivedCategory C]

/-- In a Grothendieck abelian category, every object of the derived category is the image of
a K-injective complex with injective components: its functorial K-injective resolution. -/
lemma exists_iso_Q_obj_of_isKInjective_of_injective (M : DerivedCategory C) :
    ∃ (I : CochainComplex C ℤ) (_ : I.IsKInjective) (_ : ∀ n, Injective (I.X n)),
      Nonempty (M ≅ Q.obj I) := by
  let K := Q.objPreimage M
  let i := (CochainComplex.toKInjectiveResolution.{w} C).app K
  have : QuasiIso i := (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{w} C K).2
  exact ⟨_, inferInstance, fun n ↦ inferInstance,
    ⟨(Q.objObjPreimageIso M).symm ≪≫ asIso (Q.map i)⟩⟩

end DerivedCategory

namespace CategoryTheory

open Limits

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [IsGrothendieckAbelian.{w} C] [HasDerivedCategory C] [HasDerivedCategory D]

namespace Functor

variable {F : C ⥤ D} [F.Additive] [HasInjectiveResolutions C]

/-- **Complexes of `F`-acyclic objects compute the unbounded `R(F)`.** If `F` preserves
acyclicity of complexes of `F`-acyclic objects (e.g. if `F` has finite cohomological
dimension), then for every complex `P` of `F`-acyclic objects the unit `F(P) ⟶ R(F)(P)` is an
isomorphism. Compare with a K-injective resolution `i : P ⟶ I` with injective components: `F(i)`
is a quasi-isomorphism (`Functor.PreservesAcyclicityOfRightAcyclic.quasiIso_map`). -/
theorem PreservesAcyclicityOfRightAcyclic.isIso_rightDerivedFunctorUnit_app
    (hF : F.PreservesAcyclicityOfRightAcyclic) (P : CochainComplex C ℤ)
    (hP : ∀ n, F.rightAcyclic (P.X n)) :
    IsIso (F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj P)) := by
  let I := (CochainComplex.kInjectiveResolutionFunctor.{w} C).obj P
  let i : P ⟶ I := (CochainComplex.toKInjectiveResolution.{w} C).app P
  have : QuasiIso i := (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{w} C P).2
  have hFi := hF.quasiIso_map i hP (fun n ↦ rightAcyclic_of_injective _)
  have h₁ : IsIso (DerivedCategory.Qh.map
      ((F.mapHomotopyCategory _).map ((HomotopyCategory.quotient C _).map i))) :=
    Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso D _) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 hFi)
  have h₂ : IsIso (F.rightDerivedFunctor.map
      (DerivedCategory.Qh.map ((HomotopyCategory.quotient C _).map i))) := by
    have : IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient C _).map i)) :=
      Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso C _) _
        ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2
          ((HomologicalComplex.mem_quasiIso_iff _).2 ‹_›))
    infer_instance
  have hnat := F.rightDerivedFunctorUnit.naturality ((HomotopyCategory.quotient C _).map i)
  dsimp only [Functor.comp_map] at hnat
  have : IsIso (F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient C _).obj P) ≫
      F.rightDerivedFunctor.map
        (DerivedCategory.Qh.map ((HomotopyCategory.quotient C _).map i))) := by
    rw [← hnat]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (F.rightDerivedFunctor.map
    (DerivedCategory.Qh.map ((HomotopyCategory.quotient C _).map i)))

/-- **Finite cohomological dimension bounds the amplitude of `R(F)` on unbounded complexes.** If
`F` is left exact with `R^q F = 0` for `q > N`, then `R(F)` sends `D^{≤ m}(C)` into
`D^{≤ m + N}(D)`. Represent `M` by a K-injective complex `I` with injective components; it is
exact in degrees `> m`, so `F(I)` is exact in degrees `> m + N`
(`Functor.HasRightCohomologicalDimensionLE.exactAt_map_of_rightAcyclic`). -/
theorem HasRightCohomologicalDimensionLE.isLE_rightDerivedFunctor_obj [PreservesFiniteLimits F]
    {N : ℕ} (hF : F.HasRightCohomologicalDimensionLE N) (M : DerivedCategory C) (m : ℤ)
    [M.IsLE m] : (F.rightDerivedFunctor.obj M).IsLE (m + N) := by
  obtain ⟨I, _, hI, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective_of_injective.{w} M
  have : (DerivedCategory.Q.obj I).IsLE m := DerivedCategory.TStructure.t.isLE_of_iso e m
  rw [DerivedCategory.isLE_Q_obj_iff, CochainComplex.isLE_iff] at this
  have : (DerivedCategory.Q.obj ((F.mapHomologicalComplex _).obj I)).IsLE (m + N) := by
    rw [DerivedCategory.isLE_Q_obj_iff, CochainComplex.isLE_iff]
    exact fun n hn ↦ hF.exactAt_map_of_rightAcyclic m this
      (fun n ↦ rightAcyclic_of_injective _) n hn
  exact DerivedCategory.TStructure.t.isLE_of_iso
    (F.rightDerivedFunctor.mapIso e ≪≫ F.rightDerivedFunctorObjQIso I).symm (m + N)

section Coproducts

/-- If a natural transformation `α : A ⟶ B` is an isomorphism at the objects of a diagram and at
the cocone point of a cocone `c` over it, then `B` sends `c` to a colimit cocone as soon as `A`
does. -/
noncomputable def isColimitMapCoconeOfNatTrans {X Y K : Type*} [Category* X] [Category* Y] [Category* K]
    {A B : X ⥤ Y} (α : A ⟶ B) {G : K ⥤ X} (c : Cocone G) (hA : IsColimit (A.mapCocone c))
    [∀ j, IsIso (α.app (G.obj j))] [IsIso (α.app c.pt)] : IsColimit (B.mapCocone c) := by
  let β : G ⋙ A ≅ G ⋙ B :=
    NatIso.ofComponents (fun j ↦ asIso (α.app (G.obj j))) (fun f ↦ α.naturality _)
  refine (IsColimit.precomposeHomEquiv β (B.mapCocone c)).1 (IsColimit.ofIsoColimit hA ?_)
  refine (Cocone.ext (asIso (α.app c.pt)) fun j ↦ ?_)
  dsimp [β]
  exact α.naturality (c.ι.app j)

variable (F) in
/-- The natural transformation `F(P) ⟶ R(F)(P)` on cochain complexes, induced by the unit of the
right derived functor. -/
noncomputable def rightDerivedFunctorUnitQ :
    F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ F.rightDerivedFunctor :=
  (Functor.isoWhiskerLeft (F.mapHomologicalComplex _)
      (DerivedCategory.quotientCompQhIso D)).inv ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (F.mapHomotopyCategoryFactors _).inv DerivedCategory.Qh ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (HomotopyCategory.quotient C _) F.rightDerivedFunctorUnit ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (DerivedCategory.quotientCompQhIso C).hom F.rightDerivedFunctor

/-- **Coproducts and right derived functors on unbounded complexes**
(blueprint `lem-exc-direct-image-coproducts`, homological part). Let `F` preserve coproducts of
shape `J`, let coproducts of injective objects be `F`-acyclic, and let `F` preserve acyclicity of
complexes of `F`-acyclic objects (e.g. `F` of finite cohomological dimension). Then the
unbounded right derived functor `R(F)` preserves coproducts of shape `J`.

Represent the members of a family by K-injective complexes `I_j` with injective components. The
coproduct `⨁ I_j` of complexes is a coproduct in `D(C)`; it is not K-injective, but its
components are `F`-acyclic, so `R(F)(⨁ I_j) ≅ F(⨁ I_j) = ⨁ F(I_j)`
(`Functor.PreservesAcyclicityOfRightAcyclic.isIso_rightDerivedFunctorUnit_app`). -/
theorem PreservesAcyclicityOfRightAcyclic.preservesColimitsOfShape_discrete_rightDerivedFunctor
    (J : Type*) [HasColimitsOfShape (Discrete J) C] [PreservesColimitsOfShape (Discrete J) F]
    [PreservesColimitsOfShape (Discrete J) (DerivedCategory.Q (C := C))]
    [PreservesColimitsOfShape (Discrete J) (DerivedCategory.Q (C := D))]
    (hF : F.PreservesAcyclicityOfRightAcyclic)
    (hsum : ∀ (G : Discrete J ⥤ C), (∀ j, Injective (G.obj j)) → ∀ (c : Cocone G),
      IsColimit c → F.rightAcyclic c.pt) :
    PreservesColimitsOfShape (Discrete J) F.rightDerivedFunctor := by
  constructor
  intro K
  choose I hKI hI e using fun j : Discrete J ↦
    DerivedCategory.exists_iso_Q_obj_of_isKInjective_of_injective.{w} (K.obj j)
  let G : Discrete J ⥤ CochainComplex C ℤ := Discrete.functor fun j ↦ I ⟨j⟩
  let eK : K ≅ G ⋙ DerivedCategory.Q := Discrete.natIso fun j ↦ (e j).some
  suffices PreservesColimit (G ⋙ DerivedCategory.Q) F.rightDerivedFunctor from
    preservesColimit_of_iso_diagram _ eK.symm
  let c := colimit.cocone G
  have hc : IsColimit c := colimit.isColimit G
  have : PreservesColimitsOfShape (Discrete J) (F.mapHomologicalComplex (ComplexShape.up ℤ)) :=
    HomologicalComplex.preservesColimitsOfShape_of_eval _ fun n ↦
      (inferInstance : PreservesColimitsOfShape (Discrete J)
        (HomologicalComplex.eval C (ComplexShape.up ℤ) n ⋙ F))
  refine preservesColimit_of_preserves_colimit_cocone
    (isColimitOfPreserves DerivedCategory.Q hc) ?_
  have hα (P : CochainComplex C ℤ) (hP : ∀ n, F.rightAcyclic (P.X n)) :
      IsIso ((rightDerivedFunctorUnitQ F).app P) := by
    have := hF.isIso_rightDerivedFunctorUnit_app P hP
    dsimp [rightDerivedFunctorUnitQ]
    infer_instance
  have : ∀ j, IsIso ((rightDerivedFunctorUnitQ F).app (G.obj j)) := fun j ↦
    hα _ fun n ↦ haveI := hI j n; rightAcyclic_of_injective ((I j).X n)
  have : IsIso ((rightDerivedFunctorUnitQ F).app c.pt) := hα _ fun n ↦
    hsum (G ⋙ HomologicalComplex.eval C _ n) (fun j ↦ inferInstanceAs (Injective ((I j).X n)))
      _ (isColimitOfPreserves (HomologicalComplex.eval C _ n) hc)
  exact isColimitMapCoconeOfNatTrans (rightDerivedFunctorUnitQ F) c
    (isColimitOfPreserves DerivedCategory.Q
      (isColimitOfPreserves (F.mapHomologicalComplex (ComplexShape.up ℤ)) hc))

end Coproducts

end Functor

end CategoryTheory
