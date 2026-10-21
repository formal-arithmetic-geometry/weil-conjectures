/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q86
-/
module

public import Sheaf.Paper.GaloisPartitionModules
public import Sheaf.AlgebraicGeometry.GaloisPartitionExactRefinement
public import Sheaf.Paper.PrimeFieldTensorDevissage
public import Sheaf.CategoryTheory.LocallyConstantFiniteTypeModules
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.CategoryTheory.Subobject.Basic
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.Paper.DirectedGaloisTensorFiltrationClosure
import Sheaf.Paper.DirectedGaloisConstructibleSubobjectSup
import all WeilConjectures.CategoryTheory.FiniteFiltrationRefinement
import WeilConjectures.ConstructibleSheaf.OpenClosed
import WeilConjectures.ConstructibleSheaf.Pullback
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Subobject
import Mathlib.Order.Shrink
import WeilConjectures.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images
import WeilConjectures.AlgebraicGeometry.ConstructibleModuleSubobjectNoetherian
import WeilConjectures.ConstructibleSheaf.KernelCokernel

/-!
# Finite tensor generators for a directed Galois partition

Source: ILO, Travaux de Gabber, Expose XVII, Propositions 7.4.2, 7.4.3 and 7.4.6,
Definition 7.4.5 and Lemmas 7.4.4 and 7.4.7, pp. 305--308
(blueprint: lem-per-directed-galois-finite-tensor-generators).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.GaloisPartition

private theorem modules_of_iso {X : Scheme.{u}} (P : GaloisPartition X)
    (A : Type (u + 1)) [CommRing A]
    {E F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)} (e : E ≅ F)
    (hE : P.modules A E) : P.modules A F := by
  intro i
  obtain ⟨I, hI, hf, D, hD, c, hc, ⟨ec⟩⟩ := hE i
  exact ⟨I, hI, hf, D, hD, c, hc,
    ⟨ec ≪≫ (Etale.upperStar (ModuleCat.{u + 1} A) (P.immersion i)).mapIso e⟩⟩

private theorem constructible_of_iso {X : Scheme.{u}} (P : GaloisPartition X)
    (A : Type (u + 1)) [CommRing A]
    {E F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)} (e : E ≅ F)
    (hE : P.constructible A E) : P.constructible A F := by
  have := hE.2
  exact ⟨modules_of_iso P A e hE.1, IsConstructibleSheaf.of_iso e⟩

private theorem constructible_of_isZero {X : Scheme.{u}} (P : GaloisPartition X)
    (A : Type (u + 1)) [CommRing A]
    (E : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) (hE : IsZero E) :
    P.constructible A E := by
  refine ⟨?_, IsConstructibleSheaf.of_isZero hE⟩
  intro i
  let F := (Etale.upperStar (ModuleCat.{u + 1} A) (P.immersion i)).obj E
  have hF : IsZero F :=
    (Etale.upperStar (ModuleCat.{u + 1} A) (P.immersion i)).map_isZero hE
  let I := Discrete PUnit.{u + 2}
  refine ⟨I, inferInstance, inferInstance, (Functor.const I).obj F, ?_,
    constCocone I F, ⟨isColimitConstCocone I F⟩, ⟨Iso.refl F⟩⟩
  intro j
  exact ⟨0, fun _ ↦ F, hF, ⟨Iso.refl F⟩, fun k ↦ k.elim0⟩

private theorem constructible_subobjects_directed
    (ℓ : ℕ) [Fact ℓ.Prime] {X : Scheme.{u}} [IsNoetherian X]
    (P : GaloisPartition X) (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A]
    [Algebra (ULift.{u + 1} (ZMod ℓ)) A]
    (E : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) (hE : P.modules A E)
    (S T : Subobject E) (hS : P.constructible A (S : _))
    (hT : P.constructible A (T : _)) :
    ∃ U : Subobject E, P.constructible A (U : _) ∧ S ≤ U ∧ T ≤ U := by
  classical
  let : Algebra (ZMod ℓ) A :=
    ((algebraMap (ULift.{u + 1} (ZMod ℓ)) A).comp
      ULift.ringEquiv.symm.toRingHom).toAlgebra
  obtain ⟨hAb, hLim, hColim, hExt, _⟩ := (exact_refinement ℓ X A).1 P
  let W := P.modules A
  let : Abelian W.FullSubcategory := hAb.some
  have : PreservesFiniteLimits W.ι := hLim
  have : PreservesFiniteColimits W.ι := hColim
  have : W.IsClosedUnderExtensions := hExt
  let B := (S : Sheaf X.smallEtaleTopology (ModuleCat A)) ⊞ (T : _)
  have hB : W B := W.prop_biprod hS.1 hT.1
  let f : B ⟶ E := biprod.desc S.arrow T.arrow
  let g : (⟨B, hB⟩ : W.FullSubcategory) ⟶ ⟨E, hE⟩ := ObjectProperty.homMk f
  have hIm : W (image f) := modules_of_iso P A (PreservesImage.iso W.ι g).symm
    (image g).property
  have : IsConstructibleSheaf (S : Sheaf X.smallEtaleTopology (ModuleCat A)) := hS.2
  have : IsConstructibleSheaf (T : Sheaf X.smallEtaleTopology (ModuleCat A)) := hT.2
  have : IsConstructibleSheaf B := IsConstructibleSheaf.biprod _ _
  have : IsConstructibleSheaf (kernel f) := constructible_of_mono_noetherian (kernel.ι f)
  have : IsConstructibleSheaf (cokernel (kernel.ι f)) :=
    IsConstructibleSheaf.cokernel (kernel.ι f)
  have hConstructible : IsConstructibleSheaf (image f) :=
    IsConstructibleSheaf.of_iso (Abelian.coimageIsoImage' f)
  refine ⟨imageSubobject f, constructible_of_iso P A (imageSubobjectIso f).symm
    ⟨hIm, hConstructible⟩, ?_, ?_⟩
  · apply Subobject.le_of_comm (biprod.inl ≫ factorThruImageSubobject f)
    simp only [Category.assoc, imageSubobject_arrow_comp]
    exact biprod.inl_desc _ _
  · apply Subobject.le_of_comm (biprod.inr ≫ factorThruImageSubobject f)
    simp only [Category.assoc, imageSubobject_arrow_comp]
    exact biprod.inr_desc _ _

private theorem filtered_presentation_of_subobject_sup
    {X : Scheme.{u}} (P : GaloisPartition X)
    (A : Type (u + 1)) [CommRing A]
    (E : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    (hne : ∃ S : Subobject E, P.constructible A (S : _))
    (hdir : ∀ S T : Subobject E, P.constructible A (S : _) →
      P.constructible A (T : _) → ∃ U : Subobject E,
        P.constructible A (U : _) ∧ S ≤ U ∧ T ≤ U)
    (hcover : ∀ U : Subobject E,
      (∀ S : Subobject E, P.constructible A (S : _) → S ≤ U) → U = ⊤) :
    ∃ (I : Type (u + 1)) (_ : SmallCategory I) (_ : IsFiltered I)
      (D : I ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) (c : Cocone D),
      (∀ i, P.constructible A (D.obj i)) ∧
      (∀ i, Mono (c.ι.app i)) ∧ Nonempty (IsColimit c) ∧ Nonempty (c.pt ≅ E) := by
  classical
  let S := {S : Subobject E // P.constructible A (S : _)}
  let I := Shrink.{u + 1} S
  let e := equivShrink.{u + 1} S
  have : Nonempty I := by
    obtain ⟨a, ha⟩ := hne
    exact ⟨e ⟨a, ha⟩⟩
  have : IsDirectedOrder I := ⟨fun i j ↦ by
    obtain ⟨a, ha, hi, hj⟩ := hdir (e.symm i).val (e.symm j).val
      (e.symm i).property (e.symm j).property
    refine ⟨e ⟨a, ha⟩, ?_, ?_⟩
    · change (e.symm i).val ≤ (e.symm (e ⟨a, ha⟩)).val
      simpa using hi
    · change (e.symm j).val ≤ (e.symm (e ⟨a, ha⟩)).val
      simpa using hj⟩
  let : SmallCategory I := Preorder.smallCategory I
  let f : I →o Subobject E := ⟨fun i ↦ (e.symm i).val, fun _ _ h ↦ h⟩
  let F : I ⥤ MonoOver E :=
    { obj i := MonoOver.mk (f i).arrow
      map g := MonoOver.homMk (Subobject.ofLE _ _ (f.monotone (leOfHom g)))
        (Subobject.ofLE_arrow _)
      map_id i := Subsingleton.elim _ _
      map_comp g h := Subsingleton.elim _ _ }
  let D := F ⋙ MonoOver.forget E ⋙ Over.forget E
  let c : Cocone D :=
    { pt := E
      ι :=
        { app i := (f i).arrow
          naturality i j g := by
            change Subobject.ofLE (f i) (f j) _ ≫ (f j).arrow =
              (f i).arrow ≫ 𝟙 E
            rw [Subobject.ofLE_arrow, Category.comp_id] } }
  let : HasColimitsOfSize.{u + 1, u + 1}
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
    IsGrothendieckAbelian.hasColimits _
  let : HasColimitsOfShape I
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
    HasColimitsOfSize.has_colimits_of_shape I
  let q := colimit.desc D c
  have hq (i : I) : colimit.ι D i ≫ q = (f i).arrow := colimit.ι_desc c i
  have : Mono q := IsGrothendieckAbelian.mono_of_isColimit_monoOver F
    (colimit.isColimit D) q hq
  have htop : Subobject.mk q = ⊤ := by
    apply hcover
    intro T hT
    have h := Subobject.mk_le_mk_of_comm (colimit.ι D (e ⟨T, hT⟩)) (hq (e ⟨T, hT⟩))
    simpa [f] using h
  have : IsIso q := (Subobject.isIso_iff_mk_eq_top q).mpr htop
  have : IsIso ((colimit.isColimit D).desc c) := ‹IsIso q›
  have hc : IsColimit c := (colimit.isColimit D).ofPointIso
  exact ⟨I, inferInstance, inferInstance, D, c, fun i ↦ (e.symm i).property,
    fun i ↦ inferInstanceAs (Mono (f i).arrow), ⟨hc⟩, ⟨Iso.refl E⟩⟩

/-- A finite prime-field list, chosen before the coefficient algebra, gives ambient
constructible tensor filtrations; arbitrary weakly constructible objects are small filtered
colimits of constructible subobjects. The scalar action in the ordinary mixed tensor is on N.
Source: ILO XVII, 7.4.2--7.4.7, pp. 305--308
(blueprint: lem-per-directed-galois-finite-tensor-generators).

Proof:
1. On a nonempty X use lem-per-directed-galois-tensor-filtration-closure for the fixed
finite list and abstract finite-extension generation. Tensor retracts are invariant under
isomorphisms by composing their inclusion and retraction with the isomorphism.
2. Apply the existing subobject_filtration_of_closure theorem from
WeilConjectures.CategoryTheory.FiniteFiltrationRefinement. Induction on the resulting
subobject chain, using exact_refinement and its canonical cokernel short exact sequences,
shows that all filtration terms are in the constructible partition class.
3. The zero sheaf has the constant-top filtration of length zero. If X is empty, choose
the empty generator list and the singleton filtered presentation of the zero sheaf.
4. The zero subobject is constructible in the weak class. The image of the direct sum
of two constructible subobjects is in the weak class, since its inclusion preserves
finite limits and colimits by exact_refinement. The image is constructible: its kernel
is a subsheaf of a constructible sheaf over a Noetherian coefficient ring, and the image
is the cokernel of that kernel. Hence these subobjects form a nonempty directed family.
5. Lemma lem-per-directed-galois-constructible-subobject-sup says this family exhausts E.
Shrink its poset to the site-and-coefficient universe. The diagram of representative
monomorphisms has a colimit because module sheaves form a Grothendieck abelian category.
Exactness of filtered colimits makes its comparison q to E monic. Every constructible
subobject factors through q, so the exhaustion lemma gives Subobject.mk q = top.
Thus q is an isomorphism and the canonical cocone with point E is colimiting. -/
theorem finite_tensor_generators (ℓ : ℕ) [Fact ℓ.Prime]
    (X : Scheme.{u}) [IsNoetherian X] (P : GaloisPartition X) (hP : P.IsDirected) :
    ∃ (r : ℕ)
      (C : Fin r → Sheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))),
      (IsEmpty X → r = 0) ∧
      (∀ a, P.constructible (ULift.{u + 1} (ZMod ℓ)) (C a)) ∧
      ∀ (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A]
        [Algebra (ULift.{u + 1} (ZMod ℓ)) A],
        (∀ (E : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)),
          P.constructible A E →
          ∃ (n : ℕ) (H : Fin (n + 1) → Subobject E) (hH : Monotone H),
            IsZero (H 0 : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ∧
            IsIso (H (Fin.last n)).arrow ∧ (IsZero E → n = 0) ∧
            (∀ j, P.constructible A (H j : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) ∧
            ∀ i : Fin n, ∃ (a : Fin r) (N : ModuleCat.{u + 1} A),
              Module.Finite A N ∧
              ∃ (ι : cokernel (Subobject.ofLE (H i.castSucc) (H i.succ)
                    (hH (Fin.castSucc_le_succ i))) ⟶
                  (Etale.primeFieldTensorSheaf X ℓ A N).obj (C a))
                (π : (Etale.primeFieldTensorSheaf X ℓ A N).obj (C a) ⟶
                  cokernel (Subobject.ofLE (H i.castSucc) (H i.succ)
                    (hH (Fin.castSucc_le_succ i)))),
                ι ≫ π = 𝟙 _) ∧
        (∀ (E : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)), P.modules A E →
          ∃ (I : Type (u + 1)) (_ : SmallCategory I) (_ : IsFiltered I)
            (D : I ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
            (c : Cocone D),
            (∀ i, P.constructible A (D.obj i)) ∧
            (∀ i, Mono (c.ι.app i)) ∧ Nonempty (IsColimit c) ∧ Nonempty (c.pt ≅ E)) := by
  classical
  by_cases hX : IsEmpty X
  · have := hX
    refine ⟨0, Fin.elim0, fun _ ↦ rfl, fun a ↦ a.elim0, ?_⟩
    intro A _ _ _
    constructor
    · intro E hE
      let H : Fin 1 → Subobject E := fun _ ↦ ⊤
      refine ⟨0, H, monotone_const, ?_, ?_, fun _ ↦ rfl, ?_, fun i ↦ i.elim0⟩
      · exact (Etale.isZero_sheaf_of_isEmpty E).of_iso
          (Subobject.underlyingIso (𝟙 E))
      · dsimp [H]
        infer_instance
      · intro j
        exact constructible_of_iso P A (Subobject.underlyingIso (𝟙 E)).symm hE
    · intro E _
      let I := Discrete PUnit.{u + 2}
      refine ⟨I, inferInstance, inferInstance, (Functor.const I).obj E,
        constCocone I E, fun _ ↦ ?_, fun _ ↦ inferInstanceAs (Mono (𝟙 E)),
        ⟨isColimitConstCocone I E⟩, ⟨Iso.refl E⟩⟩
      exact constructible_of_isZero P A E (Etale.isZero_sheaf_of_isEmpty E)
  · have : Nonempty X := not_isEmpty_iff.mp hX
    obtain ⟨r, C, hC, hgen⟩ := exists_tensor_filtrationClosure ℓ X P hP
    refine ⟨r, C, fun h ↦ (hX h).elim, hC, ?_⟩
    intro A _ _ _
    constructor
    · intro E hE
      by_cases hzero : IsZero E
      · let H : Fin 1 → Subobject E := fun _ ↦ ⊤
        refine ⟨0, H, monotone_const, ?_, ?_, fun _ ↦ rfl, ?_, fun i ↦ i.elim0⟩
        · exact hzero.of_iso (Subobject.underlyingIso (𝟙 E))
        · dsimp [H]
          infer_instance
        · intro j
          exact constructible_of_iso P A (Subobject.underlyingIso (𝟙 E)).symm hE
      · let T : ObjectProperty (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
          fun Q ↦ P.constructible A Q ∧
            ∃ (a : Fin r) (N : ModuleCat.{u + 1} A), Module.Finite A N ∧
              ∃ (ι : Q ⟶ (Etale.primeFieldTensorSheaf X ℓ A N).obj (C a))
                (π : (Etale.primeFieldTensorSheaf X ℓ A N).obj (C a) ⟶ Q),
                ι ≫ π = 𝟙 Q
        have : T.IsClosedUnderIsomorphisms := ⟨fun e h ↦ by
          obtain ⟨hc, a, N, hN, ι, π, hιπ⟩ := h
          refine ⟨constructible_of_iso P A e hc, a, N, hN, e.inv ≫ ι, π ≫ e.hom, ?_⟩
          calc
            (e.inv ≫ ι) ≫ (π ≫ e.hom) =
                e.inv ≫ (ι ≫ π) ≫ e.hom := by simp only [Category.assoc]
            _ = 𝟙 _ := by rw [hιπ]; simp⟩
        have hcl : T.filtrationClosure E := hgen A E hE
        obtain ⟨n, H, hH, hbot, htop, hquot⟩ :=
          CategoryTheory.subobject_filtration_of_closure T hcl
        let : Algebra (ZMod ℓ) A :=
          ((algebraMap (ULift.{u + 1} (ZMod ℓ)) A).comp
            ULift.ringEquiv.symm.toRingHom).toAlgebra
        have : (P.constructible A).IsClosedUnderExtensions :=
          ((exact_refinement ℓ X A).1 P).2.2.2.2.2.2.2
        have hterms : ∀ (j : ℕ) (hj : j < n + 1),
            P.constructible A (H ⟨j, hj⟩ : _) := by
          intro j
          induction j with
          | zero =>
            intro hj
            rw [show (⟨0, hj⟩ : Fin (n + 1)) = 0 from rfl, hbot]
            exact constructible_of_isZero P A _
              ((isZero_zero _).of_iso Subobject.botCoeIsoZero)
          | succ j ih =>
            intro hj
            let i : Fin n := ⟨j, by omega⟩
            let f := Subobject.ofLE (H i.castSucc) (H i.succ) (hH i.castSucc_le_succ)
            have hS : (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).ShortExact :=
              ⟨ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f)⟩
            exact (P.constructible A).prop_X₂_of_shortExact hS (ih (by omega)) (hquot i).1
        refine ⟨n, H, hH, ?_, ?_, fun hz ↦ (hzero hz).elim, ?_, fun i ↦ (hquot i).2⟩
        · rw [hbot]
          exact (isZero_zero _).of_iso Subobject.botCoeIsoZero
        · rw [htop]
          infer_instance
        · intro j
          exact hterms j.val j.isLt
    · intro E hE
      apply filtered_presentation_of_subobject_sup P A E
      · let Z := (HasZeroObject.zero
          (C := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))).choose
        let z : Z ⟶ E := 0
        have : Mono z := (isZero_zero _).mono z
        exact ⟨Subobject.mk z, constructible_of_isZero P A _
          ((isZero_zero _).of_iso (Subobject.underlyingIso z))⟩
      · exact constructible_subobjects_directed ℓ P A E hE
      · exact constructible_subobject_sup ℓ X P hP A E hE

end AlgebraicGeometry.Scheme.GaloisPartition
