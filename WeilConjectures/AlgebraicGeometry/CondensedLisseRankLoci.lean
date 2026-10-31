/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.AlgebraicGeometry.CoefficientHeartStratificationDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.ModuleObjects.RegularEnd
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Topology.LocallyConstant.Basic
import WeilConjectures.AlgebraicGeometry.CoefficientHeartCurveLisseDescent
import all WeilConjectures.AlgebraicGeometry.StratifiedLatticeRank
import WeilConjectures.CategoryTheory.ModuleObjects.RegularEndBijective
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.SepClosedPoint
import WeilConjectures.AlgebraicGeometry.ProEtale.SepClosedPointLift
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.OpenClosed
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
import Mathlib.CategoryTheory.Preadditive.HomOrthogonal
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Ranks and actual geometric fibres of lisse condensed modules

Source: Hemo--Richarz--Scholbach, Lemma 4.1(1)--(2), Theorem 4.13;
current blueprint lem-zl-mixed-punctual-cutoff.proof.md, paragraph 2.
(blueprint: lem-zl-condensed-lisse-rank-loci)

`MonObj.Γ R.X` is the ring of terminal sections of the condensed ring.
Sections of a module are expressed as maps from the regular module. The additive
section equivalence below is linear by its displayed scalar-compatibility equation.
The scalar map is the canonical constant-section map `MonObj.Γ.mapFunctorMonoidHom`.
The first conjunct `∀ r', (geometric-fibre property of r') ↔ r' = r` states existence and
uniqueness of the rank among locally constant functions with the geometric-fibre property
alone, as in the node; the remaining clauses are asserted of this rank.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w z

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj ZeroObject

namespace AlgebraicGeometry.ProEtale

private def regularSectionsEquiv
    {C : Type w} [Category.{v} C] [MonoidalCategory C] [Preadditive C]
    [MonoidalPreadditive C] [BraidedCategory C] (R : C) [MonObj R] [IsCommMonObj R] :
    MonObj.Γ R ≃+* End (Mod.regular R) :=
  RingEquiv.ofBijective _ Mod.regularEndRingHom_bijective

private def freeSectionCoordinates
    {C : Type w} [Category.{v} C] [MonoidalCategory C] [Abelian C]
    [MonoidalPreadditive C] [BraidedCategory C] (R : C) [MonObj R] [IsCommMonObj R]
    (n : ℕ) : (Mod.regular R ⟶ Mod.finiteFree R n) ≃+ (Fin n → MonObj.Γ R) where
  toFun f j := (regularSectionsEquiv R).symm (f ≫ biproduct.π _ j)
  invFun a := biproduct.lift fun j ↦ regularSectionsEquiv R (a j)
  left_inv f := by
    apply biproduct.hom_ext
    intro j
    simp
  right_inv a := by
    funext j
    simp
  map_add' f g := by
    funext j
    simp only [Preadditive.add_comp, map_add, Pi.add_apply]

private theorem freeSectionCoordinates_scalar
    {C : Type w} [Category.{v} C] [MonoidalCategory C] [Abelian C]
    [MonoidalPreadditive C] [BraidedCategory C] (R : C) [MonObj R] [IsCommMonObj R]
    (n : ℕ) (s : MonObj.Γ R) (f : Mod.regular R ⟶ Mod.finiteFree R n) :
    freeSectionCoordinates R n (Mod.regularEndRingHom s ≫ f) =
      fun j ↦ s * freeSectionCoordinates R n f j := by
  funext j
  change (regularSectionsEquiv R).symm
    ((Mod.regularEndRingHom s ≫ f) ≫ biproduct.π _ j) = _
  rw [Category.assoc]
  change (regularSectionsEquiv R).symm
    ((show End (Mod.regular R) from f ≫ biproduct.π _ j) *
      regularSectionsEquiv R s) = _
  rw [map_mul, RingEquiv.symm_apply_apply]
  exact mul_comm _ _

private def isoSectionCoordinates
    {C : Type w} [Category.{v} C] [MonoidalCategory C] [Abelian C]
    [MonoidalPreadditive C] [BraidedCategory C] (A : C) [MonObj A] [IsCommMonObj A]
    {F : Type z} [CommRing F] (φ : F ≃+* MonObj.Γ A) (n : ℕ)
    {M : Mod C A} (e : M ≅ Mod.finiteFree A n) :
    (Mod.regular A ⟶ M) ≃+ (Fin n → F) :=
  let post : (Mod.regular A ⟶ M) ≃+ (Mod.regular A ⟶ Mod.finiteFree A n) :=
    { toFun := fun v ↦ v ≫ e.hom
      invFun := fun v ↦ v ≫ e.inv
      left_inv := by intro v; simp
      right_inv := by intro v; simp
      map_add' := by intro f g; simp }
  post.trans ((freeSectionCoordinates A n).trans
    (AddEquiv.piCongrRight fun _ ↦ φ.symm.toAddEquiv))

private theorem isoSectionCoordinates_scalar
    {C : Type w} [Category.{v} C] [MonoidalCategory C] [Abelian C]
    [MonoidalPreadditive C] [BraidedCategory C] (A : C) [MonObj A] [IsCommMonObj A]
    {F : Type z} [CommRing F] (φ : F ≃+* MonObj.Γ A) (n : ℕ)
    {M : Mod C A} (e : M ≅ Mod.finiteFree A n) (s : F) (v : Mod.regular A ⟶ M) :
    isoSectionCoordinates A φ n e (Mod.regularEndRingHom (φ s) ≫ v) =
      fun j ↦ s * isoSectionCoordinates A φ n e v j := by
  funext j
  change φ.symm (freeSectionCoordinates A n
    ((Mod.regularEndRingHom (φ s) ≫ v) ≫ e.hom) j) = _
  rw [Category.assoc, freeSectionCoordinates_scalar]
  simp only [map_mul, RingEquiv.symm_apply_apply]
  rfl

private theorem pointSectionMap_bijective
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] (K : Type u) [Field K] [IsAlgClosed K] :
    Function.Bijective (MonObj.Γ.mapFunctorMonoidHom
      (upperStarFromPoint (Spec (.of K))) (R := R)) := by
  let F := upperStarFromPoint (Spec (.of K))
  have : F.IsEquivalence := inferInstance
  have : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  have : F.Additive := Functor.additive_of_preservesBinaryBiproducts F
  have hb := F.bijective_regularEndRingHom_comp_mapFunctor R
    (Functor.FullyFaithful.ofFullyFaithful _)
  exact (Mod.regularEndRingHom_bijective.of_comp_iff' _).mp hb

private theorem point_free_rank
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] (hR : IsField (MonObj.Γ R))
    (K : Type u) [Field K] [IsAlgClosed K] (m n : ℕ)
    (e : Mod.finiteFree (condensedRingObj R (Spec (.of K))) m ≅
      Mod.finiteFree (condensedRingObj R (Spec (.of K))) n) : m = n := by
  classical
  let A := condensedRingObj R (Spec (.of K))
  let M := Mod.regular A
  let φ := Mod.regularEndRingHom (R := A)
  let : CommRing (End M) := { (inferInstance : Ring (End M)) with
    mul_comm := fun f g ↦ by
      obtain ⟨a, rfl⟩ := Mod.regularEndRingHom_surjective f
      obtain ⟨b, rfl⟩ := Mod.regularEndRingHom_surjective g
      rw [← map_mul, ← map_mul, mul_comm a b] }
  let F := upperStarFromPoint (Spec (.of K))
  have : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  have : F.Additive := Functor.additive_of_preservesBinaryBiproducts F
  let h := RingEquiv.ofBijective (φ.comp (MonObj.Γ.mapFunctor F))
    (Mod.regularEndRingHom_bijective.comp (pointSectionMap_bijective R K))
  have : Nontrivial (MonObj.Γ R) := hR.toField.toNontrivial
  have : Nontrivial (End M) := h.symm.toEquiv.nontrivial
  have ho : HomOrthogonal (fun _ : Unit ↦ M) := by
    intro i j hij
    exact (hij (Subsingleton.elim _ _)).elim
  obtain ⟨a, _⟩ := ho.equiv_of_iso (f := fun _ : Fin m ↦ ())
    (g := fun _ : Fin n ↦ ()) e
  simpa only [Fintype.card_fin] using Fintype.card_congr a

private theorem free_rank
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] (hR : IsField (MonObj.Γ R))
    (W : Scheme.{u}) [Nonempty W] (m n : ℕ)
    (e : Mod.finiteFree (condensedRingObj R W) m ≅
      Mod.finiteFree (condensedRingObj R W) n) : m = n := by
  let w : W := Classical.choice inferInstance
  let K := AlgebraicClosure (W.residueField w)
  let b : Spec (.of K) ⟶ W := (Scheme.SpecToEquivOfField K W).symm
    ⟨w, CommRingCat.ofHom (algebraMap (W.residueField w) K)⟩
  apply point_free_rank R hR K m n
  exact (coefficientHeartFiniteFreePullbackIso R b m).symm ≪≫
    (CondensedRing.upperStar R b).mapIso e ≪≫ coefficientHeartFiniteFreePullbackIso R b n

private theorem locallyConstantRank
    {T : Type w} [TopologicalSpace T] (U : ℕ → TopologicalSpace.Opens T)
    (hex : ∀ x : T, ∃ n, x ∈ U n)
    (hunique : ∀ (x : T) (m n : ℕ), x ∈ U m → x ∈ U n → m = n) :
    ∃ r : LocallyConstant T ℕ, ∀ (x : T) (n : ℕ), x ∈ U n ↔ r x = n := by
  classical
  choose a ha using hex
  have hm (x : T) (n : ℕ) : x ∈ U n ↔ a x = n := by
    constructor
    · exact hunique x (a x) n (ha x)
    · rintro rfl
      exact ha x
  refine ⟨⟨a, IsLocallyConstant.iff_isOpen_fiber.mpr fun n ↦ ?_⟩, hm⟩
  have he : a ⁻¹' {n} = (U n : Set T) := Set.ext fun x ↦ (hm x n).symm
  rw [he]
  exact (U n).isOpen

-- Cover-local zero detection, using only the underived sheaf restriction criterion.
private theorem zeroOfCover
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    (C : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (h : ∀ i, IsZero ((CondensedRing.upperStar Λ (C.f i)).obj M)) : IsZero M := by
  have (i : C.I₀) : WeaklyEtale (C.f i) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ C.mem₀ (.mk i)
  refine CondensedRing.isZero_of_isZero_X Λ ?_
  have : IsIso (0 : M.X ⟶ 0) := by
    refine isIso_of_isIso_localizationRestriction Ab.{u + 1} (0 : M.X ⟶ 0) C.f C.mem₀
      fun i ↦ ?_
    have h₁ : IsZero ((upperStar Ab.{u + 1} (C.f i)).obj M.X) :=
      ((Mod.forget _).map_isZero (h i)).of_iso
        (CondensedRing.upperStarObjXIso Λ _ M).symm
    have h₂ : IsZero ((upperStar Ab.{u + 1} (C.f i)).obj 0) :=
      Functor.map_isZero _ (isZero_zero _)
    have : IsIso ((upperStar Ab.{u + 1} (C.f i)).map (0 : M.X ⟶ 0)) :=
      isIso_of_source_target_iso_zero _ h₁.isoZero h₂.isoZero
    exact (NatIso.isIso_map_iff
      (upperStarIsoLocalizationRestriction Ab.{u + 1} (C.f i) inferInstance) _).1 this
  exact (isZero_zero _).of_iso (asIso (0 : M.X ⟶ 0))

private theorem geometricFreeOfRank
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {X : Scheme.{u}}
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj R X))
    (C : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    (hC : ∀ i, Mod.IsFree (condensedRingObj R (C.X i))
      ((CondensedRing.upperStar R (C.f i)).obj L))
    (r : LocallyConstant X ℕ)
    (hlabel : ∀ (i : C.I₀) (n : ℕ),
      Nonempty ((CondensedRing.upperStar R (C.f i)).obj L ≅
        Mod.finiteFree (condensedRingObj R (C.X i)) n) →
      ∀ v : C.X i, n = r (C.f i v))
    (K : Type u) [Field K] [IsAlgClosed K] (b : Spec (.of K) ⟶ X) :
    Nonempty ((CondensedRing.upperStar R b).obj L ≅
      Mod.finiteFree (condensedRingObj R (Spec (.of K)))
        (r ((Scheme.SpecToEquivOfField K X b).1))) := by
  obtain ⟨i, g, hg⟩ := C.exists_comp_eq_of_isSepClosed_of_proetale b
  subst b
  obtain ⟨n, ⟨e⟩⟩ := hC i
  have hn := hlabel i n ⟨e⟩ (g (IsLocalRing.closedPoint K))
  change n = r ((Scheme.SpecToEquivOfField K X (g ≫ C.f i)).1) at hn
  subst n
  exact ⟨(CondensedRing.upperStarComp R g (C.f i)).app L ≪≫
    (CondensedRing.upperStar R g).mapIso e ≪≫
      coefficientHeartFiniteFreePullbackIso R g _⟩

section
attribute [local irreducible] CondensedRing.upperStarComp
  CondensedRing.upperStarLowerStarAdjunction upperStarFromPoint CondensedRing.upperStar

private theorem coverRankData
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] (hR : IsField (MonObj.Γ R)) (X : Scheme.{u})
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj R X))
    (hL : IsLisseCoefficientModule R L) :
    ∃ (r : LocallyConstant X ℕ) (U : ℕ → X.Opens),
      (∀ (x : X) (n : ℕ), x ∈ U n ↔ r x = n) ∧
      (∀ n, IsClosed (U n : Set X)) ∧
      (∀ (K : Type u) [Field K] [IsAlgClosed K] (b : Spec (.of K) ⟶ X),
        Nonempty ((CondensedRing.upperStar R b).obj L ≅
          Mod.finiteFree (condensedRingObj R (Spec (.of K)))
            (r ((Scheme.SpecToEquivOfField K X b).1)))) ∧
      ∀ n, ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage (U n).toScheme,
        ∀ i : C.I₀,
          Nonempty ((CondensedRing.upperStar R (C.f i ≫ (U n).ι)).obj L ≅
            Mod.finiteFree (condensedRingObj R (C.X i)) n) := by
  classical
  obtain ⟨C, hC⟩ := hL
  obtain ⟨n, e⟩ := Classical.axiomOfChoice hC
  obtain ⟨t⟩ := Classical.nonempty_pi.mpr e
  have compare {Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ X) (a b : ℕ)
      (ef : (CondensedRing.upperStar R f).obj L ≅
        Mod.finiteFree (condensedRingObj R Y) a)
      (eg : (CondensedRing.upperStar R g).obj L ≅
        Mod.finiteFree (condensedRingObj R Z) b) (w : ↑(pullback f g)) : a = b := by
    let : Nonempty ↑(pullback f g) := ⟨w⟩
    have ea := rankPullbackTrivialization R f (pullback.fst f g) L a ef
    have eb := rankPullbackTrivialization R g (pullback.snd f g) L b eg
    have ea' : Nonempty ((CondensedRing.upperStar R (pullback.snd f g ≫ g)).obj L ≅
        Mod.finiteFree (condensedRingObj R (pullback f g)) a) := by
      simpa only [pullback.condition] using ea
    obtain ⟨ia⟩ := ea'
    obtain ⟨ib⟩ := eb
    exact free_rank R hR _ a b (ia.symm ≪≫ ib)
  have compat (i j : C.I₀) :
      (fun _ : C.X i ↦ n i) ∘ pullback.fst (C.f i) (C.f j) =
        (fun _ : C.X j ↦ n j) ∘ pullback.snd (C.f i) (C.f j) := by
    funext w
    exact compare (C.f i) (C.f j) (n i) (n j) (t i) (t j) w
  obtain ⟨S, hS, _⟩ := labelledClopenPartition_existsUnique_of_fpqc C.f
    (Scheme.proetalePrecoverage_le_fpqcPrecoverage _ C.mem₀)
    (fun i _ ↦ n i) (by intro i a; by_cases h : n i = a <;> simp [h]) compat
  obtain ⟨hclosed, hdisjoint, hcover, hmem, _⟩ := hS
  have mem_cover (i : C.I₀) (v : C.X i) (r : ℕ) :
      C.f i v ∈ S r ↔ n i = r := by
    exact congrArg (fun A : Set (C.X i) ↦ v ∈ A) (hmem i r) |>.to_iff
  have hex (x : X) : ∃ n, x ∈ S n := by
    have hx : x ∈ ⋃ n, (S n : Set X) := by rw [hcover]; exact Set.mem_univ x
    exact Set.mem_iUnion.mp hx
  have hunique (x : X) (a b : ℕ) (ha : x ∈ S a) (hb : x ∈ S b) : a = b := by
    by_contra hn
    have hz : x ∈ (⊥ : X.Opens) :=
      (show S a ⊓ S b ≤ ⊥ from (hdisjoint hn).le_bot) ⟨ha, hb⟩
    exact hz
  obtain ⟨r, hrmem⟩ := locallyConstantRank S hex hunique
  have hlabel (i : C.I₀) (a : ℕ)
      (e : Nonempty ((CondensedRing.upperStar R (C.f i)).obj L ≅
        Mod.finiteFree (condensedRingObj R (C.X i)) a)) (v : C.X i) :
      a = r (C.f i v) := by
    let : Nonempty (C.X i) := ⟨v⟩
    obtain ⟨e⟩ := e
    have hn := free_rank R hR (C.X i) a (n i) (e.symm ≪≫ t i)
    exact hn.trans ((hrmem _ _).mp ((mem_cover i v _).mpr rfl)).symm
  refine ⟨r, S, hrmem, hclosed, geometricFreeOfRank R L C hC r hlabel, ?_⟩
  intro a
  apply rankRestrictedCover C n S mem_cover
    (fun Y f a ↦ Nonempty ((CondensedRing.upperStar R (X := Y) (Y := X) f).obj L ≅
      Mod.finiteFree (condensedRingObj R Y) a)) ?_ (fun i ↦ ⟨t i⟩) a
  intro Y Z f g a e
  exact rankPullbackTrivialization R f g L a e.some

end

private theorem rank_eq_of_geometricFibres
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] (hR : IsField (MonObj.Γ R)) {X : Scheme.{u}}
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj R X))
    (r r' : LocallyConstant X ℕ)
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K] (b : Spec (.of K) ⟶ X),
      Nonempty ((CondensedRing.upperStar R b).obj L ≅
        Mod.finiteFree (condensedRingObj R (Spec (.of K)))
          (r ((Scheme.SpecToEquivOfField K X b).1))))
    (h' : ∀ (K : Type u) [Field K] [IsAlgClosed K] (b : Spec (.of K) ⟶ X),
      Nonempty ((CondensedRing.upperStar R b).obj L ≅
        Mod.finiteFree (condensedRingObj R (Spec (.of K)))
          (r' ((Scheme.SpecToEquivOfField K X b).1)))) : r' = r := by
  ext x
  let K := AlgebraicClosure (X.residueField x)
  let b : Spec (.of K) ⟶ X := (Scheme.SpecToEquivOfField K X).symm
    ⟨x, CommRingCat.ofHom (algebraMap (X.residueField x) K)⟩
  have hb : (Scheme.SpecToEquivOfField K X b).1 = x :=
    congrArg Sigma.fst ((Scheme.SpecToEquivOfField K X).apply_symm_apply _)
  obtain ⟨e'⟩ := h' K b
  obtain ⟨e⟩ := h K b
  have hn := point_free_rank R hR K _ _ (e'.symm ≪≫ e)
  simpa only [hb] using hn

private theorem pointSectionCoordinates
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] (K : Type u) [Field K] [IsAlgClosed K]
    (M : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of K))) Ab.{u + 1})
      (condensedRingObj R (Spec (.of K))))
    (n : ℕ) (e : M ≅ Mod.finiteFree (condensedRingObj R (Spec (.of K))) n) :
    ∃ ec : (Mod.regular (condensedRingObj R (Spec (.of K))) ⟶ M) ≃+
      (Fin n → MonObj.Γ R),
      ∀ (s : MonObj.Γ R) (v : Mod.regular (condensedRingObj R (Spec (.of K))) ⟶ M),
        ec (Mod.regularEndRingHom
          (MonObj.Γ.mapFunctorMonoidHom (upperStarFromPoint (Spec (.of K))) s) ≫ v) =
            fun j ↦ s * ec v j := by
  let F := upperStarFromPoint (Spec (.of K))
  have : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  have : F.Additive := Functor.additive_of_preservesBinaryBiproducts F
  let φ := RingEquiv.ofBijective (MonObj.Γ.mapFunctor F (R := R))
    (pointSectionMap_bijective R K)
  exact ⟨isoSectionCoordinates _ φ n e, isoSectionCoordinates_scalar _ φ n e⟩

private theorem iteratedRankCover
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {X : Scheme.{u}}
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj R X))
    (U : X.Opens) (n : ℕ)
    (D : Scheme.Cover.{u} Scheme.proetalePrecoverage U.toScheme)
    (hD : ∀ i, Nonempty ((CondensedRing.upperStar R (D.f i ≫ U.ι)).obj L ≅
      Mod.finiteFree (condensedRingObj R (D.X i)) n)) :
    (∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage U.toScheme,
      ∀ i : C.I₀, Nonempty ((CondensedRing.upperStar R (C.f i)).obj
        ((CondensedRing.upperStar R U.ι).obj L) ≅
          Mod.finiteFree (condensedRingObj R (C.X i)) n)) ∧
    (n = 0 → IsZero ((CondensedRing.upperStar R U.ι).obj L)) := by
  have hd (i : D.I₀) : Nonempty ((CondensedRing.upperStar R (D.f i)).obj
      ((CondensedRing.upperStar R U.ι).obj L) ≅
        Mod.finiteFree (condensedRingObj R (D.X i)) n) := by
    obtain ⟨e⟩ := hD i
    exact ⟨((CondensedRing.upperStarComp R (D.f i) U.ι).app L).symm ≪≫ e⟩
  refine ⟨⟨D, hd⟩, ?_⟩
  intro hn
  subst n
  apply zeroOfCover R D
  intro i
  obtain ⟨e⟩ := hd i
  apply IsZero.of_iso _ e
  apply (IsZero.iff_id_eq_zero _).mpr
  apply biproduct.hom_ext
  intro j
  exact Fin.elim0 j

/-- The vanishing data of the rank construction, before bundling its coefficient ring.
Source: Hemo--Richarz--Scholbach, Lemma 4.1 and Theorem 4.13
(blueprint: lem-zl-condensed-lisse-rank-loci).
Proof: take the descended rank and clopen cover from `coverRankData`. At rank zero,
`iteratedRankCover` identifies the iterated restrictions with free modules of rank
zero and detects zero on that cover. Retain the geometric fibre descriptions and
discard the unused uniqueness, section-coordinate and finite-range clauses. -/
private theorem zeroLocusRankDataOfCover
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] (hR : IsField (MonObj.Γ R))
    (X : Scheme.{u}) [IsNoetherian X]
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj R X))
    (hL : IsLisseCoefficientModule R L) :
    ∃ r : LocallyConstant X ℕ,
      (∀ (K : Type u) [Field K] [IsAlgClosed K] (b : Spec (.of K) ⟶ X),
        Nonempty ((CondensedRing.upperStar R b).obj L ≅
          Mod.finiteFree (condensedRingObj R (Spec (.of K)))
            (r (Scheme.SpecToEquivOfField K X b).1))) ∧
      ∃ U : X.Opens, (U : Set X) = {x | r x = 0} ∧ IsClosed (U : Set X) ∧
        IsZero ((CondensedRing.upperStar R U.ι).obj L) := by
  obtain ⟨r, U, hr, hclosed, hfib, hcover⟩ := coverRankData R hR X L hL
  obtain ⟨C, hC⟩ := hcover 0
  exact ⟨r, hfib, U 0, Set.ext (fun x ↦ hr x 0), hclosed 0,
    (iteratedRankCover R L (U 0) 0 C hC).2 rfl⟩

/-- A lisse module over a commutative condensed ring whose terminal sections form a
field has a unique locally constant rank, actual finite-free geometric fibres,
linear terminal-section identifications, and finitely many clopen rank loci.
Source: Hemo--Richarz--Scholbach, Lemma 4.1(1)--(2), Theorem 4.13;
current blueprint lem-zl-mixed-punctual-cutoff.proof.md, paragraph 2
(blueprint: lem-zl-condensed-lisse-rank-loci).

Proof: (1) At a geometric point, the existing equivalence from condensed modules
identifies regular-module endomorphisms. The bijective regular-scalar map then
shows that the canonical constant-section map is bijective.
(2) The endomorphism ring of the regular module is commutative and nontrivial.
Mathlib's invariant-basis-number theorem for a singleton hom-orthogonal family
therefore equates the ranks of isomorphic finite free modules. For a nonempty
scheme, pull back to the algebraic closure of one residue field first.
(3) Compare the local ranks on overlaps, using (2) and the coefficient-independent
pullback helpers of StratifiedLatticeRank. Descend the constant cover labels by
fpqc labelled-clopen descent; its cover-refinement helper supplies rank-n covers.
(4) Choose the unique label at every point. Its fibres are the descended opens,
so the resulting rank function is locally constant.
(5) Lift every specified geometric point through the original pro-etale cover,
over the same algebraically closed field. Pull back the chosen trivialization
and use the descended cover-label formula to identify its rank with the rank function.
(6) Compose maps from the regular module with the fibre trivialization and the
finite-biproduct projections. The inverse regular-scalar bijection and (1) give
the section equivalence. Its scalar equation follows from commutativity and
composition, which is reversed multiplication in the endomorphism ring.
(7) Compare geometric fibres over an algebraic closure of each residue field to
prove uniqueness from the fibre property alone. Compactness gives finite range.
(8) The restricted rank-n cover from (3), with the pullback compositor inverted,
gives the asserted iterated-pullback trivializations. In rank zero these objects
are zero. The underlying abelian-sheaf restriction criterion detects that the
zero map to zero is an isomorphism, so the restricted module is zero.
Empty schemes, empty loci and rank zero are included throughout. -/
theorem condensedLisse_rank_loci
    (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X]
    (hF : IsField (MonObj.Γ R.X)) (X : Scheme.{u}) [IsNoetherian X]
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj R.X X))
    (hL : IsLisseCoefficientModule R.X L) :
    ∃ r : LocallyConstant X ℕ,
      (∀ r' : LocallyConstant X ℕ,
        (∀ (K : Type u) [Field K] [IsAlgClosed K] (b : Spec (.of K) ⟶ X),
          Nonempty ((CondensedRing.upperStar R.X b).obj L ≅
            Mod.finiteFree (condensedRingObj R.X (Spec (.of K)))
              (r' ((Scheme.SpecToEquivOfField K X b).1)))) ↔ r' = r) ∧
      (∀ (K : Type u) [Field K] [IsAlgClosed K] (b : Spec (.of K) ⟶ X),
        Function.Bijective (MonObj.Γ.mapFunctorMonoidHom
          (upperStarFromPoint (Spec (.of K))) (R := R.X)) ∧
        ∃ e : (Mod.regular (condensedRingObj R.X (Spec (.of K))) ⟶
            (CondensedRing.upperStar R.X b).obj L) ≃+
              (Fin (r ((Scheme.SpecToEquivOfField K X b).1)) → MonObj.Γ R.X),
          ∀ (s : MonObj.Γ R.X)
            (v : Mod.regular (condensedRingObj R.X (Spec (.of K))) ⟶
              (CondensedRing.upperStar R.X b).obj L),
            e (Mod.regularEndRingHom
              (MonObj.Γ.mapFunctorMonoidHom (upperStarFromPoint (Spec (.of K))) s) ≫ v) =
                fun j ↦ s * e v j) ∧
      (Set.range r).Finite ∧
      ∀ n : ℕ, ∃ U : X.Opens,
        (U : Set X) = {x | r x = n} ∧ IsClosed (U : Set X) ∧
        (∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage U.toScheme,
          ∀ i : C.I₀,
            Nonempty ((CondensedRing.upperStar R.X (C.f i)).obj
              ((CondensedRing.upperStar R.X U.ι).obj L) ≅
                Mod.finiteFree (condensedRingObj R.X (C.X i)) n)) ∧
        (n = 0 → IsZero ((CondensedRing.upperStar R.X U.ι).obj L)) := by
  classical
  obtain ⟨r, U, hrmem, hclosed, hgeom, hcover⟩ := coverRankData R.X hF X L hL
  refine ⟨r, ?_, ?_, r.range_finite, ?_⟩
  · intro r'
    constructor
    · exact rank_eq_of_geometricFibres R.X hF L r r' hgeom
    · rintro rfl
      exact hgeom
  · intro K _ _ b
    obtain ⟨e⟩ := hgeom K b
    exact ⟨pointSectionMap_bijective R.X K, pointSectionCoordinates R.X K _ _ e⟩
  · intro n
    obtain ⟨D, hD⟩ := hcover n
    exact ⟨U n, Set.ext (fun x ↦ hrmem x n), hclosed n,
      iteratedRankCover R.X L (U n) n D hD⟩

end AlgebraicGeometry.ProEtale
