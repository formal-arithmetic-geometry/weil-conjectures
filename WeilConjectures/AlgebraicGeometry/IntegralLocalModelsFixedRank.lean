/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.LisseQlbarRepresentations
import all WeilConjectures.AlgebraicGeometry.StratifiedLatticeRank
import WeilConjectures.AlgebraicGeometry.FpqcLabelledClopenDescent
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FinitelyPresentedStalk
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import WeilConjectures.AlgebraicGeometry.RegularExtensionComparison
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import Mathlib.CategoryTheory.Preadditive.HomOrthogonal
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.SepClosedPoint
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IsSepClosed
import WeilConjectures.CategoryTheory.ModuleObjects.RegularEnd

/-! # Fixed ranks of integral local models -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped TensorProduct CategoryTheory.Obj
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.LisseQlbar

namespace AlgebraicGeometry.ProEtale.RealIntegral

variable (l : ℕ) [Fact l.Prime]
variable {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
  (x : Spec (.of Ω) ⟶ X) (G : ProfiniteGrp.{u})
  [∀ P, MulAction G ((FiniteEtale.fiber x).obj P)]
  (c : Correspondence l x G)

-- A commutative coefficient object has a commutative ring of regular endomorphisms.
private theorem regularEnd_comm
    {C : Type*} [Category C] [Preadditive C] [MonoidalCategory C]
    [MonoidalPreadditive C] [SymmetricCategory C]
    (R : C) [MonObj R] [IsCommMonObj R]
    (f g : End (Mod.regular R)) : f * g = g * f := by
  have hs : Function.Surjective (Mod.regularEndRingHom (R := R)) := by
    intro h
    refine ⟨CategoryTheory.MonObj.Γ.ofHom ((CategoryTheory.MonObj.one (X := R)) ≫ h.hom), ?_⟩
    apply Mod.regular_hom_ext
    exact Mod.one_comp_regularLift_regular _
  obtain ⟨a, rfl⟩ := hs f
  obtain ⟨b, rfl⟩ := hs g
  rw [← map_mul, ← map_mul, mul_comm]

-- Pullback to a geometric point detects that the regular coefficient object is nonzero.
-- Invariant basis number for its commutative endomorphism ring then detects free rank.
private theorem integral_free_rank
    (E : PadicAlgCl.FiniteIntermediateField l) (W : Scheme.{u}) [Nonempty W]
    (m n : ℕ)
    (e : Mod.finiteFree (condensedRingObj (integerRing l E) W) m ≅
      Mod.finiteFree (condensedRingObj (integerRing l E) W) n) : m = n := by
  classical
  let Λ := integerRing l E
  let R := condensedRingObj Λ W
  let M := Mod.regular R
  let : CommRing (End M) := { (inferInstance : Ring (End M)) with
    mul_comm := regularEnd_comm R }
  have h10 : (1 : End M) ≠ 0 := by
    intro h
    have hR : IsZero R := by
      apply (IsZero.iff_id_eq_zero R).mpr
      exact congrArg (fun f : End M ↦ f.hom) h
    obtain ⟨w⟩ : Nonempty W := inferInstance
    let K := AlgebraicClosure (W.residueField w)
    let g : Spec (.of K) ⟶ W :=
      Spec.map (CommRingCat.ofHom (algebraMap (W.residueField w) K)) ≫
        W.fromSpecResidueField w
    have hK : IsZero (condensedRingObj Λ (Spec (.of K))) :=
      ((upperStar Ab.{u + 1} g).map_isZero hR).of_iso
        (asIso (condensedPullbackHom Λ g)).symm
    have hΛ : IsZero Λ :=
      IsZero.of_full_of_faithful_of_isZero (upperStarFromPoint (Spec (.of K))) Λ hK
    have hΓ := ((sheafSections (coherentTopology Profinite.{u}) Ab.{u + 1}).obj
      (op (⊤_ Profinite.{u}))).map_isZero hΛ
    have hh := ConcreteCategory.congr_hom (hΓ.eq_of_src (𝟙 _) 0)
      (ULift.up (ContinuousMap.const _ (1 : Padic.coefficientExtensionIntegers l E)))
    have hp : Nonempty (⊤_ Profinite.{u}) :=
      ⟨(terminalIsTerminal.from (Profinite.of PUnit.{u + 1})) PUnit.unit⟩
    exact one_ne_zero (congrArg (fun z ↦ z.down (Classical.choice hp)) hh)
  let : Nontrivial (End M) := nontrivial_of_ne 1 0 h10
  have ho : HomOrthogonal (fun _ : Unit ↦ M) := by
    intro i j hij
    exact (hij (Subsingleton.elim _ _)).elim
  obtain ⟨a, _⟩ := ho.equiv_of_iso (f := fun _ : Fin m ↦ ())
    (g := fun _ : Fin n ↦ ()) e
  simpa only [Fintype.card_fin] using Fintype.card_congr a

private def normalize_free
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : Y ⟶ X)
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (n : ℕ)
    (e : (((upperStar Ab.{u + 1} f).mapMod (condensedRingObj Λ X)).obj L) ≅
      Mod.finiteFree ((upperStar Ab.{u + 1} f).obj (condensedRingObj Λ X)) n) :
    (CondensedRing.upperStar Λ f).obj L ≅ Mod.finiteFree (condensedRingObj Λ Y) n :=
  (Mod.extendScalars (condensedPullbackHom Λ f)).mapIso e ≪≫
    Mod.finiteFreeIsoMap _ (Mod.regularExtensionIso _) n

-- Two comparisons with the same scalar action transport linear coordinates.
private def semilinear_coordinates
    {A B : Type*} [CommRing A] [CommRing B]
    {V U : Type*} [AddCommGroup V] [Module A V] [AddCommGroup U] [Module A U]
    {M N : Type*} [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N]
    (σ : A → B) (a : V ≃+ M) (b : U ≃+ N)
    (ha : ∀ s v, a (s • v) = σ s • a v)
    (hb : ∀ s v, b (s • v) = σ s • b v)
    (n : ℕ) (e : M ≃ₗ[B] (Fin n → N)) : V ≃ₗ[A] (Fin n → U) where
  __ := a.trans (e.toAddEquiv.trans (AddEquiv.piCongrRight fun _ ↦ b.symm))
  map_smul' s v := by
    ext j
    apply b.injective
    change b (b.symm (e (a (s • v)) j)) = b (s • b.symm (e (a v) j))
    simp only [ha, e.map_smul, hb, b.apply_symm_apply, Pi.smul_apply]

-- Descend only the rank labels needed for this cover.
private theorem rankLabels_constant
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hRank : ∀ (W : Scheme.{u}) [Nonempty W] (a b : ℕ),
      (Mod.finiteFree (condensedRingObj Λ W) a ≅
        Mod.finiteFree (condensedRingObj Λ W) b) → a = b)
    (X : Scheme.{u}) [ConnectedSpace X]
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (C : Scheme.Cover.{u} Scheme.proetalePrecoverage X) (n : C.I₀ → ℕ)
    (t : ∀ j, (CondensedRing.upperStar Λ (C.f j)).obj L ≅
      Mod.finiteFree (condensedRingObj Λ (C.X j)) (n j))
    (i : C.I₀) (z : C.X i) : ∀ j (_y : C.X j), n j = n i := by
  classical
  have compat (i j : C.I₀) :
      (fun _ : C.X i ↦ n i) ∘ pullback.fst (C.f i) (C.f j) =
        (fun _ : C.X j ↦ n j) ∘ pullback.snd (C.f i) (C.f j) := by
    funext w
    have : Nonempty ↑(pullback (C.f i) (C.f j)) := ⟨w⟩
    have ea := rankPullbackTrivialization Λ (C.f i)
      (pullback.fst (C.f i) (C.f j)) L (n i) (t i)
    have eb := rankPullbackTrivialization Λ (C.f j)
      (pullback.snd (C.f i) (C.f j)) L (n j) (t j)
    have ea' : Nonempty ((CondensedRing.upperStar Λ
        (pullback.snd (C.f i) (C.f j) ≫ C.f j)).obj L ≅
          Mod.finiteFree (condensedRingObj Λ (pullback (C.f i) (C.f j))) (n i)) := by
      simpa only [pullback.condition] using ea
    exact hRank _ (n i) (n j) (ea'.some.symm ≪≫ eb.some)
  obtain ⟨R, hR, _⟩ := labelledClopenPartition_existsUnique_of_fpqc C.f
    (Scheme.proetalePrecoverage_le_fpqcPrecoverage _ C.mem₀)
    (fun j _ ↦ n j) (by intro j a; by_cases h : n j = a <;> simp [h]) compat
  obtain ⟨hclosed, _hdisjoint, _hcover, hmem, _htest⟩ := hR
  have mem_cover (j : C.I₀) (y : C.X j) (r : ℕ) : C.f j y ∈ R r ↔ n j = r := by
    exact congrArg (fun S : Set (C.X j) ↦ y ∈ S) (hmem j r) |>.to_iff
  have hR : (R (n i) : Set X) = Set.univ :=
    IsClopen.eq_univ ⟨hclosed (n i), (R (n i)).isOpen⟩
      ⟨C.f i z, (mem_cover i z (n i)).mpr rfl⟩
  intro j y
  apply (mem_cover j y (n i)).mp
  change C.f j y ∈ (R (n i) : Set X)
  rw [hR]
  trivial

private theorem fixedRankCover
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hRank : ∀ (W : Scheme.{u}) [Nonempty W] (a b : ℕ),
      (Mod.finiteFree (condensedRingObj Λ W) a ≅
        Mod.finiteFree (condensedRingObj Λ W) b) → a = b)
    (X : Scheme.{u}) [ConnectedSpace X]
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (C : Scheme.Cover.{u} Scheme.proetalePrecoverage X) (n : C.I₀ → ℕ)
    (hn : ∀ j, Nonempty
      ((((upperStar Ab.{u + 1} (C.f j)).mapMod (condensedRingObj Λ X)).obj L) ≅
        Mod.finiteFree ((upperStar Ab.{u + 1} (C.f j)).obj
          (condensedRingObj Λ X)) (n j)))
    (i : C.I₀) (z : C.X i) (r : ℕ) (hrank : n i = r) :
    ∃ K : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ j : K.I₀, Nonempty
      ((((upperStar Ab.{u + 1} (K.f j)).mapMod (condensedRingObj Λ X)).obj L) ≅
        Mod.finiteFree ((upperStar Ab.{u + 1} (K.f j)).obj
          (condensedRingObj Λ X)) r) := by
  classical
  let t (j : C.I₀) := normalize_free Λ (C.f j) L (n j) (hn j).some
  have hconst := rankLabels_constant Λ hRank X L C n t i z
  apply rankCover C (fun j ↦ n j = n i)
    (fun j h ↦ ⟨fun y ↦ h (hconst j y)⟩)
    (fun Y f ↦ Nonempty
      ((((upperStar Ab.{u + 1} f).mapMod (condensedRingObj Λ X)).obj L) ≅
        Mod.finiteFree ((upperStar Ab.{u + 1} f).obj (condensedRingObj Λ X)) r))
  intro j hj
  rw [← hrank, ← hj]
  exact hn j

private theorem semilinear_finrank
    {A B : Type*} [CommRing A] [Nontrivial A] [CommRing B]
    {V U : Type*} [AddCommGroup V] [Module A V] [AddCommGroup U] [Module A U]
    {M N : Type*} [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N]
    (σ : A → B) (a : V ≃+ M) (b : U ≃+ N)
    (ha : ∀ s v, a (s • v) = σ s • a v)
    (hb : ∀ s v, b (s • v) = σ s • b v)
    (n : ℕ) (e : M ≃ₗ[B] (Fin n → N)) (unit : U ≃ₗ[A] A) :
    Module.finrank A V = n := by
  let q := semilinear_coordinates σ a b ha hb n e
  exact (q.trans (LinearEquiv.piCongrRight fun _ : Fin n ↦ unit)).finrank_eq.trans
    (Module.finrank_fin_fun (R := A))

-- Keep the coefficient object symbolic while constructing fibre coordinates.
private def fibre_coordinates
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] (x : Spec (.of Ω) ⟶ X)
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (n : ℕ)
    (e : (CondensedRing.upperStar Λ x).obj L ≅
      Mod.finiteFree (condensedRingObj Λ (Spec (.of Ω))) n) :
    (fibre Λ x).obj L ≃ₗ[
      CondensedRing.Evaluation.A (Scheme.ProEt.topology (Spec (.of Ω)))
        (condensedRingObj Λ (Spec (.of Ω))) (Scheme.ProEt.mk (𝟙 _))]
      (Fin n → (fibre Λ x).obj (Mod.regular (condensedRingObj Λ X))) := by
  let S := condensedRingObj Λ (Spec (.of Ω))
  let ev := CondensedRing.Evaluation.sections (Scheme.ProEt.topology (Spec (.of Ω))) S
    (Scheme.ProEt.mk (𝟙 _))
  let eU : (fibre Λ x).obj (Mod.regular (condensedRingObj Λ X)) ≅
      ev.obj (Mod.regular S) :=
    ev.mapIso (CondensedRing.upperStarObjRegularIso Λ x)
  let t₀ := (ev.mapIso e).toLinearEquiv.trans
    ((ev.mapBiproduct (fun _ : Fin n ↦ Mod.regular S)).toLinearEquiv.trans
      (ModuleCat.biproductIsoPi (fun _ : Fin n ↦ ev.obj (Mod.regular S))).toLinearEquiv)
  exact t₀.trans (LinearEquiv.piCongrRight fun _ : Fin n ↦ eU.toLinearEquiv.symm)

private theorem fibreEquivalence_finrank
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (A : Type) [CommRing A] [Nontrivial A] (scalar : A → condensedScalarRing Λ)
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] (x : Spec (.of Ω) ⟶ X)
    {G : Type u} [Group G]
    {P : ObjectProperty
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))}
    {Q : ObjectProperty (Rep.{u + 1} A G)}
    (e : FibreEquivalence Λ A scalar x G P Q)
    (tensor : TensorCompatibility Λ A scalar x G P Q e)
    (L : P.FullSubcategory) (n : ℕ)
    (freeIso : (CondensedRing.upperStar Λ x).obj L.obj ≅
      Mod.finiteFree (condensedRingObj Λ (Spec (.of Ω))) n) :
    Module.finrank A (e.functor.obj L).V = n := by
  let U : P.FullSubcategory := ⟨𝟙_ _, tensor.unit⟩
  let a : (e.functor.obj L).V ≃+ (fibre Λ x).obj L.obj :=
    (e.comparison.app L).addCommGroupIsoToAddEquiv
  let b : (e.functor.obj U).V ≃+ (fibre Λ x).obj U.obj :=
    (e.comparison.app U).addCommGroupIsoToAddEquiv
  have ha (s : A) (v : (e.functor.obj L).V) :
      a (s • v) = CondensedRing.affineScalarSection Λ (Spec (.of Ω)) (scalar s) • a v :=
    e.linear L s v
  have hb (s : A) (v : (e.functor.obj U).V) :
      b (s • v) = CondensedRing.affineScalarSection Λ (Spec (.of Ω)) (scalar s) • b v :=
    e.linear U s v
  obtain ⟨unitIso⟩ := tensor.unitTrivial
  let qU : (e.functor.obj U).V ≃ₗ[A] A :=
    ((forget₂ (Rep.{u + 1} A G) (ModuleCat.{u + 1} A)).mapIso unitIso).toLinearEquiv.trans
      (ULift.moduleEquiv : ULift.{u + 1} A ≃ₗ[A] A)
  exact semilinear_finrank
    (fun s : A ↦ CondensedRing.affineScalarSection Λ (Spec (.of Ω)) (scalar s))
    a b ha hb n (fibre_coordinates Λ x L.obj n freeIso) qU

private theorem fixedRankCover_of_fibre
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hRank : ∀ (W : Scheme.{u}) [Nonempty W] (a b : ℕ),
      (Mod.finiteFree (condensedRingObj Λ W) a ≅
        Mod.finiteFree (condensedRingObj Λ W) b) → a = b)
    (A : Type) [CommRing A] [Nontrivial A] (scalar : A → condensedScalarRing Λ)
    {X : Scheme.{u}} [ConnectedSpace X] {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ X) {G : Type u} [Group G]
    {P : ObjectProperty
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))}
    {Q : ObjectProperty (Rep.{u + 1} A G)}
    (e : FibreEquivalence Λ A scalar x G P Q)
    (tensor : TensorCompatibility Λ A scalar x G P Q e)
    (L : P.FullSubcategory) (hL : CondensedRing.LocallyFree (condensedRingObj Λ X) L.obj) :
    ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ j : C.I₀, Nonempty
      ((((upperStar Ab.{u + 1} (C.f j)).mapMod (condensedRingObj Λ X)).obj L.obj) ≅
        Mod.finiteFree ((upperStar Ab.{u + 1} (C.f j)).obj (condensedRingObj Λ X))
          (Module.finrank A (e.functor.obj L).V)) := by
  classical
  obtain ⟨C, hC⟩ := hL
  choose n hn using hC
  obtain ⟨i, g, hg⟩ := C.exists_comp_eq_of_isSepClosed_of_proetale x
  let t := normalize_free Λ (C.f i) L.obj (n i) (hn i).some
  have hpoint : Nonempty ((CondensedRing.upperStar Λ x).obj L.obj ≅
      Mod.finiteFree (condensedRingObj Λ (Spec (.of Ω))) (n i)) := by
    simpa only [hg] using rankPullbackTrivialization Λ (C.f i) g L.obj (n i) t
  have hrank := fibreEquivalence_finrank Λ A scalar x e tensor L (n i) hpoint.some
  obtain ⟨z⟩ : Nonempty (Spec (.of Ω)) := inferInstance
  exact fixedRankCover Λ hRank X L.obj C n hn i (g z) _ hrank.symm

/-- Local integral models on a connected scheme can all be chosen with the rank
of the given integral geometric fibre.

Source: latest blueprint, sec-purity-real-sheaves/sk-p-real-integral/
`p-real-integral.proof.md`, second paragraph, integral reconstruction and local rank
(blueprint: lem-real-integral-local-models-fixed-rank).

Proof in words:
1. Choose a pro-etale cover and finite free trivializations from L.property, with
ranks n_j. Extend scalars along the invertible coefficient pullback map and use the
regular-module extension comparison to normalize them to free models over the
pulled-back coefficient ring (lem-weil-pbc-regular-extension-comparison).
2. Free rank is invariant over every nonempty scheme W: endomorphisms of the regular
module are multiplications, so they form a commutative ring; it is nonzero, because
pulling back to an algebraically closed point of W and then along the point pullback
equivalence (lem-pe-point-module-pullback-equivalence) would make the coefficient
sheaf zero, while its sections over a point separate 0 and 1. Mathlib's
`HomOrthogonal.equiv_of_iso` and invariant basis number then compare multiplicities.
3. On each double overlap both normalized trivializations pull back; when the overlap
has a point, step 2 equates the labels n_i and n_j. Fpqc descent of labelled clopen
partitions (lem-sfb-fpqc-labelled-clopen-descent) gives clopen loci of X whose
preimage in each chart is that chart if its label matches and empty otherwise.
4. Lift x to a chart i of the cover and pull its trivialization back to x. Evaluation
preserves finite biproducts, and the scalar-compatible fibre comparisons of the
correspondence for L and for the tensor unit, together with the unit clause
identifying the unit's representation with A, give an A-linear isomorphism
M ≃ A^{n_i}; hence finrank_A M = n_i.
5. The clopen locus of label n_i contains the image of x, so it is all of connected X.
Every nonempty chart therefore has rank n_i; charts of another label are empty and are
discarded by the cover refinement of the stratified-rank proof
(det-lem-stratified-lattice-rank). This gives the claimed cover, including rank 0. -/
theorem integralLocalModels_fixedRank [ConnectedSpace X]
    (E : PadicAlgCl.FiniteIntermediateField l)
    (L : ObjectProperty.FullSubcategory
      (CondensedRing.LocallyFree (condensedRingObj (integerRing l E) X))) :
  ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X,
    ∀ j : 𝒰.I₀, Nonempty
      ((((ProEtale.upperStar Ab.{u + 1} (𝒰.f j)).mapMod
        (condensedRingObj (integerRing l E) X)).obj L.obj) ≅
      Mod.finiteFree
        ((ProEtale.upperStar Ab.{u + 1} (𝒰.f j)).obj
          (condensedRingObj (integerRing l E) X))
        (Module.finrank (Padic.coefficientExtensionIntegers l E)
          (((c.integral E).functor.obj L).V))) := by
  exact fixedRankCover_of_fibre (integerRing l E) (integral_free_rank l E)
    (Padic.coefficientExtensionIntegers l E) (integerScalar l E) x
    (c.integral E) (c.integralTensor E) L L.property

end AlgebraicGeometry.ProEtale.RealIntegral
