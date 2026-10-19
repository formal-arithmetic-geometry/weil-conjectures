/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q19
-/
module

public import Sheaf.Paper.OpenImmersionTensorPiece
public import Sheaf.Paper.ProjectionCompactification
public import Sheaf.Paper.ProEtaleProjectionFormulaArrows
public import Sheaf.AlgebraicGeometry.ProEtaleCanonicalPullbackComposition
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteCoefficientDirectImage
public import Sheaf.Paper.RingedProjectionRestriction
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.CategoryTheory.Monoidal.Rigid.Flat
import WeilConjectures.CategoryTheory.Monoidal.Dualizable
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients

/-!
# The compactified projection formula for locally perfect coefficients

Source: Weil blueprint, proper base change, lemma 1271
(blueprint: lemma-weil-pbc-projection-formula-compactified).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme
section Open

variable {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
  (R : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
  (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (c : (proEtaleSheafInverseImage j CommRingCat.{u + 1}).obj R ≅ S)

/-- The derived open adjunction is the localization of the termwise ordinary adjunction.
Source: Stacks, Tags 03DI and 015F
(blueprint: lemma-weil-pbc-projection-formula-compactified). -/
def proEtaleRingDerivedOpenAdjunction :
    proEtaleRingDerivedOpenExtension j R S c ⊣ proEtaleRingDerivedPullback j R S c :=
  letI : CatCommSq
      ((proEtaleRingOpenExtension j R S c).mapHomologicalComplex (ComplexShape.up ℤ))
      DerivedCategory.Q DerivedCategory.Q (proEtaleRingDerivedOpenExtension j R S c) :=
    ⟨(proEtaleRingOpenExtension j R S c).mapDerivedCategoryFactors.symm⟩
  letI : CatCommSq
      ((proEtaleRingModulePullback j R S c).mapHomologicalComplex (ComplexShape.up ℤ))
      DerivedCategory.Q DerivedCategory.Q (proEtaleRingDerivedPullback j R S c) :=
    ⟨(proEtaleRingModulePullback j R S c).mapDerivedCategoryFactors.symm⟩
  let am : proEtaleRingOpenExtension j R S c ⊣ proEtaleRingModulePullback j R S c :=
    Adjunction.ofIsRightAdjoint _
  (am.mapHomologicalComplex (ComplexShape.up ℤ)).localization
      DerivedCategory.Q (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
      DerivedCategory.Q (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
      (proEtaleRingDerivedOpenExtension j R S c) (proEtaleRingDerivedPullback j R S c)

/-- The adjunction projection is exactly the transpose of unit tensor identity.
Source: Stacks, Tags 03DI and 07A4
(blueprint: lemma-weil-pbc-projection-formula-compactified). -/
def proEtaleOpenProjection
    (a : ProEtaleTensorModel Z R) (b : ProEtaleTensorModel X S)
    (E : DerivedCategory (proEtaleRingModules X S))
    (M : DerivedCategory (proEtaleRingModules Z R)) :
    (proEtaleRingDerivedOpenExtension j R S c).obj
        (b.tensor.obj (E, (proEtaleRingDerivedPullback j R S c).obj M)) ⟶
      a.tensor.obj ((proEtaleRingDerivedOpenExtension j R S c).obj E, M) :=
  ((proEtaleRingDerivedOpenAdjunction j R S c).homEquiv _ _).symm
    (b.tensor.map (Prod.mkHom ((proEtaleRingDerivedOpenAdjunction j R S c).unit.app E)
      (𝟙 _)) ≫ (proEtaleCanonicalTensorComparison j R S c a b).inv.app
        ((proEtaleRingDerivedOpenExtension j R S c).obj E, M))

end Open
end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.ProjectionRestriction

variable {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
  [EssentiallySmall.{u + 1} C] [EssentiallySmall.{u + 1} D]
  {J : GrothendieckTopology C} {H : GrothendieckTopology D}
  {R : Sheaf J CommRingCat.{u + 1}} {S : Sheaf H CommRingCat.{u + 1}}
  {F : C ⥤ D} (o : Operation F R S) (t : o.OrdinaryTensor)

/-- The pure-section comparison is natural and has its uniquely determined unit map.
Source: Stacks, Tag 03EL; definition 1264
(blueprint: lemma-weil-pbc-projection-formula-compactified).
Proof: test on pure tensors after the canonical module unit. Naturality follows from
naturality of that unit and bilinearity. Multiplication gives the unit comparison;
the same pure-tensor equation forces it uniquely. -/
-- STATEMENT-DISPUTED: Operation permits the empty-site functor into a one-object site.
-- Pullback is zero and OrdinaryTensor holds vacuously, but its unit cannot be the
-- nonzero target coefficient ring. A unit-preservation hypothesis is missing.
theorem restrictionProjectionTensor_normalized :
    (∀ (M M' N N' : Mod R) (v : M ⟶ M') (z : N ⟶ N'),
      o.pullback.map (((tensor R).map v).app N ≫ ((tensor R).obj M').map z) ≫
          (t.iso M' N').hom =
        (t.iso M N).hom ≫ ((tensor S).map (o.pullback.map v)).app (o.pullback.obj N) ≫
          ((tensor S).obj (o.pullback.obj M')).map (o.pullback.map z)) ∧
    ∃! j : o.pullback.obj (SheafOfModules.unit
        ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) ≅
        SheafOfModules.unit
          ((sheafCompose H (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S),
      ∀ M : Mod R,
        (t.iso M (SheafOfModules.unit
          ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))).hom ≫
          (SheafOfModules.monoidalCategory S).tensorHom (𝟙 (o.pullback.obj M)) j.hom ≫
          ((SheafOfModules.monoidalCategory S).rightUnitor (o.pullback.obj M)).hom =
        o.pullback.map (((SheafOfModules.monoidalCategory R).rightUnitor M).hom) := sorry

private lemma isDualizable_finite_power
    {A : Type*} [Category A] [Preadditive A] [MonoidalCategory A]
    [MonoidalPreadditive A] [HasFiniteBiproducts A]
    (U : A) (hU : IsDualizable U) (n : ℕ) :
    IsDualizable (∏ᶜ fun _ : Fin n ↦ U) := by
  let : HasBinaryBiproducts A := HasBinaryBiproducts.of_hasBinaryProducts
  induction n with
  | zero =>
    apply IsZero.isDualizable
    rw [IsZero.iff_id_eq_zero]
    apply Pi.hom_ext
    intro i
    exact Fin.elim0 i
  | succ n hn =>
    let V := ∏ᶜ fun _ : Fin n ↦ U
    let e : U ⊞ V ≅ ∏ᶜ (fun _ : Fin (n + 1) ↦ U) :=
      { hom := Pi.lift (Fin.cases biprod.fst (fun i ↦ biprod.snd ≫ Pi.π _ i))
        inv := biprod.lift (Pi.π _ 0) (Pi.lift fun i : Fin n ↦ Pi.π _ i.succ)
        hom_inv_id := by
          apply biprod.hom_ext
          · simp
          · apply Pi.hom_ext
            intro i
            simp
        inv_hom_id := by
          apply Pi.hom_ext
          intro i
          refine Fin.cases ?_ (fun j ↦ ?_) i
          · simp
          · simp }
    exact (hU.biprod hn).of_iso e


/-- Bounded finite-free retracts give resolving coefficients on every localized site.
Source: Stacks, Tags 06YS and 07A4; definition 1264
(blueprint: lemma-weil-pbc-projection-formula-compactified).
Proof: tensoring a retract of a finite free sheaf is exact, so each term is flat.
Bounded-above flat K-flatness applies at the upper bound. Site transport retains
these exact predicates without changing coefficient size. -/
theorem restrictionStrictPerfect_flat (A : CochainComplex (Mod R) ℤ)
    (P : SheafOfModules.StrictPerfectCoefficientPackageOnSite _ A)
    (hb : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (A.X n)) :
    resolving R A := by
  classical
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := SheafOfModules.tensorPreadditive R
  let : HasFiniteBiproducts (Mod R) := HasFiniteBiproducts.of_hasFiniteProducts
  have hflat (n : ℤ) : SheafOfModules.IsFlatOnSite (J := J) (R := R) (A.X n) := by
    have hd : IsDualizable (A.X n) :=
      IsDualizable.of_retract ⟨P.i n, P.p n, P.splitting n⟩
        (isDualizable_finite_power _ isDualizable_unit (P.N n))
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R (A.X n)).symm hd.flat.2
  obtain ⟨a, b, hab⟩ := hb
  have : A.IsStrictlyLE b := (CochainComplex.isStrictlyLE_iff A b).2
    (fun n hn ↦ hab n (Or.inr hn))
  exact ⟨(CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat A).1
    (SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite R A b hflat),
    hflat⟩

private lemma resolving_resolution (A : CochainComplex (Mod R) ℤ) :
    ∃ (P : CochainComplex (Mod R) ℤ) (_hp : resolving R P) (p : P ⟶ A),
      QuasiIso p ∧ Epi p := by
  obtain ⟨P, p, hk, hf, hq, he⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients A
  let := SheafOfModules.monoidalCategory R
  have hp : resolving R P := ⟨hk, fun n ↦ (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso R (P.X n)).symm (hf n)⟩
  exact ⟨P, hp, p, hq, HomologicalComplex.epi_of_epi_f p he⟩

private lemma total_quasiIso_right (a : TensorModel R)
    {P A B : CochainComplex (Mod R) ℤ} (p : P ⟶ A) (hq : QuasiIso p)
    (hb : resolving R B) : QuasiIso ((total R).map (Prod.mkHom p (𝟙 B))) := by
  let := SheafOfModules.monoidalCategory R
  let := a.preadditive
  have hc := (CochainComplex.mappingCone.quasiIso_iff_acyclic p).1 hq
  have ht := hb.1 (CochainComplex.mappingCone p) hc
  apply (CochainComplex.mappingCone.quasiIso_iff_acyclic _).2
  intro i
  have hh : (total R).map (Prod.mkHom p (𝟙 B)) =
      HomologicalComplex.mapBifunctorMap p (𝟙 B) (tensor R) (.up ℤ) := by
    ext n : 1
    apply HomologicalComplex₂.total.hom_ext (.up ℤ)
    intro x y h
    simp [total, HomologicalComplex.ι_mapBifunctorMap]
  rw [hh]
  exact (ht i).of_iso
    (CochainComplex.mapBifunctorMappingCone₁Iso p B (tensor R))

private lemma quasiIso_pullback_snd
    {A : Type*} [Category A] [Abelian A]
    {P Q M : CochainComplex A ℤ} (q : P ⟶ M) [Epi q] [QuasiIso q] (p : Q ⟶ M) :
    QuasiIso (pullback.snd q p) := by
  let S : ShortComplex (CochainComplex A ℤ) :=
    ShortComplex.mk (kernel.ι q) q (kernel.condition q)
  have hs : S.ShortExact := { exact := ShortComplex.exact_kernel q }
  have hk : (kernel q).Acyclic := hs.acyclic_X₁ inferInstance
  have ht := hs.pullback p
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hz (i : ℤ) : IsZero ((kernel q).homology i) :=
    (HomologicalComplex.exactAt_iff_isZero_homology _ i).1 (hk i)
  have hm : Mono (HomologicalComplex.homologyMap (pullback.snd q p) n) :=
    (ht.homology_exact₂ n).mono_g ((hz n).eq_of_src _ _)
  have he : Epi (HomologicalComplex.homologyMap (pullback.snd q p) n) :=
    (ht.homology_exact₃ n (n + 1) (by simp)).epi_f ((hz (n + 1)).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

/-- Mixed representatives are uniquely fixed by their square at every flat resolution.
Source: Stacks, Tag 07A4; definition 1264
(blueprint: lemma-weil-pbc-projection-formula-compactified).
Proof: resolve the first input by a flat K-flat complex. Tensoring that resolution
with the K-flat second input is a quasi-isomorphism. Compose its localization with
the resolving-model isomorphism. Common resolution refinements give independence
and the displayed equation; its invertible left factor gives uniqueness. -/
theorem restrictionMixedTensor_existsUnique (a : TensorModel R)
    (A B : CochainComplex (Mod R) ℤ) (hb : resolving R B) :
    ∃! z : a.functor.obj (DerivedCategory.Q.obj A, DerivedCategory.Q.obj B) ≅
        DerivedCategory.Q.obj ((total R).obj (A, B)),
      ∀ (P : CochainComplex (Mod R) ℤ) (hp : resolving R P) (p : P ⟶ A), QuasiIso p →
        a.functor.map (Prod.mkHom (DerivedCategory.Q.map p) (𝟙 _)) ≫ z.hom =
          a.representative.inv.app (⟨P, hp⟩, ⟨B, hb⟩) ≫
            DerivedCategory.Q.map ((total R).map (Prod.mkHom p (𝟙 B))) := by
  classical
  let F := DerivedCategory.Q ⋙ (Functor.curry.obj a.functor).flip.obj (DerivedCategory.Q.obj B)
  let G := (Functor.curry.obj (total R)).flip.obj B ⋙ DerivedCategory.Q
  let rep (P : CochainComplex (Mod R) ℤ) (hp : resolving R P) :=
    a.representative.symm.app (⟨P, hp⟩, ⟨B, hb⟩)
  have nat {P P' : CochainComplex (Mod R) ℤ} (hp : resolving R P)
      (hp' : resolving R P') (v : P ⟶ P') :
      F.map v ≫ (rep P' hp').hom = (rep P hp).hom ≫ G.map v := by
    simpa [F, G, rep] using a.representative.inv.naturality
      (Prod.mkHom (ObjectProperty.homMk (X := ⟨P, hp⟩) (Y := ⟨P', hp'⟩) v)
        (𝟙 (⟨B, hb⟩ : (resolving R).FullSubcategory)))
  obtain ⟨P₀, hp₀, q, hq, he⟩ := resolving_resolution A
  let := hq
  let := he
  have : IsIso (F.map q) := by
    change IsIso ((a.functor.mapIso
      (Iso.prod (asIso (DerivedCategory.Q.map q)) (Iso.refl _))).hom)
    infer_instance
  have : IsIso (G.map q) := by
    have := total_quasiIso_right a q hq hb
    change IsIso (DerivedCategory.Q.map ((total R).map (Prod.mkHom q (𝟙 B))))
    infer_instance
  let z : F.obj A ≅ G.obj A := (asIso (F.map q)).symm ≪≫ rep P₀ hp₀ ≪≫ asIso (G.map q)
  have hz : F.map q ≫ z.hom = (rep P₀ hp₀).hom ≫ G.map q := by simp [z]
  have hzall (P : CochainComplex (Mod R) ℤ) (hp : resolving R P)
      (p : P ⟶ A) (hq' : QuasiIso p) :
      F.map p ≫ z.hom = (rep P hp).hom ≫ G.map p := by
    obtain ⟨T, ht, r, hr, _⟩ := resolving_resolution (pullback q p)
    have hs := quasiIso_pullback_snd q p
    let := hr
    let := hs
    let v : T ⟶ P := r ≫ pullback.snd q p
    let w : T ⟶ P₀ := r ≫ pullback.fst q p
    have hv : QuasiIso v := by dsimp [v]; infer_instance
    have hcomm : w ≫ q = v ≫ p := by simp [w, v, Category.assoc, pullback.condition]
    have : IsIso (F.map v) := by
      change IsIso ((a.functor.mapIso
        (Iso.prod (asIso (DerivedCategory.Q.map v)) (Iso.refl _))).hom)
      infer_instance
    apply (cancel_epi (F.map v)).1
    calc
      F.map v ≫ (F.map p ≫ z.hom) = F.map w ≫ (F.map q ≫ z.hom) := by
        rw [← Category.assoc, ← Functor.map_comp, ← hcomm, Functor.map_comp, Category.assoc]
      _ = F.map w ≫ ((rep P₀ hp₀).hom ≫ G.map q) := by rw [hz]
      _ = (rep T ht).hom ≫ G.map (w ≫ q) := by
        rw [← Category.assoc, nat ht hp₀ w, Category.assoc, ← Functor.map_comp]
      _ = (rep T ht).hom ≫ G.map (v ≫ p) := by rw [hcomm]
      _ = F.map v ≫ ((rep P hp).hom ≫ G.map p) := by
        rw [Functor.map_comp, ← Category.assoc, ← nat ht hp v, Category.assoc]
  refine ⟨z, hzall, ?_⟩
  intro z' hz'
  apply Iso.ext
  apply (cancel_epi (F.map q)).1
  exact (hz' P₀ hp₀ q hq).trans hz.symm

/-- The unique mixed representative comparison, with no arbitrary isomorphism choice.
Source: definition 1264 (blueprint: lemma-weil-pbc-projection-formula-compactified). -/
def restrictionMixedTensor (a : TensorModel R)
    (A B : CochainComplex (Mod R) ℤ) (hb : resolving R B) :=
  Classical.choose (restrictionMixedTensor_existsUnique a A B hb).exists

/-- The actual signed finite-total inverse on a localized ringed site. The chain map
is the existing tensorAdjunctionTotalInverse, whose summand theorem gives precisely
inclusion, finite-product inverse, retraction, with the same sign (-1)^a.
Source: definition 1264 (blueprint: lemma-weil-pbc-projection-formula-compactified). -/
def restrictionFiniteTotalInverse
    (a : TensorModel R) (b : TensorModel S)
    (tc : TensorComparison o.pullback o.leftModel a b t.iso)
    (E : Der S) (K : CochainComplex (Mod S) ℤ) (hK : K.IsKInjective)
    (rep : E ≅ DerivedCategory.Q.obj K)
    (B : CochainComplex (Mod R) ℤ)
    (P : SheafOfModules.StrictPerfectCoefficientPackageOnSite _ B)
    (hb : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (B.X n)) :
    o.right.obj (b.functor.obj (E, o.left.obj (DerivedCategory.Q.obj B))) ⟶
      a.functor.obj (o.right.obj E, DerivedCategory.Q.obj B) := by
  letI := SheafOfModules.monoidalCategory R
  letI := SheafOfModules.monoidalCategory S
  letI := a.preadditive
  letI := b.preadditive
  letI := o.kInjectives
  letI := hK
  let norm := restrictionProjectionTensor_normalized o t
  let j := Classical.choose norm.2.exists
  have hj := Classical.choose_spec norm.2.exists
  have he := fun {M M' N N' : Mod R} (v : M ⟶ M') (z : N ⟶ N') ↦ norm.1 M M' N N' v z
  let s := tensorAdjunctionTotalInverse o.pullback o.pushforward o.moduleAdjunction
    t.iso he j hj K B hb P.N P.i P.p P.splitting
  let A := (o.pushforward.mapHomologicalComplex (.up ℤ)).obj K
  let G := (o.pullback.mapHomologicalComplex (.up ℤ)).obj B
  let T := (total S).obj (K, G)
  let hf := restrictionStrictPerfect_flat B P hb
  let hg := tc.preserves B hf
  have hT : T.IsKInjective := tensorAdjunctionTotal_target_isKInjective o.pullback j K hK B
    hb P.N P.i P.p P.splitting
  let eA := o.right.mapIso rep ≪≫ o.pushforward.rightDerivedFunctorObjQIso K
  let eC := a.functor.mapIso (Iso.prod eA (Iso.refl _)) ≪≫ restrictionMixedTensor a A B hf
  letI := hT
  let eB := o.right.mapIso
    (b.functor.mapIso (Iso.prod rep (o.leftModel.factors.app B)) ≪≫
      restrictionMixedTensor b K G hg) ≪≫ o.pushforward.rightDerivedFunctorObjQIso T
  exact eB.hom ≫ DerivedCategory.Q.map s ≫ eC.inv

end AlgebraicGeometry.Scheme.ProjectionRestriction

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} {f : X ⟶ Y} (d : Compactification f) [QuasiCompact d.i]
  (RY : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
  (RZ : Sheaf (ProEt.topology d.Z) CommRingCat.{u + 1})
  (RX : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (cp : (proEtaleSheafInverseImage d.g CommRingCat.{u + 1}).obj RY ≅ RZ)
  (cj : (proEtaleSheafInverseImage d.i CommRingCat.{u + 1}).obj RZ ≅ RX)
  (a : ProEtaleTensorModel Y RY) (b : ProEtaleTensorModel d.Z RZ)
  (c : ProEtaleTensorModel X RX)
  (E : DerivedCategory (proEtaleRingModules X RX))
  (Q : DerivedCategory (proEtaleRingModules Y RY))

/-- The first arrow is the adjoint of counit tensor identity for p and j_!E.
Source: Weil blueprint, lemma 1271
(blueprint: lemma-weil-pbc-projection-formula-compactified). -/
def compactifiedProjectionPi :=
  derivedProjectionFormulaMate (proEtaleRingDerivedPullback d.g RY RZ cp)
    (proEtaleRingDerivedDirectImage d.g RY RZ cp)
    (proEtaleRingDerivedAdjunction d.g RY RZ cp) a.tensor b.tensor
    (proEtaleCanonicalTensorComparison d.g RY RZ cp a b)
    ((proEtaleRingDerivedOpenExtension d.i RZ RX cj).obj E) Q

/-- Theta is alpha inverse followed by extension of identity tensor c inverse.
The factorization identifies f with d.i followed by d.g; its coefficient identification
is exactly the composite identification, with no independent third choice.
Source: Weil blueprint, lemma 1271
(blueprint: lemma-weil-pbc-projection-formula-compactified). -/
def compactifiedProjectionTheta
    (hα : IsIso (proEtaleOpenProjection d.i RZ RX cj b c E
      ((proEtaleRingDerivedPullback d.g RY RZ cp).obj Q))) :
    b.tensor.obj ((proEtaleRingDerivedOpenExtension d.i RZ RX cj).obj E,
        (proEtaleRingDerivedPullback d.g RY RZ cp).obj Q) ≅
      (proEtaleRingDerivedOpenExtension d.i RZ RX cj).obj
        (c.tensor.obj (E, (proEtaleRingDerivedPullback (d.i ≫ d.g) RY RX
          (proEtaleRingCompositeCoefficients d.i d.g RY RZ RX cp cj)).obj Q)) :=
  (@asIso _ _ _ _ (proEtaleOpenProjection d.i RZ RX cj b c E
    ((proEtaleRingDerivedPullback d.g RY RZ cp).obj Q)) hα).symm ≪≫
      (proEtaleRingDerivedOpenExtension d.i RZ RX cj).mapIso
        (c.tensor.mapIso (Iso.prod (Iso.refl E)
          ((proEtaleCanonicalPullbackComposition d.i d.g RY RZ RX cp cj).app Q).symm))

/-- The ordered forward map pi followed by Rp_* theta.
Source: Weil blueprint, lemma 1271
(blueprint: lemma-weil-pbc-projection-formula-compactified). -/
def compactifiedProjectionForward
    (hα : IsIso (proEtaleOpenProjection d.i RZ RX cj b c E
      ((proEtaleRingDerivedPullback d.g RY RZ cp).obj Q))) :=
  compactifiedProjectionPi d RY RZ RX cp cj a b E Q ≫
    (proEtaleRingDerivedDirectImage d.g RY RZ cp).map
      (compactifiedProjectionTheta d RY RZ RX cp cj b c E Q hα).hom

/-- The reverse ordered map Rp_* theta inverse followed by rho = pi inverse.
Source: Weil blueprint, lemma 1271
(blueprint: lemma-weil-pbc-projection-formula-compactified). -/
def compactifiedProjectionReverse
    (hα : IsIso (proEtaleOpenProjection d.i RZ RX cj b c E
      ((proEtaleRingDerivedPullback d.g RY RZ cp).obj Q)))
    (hπ : IsIso (compactifiedProjectionPi d RY RZ RX cp cj a b E Q)) :=
  (proEtaleRingDerivedDirectImage d.g RY RZ cp).map
      (compactifiedProjectionTheta d RY RZ RX cp cj b c E Q hα).inv ≫
    @inv _ _ _ _ (compactifiedProjectionPi d RY RZ RX cp cj a b E Q) hπ

/-- The compactified perfect projection formula with its exact ordered inverse.
The local strict-perfect normalization of rho is recorded below on canonical slice
operations. No uniform bound, completion, constructibility or boundedness of E occurs.
Source: Weil blueprint, proper base change, lemma 1271
(blueprint: lemma-weil-pbc-projection-formula-compactified).
Proof: (1) The exact open adjunction defines alpha for arbitrary coefficients by the
unit transpose. (2) Localize at each site object. The Hom adjunction chain, using the
counit-compatible direct-image restriction comparison, identifies restriction of j_!
with local extension and carries its unit to the local unit. Tensor and pullback
restriction comparisons therefore carry alpha to exactly the local transpose.
(3) Cover each object by strict-perfect representatives of Q. Signed totalization
proves that the local pi is inverse to the specified finite-total rho. Naturality
transports this pair along each representative isomorphism. Local detection of
isomorphisms proves global pi invertible; restriction of its inverse is the specified
local inverse by uniqueness. (4) Pull the cover back to the intermediate site. Exact
coefficient-identified pullback preserves finite-free splittings and boundedness on
each cover member. The open-piece theorem makes each local alpha invertible; local
detection makes global alpha invertible. (5) The canonical composition comparison is
invertible, so theta is invertible with inverse alpha followed by j_!(1 tensor c).
(6) Rp_* preserves the two inverse equations. Associativity cancels theta against its
inverse and pi against rho in both orders. The endpoints are Rp_*j_! by definition,
including for unbounded E and locally varying bounds. -/
theorem proEtaleProjectionFormula_compactified
    (hQ : IsProEtaleSitePerfect Y RY Q) :
    ∃ hα : IsIso (proEtaleOpenProjection d.i RZ RX cj b c E
        ((proEtaleRingDerivedPullback d.g RY RZ cp).obj Q)),
    ∃ hπ : IsIso (compactifiedProjectionPi d RY RZ RX cp cj a b E Q),
      IsIso (compactifiedProjectionForward d RY RZ RX cp cj a b c E Q hα) ∧
      compactifiedProjectionForward d RY RZ RX cp cj a b c E Q hα ≫
        compactifiedProjectionReverse d RY RZ RX cp cj a b c E Q hα hπ = 𝟙 _ ∧
      compactifiedProjectionReverse d RY RZ RX cp cj a b c E Q hα hπ ≫
        compactifiedProjectionForward d RY RZ RX cp cj a b c E Q hα = 𝟙 _ := sorry


/-- Restriction of rho is exactly the signed-total inverse on each bounded local
strict-perfect representative, transported by its specified representative isomorphism.
Here Global and Local are the recorded canonical module operations on the original
site and its slice: their section, counit, tensor and K-flat normalization fields fix
all comparisons. This is the same projection inverse as above in that canonical
presentation; left-adjoint uniqueness identifies the two pullback presentations.
Source: Weil blueprint, lemma 1271, local inverse clause
(blueprint: lemma-weil-pbc-projection-formula-compactified).
Proof: on a strict-perfect local representative the signed-total chain inverse has
both inverse identities by totalization. Transport it along u using naturality of pi
and the tensor comparisons. The restriction theorem identifies the restricted global
pi with the local pi under its canonical sourceIso and targetIso. Restriction preserves
the global inverse equations. Uniqueness of an inverse now gives exactly the equation
below. This argument works on every cover member and every chosen representative,
without asserting that arbitrary derived morphisms glue or that evaluation is faithful. -/
theorem compactifiedProjection_rho_local
    (g : ProjectionRestriction.Global d.g RY RZ cp)
    (hQ : IsProEtaleSitePerfect Y RY Q) :
    ∃ hπ : IsIso (derivedProjectionFormulaMate g.operation.left g.operation.right
        g.operation.derivedAdjunction g.tensorY.functor g.tensorX.functor
        g.tensorComparison.comparison
        ((proEtaleRingDerivedOpenExtension d.i RZ RX cj).obj E) Q),
    ∀ (V : Y.ProEt) (l : ProjectionRestriction.Local d.g RY RZ cp g V)
      (B : CochainComplex (ProjectionRestriction.Mod (RY.over V)) ℤ)
      (P : SheafOfModules.StrictPerfectCoefficientPackageOnSite _ B)
      (hb : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (B.X n))
      (uQ : l.restrictionY.model.functor.obj Q ≅ DerivedCategory.Q.obj B)
      (K : CochainComplex (ProjectionRestriction.Mod
        (RZ.over ((proEtaleBaseChange d.g).obj V))) ℤ) (hK : K.IsKInjective)
      (rep : l.restrictionX.model.functor.obj
        ((proEtaleRingDerivedOpenExtension d.i RZ RX cj).obj E) ≅ DerivedCategory.Q.obj K),
      l.restrictionY.model.functor.map
          (@inv _ _ _ _ (derivedProjectionFormulaMate g.operation.left g.operation.right
            g.operation.derivedAdjunction g.tensorY.functor g.tensorX.functor
            g.tensorComparison.comparison
            ((proEtaleRingDerivedOpenExtension d.i RZ RX cj).obj E) Q) hπ) =
        (l.targetIso ((proEtaleRingDerivedOpenExtension d.i RZ RX cj).obj E) Q).hom ≫
          l.operation.right.map
            (l.tensorX.functor.map (Prod.mkHom (𝟙 _) (l.operation.left.map uQ.hom))) ≫
          ProjectionRestriction.restrictionFiniteTotalInverse l.operation l.ordinaryTensor
            l.tensorY l.tensorX l.tensorComparison
            (l.restrictionX.model.functor.obj
              ((proEtaleRingDerivedOpenExtension d.i RZ RX cj).obj E))
            K hK rep B P hb ≫
          l.tensorY.functor.map (Prod.mkHom (𝟙 _) uQ.inv) ≫
          (l.sourceIso ((proEtaleRingDerivedOpenExtension d.i RZ RX cj).obj E) Q).inv := sorry

end AlgebraicGeometry.Scheme
