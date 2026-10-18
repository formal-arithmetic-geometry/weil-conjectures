/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.RingTheory.FiniteType
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf

import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
import Sheaf.AlgebraicGeometry.PrimeLisseAffineCurveShriekConstructibility
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import Sheaf.AlgebraicGeometry.EtaleShriekRelativeMayerVietoris
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Constructibility for lisse coefficients on an open relative affine line

Source: Stacks Project, Tag 0GKY, `lemma-loc-constant-shriek-rel-dim-1`, specialized to
finite coefficient rings and affine finite-type integer bases
(blueprint: lem-weil-pbc-etale-lisse-open-relative-line-constructibility).
-/

@[expose] public section

universe u


open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Induct on an additive annihilator, without changing the coefficient ring.
For `n = p * m`, the kernel of `p` is killed by `p` and its coimage by `m < n`. -/
private theorem finiteLisse_prime_devissage
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (X : Scheme.{u})
    (P : ObjectProperty (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hzero : ∀ F, CategoryTheory.Limits.IsZero F → P F)
    (hext : ∀ (S : ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      S.ShortExact → P S.X₁ → P S.X₃ → P S.X₂)
    (hprime : ∀ (p : ℕ), p.Prime →
      ∀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      Scheme.IsFiniteLocallyConstantSheaf F → p • 𝟙 F = 0 → P F)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : Scheme.IsFiniteLocallyConstantSheaf F) : P F := by
  have induction_step (n : ℕ) : 0 < n →
      ∀ (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
        Scheme.IsFiniteLocallyConstantSheaf G → n • 𝟙 G = 0 → P G := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn G hG hkill
      have := hG
      by_cases hone : n = 1
      · have hid : 𝟙 G = 0 := by simpa [hone] using hkill
        exact hzero G ((CategoryTheory.Limits.IsZero.iff_id_eq_zero G).2 hid)
      · obtain ⟨p, hp, m, hpm⟩ := Nat.exists_prime_and_dvd hone
        have hm : 0 < m := by
          by_contra h
          have : m = 0 := Nat.eq_zero_of_not_pos h
          simp [this] at hpm
          omega
        have hmn : m < n := by
          rw [hpm]
          exact lt_mul_of_one_lt_left hm hp.one_lt
        let φ : G ⟶ G := p • 𝟙 G
        let K := CategoryTheory.Limits.kernel φ
        let Q := CategoryTheory.Limits.cokernel (CategoryTheory.Limits.kernel.ι φ)
        let S := ShortComplex.mk (CategoryTheory.Limits.kernel.ι φ)
          (CategoryTheory.Limits.cokernel.π (CategoryTheory.Limits.kernel.ι φ))
          (CategoryTheory.Limits.cokernel.condition (CategoryTheory.Limits.kernel.ι φ))
        have hS : S.ShortExact :=
          { exact := ShortComplex.exact_cokernel (CategoryTheory.Limits.kernel.ι φ) }
        have : Scheme.IsFiniteLocallyConstantSheaf K :=
          Scheme.IsFiniteLocallyConstantSheaf.kernel φ
        have : Scheme.IsFiniteLocallyConstantSheaf Q :=
          Scheme.IsFiniteLocallyConstantSheaf.cokernel (CategoryTheory.Limits.kernel.ι φ)
        have hK : p • 𝟙 K = 0 := by
          apply (cancel_mono (CategoryTheory.Limits.kernel.ι φ)).mp
          simpa [K, φ, Preadditive.nsmul_comp, Preadditive.comp_nsmul] using
            CategoryTheory.Limits.kernel.condition φ
        have hQ : m • 𝟙 Q = 0 := by
          have hcomp : (m • 𝟙 G) ≫ φ = 0 := by
            simpa [φ, Preadditive.nsmul_comp, Preadditive.comp_nsmul,
              smul_smul, ← hpm, Nat.mul_comm] using hkill
          have h := Abelian.comp_coimage_π_eq_zero hcomp
          apply (cancel_epi
            (CategoryTheory.Limits.cokernel.π (CategoryTheory.Limits.kernel.ι φ))).mp
          simpa [Q, Abelian.coimage.π, Preadditive.nsmul_comp,
            Preadditive.comp_nsmul] using h
        exact hext S hS (hprime p hp K inferInstance hK)
          (ih m hmn hm Q inferInstance hQ)
  apply induction_step (ringChar Λ)
    (Nat.pos_of_ne_zero (CharP.char_ne_zero_of_finite Λ (ringChar Λ))) F hF
  ext V x
  change ringChar Λ • x = 0
  rw [← Nat.cast_smul_eq_nsmul Λ, CharP.cast_eq_zero Λ (ringChar Λ), zero_smul]

/-- All-degree constructibility is closed under the short-exact triangles in `D⁺`.
This turns additive-annihilator induction into a reduction to prime-torsion sheaves. -/
private theorem constructibleShriek_prime_devissage
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (c : Compactification f)
    (hprime : ∀ (p : ℕ), p.Prime →
      ∀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      Scheme.IsFiniteLocallyConstantSheaf F → p • 𝟙 F = 0 → ∀ q : ℤ,
        Scheme.IsConstructibleEtaleModuleSheaf
          ((_root_.DerivedCategory.Plus.homologyFunctor
            (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) q).obj
            ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj
              ((_root_.DerivedCategory.Plus.singleFunctor
                (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj F))))
    (L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hL : Scheme.IsFiniteLocallyConstantSheaf L) (q : ℤ) :
    Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) q).obj
        ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj
          ((_root_.DerivedCategory.Plus.singleFunctor
            (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj L))) := by
  let A := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  let B := Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  let Φ := rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c
  let Q := (_root_.DerivedCategory.homologyProperty
    (constructibleSheaf (ModuleCat.{u + 1} Λ) Y)).inverseImage
      (_root_.DerivedCategory.Plus.ι (C := B))
  let P : ObjectProperty A := fun F => Q (Φ.obj
    ((_root_.DerivedCategory.Plus.singleFunctor A 0).obj F))
  have hP : P L := by
    apply finiteLisse_prime_devissage Λ X P ?_ ?_ ?_ L hL
    · intro F hF n
      exact Scheme.IsConstructibleSheaf.of_isZero
        ((_root_.DerivedCategory.Plus.homologyFunctor B n).map_isZero
          (Φ.map_isZero ((_root_.DerivedCategory.Plus.singleFunctor A 0).map_isZero hF)))
    · intro S hS h₁ h₃
      obtain ⟨δ, hδ⟩ := hS.exists_mk_singleTrianglePlus_distinguished
      exact (Q.inverseImage Φ).ext_of_isTriangulatedClosed₂ _ hδ h₁ h₃
    · intro p hp F hF hkill n
      exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1
        (hprime p hp F hF hkill n)
  exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2 (hP q)

/-- Relative Mayer--Vietoris glues the affine cases. Quantifying over open immersions
allows restrictions to compose directly, while a finite affine-cover induction handles unions. -/
private theorem lisse_shriek_of_affine_opens
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} [IsNoetherian X] [Scheme.IsSeparated X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (haffine : ∀ {V : Scheme.{u}} (j : V ⟶ X) [IsOpenImmersion j] [IsAffine V],
      ∀ (F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      Scheme.IsFiniteLocallyConstantSheaf F →
      ∀ (c : Compactification (j ≫ f)) (q : ℤ),
      Scheme.IsConstructibleEtaleModuleSheaf
        ((_root_.DerivedCategory.Plus.homologyFunctor
          (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) q).obj
          ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj
            ((_root_.DerivedCategory.Plus.singleFunctor
              (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj F))))
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : Scheme.IsFiniteLocallyConstantSheaf F) (c : Compactification f) (q : ℤ) :
    Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) q).obj
        ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj
          ((_root_.DerivedCategory.Plus.singleFunctor
            (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj F)))  := by
  let A := ModuleCat.{u + 1} Λ
  let D := Sheaf Y.smallEtaleTopology A
  let Q := (_root_.DerivedCategory.homologyProperty (constructibleSheaf A Y)).inverseImage
    (_root_.DerivedCategory.Plus.ι (C := D))
  let P : X.Opens → Prop := fun W =>
    ∀ {Z : Scheme.{u}} (j : Z ⟶ X) [IsOpenImmersion j], j.opensRange = W →
      ∀ (G : Sheaf Z.smallEtaleTopology A), Scheme.IsFiniteLocallyConstantSheaf G →
      ∀ (d : Compactification (j ≫ f)), Q
        ((rightDerivedLowerShriekOfCompactificationPlus A d).obj
          ((_root_.DerivedCategory.Plus.singleFunctor
            (Sheaf Z.smallEtaleTopology A) 0).obj G))
  have hAff : ∀ W : X.Opens, IsAffineOpen W → P W := by
    intro W hW Z j _ hj G hG d n
    have : IsAffine W.toScheme := hW
    let e : Z ≅ W.toScheme := IsOpenImmersion.isoOfRangeEq j W.ι
      (by simpa using congrArg (fun O : X.Opens => (O : Set X)) hj)
    have : IsAffine Z := IsAffine.of_isIso e.hom
    exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1
      (haffine j G hG d n)
  have hSup : ∀ U V : X.Opens, P U → P V → P (U ⊓ V) → P (U ⊔ V) := by
    intro U V hU hV hUV Z j _ hj G hG d
    have : IsLocallyNoetherian Z := isLocallyNoetherian_of_isOpenImmersion j
    have : TopologicalSpace.NoetherianSpace Z :=
      j.isOpenEmbedding.isInducing.noetherianSpace
    have : IsNoetherian Z := {}
    have : Scheme.IsSeparated Z := by
      constructor
      rw [← CategoryTheory.Limits.terminal.comp_from j]
      infer_instance
    have := hG
    let E := Sheaf Z.smallEtaleTopology A
    let K := (_root_.DerivedCategory.Plus.singleFunctor E 0).obj G
    have image (O : X.Opens) (hO : O ≤ U ⊔ V) : j ''ᵁ (j ⁻¹ᵁ O) = O := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, hj, inf_eq_right.mpr hO]
    have part (O : Z.Opens) (hP : P (j ''ᵁ O)) :
        Q ((rightDerivedLowerShriekOfCompactificationPlus A (d.precomp O.ι)).obj
          (((upperStar A O.ι).mapDerivedCategoryPlus).obj K)) := by
      let H := (upperStar A O.ι).obj G
      have hH : Scheme.IsFiniteLocallyConstantSheaf H :=
        Scheme.IsFiniteLocallyConstantSheaf.upperStar _ G
      have h := hP (O.ι ≫ j) (by simp [Scheme.Hom.opensRange_comp]) H hH
        ((d.precomp O.ι).copy (Category.assoc _ _ _))
      exact Q.prop_of_iso
        ((rightDerivedLowerShriekOfCompactificationPlus A (d.precomp O.ι)).mapIso
          (((upperStar A O.ι).mapDerivedCategoryPlusSingleFunctor 0).app G)).symm h
    have h₁ := part (j ⁻¹ᵁ U) (by rw [image U le_sup_left]; exact hU)
    have h₂ := part (j ⁻¹ᵁ V) (by rw [image V le_sup_right]; exact hV)
    have h₀ := part ((j ⁻¹ᵁ U) ⊓ (j ⁻¹ᵁ V)) (by
      rw [← Scheme.Hom.preimage_inf, image (U ⊓ V) (inf_le_left.trans le_sup_left)]
      exact hUV)
    have hc : (j ⁻¹ᵁ U) ⊔ (j ⁻¹ᵁ V) = ⊤ := by
      rw [← Scheme.Hom.preimage_sup, ← hj, Scheme.Hom.preimage_opensRange]
    obtain ⟨α, β, δ, ht⟩ := exists_distinguished_relativeMayerVietoris Λ (j ≫ f)
      (j ⁻¹ᵁ U) (j ⁻¹ᵁ V)
      (TopologicalSpace.NoetherianSpace.isCompact _)
      (TopologicalSpace.NoetherianSpace.isCompact _) hc
      (d.precomp (j ⁻¹ᵁ U).ι) (d.precomp (j ⁻¹ᵁ V).ι)
      (d.precomp ((j ⁻¹ᵁ U) ⊓ (j ⁻¹ᵁ V)).ι) d K
    have h₀' : Q (CategoryTheory.Pretriangulated.Triangle.mk α β δ).obj₁ := by
      exact h₀
    let CU := (rightDerivedLowerShriekOfCompactificationPlus A
      (d.precomp (j ⁻¹ᵁ U).ι)).obj
        (((upperStar A (j ⁻¹ᵁ U).ι).mapDerivedCategoryPlus).obj K)
    let CV := (rightDerivedLowerShriekOfCompactificationPlus A
      (d.precomp (j ⁻¹ᵁ V).ι)).obj
        (((upperStar A (j ⁻¹ᵁ V).ι).mapDerivedCategoryPlus).obj K)
    have hsum : Q (CategoryTheory.Pretriangulated.Triangle.mk α β δ).obj₂ := by
      intro n
      have : (_root_.DerivedCategory.Plus.homologyFunctor D n).Additive :=
        inferInstanceAs ((_root_.DerivedCategory.Plus.ι (C := D)) ⋙
          _root_.DerivedCategory.homologyFunctor D n).Additive
      have : CategoryTheory.Limits.PreservesBinaryBiproduct CU CV
          (_root_.DerivedCategory.Plus.homologyFunctor D n) :=
        CategoryTheory.Limits.preservesBinaryBiproduct_of_preservesBiproduct _ CU CV
      have h₁n := h₁ n
      have h₂n := h₂ n
      have : Scheme.IsConstructibleSheaf
          ((_root_.DerivedCategory.Plus.homologyFunctor D n).obj CU) := h₁n
      have : Scheme.IsConstructibleSheaf
          ((_root_.DerivedCategory.Plus.homologyFunctor D n).obj CV) := h₂n
      exact (constructibleSheaf A Y).prop_of_iso
        ((_root_.DerivedCategory.Plus.homologyFunctor D n).mapBiprod CU CV).symm
        (Scheme.IsConstructibleSheaf.biprod _ _)
    exact Q.ext_of_isTriangulatedClosed₃ _ ht h₀' hsum
  classical
  have hfin : ∀ (n : ℕ) (s : Finset X.Opens), s.card ≤ n →
      (∀ V ∈ s, IsAffineOpen V) → P (s.sup id) := by
    intro n
    induction n with
    | zero =>
      intro s hs _
      rw [Finset.card_eq_zero.mp (Nat.le_zero.mp hs), Finset.sup_empty]
      exact hAff _ (isAffineOpen_bot X)
    | succ n ih =>
      intro s hs ha
      induction s using Finset.induction_on with
      | empty => exact hAff _ (isAffineOpen_bot X)
      | insert V s hV _ =>
        rw [Finset.card_insert_of_notMem hV] at hs
        have hVs := ha V (Finset.mem_insert_self V s)
        have has : ∀ W ∈ s, IsAffineOpen W :=
          fun W hW => ha W (Finset.mem_insert_of_mem hW)
        rw [Finset.sup_insert]
        refine @hSup _ _ (hAff _ hVs) (ih s (by omega) has) ?_
        have hi : V ⊓ s.sup id = (s.image (V ⊓ ·)).sup id := by
          rw [Finset.sup_inf_distrib_left, Finset.sup_image]
          rfl
        rw [id_eq, hi]
        refine @ih _ (Finset.card_image_le.trans (by omega)) ?_
        intro W hW
        obtain ⟨W', hW', rfl⟩ := Finset.mem_image.mp hW
        exact hVs.inf (has W' hW')
  have hP : ∀ W : X.Opens, P W := by
    intro W
    obtain ⟨s, hs, hW⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp
      (TopologicalSpace.NoetherianSpace.isCompact (W : Set X))
    have heq : (hs.toFinset.image Subtype.val).sup id = W := by
      apply le_antisymm
      · simp only [Finset.sup_le_iff, Finset.mem_image, Set.Finite.mem_toFinset, id_eq,
          forall_exists_index, and_imp]
        rintro _ V hV rfl
        rw [hW]
        exact le_iSup₂ (f := fun (i : X.affineOpens) (_ : i ∈ s) => (i : X.Opens)) V hV
      · rw [hW]
        exact iSup₂_le fun V hV => Finset.le_sup
          (f := id) (Finset.mem_image_of_mem _ (hs.mem_toFinset.mpr hV))
    rw [← heq]
    refine @hfin _ _ le_rfl ?_
    intro V hV
    obtain ⟨V', _, rfl⟩ := Finset.mem_image.mp hV
    exact V'.2
  have h := hP ⊤ (𝟙 X) (Scheme.Hom.opensRange_of_isIso _) F hF
    (c.copy (Category.id_comp f)) q
  exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2 h


/-- Lisse sheaves with finite module values on an open relative affine line over a
finite-type integer base have constructible compactly supported cohomology sheaves.
Source: Stacks Project, Tag 0GKY, `lemma-loc-constant-shriek-rel-dim-1`
(blueprint: lem-weil-pbc-etale-lisse-open-relative-line-constructibility).

Proof:
Finite type over the integers makes the relative affine line Noetherian. The open source
is separated and Noetherian, hence has a finite affine cover with affine intersections.
Relative Mayer--Vietoris, the short-exact triangles, and Serre closure of constructible
sheaves reduce the result for the prescribed compactification to its affine restrictions.

On each affine restriction, induct on a positive additive annihilator of the sheaf, initially
`ringChar Λ`. If `n = p * m` with `p` prime, the kernel of multiplication by `p` is killed by
`p`, and the quotient by that kernel is killed by `m < n`. Both remain finite locally constant.
The short-exact triangle and the triangulated constructible-homology property combine these
two cases; annihilator one gives a zero object. Thus it suffices to treat a prime-torsion lisse
sheaf on an affine smooth relative curve. Apply the affine prime-torsion constructibility
lemma to that restriction: the open immersion is smooth of relative dimension zero, and
composition with the affine-line projection gives relative dimension one. -/
theorem isConstructibleEtaleModuleSheaf_lisse_openRelativeLine_shriek
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (R : Type u) [CommRing R] [Algebra.FiniteType ℤ R]
    (U : (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of R))).Opens)
    (L : Sheaf U.toScheme.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hL : ∃ d : Scheme.LocallyConstantDatum L, ∀ i : d.cover.I₀,
      ∃ M : ModuleCat.{u + 1} Λ, Finite M ∧
        Nonempty ((L.over (d.cover.etalePrecoverageToEtale i)) ≅
          (constantSheaf
            (U.toScheme.smallEtaleTopology.over (d.cover.etalePrecoverageToEtale i))
            (ModuleCat.{u + 1} Λ)).obj M))
    (c : Compactification
      (U.ι ≫ (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of R)) ↘ Spec (.of R))))
    (q : ℤ) :
    Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor
        (Sheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) q).obj
        ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj
          ((_root_.DerivedCategory.Plus.singleFunctor
            (Sheaf U.toScheme.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj L))) := by
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  let A := AffineSpace (ULift.{u} (Fin 1)) (Spec (.of R))
  have : IsLocallyNoetherian A :=
    LocallyOfFiniteType.isLocallyNoetherian (A ↘ Spec (.of R))
  have : IsNoetherian A := {}
  have : IsLocallyNoetherian U.toScheme :=
    LocallyOfFiniteType.isLocallyNoetherian U.ι
  have : TopologicalSpace.NoetherianSpace U.toScheme :=
    (Scheme.Hom.isOpenEmbedding U.ι).isInducing.noetherianSpace
  have : IsNoetherian U.toScheme := {}
  have : Scheme.IsSeparated U.toScheme := by
    constructor
    rw [← CategoryTheory.Limits.terminal.comp_from U.ι]
    infer_instance
  have hfinite : Scheme.IsFiniteLocallyConstantSheaf L :=
    (Scheme.finite_locally_constant_module_values_iff L).1.mp hL
  apply lisse_shriek_of_affine_opens Λ
    (U.ι ≫ (A ↘ Spec (.of R))) ?_ L hfinite c q
  intro V j _ _ F hF cV n
  have hdim : SmoothOfRelativeDimension 1 (A ↘ Spec (.of R)) := by
    simpa using (inferInstance : SmoothOfRelativeDimension
      (Nat.card (ULift.{u} (Fin 1))) (A ↘ Spec (.of R)))
  have : SmoothOfRelativeDimension 1 (j ≫ U.ι ≫ (A ↘ Spec (.of R))) := by
    have : SmoothOfRelativeDimension 0 (j ≫ U.ι) :=
      (AlgebraicGeometry.Etale.iff_smoothOfRelativeDimension_zero _).1 inferInstance
    exact smoothOfRelativeDimension_comp 0 1 (j ≫ U.ι) (A ↘ Spec (.of R))
  apply constructibleShriek_prime_devissage Λ (j ≫ U.ι ≫ (A ↘ Spec (.of R)))
    cV ?_ F hF n
  intro p hp G hG hkill m
  exact isConstructibleEtaleModuleSheaf_prime_lisse_affine_curve_shriek Λ R
    (j ≫ U.ι ≫ (A ↘ Spec (.of R)))
    p hp G hG hkill cV m

end AlgebraicGeometry.Etale
