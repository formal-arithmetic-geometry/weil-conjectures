/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.AlgebraicGeometry.Properties
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import all WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartClosure
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleLocallyFreeModels
import WeilConjectures.AlgebraicGeometry.SixFunctors.StratificationGenericNeighborhood
import WeilConjectures.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends
import WeilConjectures.AlgebraicGeometry.GaloisBaseChangeFiberTransitivity
import WeilConjectures.Mathlib.Topology.Sober

/-!
# Dense lisse open for a condensed Weil module

Source: literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/
`sec-deligne-laumon-general/sec-reduction-to-the-relative-affine-line/`
`sk-prop-wgen-relative-line/thm-zl-relative-line-stratification.proof.md`,
paragraphs 1 and 4 (blueprint: lem-zl-condensed-weil-dense-lisse-open).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The restriction of a Weil isomorphism `θ : Φ^* M ≅ M` to a Frobenius-stable open:
for `j : U ⟶ X` and `φ : U ⟶ U` with `φ ≫ j = j ≫ Φ`, the composite
`φ^* j^* M ≅ (φ ≫ j)^* M = (j ≫ Φ)^* M ≅ j^* Φ^* M ≅ j^* M` of the pullback compositors,
the square and `j^* θ`.
Source: literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/
`sec-deligne-laumon-general/sec-reduction-to-the-relative-affine-line/`
`sk-prop-wgen-relative-line/thm-zl-relative-line-stratification.proof.md`,
paragraph 4, restriction of the Weil structure
(blueprint: lem-zl-condensed-weil-dense-lisse-open). -/
def restrictedWeilIso (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {U X : Scheme.{u}} {j : U ⟶ X} {φ : U ⟶ U} {Φ : X ⟶ X}
    (h : φ ≫ j = j ≫ Φ)
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (θ : (CondensedRing.upperStar Λ Φ).obj M ≅ M) :
    (CondensedRing.upperStar Λ φ).obj ((CondensedRing.upperStar Λ j).obj M) ≅
      (CondensedRing.upperStar Λ j).obj M :=
  (CondensedRing.upperStarComp Λ φ j).symm.app M ≪≫
    eqToIso (congrArg (fun g ↦ (CondensedRing.upperStar Λ g).obj M) h) ≪≫
    (CondensedRing.upperStarComp Λ j Φ).app M ≪≫ (CondensedRing.upperStar Λ j).mapIso θ

attribute [local irreducible] CondensedRing.upperStar CondensedRing.upperStarComp

private theorem genericPoint_homeomorph {X : Type u} [TopologicalSpace X]
    [QuasiSober X] [T0Space X] (e : X ≃ₜ X) {x : X} (hx : x ∈ genericPoints X) :
    e x ∈ genericPoints X := by
  apply mem_genericPoints_iff_forall_specializes.mpr
  intro y hy
  have h := (mem_genericPoints_iff_forall_specializes.mp hx) (e.symm y)
    (by simpa using hy.map e.symm.continuous)
  simpa using congrArg e h

/-- Descend the lisse restriction along the actual generic-neighborhood pullback. -/
private theorem lisse_neighborhood
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S : Scheme.{u}}
    (a : S ⟶ X) (W : X.Opens)
    [Surjective (pullback.fst W.ι a)] [IsClosedImmersion (pullback.fst W.ι a)]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsLisseCoefficientModule Λ ((CondensedRing.upperStar Λ a).obj M)) :
    IsLisseCoefficientModule Λ ((CondensedRing.upperStar Λ W.ι).obj M) :=
  heartLisse_closed_square Λ W.ι a (pullback.fst W.ι a) (pullback.snd W.ι a)
    pullback.condition M hM

/-- The union of the chosen generic neighborhoods contains all generic points. -/
private theorem genericPoints_subset_iSup (X : Scheme.{u})
    (η : irreducibleComponents X → X) (W : irreducibleComponents X → X.Opens)
    (hη : ∀ C, ∀ x : X, IsGenericPoint x C.val → x = η C)
    (hW : ∀ C, η C ∈ (⨆ C, W C : X.Opens)) :
    genericPoints X ⊆ ((⨆ C, W C : X.Opens) : Set X) := by
  intro x hx
  let C : irreducibleComponents X := ⟨closure {x}, hx⟩
  have heq : x = η C := hη C x rfl
  rw [heq]
  exact hW C

/-- Generic lissity from an actual finite stratification. -/
private theorem generic_lisse_of_stratification
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) [IsNoetherian X]
    (S : X.FiniteLocallyClosedStratification)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hS : ∀ a : Fin S.n,
      IsLisseCoefficientModule Λ ((CondensedRing.upperStar Λ (S.immersion a)).obj M)) :
    ∃ U : X.Opens, genericPoints X ⊆ (U : Set X) ∧
      IsLisseCoefficientModule Λ ((CondensedRing.upperStar Λ U.ι).obj M) := by
  classical
  obtain ⟨η, j, W, hW, _, hgeneric⟩ :=
    (X.exists_stratification_generic_neighborhoods S).2
  refine ⟨⨆ C, W C, genericPoints_subset_iSup X η W (fun C ↦ (hW C).2.1) hgeneric, ?_⟩
  apply heartLisse_iSup Λ W M
  intro C
  have : Surjective (pullback.fst (W C).ι (S.immersion (j C))) := (hW C).2.2.2.2.2.2.1
  have : IsClosedImmersion (pullback.fst (W C).ι (S.immersion (j C))) :=
    (hW C).2.2.2.2.2.2.2.1
  exact lisse_neighborhood Λ (S.immersion (j C)) (W C) M (hS (j C))

/-- Generic lissity as a property of an unbundled coefficient object. -/
private def GenericLisseObjectProperty
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    (X : Scheme.{u}) : Prop :=
  ∀ (hcomm : IsCommMonObj Λ),
    letI := hcomm
    ∀ (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
    IsConstantModelConstructible Λ X M →
      ∃ U : X.Opens, genericPoints X ⊆ (U : Set X) ∧
        IsLisseCoefficientModule Λ ((CondensedRing.upperStar Λ U.ι).obj M)

/-- Generic lissity from the coefficient heart. -/
private theorem generic_lisse_open (ℓ : ℕ) [Fact ℓ.Prime]
    (L : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    (hL : L = Profinite.padicAlgClCondensedRing ℓ)
    (X : Scheme.{u}) [IsNoetherian X] :
    GenericLisseObjectProperty (coefficientHeartRingObj L) X := by
  intro hcomm
  let := hcomm
  intro M hM
  obtain ⟨S, hS⟩ := (((coefficientHeart_closure ℓ L (Or.inr hL)).2 X).2.2.2.2.2.2 M).mp hM
  exact generic_lisse_of_stratification (coefficientHeartRingObj L) X S M hS

/-- Shrink an open containing the geometric generic points over the finite-field model. -/
private theorem dense_model_open (D : WeilConjectures.FiniteFieldDatum.{u})
    (Y₀ : Over (Spec (.of D.k₀)))
    (U : (pullback Y₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).Opens)
    (hgen : genericPoints ↥(pullback Y₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) : Scheme.{u}) ⊆ U.1) :
    ∃ U₀ : Y₀.left.Opens, Dense (U₀ : Set Y₀.left) ∧
      Set.range (pullback.snd U₀.ι (pullback.fst Y₀.hom
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))) ⊆ Set.range U.ι := by
  classical
  let b := Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))
  let X := pullback Y₀.hom b
  let p : X ⟶ Y₀.left := pullback.fst Y₀.hom b
  let : Y₀.left.Over (Spec (.of D.k₀)) := ⟨Y₀.hom⟩
  have : IsGalois D.k₀ D.k := inferInstance
  have hp : IsClosedMap p := isClosedMap_pullback_fst_of_isGalois D.k₀ D.k Y₀.left
  let U₀ : Y₀.left.Opens := ⟨(p '' (U : Set X)ᶜ)ᶜ,
    (hp _ U.isOpen.isClosed_compl).isOpen_compl⟩
  have hpre : genericPoints X ⊆ p ⁻¹' (U₀ : Set Y₀.left) := by
    intro x hx
    rintro ⟨y, hy, hxy⟩
    obtain ⟨σ, hσ⟩ := exists_galois_map_eq_of_projection_eq D.k₀ D.k Y₀.left x y hxy.symm
    let g := D.galoisMap Y₀.hom σ
    have : IsIso g := ⟨⟨D.galoisMap Y₀.hom σ.symm,
      (D.galoisMap_inverse Y₀.hom σ).1, (D.galoisMap_inverse Y₀.hom σ).2⟩⟩
    have hg : g x = y := hσ
    exact hy (hgen (hg ▸ genericPoint_homeomorph (Scheme.Hom.homeomorph g) hx))
  have hdpre : Dense (p ⁻¹' (U₀ : Set Y₀.left)) := dense_of_genericPoints_subset hpre
  have hU₀ : Dense (U₀ : Set Y₀.left) := by
    intro y
    obtain ⟨x, rfl⟩ := p.surjective y
    exact closure_mono (Set.image_preimage_subset p (U₀ : Set Y₀.left))
      (mem_closure_image p.continuous.continuousAt (hdpre x))
  let q := pullback.snd U₀.ι p
  have hqU : Set.range q ⊆ Set.range U.ι := by
    rintro x ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hz : p (q z) ∈ U₀ := by
      have hh := congrArg (fun f ↦ f z) (pullback.condition (f := U₀.ι) (g := p))
      change U₀.ι (pullback.fst U₀.ι p z) = p (q z) at hh
      rw [← hh]
      exact (pullback.fst U₀.ι p z).property
    by_contra hn
    exact hz ⟨q z, hn, rfl⟩
  exact ⟨U₀, hU₀, hqU⟩

/-- Restrict a lisse module through an open factorization. -/
private theorem lisse_of_range_subset
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}}
    (U : X.Opens) (q : Y ⟶ X) (hqU : Set.range q ⊆ Set.range U.ι)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hU : IsLisseCoefficientModule Λ ((CondensedRing.upperStar Λ U.ι).obj M)) :
    IsLisseCoefficientModule Λ ((CondensedRing.upperStar Λ q).obj M) := by
  let r := IsOpenImmersion.lift U.ι q hqU
  have hr : r ≫ U.ι = q := IsOpenImmersion.lift_fac _ _ _
  have h := CondensedRing.locFree_pullback Λ r _ hU
  exact CondensedRing.locFree_iso
    ((eqToIso (congrArg (fun f ↦ (CondensedRing.upperStar Λ f).obj M) hr)).symm ≪≫
      (CondensedRing.upperStarComp Λ r U.ι).app M) h

/-- Base change an automorphism fixing the model; its inverse gives the inverse map. -/
private theorem pullback_automorphism {U₀ Y X : Scheme.{u}} (j₀ : U₀ ⟶ Y)
    (p : X ⟶ Y) (Φ : X ⟶ X) [IsIso Φ] (hΦ : Φ ≫ p = p) :
    ∃ φ : pullback j₀ p ⟶ pullback j₀ p, IsIso φ ∧
      φ ≫ pullback.snd j₀ p = pullback.snd j₀ p ≫ Φ := by
  let φ : pullback j₀ p ⟶ pullback j₀ p :=
    pullback.map j₀ p j₀ p (𝟙 _) Φ (𝟙 _)
      (by simp) (by simpa using hΦ.symm)
  have hφ : φ ≫ pullback.snd j₀ p = pullback.snd j₀ p ≫ Φ := by simp [φ]
  have hφiso : IsIso φ := by
    let ψ : pullback j₀ p ⟶ pullback j₀ p :=
      pullback.map j₀ p j₀ p (𝟙 _) (inv Φ) (𝟙 _)
        (by simp) (by
          simp only [Category.comp_id]
          rw [← cancel_epi Φ, IsIso.hom_inv_id_assoc]
          exact hΦ)
    exact ⟨⟨ψ, by apply pullback.hom_ext <;> simp [φ, ψ],
      by apply pullback.hom_ext <;> simp [φ, ψ]⟩⟩
  exact ⟨φ, hφiso, hφ⟩

/-- Add an automorphism over the model to an open carrying an arbitrary property. -/
private theorem open_with_automorphism {X Y : Scheme.{u}}
    (p : X ⟶ Y) (Φ : X ⟶ X) [IsIso Φ] (hΦ : Φ ≫ p = p)
    (P : ∀ V : Scheme.{u}, (V ⟶ Y) → Prop)
    (hP : ∃ U₀ : Y.Opens, Dense (U₀ : Set Y) ∧ P U₀.toScheme U₀.ι) :
    ∃ (V : Scheme.{u}) (j : V ⟶ Y),
      IsOpenImmersion j ∧ Dense (Set.range j.base) ∧
      IsOpenImmersion (pullback.snd j p) ∧
      ∃ φ : pullback j p ⟶ pullback j p,
        IsIso φ ∧ ∃ _hφ : φ ≫ pullback.snd j p = pullback.snd j p ≫ Φ, P V j := by
  obtain ⟨U₀, hd, hU₀⟩ := hP
  obtain ⟨φ, hφiso, hφ⟩ := pullback_automorphism U₀.ι p Φ hΦ
  refine ⟨U₀.toScheme, U₀.ι, inferInstance, ?_, inferInstance, φ, hφiso, hφ, hU₀⟩
  simpa only [Scheme.Opens.range_ι] using hd

/-- Combine two choices without expanding the final geometric proposition under recursors. -/
private theorem combine_choices {α β : Type*} {P : α → Prop} {Q : α → β → Prop}
    {R : Prop} (hP : ∃ a, P a) (hQ : ∀ a, P a → ∃ b, Q a b)
    (hR : ∀ a, P a → ∀ b, Q a b → R) : R := by
  obtain ⟨a, ha⟩ := hP
  obtain ⟨b, hb⟩ := hQ a ha
  exact hR a ha b hb

/-- Geometric Frobenius fixes the projection to its finite-field model. -/
private theorem geometricFrobenius_projection
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (Y₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] :
    (D.geometricFrobenius Y₀).hom ≫ pullback.fst Y₀.hom
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) =
      pullback.fst Y₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) :=
  (D.galoisMap_projections Y₀.hom _).1

/-- Descend a generic lisse open with the geometric scheme and projection abstract. -/
private theorem lisse_model_open
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {G Y : Scheme.{u}} (p : G ⟶ Y)
    (hdesc : ∀ U : G.Opens, genericPoints G ⊆ (U : Set G) →
      ∃ U₀ : Y.Opens, Dense (U₀ : Set Y) ∧
        Set.range (pullback.snd U₀.ι p) ⊆ Set.range U.ι)
    (M : Mod (Sheaf (Scheme.ProEt.topology G) Ab.{u + 1}) (condensedRingObj Λ G))
    (hgeneric : ∃ U : G.Opens, genericPoints G ⊆ (U : Set G) ∧
      IsLisseCoefficientModule Λ ((CondensedRing.upperStar Λ U.ι).obj M)) :
    ∃ U₀ : Y.Opens, Dense (U₀ : Set Y) ∧
      IsLisseCoefficientModule Λ ((CondensedRing.upperStar Λ
        (pullback.snd U₀.ι p)).obj M) := by
  refine combine_choices hgeneric (fun U hU ↦ hdesc U hU.1) ?_
  intro U hU U₀ hU₀
  exact ⟨U₀, hU₀.1, lisse_of_range_subset Λ U _ hU₀.2 M hU.2⟩

/-- Add Frobenius with the geometric scheme, projection and automorphism abstract. -/
private theorem dense_lisse_from_generic
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {G Y : Scheme.{u}}
    (p : G ⟶ Y) (Φ : G ⟶ G) [IsIso Φ] (hΦ : Φ ≫ p = p)
    (hdesc : ∀ U : G.Opens, genericPoints G ⊆ (U : Set G) →
      ∃ U₀ : Y.Opens, Dense (U₀ : Set Y) ∧
        Set.range (pullback.snd U₀.ι p) ⊆ Set.range U.ι)
    (M : Mod (Sheaf (Scheme.ProEt.topology G) Ab.{u + 1}) (condensedRingObj Λ G))
    (hgeneric : ∃ U : G.Opens, genericPoints G ⊆ (U : Set G) ∧
      IsLisseCoefficientModule Λ ((CondensedRing.upperStar Λ U.ι).obj M)) :
    ∃ (U₀ : Scheme.{u}) (j₀ : U₀ ⟶ Y),
      IsOpenImmersion j₀ ∧ Dense (Set.range j₀.base) ∧
      IsOpenImmersion (pullback.snd j₀ p) ∧
      ∃ φ : pullback j₀ p ⟶ pullback j₀ p,
        IsIso φ ∧ ∃ _hφ : φ ≫ pullback.snd j₀ p = pullback.snd j₀ p ≫ Φ,
          IsLisseCoefficientModule Λ
            ((CondensedRing.upperStar Λ (pullback.snd j₀ p)).obj M) := by
  exact open_with_automorphism p Φ hΦ
    (fun V j ↦ IsLisseCoefficientModule Λ ((CondensedRing.upperStar Λ
      (pullback.snd j p)).obj M)) (lisse_model_open Λ p hdesc M hgeneric)

/-- The finite-type geometric fibre is Noetherian. -/
private theorem geometricFiber_noetherian
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (Y₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] :
    IsNoetherian (D.geometricFiber Y₀).left :=
  { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian
      (pullback.snd Y₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
    toCompactSpace := QuasiCompact.compactSpace_of_compactSpace
      (pullback.snd Y₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))) }

/-- Package generic lissity so equality transport keeps the module arguments abstract. -/
private def GenericLisseProperty
    (A : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
    (X : Scheme.{u}) : Prop :=
  GenericLisseObjectProperty A.X X

/-- The coefficient-ring model has the generic-lissity property. -/
private theorem generic_lisse_property_model (ℓ : ℕ) [Fact ℓ.Prime]
    (L : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    (hL : L = Profinite.padicAlgClCondensedRing ℓ)
    (X : Scheme.{u}) [IsNoetherian X] :
    GenericLisseProperty (Mon.mk (coefficientHeartRingObj L)) X := by
  exact generic_lisse_open ℓ L hL X

/-- Equality transport with both coefficient monoids abstract. -/
private theorem generic_property_transport
    (A B : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
    (h : A = B) (X : Scheme.{u}) (hB : GenericLisseProperty B X) :
    GenericLisseProperty A X :=
  Eq.mpr (congrArg (fun C ↦ GenericLisseProperty C X) h) hB

/-- Apply generic lissity while keeping the coefficient object unbundled. -/
private theorem generic_property_apply
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    [IsCommMonObj Λ] (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsConstantModelConstructible Λ X M) (hP : GenericLisseObjectProperty Λ X) :
    ∃ U : X.Opens, genericPoints X ⊆ (U : Set X) ∧
      IsLisseCoefficientModule Λ ((CondensedRing.upperStar Λ U.ι).obj M) :=
  hP inferInstance M hM

/-- Unbundle the generic-lissity property before supplying a module argument. -/
private theorem generic_property_unbundle
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    (X : Scheme.{u}) (hP : GenericLisseProperty (Mon.mk Λ) X) :
    GenericLisseObjectProperty Λ X :=
  hP

/-- Keep the unbundled coefficient object and geometric scheme abstract through assembly. -/
private theorem exists_dense_lisse_open_monoid
    (ℓ : ℕ) [Fact ℓ.Prime]
    (L : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    (hL : L = Profinite.padicAlgClCondensedRing ℓ)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (hA : Mon.mk Λ = Mon.mk (coefficientHeartRingObj L))
    {G Y : Scheme.{u}} [IsNoetherian G]
    (p : G ⟶ Y) (Φ : G ⟶ G) [IsIso Φ] (hΦ : Φ ≫ p = p)
    (hdesc : ∀ U : G.Opens, genericPoints G ⊆ (U : Set G) →
      ∃ U₀ : Y.Opens, Dense (U₀ : Set Y) ∧
        Set.range (pullback.snd U₀.ι p) ⊆ Set.range U.ι)
    (M : Mod (Sheaf (Scheme.ProEt.topology G) Ab.{u + 1}) (condensedRingObj Λ G))
    (hM : IsConstantModelConstructible Λ G M) :
    ∃ (U₀ : Scheme.{u}) (j₀ : U₀ ⟶ Y),
      IsOpenImmersion j₀ ∧ Dense (Set.range j₀.base) ∧
      IsOpenImmersion (pullback.snd j₀ p) ∧
      ∃ φ : pullback j₀ p ⟶ pullback j₀ p,
        IsIso φ ∧ ∃ _hφ : φ ≫ pullback.snd j₀ p = pullback.snd j₀ p ≫ Φ,
          IsLisseCoefficientModule Λ
            ((CondensedRing.upperStar Λ (pullback.snd j₀ p)).obj M) := by
  exact dense_lisse_from_generic Λ p Φ hΦ hdesc M
    (generic_property_apply Λ G M hM
      (generic_property_unbundle Λ G
        (generic_property_transport (Mon.mk Λ) (Mon.mk (coefficientHeartRingObj L)) hA G
          (generic_lisse_property_model ℓ L hL G))))

-- Keep the original public binder names, including the existential square witness.

/-- A constructible condensed Weil module is lisse on a dense open descending to the
finite-field model, and its Weil isomorphism restricts to that open.
Source: literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/
`sec-deligne-laumon-general/sec-reduction-to-the-relative-affine-line/`
`sk-prop-wgen-relative-line/thm-zl-relative-line-stratification.proof.md`,
paragraphs 1 and 4 (blueprint: lem-zl-condensed-weil-dense-lisse-open).

The pullback `pullback j₀ p` is the geometric base change of the open immersion
`j₀ : U₀ ⟶ T₀`; its second projection is the open immersion `j : U ⟶ T`.
The morphism `φ` records the induced geometric Frobenius on this pullback by its
commuting square with the geometric Frobenius of `T`. The square `hφ` is exactly
the datum of `restrictedWeilIso`: the restricted Weil isomorphism of the node is
`restrictedWeilIso Λ hφ θ : φ^* j^* M ≅ j^* M`, the restriction of the given `θ`
(not an arbitrary isomorphism).

Proof: (1) The stratified-lissity criterion gives a finite lisse stratification.
Choose an open neighborhood of each component generic point inside its stratum image.
The actual pullback to the stratum is a surjective closed immersion. Descend lissity
through this immersion, then glue over the union U of the neighborhoods.
(2) The geometric base-change projection p is closed because the field extension
is algebraic. Define U₀ as the complement of p(X \ U).
(3) Every point in the fibre of a geometric generic point is another generic point:
Galois transitivity of the fibre identifies them by a scheme automorphism. Therefore
p⁻¹(U₀) contains all geometric generic points and is dense. Surjectivity and continuity
of p imply that U₀ is dense.
(4) The geometric pullback of U₀ factors through U, so the restricted module is lisse.
(5) Geometric Frobenius fixes p. The universal property of the pullback constructs
its restriction and inverse. The resulting square defines `restrictedWeilIso Λ hφ θ`.
All constructions include the empty scheme.
-/
theorem exists_dense_lisse_open_of_constructible_weil
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : ℓ ≠ D.p)
    (Y₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    [IsSeparated Y₀.hom] [IsReduced Y₀.left]
    (M : Mod (Sheaf (Scheme.ProEt.topology (D.geometricFiber Y₀).left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (D.geometricFiber Y₀).left))
    (_hM : IsConstantModelConstructible
      (Profinite.padicAlgClRingObj ℓ)
      (D.geometricFiber Y₀).left M)
    (θ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ)
      (D.geometricFrobenius Y₀).hom).obj M ≅ M) :
    let p : (D.geometricFiber Y₀).left ⟶ Y₀.left :=
      pullback.fst Y₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))
    ∃ (U₀ : Scheme.{u}) (j₀ : U₀ ⟶ Y₀.left),
      IsOpenImmersion j₀ ∧ Dense (Set.range j₀.base) ∧
      IsOpenImmersion (pullback.snd j₀ p) ∧
      ∃ φ : pullback j₀ p ⟶
          pullback j₀ p,
        IsIso φ ∧
        ∃ hφ : φ ≫ pullback.snd j₀ p =
          pullback.snd j₀ p ≫
            (D.geometricFrobenius Y₀).hom,
        IsLisseCoefficientModule (Profinite.padicAlgClRingObj ℓ)
          ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ)
            (pullback.snd j₀ p)).obj M) := by
  clear θ
  let : IsNoetherian (D.geometricFiber Y₀).left := geometricFiber_noetherian D Y₀
  exact exists_dense_lisse_open_monoid ℓ (Profinite.padicAlgClCondensedRing ℓ) rfl
    (Profinite.padicAlgClRingObj ℓ) rfl
    (G := (D.geometricFiber Y₀).left) (Y := Y₀.left)
    (pullback.fst Y₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
    (D.geometricFrobenius Y₀).hom (geometricFrobenius_projection D Y₀)
    (dense_model_open D Y₀) M _hM

set_option linter.unusedVariables false in
end AlgebraicGeometry.ProEtale
