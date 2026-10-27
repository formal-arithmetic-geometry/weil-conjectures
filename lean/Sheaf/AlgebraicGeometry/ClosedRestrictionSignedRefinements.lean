/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Sheaf.AlgebraicGeometry.FiniteClosedCoverResolution
public import Sheaf.AlgebraicGeometry.ClosedRestrictionSignedData
import Sheaf.AlgebraicGeometry.ClosedRestrictionSignedRows
import Sheaf.AlgebraicGeometry.ClosedRestrictionSignedRowMaps

/-!
# Signed closed-restriction complexes and ordered refinements

Source: Stacks Project, proetale.tex, Tag 09AH (lemma-ses-associated-to-open), for
closed units; the signed construction and refinement identities are agent deductions
in the DAG proof, using the deleted-position calculation of Tag 01FG.
(blueprint: lem-sfb-closed-restriction-signed-refinements).

The existing finite-intersection, graded-term, differential, sorting-sign and total
constructions are reused. There is no covering or exactness condition in this module.
All maps below are natural transformations of the actual module-sheaf functors.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry

/-- A simultaneous choice of signed rows and all ordered refinement chain maps.
The mixed unit equation specifies the actual restriction along the induced map of
intersections. `finiteClosedRefinementSign` is zero for repetitions and is the unique
sorting-permutation sign otherwise. Functor and natural-transformation types express
naturality for every module map and, by whiskering, every small parameter diagram.
Identity and composition give the same statement for parameter diagrams of refinements.
Total maps are pinned on every summand and use horizontal degree first, hence the
existing total convention is d_D + (-1)^p d_K, also for unbounded K.
Source: the signed-refinement deduction from Stacks Tags 09AH and 01FG
(blueprint: lem-sfb-closed-restriction-signed-refinements). -/
structure SignedClosedRefinementSystem {X Z : Scheme.{u}} (i : Z ⟶ X)
    (A : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) where
  row : ∀ F : SignedClosedFamily i, SignedClosedRow i F A
  mixed : ∀ (F G : SignedClosedFamily i) (f : Fin G.length → Fin F.length)
    (_hf : ∀ b, Nonempty (G.members b ⟶ F.members (f b)))
    (s : Finset (Fin F.length)) (t : Finset (Fin G.length)),
    finiteClosedRestriction (finiteClosedIntersection F.members s).hom A ⟶
      finiteClosedRestriction (finiteClosedIntersection G.members t).hom A
  mixed_unit : ∀ (F G : SignedClosedFamily i) (f : Fin G.length → Fin F.length)
    (hf : ∀ b, Nonempty (G.members b ⟶ F.members (f b)))
    (s : Finset (Fin F.length)) (t : Finset (Fin G.length)), s ⊆ t.image f →
    finiteClosedUnit (finiteClosedIntersection F.members s).hom A ≫ mixed F G f hf s t =
      finiteClosedUnit (finiteClosedIntersection G.members t).hom A
  refine : ∀ (F G : SignedClosedFamily i) (f : Fin G.length → Fin F.length)
    (_hf : ∀ b, Nonempty (G.members b ⟶ F.members (f b))), (row F).rows ⟶ (row G).rows
  refine_components : ∀ (F G : SignedClosedFamily i) (f : Fin G.length → Fin F.length)
    (hf : ∀ b, Nonempty (G.members b ⟶ F.members (f b)))
    (M : ringedSiteModules.{u + 1} (proEtaleModuleCoefficients A)) (p : ℕ),
    ((row F).terms p).inv.app M ≫ ((refine F G f hf).app M).f (p : ℤ) ≫
      ((row G).terms p).hom.app M =
        (finiteClosedRefinementMap F.members G.members A f (mixed F G f hf) p).app M
  refine_augment : ∀ (F G : SignedClosedFamily i) (f : Fin G.length → Fin F.length)
    (hf : ∀ b, Nonempty (G.members b ⟶ F.members (f b))),
    (row F).alpha ≫ refine F G f hf = (row G).alpha
  refine_id : ∀ (F : SignedClosedFamily i)
    (hf : ∀ b, Nonempty (F.members b ⟶ F.members (id b))),
    refine F F id hf = 𝟙 (row F).rows
  refine_comp : ∀ (F G H : SignedClosedFamily i)
    (f : Fin G.length → Fin F.length) (g : Fin H.length → Fin G.length)
    (hf : ∀ b, Nonempty (G.members b ⟶ F.members (f b)))
    (hg : ∀ c, Nonempty (H.members c ⟶ G.members (g c)))
    (hfg : ∀ c, Nonempty (H.members c ⟶ F.members ((f ∘ g) c))),
    refine F G f hf ≫ refine G H g hg = refine F H (f ∘ g) hfg
  totalMap : ∀ (F G : SignedClosedFamily i) (f : Fin G.length → Fin F.length)
    (_hf : ∀ b, Nonempty (G.members b ⟶ F.members (f b))),
    @finiteClosedTotal X A (row F).rows (row F).additive ⟶
      @finiteClosedTotal X A (row G).rows (row G).additive
  totalMap_components : ∀ (F G : SignedClosedFamily i)
    (f : Fin G.length → Fin F.length)
    (hf : ∀ b, Nonempty (G.members b ⟶ F.members (f b)))
    (K : CochainComplex (ringedSiteModules.{u + 1} (proEtaleModuleCoefficients A)) ℤ)
    (p q n : ℤ) (hpq : p + q = n),
    ((@finiteClosedDouble X A (row F).rows (row F).additive).obj K).ιTotal
        (ComplexShape.up ℤ) p q n hpq ≫ ((totalMap F G f hf).app K).f n =
      ((refine F G f hf).app (K.X q)).f p ≫
        ((@finiteClosedDouble X A (row G).rows (row G).additive).obj K).ιTotal
          (ComplexShape.up ℤ) p q n hpq
  totalMap_augment : ∀ (F G : SignedClosedFamily i) (f : Fin G.length → Fin F.length)
    (hf : ∀ b, Nonempty (G.members b ⟶ F.members (f b))),
    (row F).totalAugment ≫ totalMap F G f hf = (row G).totalAugment

private def signedClosedTotalMap {X Z : Scheme.{u}} {i : Z ⟶ X}
    {A : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    {F G : SignedClosedFamily i} (D : SignedClosedRow i F A) (D' : SignedClosedRow i G A)
    (ρ : D.rows ⟶ D'.rows) :
    @finiteClosedTotal X A D.rows D.additive ⟶
      @finiteClosedTotal X A D'.rows D'.additive :=
  letI := D.additive
  letI := D'.additive
  Functor.whiskerRight
    (Functor.whiskerRight (NatTrans.mapHomologicalComplex ρ (ComplexShape.up ℤ))
      (HomologicalComplex₂.flipFunctor (ringedSiteModules.{u + 1} (proEtaleModuleCoefficients A))
        (ComplexShape.up ℤ) (ComplexShape.up ℤ)))
    (HomologicalComplex₂.totalFunctor (ringedSiteModules.{u + 1} (proEtaleModuleCoefficients A))
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ))

private theorem signedClosedTotalMap_components {X Z : Scheme.{u}} {i : Z ⟶ X}
    {A : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    {F G : SignedClosedFamily i} (D : SignedClosedRow i F A) (D' : SignedClosedRow i G A)
    (ρ : D.rows ⟶ D'.rows)
    (K : CochainComplex (ringedSiteModules.{u + 1} (proEtaleModuleCoefficients A)) ℤ)
    (p q n : ℤ) (hpq : p + q = n) :
    ((@finiteClosedDouble X A D.rows D.additive).obj K).ιTotal
        (ComplexShape.up ℤ) p q n hpq ≫ ((signedClosedTotalMap D D' ρ).app K).f n =
      (ρ.app (K.X q)).f p ≫
        ((@finiteClosedDouble X A D'.rows D'.additive).obj K).ιTotal
          (ComplexShape.up ℤ) p q n hpq := by
  let : D.rows.Additive := D.additive
  let : D'.rows.Additive := D'.additive
  exact HomologicalComplex₂.ιTotal_map
    ((@finiteClosedDouble X A D.rows D.additive).obj K)
    ((@finiteClosedDouble X A D'.rows D'.additive).obj K)
    ((HomologicalComplex₂.flipFunctor (ringedSiteModules.{u + 1} (proEtaleModuleCoefficients A))
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex ρ (ComplexShape.up ℤ)).app K))
    (ComplexShape.up ℤ) p q n hpq

private theorem signedClosedRow_augment_naturality {X Z : Scheme.{u}} {i : Z ⟶ X}
    {A : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    {F G : SignedClosedFamily i} (D : SignedClosedRow i F A) (D' : SignedClosedRow i G A)
    (ρ : D.rows ⟶ D'.rows) (hρ : D.alpha ≫ ρ = D'.alpha)
    (M : ringedSiteModules.{u + 1} (proEtaleModuleCoefficients A)) :
    D.augment.app M ≫ (ρ.app M).f 0 = D'.augment.app M := by
  have h := congrArg (fun t ↦ (t.app M).f 0) hρ
  simp only [NatTrans.comp_app, HomologicalComplex.comp_f, D.alpha_f, D'.alpha_f,
    Category.assoc] at h
  exact (cancel_epi
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      ((finiteClosedRestriction i A).obj M)).hom).mp h

private theorem signedClosedTotalMap_augment {X Z : Scheme.{u}} {i : Z ⟶ X}
    {A : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    {F G : SignedClosedFamily i} (D : SignedClosedRow i F A) (D' : SignedClosedRow i G A)
    (ρ : D.rows ⟶ D'.rows) (hρ : D.alpha ≫ ρ = D'.alpha) :
    D.totalAugment ≫ signedClosedTotalMap D D' ρ = D'.totalAugment := by
  apply NatTrans.ext
  funext K
  apply HomologicalComplex.Hom.ext
  funext n
  change (D.totalAugment.app K).f n ≫ ((signedClosedTotalMap D D' ρ).app K).f n =
    (D'.totalAugment.app K).f n
  rw [D.totalAugment_f, D'.totalAugment_f, Category.assoc,
    signedClosedTotalMap_components, ← Category.assoc,
    signedClosedRow_augment_naturality D D' ρ hρ]

/-- The signed closed-restriction construction, without a covering hypothesis.
Source: Stacks Project, Tag 09AH supplies the units only; the signed and ordered
refinement identities are the agent deduction recorded in the DAG.
(blueprint: lem-sfb-closed-restriction-signed-refinements).

Proof:
1. Form scheme-theoretic intersections as finite products over X. Apply the actual
inverse and direct images with inverse-image coefficient rings. Their additivity
and the finite biproducts define the existing terms and matrices. Fix the normalized
adjunction of def-sfb-proetale-unit-normalized-adjunction.
2. Apply lem-sf-proetale-tensor-composition-unit to successive intersections and to
Z_J -> Z -> X. Its unit equation gives restriction composition and the augmentation
unit equation. Coherence follows from uniqueness of the conjugate unit comparison
(lem-weil-pbc-conjugate-iso-unit-equation), and uniqueness of fibre-product arrows.
3. Pair the two orders of deleting any two positions. Their restrictions agree and
their signs are opposite, so d squared is zero, including the augmentation column.
4. For an injective image tuple, lem-pc-signed-face-permutation identifies the sign
of each deleted position before and after sorting. The restriction composites agree,
so the signed refinement commutes with the differential on these components.
5. A noninjective tuple has no injective faces unless there is exactly one repeated
pair. In that case only its two deletions survive; their maps agree and their signs
are opposite by the same signed-face lemma. They cancel in every characteristic.
6. In degree zero the sign is one, proving augmentation compatibility. Identity
refinements have identity entries. For composition, repetitions give zero on both
sides; otherwise sorting signs multiply and the restriction maps compose.
7. Naturality of units makes all matrices commute with every module morphism.
This is precisely the arrow condition for application to every small diagram;
composition in step 6 supplies diagrams of refinements as well.
8. Apply step 7 to the differential of K. The horizontal and vertical differentials
commute. In the total their mixed terms have opposite signs, while both pure squares
vanish. The finite horizontal support allows every unbounded K. Refinements commute
with both differentials and preserve horizontal degree, giving the stated total maps.
No exactness is asserted and no cover was used. -/
theorem closedRestriction_signed_refinements {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i]
    (_hqc : ∃ U : X.Opens, Set.range U.ι = (Set.range i)ᶜ ∧ QuasiCompact U.ι)
    (A : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    Nonempty (SignedClosedRefinementSystem i A) := by
  classical
  let row : ∀ F : SignedClosedFamily i, SignedClosedRow i F A :=
    fun F ↦ Classical.choice (signedClosedRow_exists i _hqc A F)
  obtain ⟨maps⟩ := signedClosedRow_maps i _hqc A row
  exact ⟨{
    row := row
    mixed := maps.mixed
    mixed_unit := maps.mixed_unit
    refine := maps.refine
    refine_components := maps.refine_components
    refine_augment := maps.refine_augment
    refine_id := maps.refine_id
    refine_comp := maps.refine_comp
    totalMap := fun F G f hf ↦ signedClosedTotalMap (row F) (row G) (maps.refine F G f hf)
    totalMap_components := fun F G f hf K p q n hpq ↦
      signedClosedTotalMap_components (row F) (row G) (maps.refine F G f hf) K p q n hpq
    totalMap_augment := fun F G f hf ↦
      signedClosedTotalMap_augment (row F) (row G) (maps.refine F G f hf)
        (maps.refine_augment F G f hf)
  }⟩

end AlgebraicGeometry
