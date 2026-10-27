/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q109
-/
module

public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.Paper.CoefficientHeartStratificationDefs
public import Sheaf.Paper.CoefficientHeartCurveLisseDescent
public import Sheaf.AlgebraicGeometry.CoefficientSectionsLocalization
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Sheaf.Algebra.Category.ModuleCat.Sheaf.HomIsSheaf
import Sheaf.CategoryTheory.SiteCoveringAxioms
import Sheaf.AlgebraicGeometry.WeaklyEtaleStability
import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Lisse Hom descent from coefficient-section restriction

Source: blueprint main-20261015, direct-images proof, paragraph (3), auxiliary
ringed-site argument extracted in the Q12 and Q103 reports; Stacks Tags 01IT,
03EM and 04TQ (blueprint: lem-sfb-sectionwise-open-lisse-hom-descent).

The maps below use the actual coefficient mate, module inverse image, finite-free
comparison and composition comparisons. The theorem concerns given lisse objects.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- A member of a pro-etale covering as an object of the small pro-etale site.
The weak-etaleness witness is taken from the defining covering condition.
Source: direct-images paragraph (3), affine covering refinement, step 2
(blueprint: lem-sfb-sectionwise-open-lisse-hom-descent). -/
def sfbOpenHomCoverObject {X : Scheme.{u}}
    (C : Scheme.Cover.{v} Scheme.proetalePrecoverage X) (i : C.I₀) : X.ProEt :=
  MorphismProperty.Over.mk _ (C.f i)
    (Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ C.mem₀ (.mk i))

/-- Actual restriction of coefficient sections from an affine test object to its open
fibre, with the canonical localization identification at the source.
Source: the auxiliary ringed-site argument in direct-images paragraph (3), step 1
(blueprint: lem-sfb-sectionwise-open-lisse-hom-descent). -/
def sfbOpenHomCoefficientRestriction
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    {X V : Scheme.{u}} (j : V ⟶ X) (W : X.ProEt) :
    (condensedRingObj Λ X).obj.obj (op W) ⟶
      (condensedRingObj Λ (pullback W.hom j)).obj.obj
        (op (Scheme.ProEt.mk (𝟙 (pullback W.hom j)))) :=
  sfbCoefficientSectionMap Λ W ≫ sfbCoefficientGlobalMap Λ (pullback.fst W.hom j)

/-- A matrix entry of a map between finite free coefficient modules: project the
image of the indicated standard generator and evaluate at the global unit section.
Source: the auxiliary ringed-site argument in direct-images paragraph (3), step 3
(blueprint: lem-sfb-sectionwise-open-lisse-hom-descent). -/
def sfbOpenHomMatrixEntry
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) {a b : ℕ}
    (h : Mod.finiteFree (condensedRingObj Λ X) a ⟶
      Mod.finiteFree (condensedRingObj Λ X) b) (row : Fin b) (col : Fin a) :
    (condensedRingObj Λ X).obj.obj (op (Scheme.ProEt.mk (𝟙 X))) :=
  ((biproduct.ι (fun _ : Fin a ↦ Mod.regular (condensedRingObj Λ X)) col ≫ h ≫
    biproduct.π (fun _ : Fin b ↦ Mod.regular (condensedRingObj Λ X)) row).hom.hom.app
      (op (Scheme.ProEt.mk (𝟙 X)))).hom
    (sfbSectionOne Λ X (Scheme.ProEt.mk (𝟙 X)))

/-- The canonical comparison for the Cartesian square with sides `f` and `j`.
It is formed from the recorded composition isomorphisms and the pullback equation.
Source: the auxiliary ringed-site argument in direct-images paragraph (3), step 6
(blueprint: lem-sfb-sectionwise-open-lisse-hom-descent). -/
def sfbOpenHomPullbackComparison
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X V Y : Scheme.{u}} (f : Y ⟶ X) (j : V ⟶ X)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (CondensedRing.upperStar Λ (pullback.fst f j)).obj
        ((CondensedRing.upperStar Λ f).obj M) ≅
      (CondensedRing.upperStar Λ (pullback.snd f j)).obj
        ((CondensedRing.upperStar Λ j).obj M) :=
  ((CondensedRing.upperStarComp Λ (pullback.fst f j) f).app M).symm ≪≫
    eqToIso (congrArg (fun k : pullback f j ⟶ X ↦ (CondensedRing.upperStar Λ k).obj M)
      (pullback.condition (f := f) (g := j))) ≪≫
    (CondensedRing.upperStarComp Λ (pullback.snd f j) j).app M

/-- Pull back a morphism on the open part and conjugate by the canonical Cartesian
composition comparisons. Source: the auxiliary ringed-site argument in direct-images
paragraph (3), steps 3 and 6 (blueprint: lem-sfb-sectionwise-open-lisse-hom-descent). -/
def sfbOpenHomPullback
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X V Y : Scheme.{u}} (f : Y ⟶ X) (j : V ⟶ X)
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (h : (CondensedRing.upperStar Λ j).obj M ⟶ (CondensedRing.upperStar Λ j).obj N) :
    (CondensedRing.upperStar Λ (pullback.fst f j)).obj
        ((CondensedRing.upperStar Λ f).obj M) ⟶
      (CondensedRing.upperStar Λ (pullback.fst f j)).obj
        ((CondensedRing.upperStar Λ f).obj N) :=
  (sfbOpenHomPullbackComparison Λ f j M).hom ≫
    (CondensedRing.upperStar Λ (pullback.snd f j)).map h ≫
      (sfbOpenHomPullbackComparison Λ f j N).inv

/-- Pull back a local map and use the composition comparison to regard its source
and target as single pullbacks from the base. This makes overlap agreement literal,
up to transport along the equality of the two structure morphisms.
Source: the auxiliary ringed-site argument in direct-images paragraph (3), steps 4--5
(blueprint: lem-sfb-sectionwise-open-lisse-hom-descent). -/
def sfbOpenHomCompositePullback
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X W T : Scheme.{u}} (w : W ⟶ X) (q : T ⟶ W)
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (h : (CondensedRing.upperStar Λ w).obj M ⟶ (CondensedRing.upperStar Λ w).obj N) :
    (CondensedRing.upperStar Λ (q ≫ w)).obj M ⟶
      (CondensedRing.upperStar Λ (q ≫ w)).obj N :=
  (CondensedRing.upperStarComp Λ q w).hom.app M ≫
    (CondensedRing.upperStar Λ q).map h ≫
      (CondensedRing.upperStarComp Λ q w).inv.app N

/-- Coefficient-section bijections imply actual Hom descent for given lisse modules,
including the entrywise inverse in every affine trivialization, agreement on arbitrary
overlap refinements, unique gluing, independence of cover and bases, and base change.

Source: blueprint main-20261015, direct-images proof, paragraph (3), auxiliary
ringed-site lemma extracted in the Q12 report and split in the Q103 report;
Stacks Tags 01IT, 03EM and 04TQ
(blueprint: lem-sfb-sectionwise-open-lisse-hom-descent).

Proof:
1. Use def-weil-pbc-internal-abelian-sheaf-module-equivalence to pass to sectionwise
   module sheaves. By lem-sfb-coefficient-sections-localization, inverse image along
   a site object is slice restriction with the specified coefficient identification.
2. Compose the two lisse covers (def-sfb-lisse-coefficient-module), then refine by all
   affine opens (lem-weil-pbc-affine-opens-basis). Weak etaleness remains valid by
   sk-lem-pe-weakly-etale-stability. The finite-affine covering witnesses in
   def-weil-pbc-proetale-site still witness the covering after refinement. The same
   argument gives affine covers of overlaps, without assuming overlaps are affine.
3. By lem-sfb-ringed-site-free-matrix-scalar-extension, morphisms in fixed finite
   free bases are matrices of coefficient sections. Actual restriction acts entrywise
   by the displayed coefficient map. Its assumed bijectivity gives a unique inverse
   matrix, even when the open fibre of the affine chart is not affine.
4. Extend the matrix on each chart. On every affine refinement of an overlap, express
   both candidate maps in the first chart's bases. Their open restrictions coincide,
   so entrywise injectivity gives equality. Apply lem-pur-sheaf-hom-is-sheaf first
   for separatedness on overlaps and then for unique gluing on the original cover.
5. The glued map restricts to the original map, as can be checked on the open cover.
   Chartwise injectivity and Hom-sheaf separatedness prove global injectivity.
   Hence every choice of cover and bases gives this same inverse. All restrictions
   to overlap refinements agree, and the inverse matrices glue uniquely.
6. Apply the same argument on Y. Naturality of the composition comparisons in
   sk-def-sfb-module-pushforward-pullback identifies the restriction of f^*e(u) with
   g^*u under sfbOpenHomPullbackComparison. Injectivity on Y proves the equality.
7. Zero ranks give empty matrices. The empty cover of the empty scheme gives a
   singleton Hom set by the Hom sheaf axiom. For the identity open the inverse
   is the identity. No connectedness, separation or Noetherianity is used.
-/
theorem sfbSectionwiseOpenLisseHomDescent
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X V : Scheme.{u}} (j : V ⟶ X) [IsOpenImmersion j]
    (hsec : ∀ W : X.ProEt, IsAffine W.left →
      Function.Bijective (sfbOpenHomCoefficientRestriction Λ j W).hom)
    (M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsLisseCoefficientModule Λ M) (hN : IsLisseCoefficientModule Λ N) :
    ∃ e : (M ⟶ N) ≃
        ((CondensedRing.upperStar Λ j).obj M ⟶ (CondensedRing.upperStar Λ j).obj N),
      (∀ h : M ⟶ N, e h = (CondensedRing.upperStar Λ j).map h) ∧
      (∀ (C : Scheme.Cover.{v} Scheme.proetalePrecoverage X)
        (hC : ∀ i : C.I₀, IsAffine (C.X i)) (a b : C.I₀ → ℕ)
        (α : ∀ i : C.I₀, (CondensedRing.upperStar Λ (C.f i)).obj M ≅
          Mod.finiteFree (condensedRingObj Λ (C.X i)) (a i))
        (β : ∀ i : C.I₀, (CondensedRing.upperStar Λ (C.f i)).obj N ≅
          Mod.finiteFree (condensedRingObj Λ (C.X i)) (b i))
        (u : (CondensedRing.upperStar Λ j).obj M ⟶ (CondensedRing.upperStar Λ j).obj N),
        (∀ (i : C.I₀) (row : Fin (b i)) (col : Fin (a i)),
          sfbOpenHomMatrixEntry Λ (C.X i)
              ((α i).inv ≫ (CondensedRing.upperStar Λ (C.f i)).map (e.symm u) ≫
                (β i).hom) row col =
            (sfbCoefficientSectionMap Λ (sfbOpenHomCoverObject C i)).hom
            ((Equiv.ofBijective
              (sfbCoefficientSectionMap Λ (sfbOpenHomCoverObject C i) ≫
                sfbCoefficientGlobalMap Λ (pullback.fst (C.f i) j)).hom
              (hsec (sfbOpenHomCoverObject C i) (hC i))).symm
              (sfbOpenHomMatrixEntry Λ (pullback (C.f i) j)
                (((CondensedRing.upperStar Λ (pullback.fst (C.f i) j)).mapIso (α i) ≪≫
                    coefficientHeartFiniteFreePullbackIso Λ
                      (pullback.fst (C.f i) j) (a i)).inv ≫
                  sfbOpenHomPullback Λ (C.f i) j u ≫
                  ((CondensedRing.upperStar Λ (pullback.fst (C.f i) j)).mapIso (β i) ≪≫
                    coefficientHeartFiniteFreePullbackIso Λ
                      (pullback.fst (C.f i) j) (b i)).hom) row col))) ∧
        (∀ (i k : C.I₀) (T : X.ProEt)
          (q : T ⟶ sfbOpenHomCoverObject C i) (r : T ⟶ sfbOpenHomCoverObject C k),
          HEq (sfbOpenHomCompositePullback Λ (C.f i) q.left
              ((CondensedRing.upperStar Λ (C.f i)).map (e.symm u)))
            (sfbOpenHomCompositePullback Λ (C.f k) r.left
              ((CondensedRing.upperStar Λ (C.f k)).map (e.symm u)))) ∧
        (∀ k : ∀ i : C.I₀, (CondensedRing.upperStar Λ (C.f i)).obj M ⟶
              (CondensedRing.upperStar Λ (C.f i)).obj N,
          (∀ i : C.I₀, (CondensedRing.upperStar Λ (pullback.fst (C.f i) j)).map (k i) =
            sfbOpenHomPullback Λ (C.f i) j u) →
          ∃! h : M ⟶ N, ∀ i : C.I₀, (CondensedRing.upperStar Λ (C.f i)).map h = k i)) ∧
      ∀ (Y : Scheme.{u}) (f : Y ⟶ X),
        (∀ W : Y.ProEt, IsAffine W.left →
          Function.Bijective
            (sfbOpenHomCoefficientRestriction Λ (pullback.fst f j) W).hom) →
        IsLisseCoefficientModule Λ ((CondensedRing.upperStar Λ f).obj M) →
        IsLisseCoefficientModule Λ ((CondensedRing.upperStar Λ f).obj N) →
        ∃ e' : ((CondensedRing.upperStar Λ f).obj M ⟶
              (CondensedRing.upperStar Λ f).obj N) ≃
            ((CondensedRing.upperStar Λ (pullback.fst f j)).obj
                ((CondensedRing.upperStar Λ f).obj M) ⟶
              (CondensedRing.upperStar Λ (pullback.fst f j)).obj
                ((CondensedRing.upperStar Λ f).obj N)),
          (∀ h : (CondensedRing.upperStar Λ f).obj M ⟶ (CondensedRing.upperStar Λ f).obj N,
            e' h = (CondensedRing.upperStar Λ (pullback.fst f j)).map h) ∧
          ∀ u : (CondensedRing.upperStar Λ j).obj M ⟶ (CondensedRing.upperStar Λ j).obj N,
            (CondensedRing.upperStar Λ f).map (e.symm u) =
              e'.symm (sfbOpenHomPullback Λ f j u) := by
  sorry

end AlgebraicGeometry.ProEtale
