/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q140
-/
module

public import Sheaf.AlgebraicGeometry.AffineEtaleDerivedModuleRealization
public import Sheaf.Algebra.Homology.DerivedInternalHomMixedUniverses
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Category.Grp.Ulift
public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs

import Sheaf.RingTheory.NoetherianPseudoCoherentCohomologyCriterion
import WeilConjectures.RingTheory.RingPseudoCoherent
import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence
import WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex
import WeilConjectures.AlgebraicGeometry.AffineDerivedTildeHomologyComparison
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Sheaf.Paper.AffineProjectiveComplexDerivedHom
import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.Algebra.Homology.DerivedHomFiniteFreeModel
import Sheaf.AlgebraicGeometry.DerivedEtaleZariskiEquivalence
import Mathlib.Algebra.Homology.HomotopyCategory.KProjective
import WeilConjectures.Algebra.Homology.BoundedBelowInjectiveResolution

/-! # Affine étale realization and derived internal Hom

Source: Stacks Project, spaces-perfect.tex, Tag 08JP(1), and perfect.tex,
Tag 0A6H(3)(a); more-algebra.tex, Tag 066E(2)
(blueprint: lem-sfb-affine-etale-derived-hom-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u wE
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules

/-- Lift the sections of an étale module sheaf, retaining the actual structure sheaf
and scalar action. Restrictions are the same maps conjugated by ULift.up/down.
This is the canonical size transport needed for Hom on the full small étale site,
whose object universe is u+1 although its structure rings lie in u.
Source: Stacks 08JP, interpreted with the size convention of 000H
(blueprint: lem-sfb-affine-etale-derived-hom-realization). -/
def smallEtaleModuleSectionLift (X : Scheme.{u}) :
    SmallEtaleModules X ⥤ SheafOfModules.{u + 1} (smallEtaleModuleRing X) where
  obj M :=
    { val :=
        { obj V := (ModuleCat.uliftFunctor.{u + 1} _).obj (M.val.obj V)
          map {V W} f := ModuleCat.ofHom
            (Y := (ModuleCat.restrictScalars ((smallEtaleModuleRing X).obj.map f).hom).obj
              ((ModuleCat.uliftFunctor.{u + 1} _).obj (M.val.obj W)))
            { toFun := fun m ↦ ULift.up (M.val.map f m.down)
              map_add' := fun m n ↦ congrArg ULift.up (map_add (M.val.map f).hom m.down n.down)
              map_smul' := fun r m ↦ congrArg ULift.up (M.val.map_smul f r m.down) }
          map_id V := by ext m; exact congrArg ULift.up (by simp)
          map_comp f g := by
            ext m
            exact congrArg ULift.up (M.val.map_comp_apply f g m.down) }
      isSheaf := Presheaf.isSheaf_comp_of_isSheaf X.smallEtaleTopology M.val.presheaf
        AddCommGrpCat.uliftFunctor M.isSheaf }
  map f :=
    { val :=
        { app V := (ModuleCat.uliftFunctor.{u + 1} _).map (f.val.app V)
          naturality {V W} g := by
            ext m
            exact congrArg ULift.up (CategoryTheory.congr_fun (f.val.naturality g) m.down) } }
  map_id M := by ext V m; rfl
  map_comp f g := by ext V m; rfl

/-- The explicit section identification for the canonical size lift, with inverse
ULift.up and forward map ULift.down. In particular this also identifies degree-zero
sections without any choice of an unrelated map.
Source: Stacks 000H, used in 08JP
(blueprint: lem-sfb-affine-etale-derived-hom-realization). -/
def smallEtaleModuleSectionLiftEquiv (X : Scheme.{u}) (M : SmallEtaleModules X)
    (V : X.Etaleᵒᵖ) :
    ((smallEtaleModuleSectionLift X).obj M).val.obj V ≃ₗ[(smallEtaleModuleRing X).obj.obj V]
      M.val.obj V := ULift.moduleEquiv

/-- Section lifting preserves addition of module maps, componentwise.
Source: Stacks 000H, size convention for the comparison of 08JP
(blueprint: lem-sfb-affine-etale-derived-hom-realization). -/
instance smallEtaleModuleSectionLift_additive (X : Scheme.{u}) :
    (smallEtaleModuleSectionLift X).Additive where
  map_add := by intros M N f g; ext V m; rfl

/-- The full category of pairs (E,F) with finite cohomology and an upper bound for E,
and only a lower bound for F. Its inherited arrows express the required variance.
Source: Stacks 08JP(1), 0A6H(3)(a), and the Noetherian criterion 066E(2)
(blueprint: lem-sfb-affine-etale-derived-hom-realization). -/
def affineEtaleDerivedHomPairProperty (A : Type u) [CommRing A] :
    ObjectProperty ((DerivedCategory (ModuleCat.{u} A))ᵒᵖ ×
      DerivedCategory (ModuleCat.{u} A)) :=
  fun T ↦
    (∀ i : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj T.1.unop)) ∧
    (∃ b : ℤ, ∀ i : ℤ, b < i → IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj T.1.unop)) ∧
    (∃ a : ℤ, ∀ i : ℤ, i < a → IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj T.2))

/-- Re-express the chosen derived localization using the definitionally identical
commutative presentation of the étale structure sheaf. This retains the instance h.
Source: Stacks 08JP, ordinary unbounded derived category
(blueprint: lem-sfb-affine-etale-derived-hom-realization). -/
@[instance_reducible, instance]
def smallEtaleCommRingHasDerivedCategory (X : Scheme.{u})
    [h : HasDerivedCategory.{wE} (SheafOfModules.{u + 1} (smallEtaleModuleRing X))] :
    HasDerivedCategory.{wE} (SheafOfModules.{u + 1}
      ((sheafCompose X.smallEtaleTopology (forget₂ CommRingCat.{u} RingCat.{u})).obj
        ⟨X.etaleStructurePresheaf, X.isSheaf_etaleStructurePresheaf⟩)) := h

/-- The affine associated étale functor, with its canonical section-universe transport,
commutes naturally with derived Hom on exactly the admissible pairs. The factorization
through Q fixes the realization on all complexes and their maps. The natural isomorphism
is in the derived category itself, contravariantly in E and covariantly in F.

Source: Stacks spaces-perfect.tex 08JP(1), perfect.tex 0A6H(3)(a), more-algebra.tex 066E(2)
(blueprint: lem-sfb-affine-etale-derived-hom-realization).

Proof:
1. The Noetherian cohomology criterion (lem-weil-pbc-noetherian-pseudocoherent-cohomology-
   criterion) makes E pseudo-coherent. Choose a bounded-above finite free model P via
   def-pc-ring-pseudo-coherent-complex.
2. The affine equivalence lem-pc-affine-qcoh-derived-equivalence realizes P by termwise
   tilde, hence by a pseudo-coherent complex (def-pur-pseudo-coherent-complex).
   new-affine-derived-tilde-homology-comparison transfers the lower bound of F.
3. Choose a lower truncated representative of F using def-sbc-standard-tstructure-derived-
   category. The lem-sc-affine-projective-complex-derived-hom and
   lem-sc-derived-hom-finite-free-model computations identify both Hom complexes.
   Only a-n <= p <= b contributes in degree n. The tilde sections and finite-free
   comparisons (lem-weil-pbc-spec-module-tilde-sections and lem-weil-pbc-spec-tilde-free-
   module) identify each finite product and commute with d_F h - (-1)^n h d_P.
4. The exact affine realization lem-sfb-affine-etale-derived-module-realization and
   lem-trf-scheme-zariski-etale-quasi-coherent-equivalence identify epsilon* tilde M
   with a_A(M). Apply this termwise and use lem-sfb-derived-etale-zariski-equivalence.
   Sectionwise ULift is exact and changes neither scalar actions nor sections, up to
   its specified up/down equivalence; hence the same identifications hold after lift.
5. Compose Step 3 after epsilon* with lem-sfb-zariski-etale-pseudocoherent-rhom.
   This gives the displayed comparison. Bounded-above projective models are K-projective
   (lem-sc-bounded-above-projective-kprojective); bounded-below targets have injective
   resolutions (lem-sc-bounded-below-injective-resolution). Pre- and postcomposition
   commute with h mapped to tilde h and epsilon* h, so these isomorphisms are natural
   on the full pair category. No finite generation of F is used. -/
theorem affineEtaleDerivedHomRealization (A : Type u) [CommRing A] [IsNoetherianRing A]
    [HasDerivedCategory.{wE}
      (SheafOfModules.{u + 1} (smallEtaleModuleRing (Spec (.of A))))]
    (c : ZariskiEtaleModuleContext (Spec (.of A))) :
    ∃ _ha : (affineEtaleAssociatedFunctor A c ⋙
      smallEtaleModuleSectionLift (Spec (.of A))).Additive,
    ∃ a : DerivedCategory (ModuleCat.{u} A) ⥤
      DerivedCategory (SheafOfModules.{u + 1} (smallEtaleModuleRing (Spec (.of A)))),
      Nonempty (DerivedCategory.Q ⋙ a ≅
        (affineEtaleAssociatedFunctor A c ⋙
          smallEtaleModuleSectionLift (Spec (.of A))).mapHomologicalComplex
            (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) ∧
      Nonempty ((affineEtaleDerivedHomPairProperty A).ι ⋙
        ordinaryModuleDerivedInternalHom A ⋙ a ≅
        (affineEtaleDerivedHomPairProperty A).ι ⋙ a.op.prod a ⋙
          derivedInternalHomMixedUniverses.{u + 1, u, u, wE}
            (Spec (.of A)).smallEtaleTopology
            ⟨(Spec (.of A)).etaleStructurePresheaf,
              (Spec (.of A)).isSheaf_etaleStructurePresheaf⟩) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
