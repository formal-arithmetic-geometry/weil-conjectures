/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q154
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.ConstructibleSheaf.Defs
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.Paper.ProEtaleFixedModuleLocalConstancy
import Sheaf.AlgebraicGeometry.ProEtaleSheafTopologicalInvariance
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Sheaf.CategoryTheory.Adjunction.LiftsGroupRingObjects
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
import Sheaf.Paper.PbcCompletedPullbackActual
import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance
import Sheaf.Paper.ProEtaleSurjectiveClosedCoverRefinement
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap
import Sheaf.AlgebraicGeometry.UniversalHomeomorphismInvariance

/-!
# Surjective closed immersions and ordinary module sheaves

Source: Stacks Project, Tag 09AB (lemma-thickening), Tag 04DZ
(theorem-topological-invariance), and Modules on Sites, lemma-pullback-locally-constant
(blueprint: lem-sfb-surjective-closed-module-invariance).

The two local-model predicates expand the finite and finite-projective clauses of this
node. They use the existing constant sheaves and localized restrictions. The Boolean
selects whether a finite-free splitting is required; it does not change the chosen site.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The finite local models in this node on the etale site. For `projective = true`,
each model is explicitly a retract of a finite free module; for `false`, only finiteness
is required. This refines the existing `LocallyConstantDatum`, with the same covers and
localized constant module sheaves, rather than using a stalk-finiteness surrogate.
Source: Stacks, Modules on Sites, lemma-pullback-locally-constant, with the finite-model
clause of blueprint det-sf-flat-model-generation
(blueprint: lem-sfb-surjective-closed-module-invariance). -/
def sfbEtaleFiniteLocalModels {Y : Scheme.{u}} (A : Type (u + 1)) [CommRing A]
    (H : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) (projective : Bool) : Prop :=
  ∃ d : LocallyConstantDatum H, ∀ j : d.cover.I₀,
    ∃ M : ModuleCat.{u + 1} A, Finite M ∧
      Nonempty (H.over (d.cover.etalePrecoverageToEtale j) ≅
        (constantSheaf
          (Y.smallEtaleTopology.over (d.cover.etalePrecoverageToEtale j))
          (ModuleCat.{u + 1} A)).obj M) ∧
      (projective = true → ∃ (n : ℕ) (i : M →ₗ[A] (Fin n → A))
        (r : (Fin n → A) →ₗ[A] M), r.comp i = LinearMap.id)

/-- The finite local models in this node on the original small pro-etale ringed site.
This is the covering datum of `IsLocallyConstantProEtaleModuleSheaf` with finite models,
and, when requested, explicit finite-free splittings. No etale-origin condition occurs.
Source: Stacks, Modules on Sites, lemma-pullback-locally-constant, and Tag 09AB;
blueprint det-sf-flat-model-generation, clause (2)
(blueprint: lem-sfb-surjective-closed-module-invariance). -/
def sfbProEtaleFiniteLocalModels (Y : Scheme.{u}) (A : Type u) [CommRing A]
    (H : proEtaleRingModules Y (proEtaleConstantRing Y A)) (projective : Bool) : Prop :=
  ∃ (I : Type (u + 1)) (U : I → Y.ProEt)
    (f : ∀ j : I, U j ⟶ ProEt.mk (𝟙 Y)),
    Presieve.ofArrows U f ∈ (ProEt.precoverage Y).coverings _ ∧
      ∀ j : I, ∃ M : ModuleCat.{u + 1} (ULift.{u + 1, u} A), Finite M ∧
        Nonempty (H.over (U j) ≅ proEtaleConstantModuleSheafOver Y A (U j) M) ∧
        (projective = true → ∃ (n : ℕ)
          (i : M →ₗ[ULift.{u + 1, u} A] (Fin n → ULift.{u + 1, u} A))
          (r : (Fin n → ULift.{u + 1, u} A) →ₗ[ULift.{u + 1, u} A] M),
          r.comp i = LinearMap.id)

/-- Surjective closed restriction on the etale site: the actual adjunction is an
adjoint equivalence, constants pull back to the same module models, and finite local
models, with or without finite-free splittings, are preserved and reflected.
Source: Stacks, Tags 04DZ, 03SI and Modules on Sites, lemma-pullback-locally-constant
(blueprint: lem-sfb-surjective-closed-module-invariance).

Proof: (1) A surjective closed immersion and all its base changes are universal
homeomorphisms [lem-weil-pbc-surjective-closed-immersion-universal-homeomorphism].
Etale topological invariance gives the set-sheaf equivalence and invertible actual
adjunction maps [thm-weil-pbc-universal-homeomorphism-invariance].
(2) The constant-coefficient inverse-image theorem identifies the module and abelian
units [lem-pe-constant-left-module-inverse-image,
prop-weil-pbc-inverse-image-modules-exact]. Finite-product adjunction lifting identifies
the abelian and set units [lem-weil-pbc-adjunction-lifts-group-ring-objects]. An inverse
of a bijective linear map is linear. Thus the actual module unit is invertible.
(3) Direct image reflects isomorphisms; the adjunction triangle then makes its counit
invertible [lem-weil-pbc-ringed-topoi-module-adjunction]. These natural maps give the
claimed equivalences. (4) Geometric inverse image preserves arbitrary constant modules
[lem-sfb-geometric-inverse-image-constant-module].
(5) Pull a trivializing cover back: etale base change preserves covers, localization
is object restriction, and inverse image commutes with these restrictions
[lem-weil-pbc-etale-base-change-continuous,
lem-weil-pbc-etale-site-localization-open,
lem-weil-pbc-etale-inverse-image-algebraic-structures].
(6) Conversely lift each etale object across h by the etale site equivalence and use
covering reflection [lemma-weil-pbc-universal-homeomorphism-site-equivalence,
lemma-weil-pbc-universal-homeomorphism-coverings]. The base-changed fully faithful
module inverse image lifts each trivialization and its inverse uniquely.
(8) All local models and their splitting maps are unchanged. Empty covers, rank zero,
zero rings and modules are allowed; no Noetherianity or nilpotence bound was used. -/
theorem sfbEtale_surjectiveClosed_module_invariance
    {T Y : Scheme.{u}} (h : T ⟶ Y) [IsClosedImmersion h] [Surjective h]
    (A : Type (u + 1)) [CommRing A] [Finite A] :
    IsIso (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) h).unit ∧
    IsIso (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) h).counit ∧
    (Etale.upperStar (ModuleCat.{u + 1} A) h).IsEquivalence ∧
    (Etale.lowerStar (ModuleCat.{u + 1} A) h).IsEquivalence ∧
    (∀ M : ModuleCat.{u + 1} A,
      Nonempty ((Etale.upperStar (ModuleCat.{u + 1} A) h).obj
        ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M) ≅
          (constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M)) ∧
    (∀ (H : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) (projective : Bool),
      sfbEtaleFiniteLocalModels A H projective ↔
        sfbEtaleFiniteLocalModels A
          ((Etale.upperStar (ModuleCat.{u + 1} A) h).obj H) projective) := by
  sorry

/-- Surjective closed restriction on the pro-etale site, for the published ordinary
constant-ring module operations and their tensor-unit-normalized adjunction.
Source: Stacks, Tag 09AB, Modules on Sites, lemma-adjoint-pullback-pushforward-modules
and lemma-pullback-locally-constant; blueprint det-sf-flat-model-generation, clause (2)
(blueprint: lem-sfb-surjective-closed-module-invariance).

Proof: (1) A surjective closed immersion and each base change are universal
homeomorphisms [lem-weil-pbc-surjective-closed-immersion-universal-homeomorphism].
Pro-etale topological invariance makes the actual set unit and counit invertible
[lem-trf-proetale-topological-invariance].
(2) Constant-coefficient inverse image agrees with abelian inverse image and its unit
[lem-pe-constant-left-module-inverse-image]. The finite-product adjunction lifting
identifies this with the set unit [lem-weil-pbc-adjunction-lifts-group-ring-objects].
The canonical constant-ring map and module adjunction give exactly the scalar actions
used here [prop-weil-pbc-proetale-constant-ring-map,
lem-weil-pbc-ringed-topoi-module-adjunction]. The inverse of an invertible underlying
linear map is linear, so the actual module unit is invertible.
(3) Direct image reflects isomorphisms and the triangle identity makes the actual
counit invertible; these natural maps exhibit the quasi-inverse equivalences.
(4) The geometric constant-module comparison preserves every model, without finiteness
[lem-sfb-geometric-inverse-image-constant-module].
(5) Base change preserves weakly etale arrows and fpqc covers
[lem-weil-pbc-weakly-etale-composition-base-change,
lem-galois-fpqc-covering-base-change]. Object inverse image is localized restriction
[lem-sfb-proetale-object-inverse-image-restriction], so a trivializing cover pulls back.
(7) Conversely refine a trivializing cover on T by a cover on Y
[new-lem-weil-pbc-proetale-surjective-closed-cover-refinement]. Each refined member
W is a base change of h and maps to an old cover member; that map is weakly etale
[lem-trf-weakly-etale-between-objects]. Pull its trivialization back. Composition and
localized-restriction compatibility identify its left side with the base-changed
pullback of H. The constant-module comparison identifies its right side with the
same model. Full faithfulness for the base-changed surjective closed immersion lifts
this isomorphism and its inverse to Y; faithfulness identifies their composites.
(8) The unchanged models and splitting maps give both equivalences of finite local
conditions. Empty schemes and empty covers, the zero ring and rank zero are included.
No assertion that every weakly etale object lifts, no Noetherianity and no uniform
nilpotence bound is required. -/
theorem sfbProEtale_surjectiveClosed_module_invariance
    {T Y : Scheme.{u}} (h : T ⟶ Y) [IsClosedImmersion h] [Surjective h]
    (A : Type u) [CommRing A] [Finite A] :
    IsIso (proEtaleConstantRingAdjunction A h).unit ∧
    IsIso (proEtaleConstantRingAdjunction A h).counit ∧
    (proEtaleConstantRingPullback A h).IsEquivalence ∧
    (proEtaleConstantRingPushforward A h).IsEquivalence ∧
    (∀ M : ModuleCat.{u + 1} (ULift.{u + 1, u} A),
      Nonempty ((proEtaleConstantRingPullback A h).obj
        (proEtaleConstantModuleSheaf Y A M) ≅ proEtaleConstantModuleSheaf T A M)) ∧
    (∀ (H : proEtaleRingModules Y (proEtaleConstantRing Y A)) (projective : Bool),
      sfbProEtaleFiniteLocalModels Y A H projective ↔
        sfbProEtaleFiniteLocalModels T A
          ((proEtaleConstantRingPullback A h).obj H) projective) := by
  sorry

end AlgebraicGeometry.Scheme
