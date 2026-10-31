/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleComparisonPullbackSections
public import WeilConjectures.AlgebraicGeometry.ClassicalContinuityMapSupplement

import WeilConjectures.CategoryTheory.ConstantRingModuleSheaves
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import WeilConjectures.CategoryTheory.ConstantLeftModuleInverseImage
import WeilConjectures.AlgebraicGeometry.CofilteredEtaleLimitSections
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits

/-! # The comparison morphism and its inverse image

Source: current blueprint (slopmaster2-20261031), part-six-operations/
sec-proetale-coefficients/sec-pe-comparison/sk-prop-pe-comparison-morphism;
Stacks Project, Tags 099R, 0GLZ, 099S and 00YV
(blueprint: sk-prop-pe-comparison-morphism).

The direct image below is the existing restriction functor along `Scheme.toProEt X`.
Set inverse image is the left Kan extension followed by sheafification in the recorded
comparison adjunction. Fixed-ring module sheaves are encoded as `ModuleCat`-valued
sheaves; `constant_ring_module_sheaves` identifies these with `ringedSiteModules` over
`constantSheaf`, preserving the sections and their constant scalar actions.

The affine formula is stated as the universal property of the restriction cocone.
The unit is bijective at each etale stage, identifying its diagram with `i ↦ F(Uᵢ)`.
Thus it asserts the canonical colimit formula, including its maps, without choosing
an arbitrary bijection of the two sets. The same convention applies to module sections.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- The geometric comparison, its section formula, coefficient functors and affine
continuity, for an arbitrary scheme and arbitrary discrete commutative coefficients.
Source: current blueprint (slopmaster2-20261031), part-six-operations/
sec-proetale-coefficients/sec-pe-comparison/sk-prop-pe-comparison-morphism,
formulas (2.5)--(2.6);
Stacks Project, Tags 099R, 0GLZ, 099S and 00YV
(blueprint: sk-prop-pe-comparison-morphism).

Proof:
1. The inclusion `Scheme.toProEt X` is continuous and preserves finite limits.
   The recorded `Scheme.proEtaleSiteComparison X` gives the geometric adjunction;
   its right adjoint is restriction, on objects, restrictions and sheaf morphisms.
2. Apply `proEtaleComparisonPullbackSections X`. Compose its natural isomorphism
   with its section equivalences to obtain `e` below. Its restriction equation and
   naturality in F give exactly the two equations for `e`. At etale objects the
   unit is the usual restriction identification, hence bijective.
3. The left adjoint preserves colimits; the recorded finite-limit comparison gives
   left exactness. These prove the two exactness assertions on set sheaves.
   Apply constant left-module inverse image (Stacks 00YV) to addition and scalar
   endomorphisms. This is also the module-valued Kan extension and sheafification,
   since restriction retains the operations and the adjunction on module maps.
   It gives the module adjunction and the underlying-set comparison `q`; its unit
   equation is the compatibility of the lifted adjunction with the set adjunction.
   Kernels are transported equalizers and cokernels are preserved by the left
   adjoint, so module inverse image preserves finite limits and finite colimits.
   Constant-ring module sheaves and fixed-ring module-valued sheaves agree by
   `constant_ring_module_sheaves`; no finiteness of the ring is used.
4. For an affine presentation apply etale section continuity (Tag 099S, degree zero)
   to the etale pullback section formula of step 2. The affine stages are qcqs and
   their transition maps are affine. The limit cocone maps are the section
   restrictions: the unit followed by the diagonal at a stage, pulled back to the
   limit, is the unit followed by the section `(uᵢ, id)`. This follows from the
   restriction and composition-unit equations for etale inverse image. Hence
   `sectionCocone P` is a colimit. Its stage units identify its diagram with F on
   the etale stages and identify the canonical colimit maps, proving (2.6).
5. Forget module coefficients. The comparison of step 3 identifies underlying
   inverse images and their units. Filtered module colimits have the same element
   representatives and eventual equality as filtered set colimits. The canonical
   restriction map is linear and its underlying function is bijective by step 4,
   so the module restriction cocone is also a colimit. -/
theorem comparisonMorphism (X : Scheme.{u}) :
    Nonempty
      (Functor.sheafPullbackConstruction.sheafPullback (Scheme.toProEt X)
        (Type (u + 1)) X.smallEtaleTopology (Scheme.ProEt.topology X) ⊣
      (Scheme.toProEt X).sheafPushforwardContinuous
        (Type (u + 1)) X.smallEtaleTopology (Scheme.ProEt.topology X)) ∧
    PreservesFiniteLimits
      (Functor.sheafPullbackConstruction.sheafPullback (Scheme.toProEt X)
        (Type (u + 1)) X.smallEtaleTopology (Scheme.ProEt.topology X)) ∧
    PreservesFiniteColimits
      (Functor.sheafPullbackConstruction.sheafPullback (Scheme.toProEt X)
        (Type (u + 1)) X.smallEtaleTopology (Scheme.ProEt.topology X)) ∧
    (∃ e : ∀ (F : Sheaf X.smallEtaleTopology (Type (u + 1))) (V : X.ProEt),
      ((Functor.sheafPullbackConstruction.sheafPullback (Scheme.toProEt X)
        (Type (u + 1)) X.smallEtaleTopology (Scheme.ProEt.topology X)).obj F).obj.obj
          (op V) ≃
        ((Scheme.etaleSetPullback V.hom).obj F).obj.obj
          (op (Scheme.Etale.mk (𝟙 V.left))),
      (∀ (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
        (V W : X.ProEt) (g : W ⟶ V)
        (s : ((Functor.sheafPullbackConstruction.sheafPullback (Scheme.toProEt X)
          (Type (u + 1)) X.smallEtaleTopology (Scheme.ProEt.topology X)).obj F).obj.obj
            (op V)),
        e F W (((Functor.sheafPullbackConstruction.sheafPullback (Scheme.toProEt X)
          (Type (u + 1)) X.smallEtaleTopology (Scheme.ProEt.topology X)).obj F).obj.map
            g.op s) = proEtaleComparisonSectionRestriction F g (e F V s)) ∧
      (∀ (F G : Sheaf X.smallEtaleTopology (Type (u + 1))) (ψ : F ⟶ G)
        (V : X.ProEt)
        (s : ((Functor.sheafPullbackConstruction.sheafPullback (Scheme.toProEt X)
          (Type (u + 1)) X.smallEtaleTopology (Scheme.ProEt.topology X)).obj F).obj.obj
            (op V)),
        e G V (((Functor.sheafPullbackConstruction.sheafPullback (Scheme.toProEt X)
          (Type (u + 1)) X.smallEtaleTopology (Scheme.ProEt.topology X)).map ψ).hom.app
            (op V) s) = ((Scheme.etaleSetPullback V.hom).map ψ).hom.app
              (op (Scheme.Etale.mk (𝟙 V.left))) (e F V s)) ∧
      (∀ (F : Sheaf X.smallEtaleTopology (Type (u + 1))) (U : X.Etale)
        (s : F.obj.obj (op U)),
        e F ((Scheme.toProEt X).obj U)
          (((Scheme.proEtaleSiteComparison X).unit.app F).hom.app (op U) s) =
            proEtaleComparisonEtaleSection F U s)) ∧
    (∀ (F : Sheaf X.smallEtaleTopology (Type (u + 1))) (U : X.Etale),
      Function.Bijective (((Scheme.proEtaleSiteComparison X).unit.app F).hom.app (op U))) ∧
    (∀ (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
      (I : Type (u + 1)) [SmallCategory I] [IsCofiltered I] (P : AffinePresentation X I),
      Nonempty (IsColimit (sectionCocone P
        (((Functor.sheafPullbackConstruction.sheafPullback (Scheme.toProEt X)
          (Type (u + 1)) X.smallEtaleTopology (Scheme.ProEt.topology X)).obj F).obj)))) ∧
    (∀ (Λ : Type (u + 1)) [CommRing Λ],
      Nonempty (comparisonUpperStar (ModuleCat.{u + 1} Λ) X ⊣
        comparisonLowerStar (ModuleCat.{u + 1} Λ) X) ∧
      PreservesFiniteLimits (comparisonUpperStar (ModuleCat.{u + 1} Λ) X) ∧
      PreservesFiniteColimits (comparisonUpperStar (ModuleCat.{u + 1} Λ) X) ∧
      (∃ q : comparisonUpperStar (ModuleCat.{u + 1} Λ) X ⋙
          sheafCompose (Scheme.ProEt.topology X) (forget (ModuleCat.{u + 1} Λ)) ≅
        sheafCompose X.smallEtaleTopology (forget (ModuleCat.{u + 1} Λ)) ⋙
          Functor.sheafPullbackConstruction.sheafPullback (Scheme.toProEt X)
            (Type (u + 1)) X.smallEtaleTopology (Scheme.ProEt.topology X),
        ∀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (U : X.Etale)
          (s : F.obj.obj (op U)),
          (q.hom.app F).hom.app (op ((Scheme.toProEt X).obj U))
            (((comparisonAdjunction (ModuleCat.{u + 1} Λ) X).unit.app F).hom.app
              (op U) s) =
          (((Scheme.proEtaleSiteComparison X).unit.app
            ((sheafCompose X.smallEtaleTopology
              (forget (ModuleCat.{u + 1} Λ))).obj F)).hom.app (op U) s)) ∧
      (∀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (U : X.Etale),
        IsIso (((comparisonAdjunction (ModuleCat.{u + 1} Λ) X).unit.app F).hom.app
          (op U))) ∧
      (∀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
        (I : Type (u + 1)) [SmallCategory I] [IsCofiltered I] (P : AffinePresentation X I),
        Nonempty (IsColimit
          (sectionCocone P ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).obj F).obj)))) := by
  sorry

end AlgebraicGeometry.ProEtale
