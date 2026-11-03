/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SkPropSfExistence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
public import Mathlib.CategoryTheory.Adjunction.Restrict

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StandingFieldCtfStability
import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
import WeilConjectures.AlgebraicGeometry.LocallyConstantPerfectComplex
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.AdmissibleBoundedConstructibleTriangulated
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CtfLocallyClosedPerfectGeneration
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntTensorProjection
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.AdmissibleTensorConstructibility
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralOpenImageProperFormulas
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperLocalizingAdmissibleCoefficients
import WeilConjectures.AlgebraicGeometry.Rational.RationalOpenDirectImageConstructible
import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteOpenDirectImageCtf
import WeilConjectures.Compactification.Over
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
import WeilConjectures.CategoryTheory.DerivedCategory.SixFunctors.NativeInternalHomExact
import Mathlib.CategoryTheory.Triangulated.Opposite.Subcategory
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# The three adjunctions on constructible finite-Tor complexes

Source: latest blueprint, part-six-operations/sec-six-functors/sec-the-remaining-operations/
sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-adjunctions.md and its proof;
standing field convention confirmed by Wei Yang #1412.
(blueprint: det-thm-sf-ctf-stability-adjunctions).

The ambient categories are the ordinary derived categories of internal modules over
p_X^* Λ. The exceptional adjunction is on their localizing subcategories. The Hom,
unit and counit equations below specify restriction of these very adjunctions.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] upperStarFromPoint

/-- The ordinary, right-factor tensor--Hom, and exceptional adjunctions restrict to
the full bounded constructible finite-Tor subcategories, with the ambient maps.
The last conjunct applies to every specified localizing adjunction: its existence and
uniqueness are supplied by `sk_prop_sf_existence`, so no additional choice of f^! is made.

Source: latest blueprint, part-six-operations/sec-six-functors/sec-the-remaining-operations/
sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-adjunctions.md, clauses (1)--(3), and its proof.
(blueprint: det-thm-sf-ctf-stability-adjunctions).

Proof plan, following the node:
1. By sk-def-sfb-constructible and sk-def-localizing-closure, the constructible finite-Tor
   categories are full in the ambient derived categories,
   and in their localizing closures. Thus their Hom sets, identities and composition
   are the ambient ones. The inclusion in the closure sends a generator to itself.
2. det-thm-sf-ctf-stability-direct-images gives preservation by pullback, pushforward,
   tensor, compact support and exceptional inverse image in the standing field scope.
   det-thm-sf-ctf-stability-internal-hom gives preservation by RHom(K,-). Restrict the functors
   on objects and arrows using these preservation assertions and full inclusions.
3. Restrict `derivedUpperStarLowerStarAdjunction` of det-def-sfb-module-derived-pushpull
   along these inclusions. Its natural
   Hom equivalence is unchanged, proving clause (1).
4. Transport `derivedTensorHomAdjunction` of det-def-sfb-derived-tensor-hom through
   the derived Koszul symmetry of def-sfb-modobj-symmetric-tensor
   to write the left adjoint as - tensor K, then restrict its Hom equivalence. This
   is clause (2); the coefficient tensor remains the relative derived module tensor.
5. For the specified compactification and specified localizing right adjoint of
   sk-prop-sf-existence, restrict
   its adjunction through the full inclusions of Dctf into Loc(Dctf). This is clause (3).
6. The image of the identity by each Hom equivalence is its ambient unit, and the
   inverse image of the identity is its ambient counit. Fullness leaves naturality
   and the triangle identities unchanged, giving the three displayed compatibilities.
-/
theorem constructibleFiniteTor_adjunctions_of_finite_or_isAlgClosed
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (_hk : Finite k ∨ IsAlgClosed k) (_hcd : BaseFieldFiniteCD ℓ k)
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (_hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ) :
    let PX := constantModelBoundedConstructible Λ X ⊓
      fun K ↦ DerivedCategory.finiteTorAmplitude _ K
    let PY := constantModelBoundedConstructible Λ Y ⊓
      fun K ↦ DerivedCategory.finiteTorAmplitude _ K
    (∃ (F₀ : ConstantModelConstructibleFiniteTor Λ Y ⥤ ConstantModelConstructibleFiniteTor Λ X)
      (G₀ : ConstantModelConstructibleFiniteTor Λ X ⥤ ConstantModelConstructibleFiniteTor Λ Y)
      (α : F₀ ⋙ PX.ι ≅ PY.ι ⋙ (moduleObjectDerivedPullback Λ f))
      (β : G₀ ⋙ PY.ι ≅ PX.ι ⋙ (moduleObjectDerivedPushforward Λ f)) (adj₀ : F₀ ⊣ G₀),
      (∀ (M : ConstantModelConstructibleFiniteTor Λ Y) (N : ConstantModelConstructibleFiniteTor Λ X)
          (g : F₀.obj M ⟶ N),
        PY.ι.map (adj₀.homEquiv M N g) =
          (derivedUpperStarLowerStarAdjunction Λ f).homEquiv (PY.ι.obj M) (PX.ι.obj N)
            (α.inv.app M ≫ PX.ι.map g) ≫ β.inv.app N) ∧
      (∀ M : ConstantModelConstructibleFiniteTor Λ Y, PY.ι.map (adj₀.unit.app M) =
        (derivedUpperStarLowerStarAdjunction Λ f).unit.app (PY.ι.obj M) ≫
          (moduleObjectDerivedPushforward Λ f).map (α.inv.app M) ≫ β.inv.app (F₀.obj M)) ∧
      (∀ N : ConstantModelConstructibleFiniteTor Λ X, PX.ι.map (adj₀.counit.app N) =
        α.hom.app (G₀.obj N) ≫ (moduleObjectDerivedPullback Λ f).map (β.hom.app N) ≫
          (derivedUpperStarLowerStarAdjunction Λ f).counit.app (PX.ι.obj N))) ∧
    (∀ K : ConstantModelConstructibleFiniteTor Λ X,
      let tensorAdj := (derivedTensorHomAdjunction Λ K.obj).ofNatIsoLeft
        (@BraidedCategory.tensorLeftIsoTensorRight _ _ _
          (DerivedCategory.braidedCategory' _) K.obj)
      ∃ (F₀ : ConstantModelConstructibleFiniteTor Λ X ⥤ ConstantModelConstructibleFiniteTor Λ X)
      (G₀ : ConstantModelConstructibleFiniteTor Λ X ⥤ ConstantModelConstructibleFiniteTor Λ X)
      (α : F₀ ⋙ PX.ι ≅ PX.ι ⋙ (MonoidalCategory.tensorRight K.obj))
      (β : G₀ ⋙ PX.ι ≅ PX.ι ⋙ ((derivedHom Λ X).obj (Opposite.op K.obj))) (adj₀ : F₀ ⊣ G₀),
      (∀ (M : ConstantModelConstructibleFiniteTor Λ X) (N : ConstantModelConstructibleFiniteTor Λ X)
          (g : F₀.obj M ⟶ N),
        PX.ι.map (adj₀.homEquiv M N g) =
          (tensorAdj).homEquiv (PX.ι.obj M) (PX.ι.obj N)
            (α.inv.app M ≫ PX.ι.map g) ≫ β.inv.app N) ∧
      (∀ M : ConstantModelConstructibleFiniteTor Λ X, PX.ι.map (adj₀.unit.app M) =
        (tensorAdj).unit.app (PX.ι.obj M) ≫
          ((derivedHom Λ X).obj (Opposite.op K.obj)).map (α.inv.app M) ≫ β.inv.app (F₀.obj M)) ∧
      (∀ N : ConstantModelConstructibleFiniteTor Λ X, PX.ι.map (adj₀.counit.app N) =
        α.hom.app (G₀.obj N) ≫ (MonoidalCategory.tensorRight K.obj).map (β.hom.app N) ≫
          (tensorAdj).counit.app (PX.ι.obj N))) ∧
    (∀ (c : Compactification.BoundaryCompactification f)
      (h : ∀ K, localizingClosureProEtale Λ X K → localizingClosureProEtale Λ Y
        ((rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K))
      (G : (localizingClosureProEtale Λ Y).FullSubcategory ⥤
        (localizingClosureProEtale Λ X).FullSubcategory)
      (adj : localizingLowerShriek Λ c.obj.obj h ⊣ G),
      let iX : ConstantModelConstructibleFiniteTor Λ X ⥤
          (localizingClosureProEtale Λ X).FullSubcategory :=
        ObjectProperty.ιOfLE (fun K hK _P _hP hSP ↦ hSP K hK)
      let iY : ConstantModelConstructibleFiniteTor Λ Y ⥤
          (localizingClosureProEtale Λ Y).FullSubcategory :=
        ObjectProperty.ιOfLE (fun K hK _P _hP hSP ↦ hSP K hK)
      ∃ (F₀ : ConstantModelConstructibleFiniteTor Λ X ⥤ ConstantModelConstructibleFiniteTor Λ Y)
      (G₀ : ConstantModelConstructibleFiniteTor Λ Y ⥤ ConstantModelConstructibleFiniteTor Λ X)
      (α : F₀ ⋙ iY ≅ iX ⋙ (localizingLowerShriek Λ c.obj.obj h))
      (β : G₀ ⋙ iX ≅ iY ⋙ G) (adj₀ : F₀ ⊣ G₀),
      (∀ (M : ConstantModelConstructibleFiniteTor Λ X) (N : ConstantModelConstructibleFiniteTor Λ Y)
          (g : F₀.obj M ⟶ N),
        iX.map (adj₀.homEquiv M N g) =
          (adj).homEquiv (iX.obj M) (iY.obj N)
            (α.inv.app M ≫ iY.map g) ≫ β.inv.app N) ∧
      (∀ M : ConstantModelConstructibleFiniteTor Λ X, iX.map (adj₀.unit.app M) =
        (adj).unit.app (iX.obj M) ≫
          G.map (α.inv.app M) ≫ β.inv.app (F₀.obj M)) ∧
      (∀ N : ConstantModelConstructibleFiniteTor Λ Y, iY.map (adj₀.counit.app N) =
        α.hom.app (G₀.obj N) ≫ (localizingLowerShriek Λ c.obj.obj h).map (β.hom.app N) ≫
          (adj).counit.app (iY.obj N))) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
