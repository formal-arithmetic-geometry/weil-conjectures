/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixCtfGenerators
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients

import WeilConjectures.AlgebraicGeometry.PerfectLocalModelCtf
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing

/-! # Locally perfect models have constructible finite-Tor locally closed extensions.

Source: blueprint latest, sec-six-functors-basics/sk-prop-scalar-six,
det-prop-scalar-six-ctf.proof.md, (2), local models.
(blueprint: lem-route-sfb-perfect-locally-closed-extension).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  Functor.leftDerivedFunctor HasDerivedCategory.ofHasKInjectiveResolutions
  HasDerivedCategory.standard

/-- Locally perfect models have constructible finite-Tor locally closed extensions.

Source: blueprint latest, sec-six-functors-basics/sk-prop-scalar-six,
det-prop-scalar-six-ctf.proof.md, (2), local models.
(blueprint: lem-route-sfb-perfect-locally-closed-extension).

Proof in words: X is finite type over the Noetherian spectrum of k, hence locally
Noetherian, and quasi-compact, so Noetherian. The immersion i is locally of finite
type, so S is locally Noetherian, and its underlying space is Noetherian as a subspace
of the Noetherian space of X. Hence
constantModelBoundedConstructible_finiteTorAmplitude_of_isLocallyPerfectScalarModel
applies to Q: it is bounded constant-model constructible with finite Tor amplitude on S.
Give S the composite structure map i ≫ X.hom; it is finite type, quasi-compact and
separated, and i lies over Spec k. Factor i through its scheme-theoretic image as
i.toImage followed by i.imageι: the closed immersion i.imageι is proper and i.toImage
is a quasi-compact open immersion, so this is a boundary compactification of i. The
last clause of compactification_localizing (no finite cohomological dimension on k)
applied to this compactification and Q gives the conclusion, since
sfbLocallyClosedDerivedExtension Λ i hi is definitionally the composite of the
extension by zero along i.toImage with the derived direct image along i.imageι. -/
theorem sfbPerfectLocallyClosedExtension (ell : ℕ) [Fact ell.Prime]
    (Λ : ScalarSixRing.{u}) (hΛ : IsLocalizingAdmissibleCoefficient ell Λ.X)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (S : Scheme.{u}) (i : S ⟶ X.left) (hi : IsImmersion i)
    (Q : DerivedCategory (ModuleRingedComparison.internalModules Λ.X S))
    (hQ : IsLocallyPerfectScalarModel Λ.X S Q) :
    constantModelBoundedConstructible Λ.X X.left
        ((sfbLocallyClosedDerivedExtension Λ i hi).obj Q) ∧
      DerivedCategory.finiteTorAmplitude _
        ((sfbLocallyClosedDerivedExtension Λ i hi).obj Q) := by
  let : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let : IsNoetherian X.left := {}
  let : IsImmersion i := hi
  let : TopologicalSpace.NoetherianSpace S := i.isEmbedding.isInducing.noetherianSpace
  let : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian i
  have hQS :=
    constantModelBoundedConstructible_finiteTorAmplitude_of_isLocallyPerfectScalarModel
      ell Λ.X hΛ S Q hQ
  let : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
  have : LocallyOfFiniteType (X.left ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType X.hom)
  have : QuasiCompact (X.left ↘ Spec (.of k)) := inferInstanceAs (QuasiCompact X.hom)
  have : IsSeparated (X.left ↘ Spec (.of k)) := inferInstanceAs (IsSeparated X.hom)
  let : S.Over (Spec (.of k)) := ⟨i ≫ X.hom⟩
  have : i.IsOver (Spec (.of k)) := ⟨rfl⟩
  have : LocallyOfFiniteType (S ↘ Spec (.of k)) := by
    change LocallyOfFiniteType (i ≫ X.hom)
    infer_instance
  have : QuasiCompact (S ↘ Spec (.of k)) := by
    change QuasiCompact (i ≫ X.hom)
    infer_instance
  have : IsSeparated (S ↘ Spec (.of k)) := by
    change IsSeparated (i ≫ X.hom)
    infer_instance
  let c : Compactification i :=
    { Z := i.image
      g := i.imageι
      i := i.toImage
      comm := (Scheme.Hom.toImage_imageι i).symm
      isProper := inferInstance
      isOpenImmersion := inferInstance }
  let c' : Compactification.BoundaryCompactification i := ⟨⟨c, inferInstance⟩⟩
  exact (compactification_localizing Λ.X ell k i c' hΛ).2.2.2 Q hQS

end AlgebraicGeometry.ProEtale.CondensedRing
