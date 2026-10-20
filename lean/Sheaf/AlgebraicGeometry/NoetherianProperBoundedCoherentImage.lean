/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R2
-/
module

public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections
public import WeilConjectures.AlgebraicGeometry.Coherent
import Sheaf.AlgebraicGeometry.DirectImageBoundedCoherent
import WeilConjectures.AlgebraicGeometry.ModuleSupportProperOverBase
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex

/-! # Bounded coherent direct image in the Noetherian proper case

Source: Stacks Project, Tag 08E2, specialized to a proper morphism; Tag 02O5.
(blueprint: lem-pc-noetherian-proper-bounded-coherent-image).
-/

@[expose] public section
set_option autoImplicit false
universe u wY wT
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

namespace Modules

/-- Higher direct images of a finitely presented quasi-coherent module have finite
global sections over a Noetherian affine base under a proper morphism.
Source: Stacks Project, Tag 02O6. Apply the library theorem
`finite_sections_higherDirectImage`, which establishes this affine finiteness. -/
theorem finite_sections_proper_on_affine {X T : Scheme.{u}} (f : X ⟶ T) [IsProper f]
    [HasInjectiveResolutions X.Modules] (F : X.Modules) [F.IsFinitePresentation]
    [IsAffine T] [IsNoetherianRing Γ(T, ⊤)] [F.IsQuasicoherent] (q : ℕ) :
    Module.Finite Γ(T, ⊤) Γ((higherDirectImage f q).obj F, ⊤) := by
  exact finite_sections_higherDirectImage f F q

end Modules

/-- A proper morphism over a Noetherian base preserves bounded coherent cohomology.
This asserts neither a finite-free representative nor pseudo-coherence or a base-change
comparison. Source: Stacks Project, Tag 08E2, Lemma 36.11.3; Tag 02O5.

Proof: The source is locally Noetherian because p is locally of finite type. Each
coherent cohomology sheaf is therefore quasi-coherent and of finite type. The
scheme-theoretic support characterization supplies a closed immersion j with
support proper over T exactly when j followed by p is proper. Both j and p are
proper, so this condition holds. Apply `directImage_isBounded_coherent` to A with
these proper supports. This theorem supplies both boundedness and coherence of
the derived image, with independent supplied derived localizations. The argument
also covers zero modules and empty schemes.
(blueprint: lem-pc-noetherian-proper-bounded-coherent-image). -/
theorem noetherian_proper_directImage_bounded_coherent
    {Y T : Scheme.{u}} [IsNoetherian T] (p : Y ⟶ T)
    [IsProper p]
    [HasDerivedCategory.{wY}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{wT}
      (SheafOfModules.{u} (moduleRings T.toRingedSpace))]
    (A : schemeDerivedCategory Y)
    (hbounded : ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i →
      IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) i).obj A))
    (hcoherent : ∀ i : ℤ, RingedSpace.IsCoherent Y.toRingedSpace
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) i).obj A)) :
    (∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i →
      IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings T.toRingedSpace)) i).obj
          ((schemeDerivedDirectImage p).obj A))) ∧
    (∀ i : ℤ, RingedSpace.IsCoherent T.toRingedSpace
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings T.toRingedSpace)) i).obj
          ((schemeDerivedDirectImage p).obj A))) := by
  have hloc : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian p
  have hsupport : ∀ i : ℤ, Scheme.Modules.HasSupportProperOver p
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) i).obj A) := by
    intro i
    have hc := hcoherent i
    obtain ⟨hq, hft⟩ :=
      (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType Y _).mp hc
    let F := (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) i).obj A
    have := hq
    have := hft
    obtain ⟨Z, j, hj, hJ⟩ :=
      (Scheme.Modules.module_support_proper_over_base p F).2.2
    have := hj
    apply hJ.2.2.2.2.mpr
    infer_instance
  exact directImage_isBounded_coherent p A hbounded hcoherent hsupport

end AlgebraicGeometry.Scheme
