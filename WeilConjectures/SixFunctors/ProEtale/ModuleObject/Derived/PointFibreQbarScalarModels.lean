/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.PointTensorReduction.CondensedPointTensorReduction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.PointFibreTensorModels
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.PointFibreTensorRationalCompatibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ExactScalarPointCup
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.NativeTerminalSectionsComparison
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.NativeTerminalSectionsComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.CommonFieldLatticeGenerators
public import WeilConjectures.AlgebraicGeometry.CondensedGeometricPoint.CondensedGeometricPointPerfectGeneral
public import WeilConjectures.AlgebraicGeometry.FinitePointComparison.CondensedPointDerivedScalarComparison
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionConstraintCoherence
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedCondensedCoefficients

/-! # Rational point-fibre scalar coherence

Source: latest blueprint, `sk-thm-sf-kunneth-relative`, finite-reduction and
scalar-extension clause, specialized to the geometric point; DAG proof Steps 1--4
(blueprint: lem-sf-point-fibre-qbar-scalar-coherence).

The native cup is transported through evaluation at 1 and the canonical singleton
scalar-ring isomorphism. Identity, composition and passage to the algebraic closure
are equations on the ambient fibre/change comparisons, with balanced-tensor
normalizations for the ordinary derived unitors and compositors.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.CondensedRing.PointTensorReduction
open AlgebraicGeometry.ProEtale.PurityTransport
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct ChangeOfRings

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Identity inclusions induce the identity of bundled condensed rings.
Source: coefficient inclusions in Step 4
(blueprint: def-sf-qbar-scalar-coherence-models).
Proof: the underlying continuous-map inclusion is definitionally the identity. -/
theorem qbarFieldMap_id (ell : ℕ) [Fact ell.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ell) :
    qbarFieldMap.{u} ell (le_refl E) = 𝟙 _ := by
  rfl

/-- Bundled finite coefficient inclusions compose strictly.
Source: coefficient inclusions in Step 4
(blueprint: def-sf-qbar-scalar-coherence-models).
Proof: both underlying maps postcompose with the same field inclusion. -/
theorem qbarFieldMap_comp (ell : ℕ) [Fact ell.Prime]
    (E F G : PadicAlgCl.FiniteIntermediateField ell) (hEF : E ≤ F) (hFG : F ≤ G) :
    qbarFieldMap.{u} ell (hEF.trans hFG) =
      qbarFieldMap ell hEF ≫ qbarFieldMap ell hFG := by
  rfl

/-- The finite inclusions commute with the inclusion into the algebraic closure.
Source: coefficient cocone in Step 4
(blueprint: def-sf-qbar-scalar-coherence-models).
Proof: forget the bundled ring structure and apply the coefficient-cocone identity. -/
theorem qbarClosureMap_comp (ell : ℕ) [Fact ell.Prime]
    (E F : PadicAlgCl.FiniteIntermediateField ell) (h : E ≤ F) :
    qbarFieldMap.{u} ell h ≫ qbarClosureMap ell F = qbarClosureMap ell E := by
  apply CommMon.hom_ext
  exact Profinite.padicSubfieldRingObjMap_comp_toPadicAlgCl ell h

set_option maxHeartbeats 6400000 in
-- Comparing the two sheaf scalar actions expands the internal-module instances.
/-- Regular-module point sections in the fixed singleton scalar coordinates.
Source: terminal evaluation and singleton-section transport, Step 1
(blueprint: def-sf-qbar-scalar-coherence-models).
Proof: apply normalized terminal evaluation with the scalar map already
composed with the inverse singleton section-ring isomorphism. The domain and
codomain are definitionally the recorded two presentations of scalar sections. -/
theorem qbarNativeSections_exists (Λ : ScalarSixRing.{u})
    (k : Type u) [Field k] [IsAlgClosed k] :
    ∃ q : condensedRingCoefficientSections Λ.X (Spec (.of k)) ⋙ qbarNativeRestriction Λ ≅
        CohomologyTransport.sections Λ.X (Spec (.of k)),
      ∀ (M : ModuleRingedComparison.internalModules Λ.X (Spec (.of k)))
        (f : (condensedRingCoefficientSections Λ.X (Spec (.of k))).obj M),
        (q.hom.app M) f =
          (((constantSheafAdj (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1}
            (MorphismProperty.Over.mkIdTerminal @WeaklyEtale (Spec (.of k)))).homEquiv
              (𝟙_ Ab.{u + 1}) M.X)
                (η[condensedRingObj Λ.X (Spec (.of k))] ≫ f.hom)).hom (ULift.up 1) := by
  let t := (InternalAbelianSheafModule.sectionGlobalEquiv
    (coherentTopology Profinite.{u}) Λ.X (⊤_ Profinite.{u}) terminalIsTerminal).symm.toRingHom
  let J := Scheme.ProEt.topology (Spec (.of k))
  let O := condensedRingObj Λ.X (Spec (.of k))
  let s := (condensedRingScalarSections Λ.X (Spec (.of k))).comp t
  let U := Scheme.ProEt.mk (𝟙 (Spec (.of k)))
  let hU := MorphismProperty.Over.mkIdTerminal @WeaklyEtale (Spec (.of k))
  let q : regularSections J O s ≅ Evaluation.sections J O U ⋙
      ModuleCat.restrictScalars
        ((InternalAbelianSheafModule.sectionGlobalEval J O U).comp s) :=
    NatIso.ofComponents (fun M ↦ LinearEquiv.toModuleIso
    (LinearEquiv.ofBijective (terminal_linear J O s U M)
      (terminal_eval_bijective J O s U hU M))) (by
        intro M N f
        ext g
        rfl)
  change ∃ q : condensedRingCoefficientSections Λ.X (Spec (.of k)) ⋙
      qbarNativeRestriction Λ ≅ CohomologyTransport.sections Λ.X (Spec (.of k)), _
  exact ⟨q, fun _ _ ↦ rfl⟩


end AlgebraicGeometry.ProEtale.CondensedRing
