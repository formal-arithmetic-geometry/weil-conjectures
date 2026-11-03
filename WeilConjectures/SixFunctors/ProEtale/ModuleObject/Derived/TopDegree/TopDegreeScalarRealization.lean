/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.TopDegree.TopDegreeTraceDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.NativeTerminalSectionsComparison
public import WeilConjectures.AlgebraicGeometry.SixFunctors.PointProEtaleSectionsExactOfUniverses
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CohomologyTransport.CondensedIsomorphismCohomologyTransport
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

/-! # The actual scalar realization at the geometric point

Source: sk-cor-trace, steps 1 and 11, using terminal evaluation at 1.
(blueprint: lem-pd-native-scalar-realization-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open CategoryTheory.InternalAbelianSheafModule CategoryTheory.MonObj
open AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing.TopDegree

/-- The native scalar ring and its actual singleton value are canonically
isomorphic. Source: terminal profinite sections
(blueprint: lem-pd-native-scalar-realization-comparison). -/
def scalarRingComparison
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] : Γ Λ ≃+* condensedScalarRing Λ :=
  sectionGlobalEquiv (coherentTopology Profinite.{u}) Λ (⊤_ Profinite.{u})
    terminalIsTerminal

-- Keep the scalar localization used by the fixed point fibre.
attribute [-instance] residueLisseAlgebraHasDerivedCategory in
/-- The actual derived regular-unit sections, restricted through the canonical
scalar ring isomorphism, agree with the specified exact scalar realization.
Source: sk-cor-trace, steps 1 and 11
(blueprint: lem-pd-native-scalar-realization-comparison).
Proof: terminal evaluation at 1 is a linear natural isomorphism on the heart.
It identifies the regular-module scalar action with evaluation followed by
restriction through the singleton scalar ring isomorphism. Apply the exact
functor construction on derived categories and its composition comparison.
Finally use the canonical exact/right-derived section comparison. All these
functors and maps are the fixed library constructions, not chosen isomorphisms. -/
def scalarRealizationComparison
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (k : Type u) [Field k] [IsAlgClosed k] :
    TraceCupPoint.fiber Λ k ⋙
        (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
          (scalarRingComparison Λ).symm.toRingHom).mapDerivedCategory ≅
      (CohomologyTransport.sections Λ (Spec (.of k))).mapDerivedCategory := by
  let F := condensedRingCoefficientSections Λ (Spec (.of k))
  let G := ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (scalarRingComparison Λ).symm.toRingHom
  let J := Scheme.ProEt.topology (Spec (.of k))
  let O := condensedRingObj Λ (Spec (.of k))
  let s := (condensedRingScalarSections Λ (Spec (.of k))).comp
    (scalarRingComparison Λ).symm.toRingHom
  let V := Scheme.ProEt.mk (𝟙 (Spec (.of k)))
  let hV := MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.WeaklyEtale
    (Spec (.of k))
  let q := native_terminalSectionsComparison J O s V hV
  change F ⋙ G ≅ CohomologyTransport.sections Λ (Spec (.of k)) at q
  exact Functor.isoWhiskerRight (TraceCupPoint.exactComparison Λ k) G.mapDerivedCategory ≪≫
    (Functor.mapDerivedCategoryCompIso F G).symm ≪≫ Functor.mapDerivedCategoryNatIso q

end AlgebraicGeometry.ProEtale.CondensedRing.TopDegree
