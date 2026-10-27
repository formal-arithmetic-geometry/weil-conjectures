module

public import Sheaf.Topology.ContinuousMapCondensedRingMap
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing
public import Sheaf.Paper.CoefficientHeartStratificationDefs
public import Sheaf.AlgebraicGeometry.FiniteConstantLocalModel
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.CategoryTheory.Triangulated.Triangulated

import Sheaf.Paper.CoefficientHeartLisseExtensionConstructible
import Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport
import Sheaf.CategoryTheory.InternalSectionScalarAdjunction
import Sheaf.AlgebraicGeometry.LocalFinitePresentationInverseImage
import Sheaf.AlgebraicGeometry.LocallyClosedExtensionCoherence
import Sheaf.Topology.NoetherianGoodStratificationRefinement
import Sheaf.CategoryTheory.ScalarInverseImageTowerDiagram
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Finite-field support devissage for all-continuous coefficients

Source: main-20261015, sk-thm-sf-ctf-stability-direct-images.proof.md, paragraph (3).
(blueprint: lem-sfb-continuous-algcl-finite-stage-devissage).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The exact open-then-closed support extension, using the published internal modules.
Source: Hemo--Richarz--Scholbach Lemma 3.4; blueprint direct-images proof (3).
(blueprint: lem-sfb-continuous-algcl-finite-stage-devissage). -/
def finiteStageSupportExtension
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S Z T : Scheme.{u}}
    (j : S ⟶ Z) (hj : IsOpenImmersion j) (i : Z ⟶ T) :
    Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S) ⥤
      Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T) :=
  letI := hj
  openImmersionLowerShriek Λ j ⋙ lowerStar Λ i

/-- The ordinary scalar/support comparison is the open scalar isomorphism followed
by the closed pushforward mate; all arrows have the destination coefficient action.
Source: blueprint direct-images proof (3), canonical support projection comparison.
(blueprint: lem-sfb-continuous-algcl-finite-stage-devissage). -/
def finiteStageSupportScalarMap
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (ρ : Λ ⟶ Λ') [IsMonHom ρ] {S Z T : Scheme.{u}}
    (j : S ⟶ Z) (hj : IsOpenImmersion j) (i : Z ⟶ T)
    (N : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)) :
    (Mod.extendScalars (coefficientMap ρ T)).obj
        ((finiteStageSupportExtension Λ j hj i).obj N) ⟶
      (finiteStageSupportExtension Λ' j hj i).obj
        ((Mod.extendScalars (coefficientMap ρ S)).obj N) :=
  letI := hj
  (pushHom ρ i).app ((openImmersionLowerShriek Λ j).obj N) ≫
    (lowerStar Λ' i).map ((openImmersionShriekIso ρ j).hom.app N)

/-- The composite ordinary comparison for the two specified support immersions.
Source: blueprint direct-images proof (3), support composition and scalar comparison.
(blueprint: lem-sfb-continuous-algcl-finite-stage-devissage). -/
def finiteStageDoubleSupportScalarMap
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (ρ : Λ ⟶ Λ') [IsMonHom ρ] {V W S Z T : Scheme.{u}}
    (v : V ⟶ W) (hv : IsOpenImmersion v) (c : W ⟶ S)
    (j : S ⟶ Z) (hj : IsOpenImmersion j) (i : Z ⟶ T)
    (N : Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1}) (condensedRingObj Λ V)) :
    (Mod.extendScalars (coefficientMap ρ T)).obj
        ((finiteStageSupportExtension Λ j hj i).obj
          ((finiteStageSupportExtension Λ v hv c).obj N)) ⟶
      (finiteStageSupportExtension Λ' j hj i).obj
        ((finiteStageSupportExtension Λ' v hv c).obj
          ((Mod.extendScalars (coefficientMap ρ V)).obj N)) :=
  finiteStageSupportScalarMap ρ j hj i
      ((finiteStageSupportExtension Λ v hv c).obj N) ≫
    (finiteStageSupportExtension Λ' j hj i).map (finiteStageSupportScalarMap ρ v hv c N)

/-- The supported module placed in degree zero of the ordinary unbounded derived category.
Source: blueprint direct-images proof (3), the complexes C_t and G_t.
(blueprint: lem-sfb-continuous-algcl-finite-stage-devissage). -/
def finiteStageSupportedComplex
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {V W S Z T : Scheme.{u}}
    (v : V ⟶ W) (hv : IsOpenImmersion v) (c : W ⟶ S)
    (j : S ⟶ Z) (hj : IsOpenImmersion j) (i : Z ⟶ T)
    (N : Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1}) (condensedRingObj Λ V)) :
    DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)) :=
  (DerivedCategory.singleFunctor _ 0).obj
    ((finiteStageSupportExtension Λ j hj i).obj
      ((finiteStageSupportExtension Λ v hv c).obj N))

/-- The canonical derived-to-ordinary support comparison: the total-left-derived
counit followed by the ordinary balanced scalar/support mate, in degree zero.
Source: blueprint direct-images proof (3), derived support projection normalization.
(blueprint: lem-sfb-continuous-algcl-finite-stage-devissage). -/
def finiteStageDerivedSupportMap
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (ρ : Λ ⟶ Λ') [IsMonHom ρ] {V W S Z T : Scheme.{u}}
    (v : V ⟶ W) (hv : IsOpenImmersion v) (c : W ⟶ S)
    (j : S ⟶ Z) (hj : IsOpenImmersion j) (i : Z ⟶ T)
    (N : Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1}) (condensedRingObj Λ V)) :
    (Mod.extendScalars (coefficientMap ρ T)).leftDerivedFunctor.obj
      (finiteStageSupportedComplex Λ v hv c j hj i N) ⟶
        finiteStageSupportedComplex Λ' v hv c j hj i
          ((Mod.extendScalars (coefficientMap ρ V)).obj N) :=
  let F := Mod.extendScalars (coefficientMap ρ T)
  let M := (finiteStageSupportExtension Λ j hj i).obj
    ((finiteStageSupportExtension Λ v hv c).obj N)
  F.leftDerivedFunctorCounit.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj ((CochainComplex.singleFunctor _ 0).obj M)) ≫
    DerivedCategory.Q.map ((F.mapCochainComplexSingleFunctor 0).hom.app M) ≫
      (DerivedCategory.singleFunctor _ 0).map
        (finiteStageDoubleSupportScalarMap ρ v hv c j hj i N)

/-- The actual coefficient map induced by inclusion of the finite subfield, with its
restricted norm topology. Source: blueprint direct-images proof (3).
(blueprint: lem-sfb-continuous-algcl-finite-stage-devissage). -/
abbrev finiteStageFieldMap (ℓ : ℕ) [Fact ℓ.Prime] (Ω : Type u) [NormedField Ω]
    [Algebra ℚ_[ℓ] Ω] (E : IntermediateField ℚ_[ℓ] Ω) :
    Profinite.continuousCoefficientRingObj E ⟶ Profinite.continuousCoefficientRingObj Ω :=
  (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (Profinite.continuousMapRingSheafMapOfUniverse
        (algebraMap E Ω) continuous_subtype_val)

/-- Witnesses of exactly the finite-field model and support filtration assertions.
All functors are the published internal-module functors; the comparison is the actual
total-left-derived counit followed by the scalar/support mate, rather than a chosen map.
Source: blueprint direct-images proof (3), good refinement and localization filtration.
(blueprint: lem-sfb-continuous-algcl-finite-stage-devissage). -/
def ContinuousAlgClFiniteStageDevissage
    (ℓ : ℕ) [Fact ℓ.Prime] (Ω : Type u) [NormedField Ω] [Algebra ℚ_[ℓ] Ω]
    {S T : Scheme.{u}} (a : S ⟶ T)
    (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj Ω) S)) : Prop :=
  ∃ (Z : Scheme.{u}) (j : S ⟶ Z) (hj : IsOpenImmersion j) (i : Z ⟶ T),
    IsClosedImmersion i ∧ j ≫ i = a ∧
    ∃ P : S.FiniteLocallyClosedStratification,
      (∀ t : Fin P.n, Topology.IsConstructible (P.stratum t)) ∧
      (∀ t : Fin P.n, ∃ A : Set (Fin P.n),
        closure (P.stratum t) = ⋃ s ∈ A, P.stratum s) ∧
      (IsEmpty S → P.n = 0) ∧
      ∃ E : Fin P.n → IntermediateField ℚ_[ℓ] Ω,
        (∀ t : Fin P.n, FiniteDimensional ℚ_[ℓ] (E t)) ∧
        ∃ (W : Fin P.n → Scheme.{u}) (v : ∀ t : Fin P.n, P.domain t ⟶ W t)
          (hv : ∀ t : Fin P.n, IsOpenImmersion (v t)) (c : ∀ t : Fin P.n, W t ⟶ S),
          (∀ t : Fin P.n, IsClosedImmersion (c t)) ∧
          (∀ t : Fin P.n, v t ≫ c t = P.immersion t) ∧
          ∃ N : ∀ t : Fin P.n,
            Mod (Sheaf (Scheme.ProEt.topology (P.domain t)) Ab.{u + 1})
              (condensedRingObj (Profinite.continuousCoefficientRingObj (E t)) (P.domain t)),
            (∀ t : Fin P.n,
              IsLisseCoefficientModule (Profinite.continuousCoefficientRingObj (E t)) (N t)) ∧
            (∀ t : Fin P.n, Nonempty
              ((Mod.extendScalars (coefficientMap (finiteStageFieldMap ℓ Ω (E t))
                (P.domain t))).obj (N t) ≅
                  (upperStar (Profinite.continuousCoefficientRingObj Ω) (P.immersion t)).obj L)) ∧
            (∀ t : Fin P.n,
              constantModelBoundedConstructible (Profinite.continuousCoefficientRingObj (E t)) T
                (finiteStageSupportedComplex (Profinite.continuousCoefficientRingObj (E t))
                  (v t) (hv t) (c t) j hj i (N t))) ∧
            (∀ t : Fin P.n,
              IsIso (finiteStageDerivedSupportMap (finiteStageFieldMap ℓ Ω (E t))
                (v t) (hv t) (c t) j hj i (N t))) ∧
            ∃ F : Fin (P.n + 1) → DerivedCategory
              (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
                (condensedRingObj (Profinite.continuousCoefficientRingObj Ω) T)),
              IsZero (F 0) ∧
              Nonempty (F (Fin.last P.n) ≅ (DerivedCategory.singleFunctor _ 0).obj
                ((finiteStageSupportExtension (Profinite.continuousCoefficientRingObj Ω)
                  j hj i).obj L)) ∧
              ∀ t : Fin P.n,
                ∃ (f : F t.castSucc ⟶ F t.succ)
                  (g : F t.succ ⟶
                    finiteStageSupportedComplex (Profinite.continuousCoefficientRingObj Ω)
                      (v t) (hv t) (c t) j hj i
                      ((Mod.extendScalars (coefficientMap (finiteStageFieldMap ℓ Ω (E t))
                        (P.domain t))).obj (N t)))
                  (h : finiteStageSupportedComplex (Profinite.continuousCoefficientRingObj Ω)
                      (v t) (hv t) (c t) j hj i
                      ((Mod.extendScalars (coefficientMap (finiteStageFieldMap ℓ Ω (E t))
                        (P.domain t))).obj (N t)) ⟶ (F t.castSucc) ⟦(1 : ℤ)⟧),
                  Triangle.mk f g h ∈ distTriang _

/-- Finite-field scalar generators give a good finite support devissage of a lisse
all-continuous algebraic-closure coefficient module.

Source: main-20261015, sk-thm-sf-ctf-stability-direct-images.proof.md, paragraph (3);
Hemo--Richarz--Scholbach Lemma 3.4 for exact support extension.
(blueprint: lem-sfb-continuous-algcl-finite-stage-devissage).

Proof plan, following the seven steps of the node:
1. Finite-type schemes over a field are Noetherian. Their subsets are quasi-compact.
Lisse modules are finite constant local models. Apply
lem-sfb-continuous-algcl-stratified-finite-models to obtain the finite-field models.
2. Apply lem-sfb-noetherian-good-stratification-refinement. Order the good strata by
removing maximal strata first; initial unions are open. Give their successive differences
the reduced induced scheme structures from lem-weil-pbc-reduced-induced-closed-subscheme.
3. Factor the reduced strata through the original model strata using
lem-weil-pbc-reduced-source-factors-through-closed-subscheme. Pull back the models:
lem-sfb-local-finite-presentation-inverse-image preserves the trivializing covers.
The scalar/inverse-image tower comparison and internal/sectionwise transport identify
the ordinary scalar extensions with the restrictions of L.
4. Factor the composite support immersions; composition of closed immersions applies.
lem-sfb-locally-closed-extension-coherence compares the two-stage extensions, and
lem-sfb-coefficient-heart-lisse-extension-constructible makes C_t bounded constructible.
5. lem-sfb-finite-stage-supported-generation identifies derived support/scalar extension;
the lisse input is concentrated in degree zero. The normalization in
lem-sfb-supported-common-field-scalar-models with both fields equal to E_t identifies
this with the actual support mate followed by the derived counit used above, in B-modules.
6. Apply lem-weil-pbc-proetale-ringed-open-closed to consecutive initial open unions.
Internal-module transport and support coherence give the exact localization sequences.
7. lem-weil-pbc-complex-ses-triangle supplies the distinguished triangles after placing
these sequences in degree zero. The last open is S. If S is empty take no strata and
only the zero object. Rank-zero models and different fields on different strata cause
no change to this construction. -/
theorem continuousAlgCl_finite_stage_devissage
    (ℓ : ℕ) [Fact ℓ.Prime] (Ω : Type u) [NormedField Ω]
    [NormedAlgebra ℚ_[ℓ] Ω] [IsAlgClosure ℚ_[ℓ] Ω]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (S T : Scheme.{u}) [S.Over (Spec (.of k))] [T.Over (Spec (.of k))]
    [IsSeparated (S ↘ Spec (.of k))] [LocallyOfFiniteType (S ↘ Spec (.of k))]
    [QuasiCompact (S ↘ Spec (.of k))]
    [IsSeparated (T ↘ Spec (.of k))] [LocallyOfFiniteType (T ↘ Spec (.of k))]
    [QuasiCompact (T ↘ Spec (.of k))]
    (a : S ⟶ T) [a.IsOver (Spec (.of k))] [IsImmersion a]
    (ha : Topology.IsConstructible (Set.range a))
    (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj Ω) S))
    (hL : IsLisseCoefficientModule (Profinite.continuousCoefficientRingObj Ω) L) :
    ContinuousAlgClFiniteStageDevissage ℓ Ω a L := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
