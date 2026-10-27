module

public import Sheaf.AlgebraicGeometry.RelativePseudoCoherentComplex
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.AlgebraicGeometry.AffineGlobalHomBaseChangeMap
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.Noetherian.Defs
import Sheaf.AlgebraicGeometry.MPseudoCoherentComplex
import WeilConjectures.AlgebraicGeometry.AffineDerivedPushforwardTExact
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.NagataFinitePresentationEnvelope
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import WeilConjectures.AlgebraicGeometry.ProperFinitePresentationClosedLimitEnvelope
import WeilConjectures.AlgebraicGeometry.ExistsIsSeparatedOverPullbackMap
import WeilConjectures.AlgebraicGeometry.ProperNoetherianStage
import Sheaf.AlgebraicGeometry.UniformAffinePullbackCohomologyBound
import WeilConjectures.AlgebraicGeometry.UnboundedDerivedFunctorCohomologicalBound
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.AlgebraicGeometry.QCqsDerivedProjectionMate
import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence
import WeilConjectures.AlgebraicGeometry.GlobalSectionsDirectImageKInjectiveAcyclic
import WeilConjectures.AlgebraicGeometry.DerivedAdjoint
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.AlgebraicGeometry.DerivedDirectImagePreservesQCoh
import WeilConjectures.AlgebraicGeometry.AffineDerivedTensorChartComparison

/-! # Finite-degree Noetherian approximation of relative complexes

Source: the agent-formulated descente input for the Kiehl paragraph after Stacks
Tag 0CSD, perfect.tex, lemma-flat-proper-pseudo-coherent-direct-image-general;
More on Morphisms, Tags 09UI and 0CSU
(blueprint: lem-sfb-relative-complex-noetherian-cohomology-approximation).

The primary Kiehl source for the approximation assertion remains wanted, as recorded
in the DAG. The sections comparison is specified by its underived identity and its
right-derived-unit equation; thus the scalar adjoint is the prescribed canonical map.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u w

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace AlgebraicGeometry

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
variable [∀ (R : Type u) [Ring R], HasDerivedCategory.{w} (ModuleCat.{u} R)]

/-- The scalar-extension adjoint of the map on derived sections induced by gamma.
The comparison c is normalized in the approximation theorem by the actual identity
on underived sections and the right-derived-unit equation. Extension of scalars is
computed on K-flat resolutions, including for non-flat coefficient maps.
Source: agent-formulated Kiehl descente input after Stacks Tag 0CSD; Tag 0AA7
for the scalar adjunction
(blueprint: lem-sfb-relative-complex-noetherian-cohomology-approximation). -/
def relativeApproximationScalarAdjoint
    {A A₀ : CommRingCat.{u}} {X X₀ : Scheme.{u}}
    (f : X ⟶ Spec A) (f₀ : X₀ ⟶ Spec A₀) (g : Spec A ⟶ Spec A₀)
    (u₀ : X ⟶ X₀) (E : schemeDerivedCategory X) (E₀ : schemeDerivedCategory X₀)
    (γ : E₀ ⟶ (schemeDerivedDirectImage u₀).obj E)
    (c : schemeDerivedDirectImage u₀ ⋙ affineDerivedGlobalSections f₀ ≅
      affineDerivedGlobalSections f ⋙
        (ModuleCat.restrictScalars.{u} (affineBaseRingMap g)).mapDerivedCategory) :
    (affineDerivedExtension g).obj ((affineDerivedGlobalSections f₀).obj E₀) ⟶
      (affineDerivedGlobalSections f).obj E :=
  ((affineDerivedExtensionAdjunction g).homEquiv _ _).symm
    ((affineDerivedGlobalSections f₀).map γ ≫ c.hom.app E)

/-- Finite-degree Noetherian approximation of a relatively pseudo-coherent complex.
Source: agent-formulated descente input for the Kiehl assertion following Stacks
Tag 0CSD (perfect.tex); Tags 09UI and 0CSU for quasi-coherence and boundedness
(blueprint: lem-sfb-relative-complex-noetherian-cohomology-approximation).

Proof plan, following the seven steps of the DAG:
1. Apply relative (i-1)-pseudo-coherence and
   lem-sfb-relative-m-pseudocoherent-high-qcoh to each cohomology sheaf. Relative
   0-pseudo-coherence gives local upper bounds. Affine pushforward t-exactness
   (lem-sc-affine-derived-pushforward-t-exact) and quasi-compactness give one bound.
2. Embed X as a closed subscheme of the finite-presentation envelope
   (def-nagata-finite-type-closed-in-fp, prop-nagata-finite-type-closed-in-fp);
   use lem-weil-pbc-proper-closed-in-proper-fp-envelope-part in the proper case.
3. Spread the envelope to a Noetherian integer algebra using
   lemma-nagata-noetherian-inverse-system-affine and thm-pd-spreading-out.
   Descend separatedness by lem-weil-pbc-descend-separated and properness by
   lem-weil-pbc-proper-noetherian-stage.
4. Fix the bound N of lem-pc-j2-uniform-affine-pullback-cohomology-bound before
   applying lem-sfb-prescribed-envelope-relative-sheaf-descente with a=n-N+1.
   The resulting model is affine over the fixed envelope, so the same N applies.
5. Apply lem-pc-unbounded-derived-functor-cohomological-bound to the cone.
   Its derived sections vanish in degrees at least n. Triangulatedness and
   lem-sf-derived-homology-long-exact give an isomorphism above n and an epimorphism at n.
6. Use lem-pc-qcqs-derived-projection-mate, lem-pc-affine-qcoh-derived-equivalence,
   lem-pc-derived-direct-image-preserves-qcoh, and
   lem-pc-affine-derived-tensor-chart-comparison to identify the source with derived
   scalar extension. The K-injective comparison of
   lem-pc-global-sections-direct-image-kinjective-acyclic identifies the target with
   sections on X. The projection mate is adjoint to precisely the map induced by gamma;
   uniqueness of adjoints identifies it with relativeApproximationScalarAdjoint.
7. The closed model is separated finite type by
   lem-pod-separated-finite-type-base-change, lem-weil-pbc-closed-immersion-finite,
   and lem-weil-pbc-finite-over-separated-finite-type. Properness follows from
   lem-weil-pbc-proper-base-change and lem-weil-pbc-closed-immersion-proper when f is proper.
   No ordinary base-change identification or flatness is imposed.
-/
theorem exists_relative_complex_noetherian_cohomology_approximation
    {A : CommRingCat.{u}} {X : Scheme.{u}}
    (f : X ⟶ Spec A) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (E : schemeDerivedCategory X) (hE : X.IsPseudoCoherentRelativeTo f E) :
    schemeDerivedQCohProperty X E ∧
    (∃ b : ℤ, ∀ i : ℤ, b < i → IsZero
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj E)) ∧
    ∀ n : ℤ, ∃ A₀ : CommRingCat.{u}, IsNoetherianRing A₀ ∧
      ∃ (g : Spec A ⟶ Spec A₀) (X₀ : Scheme.{u}) (f₀ : X₀ ⟶ Spec A₀),
        IsSeparated f₀ ∧ LocallyOfFiniteType f₀ ∧ QuasiCompact f₀ ∧
        ∃ (u₀ : X ⟶ X₀) (j : X ⟶ pullback f₀ g),
          IsClosedImmersion j ∧ j ≫ pullback.fst f₀ g = u₀ ∧
          j ≫ pullback.snd f₀ g = f ∧ (IsProper f → IsProper f₀) ∧
          ∃ E₀ : schemeDerivedCategory X₀,
            (∀ i : ℤ, RingedSpace.IsCoherent X₀.toRingedSpace
              ((DerivedCategory.homologyFunctor
                (SheafOfModules.{u} (moduleRings X₀.toRingedSpace)) i).obj E₀)) ∧
            (∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero
              ((DerivedCategory.homologyFunctor
                (SheafOfModules.{u} (moduleRings X₀.toRingedSpace)) i).obj E₀)) ∧
            ∃ γ : E₀ ⟶ (schemeDerivedDirectImage u₀).obj E,
              ∃ c₀ : RingedSpace.moduleDirectImage u₀.toLRSHom.toShHom ⋙
                  affineGlobalSections f₀ ≅
                affineGlobalSections f ⋙
                  ModuleCat.restrictScalars.{u} (affineBaseRingMap g),
              ∃ c : schemeDerivedDirectImage u₀ ⋙ affineDerivedGlobalSections f₀ ≅
                affineDerivedGlobalSections f ⋙
                  (ModuleCat.restrictScalars.{u} (affineBaseRingMap g)).mapDerivedCategory,
                (∀ (M : SheafOfModules.{u} (moduleRings X.toRingedSpace))
                  (x : (affineGlobalSections f₀).obj
                    ((RingedSpace.moduleDirectImage u₀.toLRSHom.toShHom).obj M)),
                  (c₀.hom.app M) x = x) ∧
                (∀ J : HomotopyCategory
                    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ),
                  (Functor.rightDerivedFunctorCompUnit
                      (RingedSpace.moduleDirectImage u₀.toLRSHom.toShHom)
                      (affineGlobalSections f₀)).app J ≫
                    (affineGlobalSectionsDerivedIso f₀).hom.app
                      ((schemeDerivedDirectImage u₀).obj (DerivedCategory.Qh.obj J)) ≫
                    c.hom.app (DerivedCategory.Qh.obj J) =
                  DerivedCategory.Qh.map
                    ((c₀.hom.mapHomotopyCategory (ComplexShape.up ℤ)).app J) ≫
                    (affineGlobalSections f ⋙
                      ModuleCat.restrictScalars.{u} (affineBaseRingMap g)
                        ).rightDerivedFunctorUnit.app J ≫
                    (Functor.rightDerivedFunctorCompMapDerivedCategoryIso
                        (affineGlobalSections f)
                        (ModuleCat.restrictScalars.{u} (affineBaseRingMap g)) ≪≫
                      Functor.isoWhiskerRight (affineGlobalSectionsDerivedIso f)
                        (ModuleCat.restrictScalars.{u}
                          (affineBaseRingMap g)).mapDerivedCategory).hom.app
                            (DerivedCategory.Qh.obj J)) ∧
                (∀ i : ℤ, n < i → IsIso
                  ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
                    (relativeApproximationScalarAdjoint f f₀ g u₀ E E₀ γ c))) ∧
                Epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map
                  (relativeApproximationScalarAdjoint f f₀ g u₀ E E₀ γ c)) := by
  sorry

end AlgebraicGeometry
