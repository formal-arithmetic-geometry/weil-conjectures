/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q100
-/
module

public import Sheaf.AlgebraicGeometry.NodalLogCanonicalReconstruction
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import WeilConjectures.AlgebraicGeometry.Modules.HomTensor.Basic
public import WeilConjectures.AlgebraicGeometry.Modules.HomObjSections
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.AlgebraicGeometry.EffectiveCartier
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible

import Sheaf.TraceFormula.GenericFibrePointsSmooth
import Sheaf.AlgebraicGeometry.SmoothTraitCurveLocalProperties
import Sheaf.AlgebraicGeometry.FibreStalkQuotient
import WeilConjectures.Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Sheaf.AlgebraicGeometry.TraitNodalEtaleDvrModel
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Sheaf.AlgebraicGeometry.LCICurveFundamentalClass
import Sheaf.AlgebraicGeometry.EtaleSourceAdjunctionLine
import WeilConjectures.AlgebraicGeometry.Modules.Differentials
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties

/-!
# Integrality of logarithmic dualizing pullback at nodal images

Source: Stacks Project, curves.tex, Tag 0CBY; duality.tex, fundamental-class-lci
and shriek-etale; the nine-step branch-integrality and pole-descent argument of
(blueprint: lem-sfb-log-pullback-nodal-image-integrality).

The Hom line maps canonically into Hom with the generic-localized target. On a
stalk this is exactly M_eta -> M_eta[1/pi]: the source line is finite locally free,
and the generic inclusion is the principal open obtained by inverting pi.
The generic section is represented by its adjoint Hom section, without any frame.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

/-- The canonical map from F^dual tensor G to Hom(F, q_* q^*G), using evaluation
and the section-normalized adjunction unit. For generic restriction its stalk is
localization of the Hom line. Source: Stacks, Sheaves, Tag 0096; curves.tex, Tag 0CBY
(blueprint: lem-sfb-log-pullback-nodal-image-integrality). -/
def nodalLogGenericHomMap {Y Z : Scheme.{u}} (q : Z ⟶ Y) (F G : Y.Modules) :
    Fᵛ ⊗ₘ G ⟶ Scheme.Modules.homObj F
      ((Scheme.Modules.pushforward q).obj ((Scheme.Modules.tensorPullback q).obj G)) :=
  Scheme.Modules.dualTensorHom F G ≫
    SheafOfModules.homObjMap (R := Y.sheaf) (𝟙 F)
      ((Scheme.Modules.tensorPullbackSectionAdjunction q).unit.app G)

/-- A generic line comparison as a section of Hom(F, q_* q^*G), via the actual
adjunction unit. Source: Stacks, Sheaves, Tag 0096; curves.tex, Tag 0CBY
(blueprint: lem-sfb-log-pullback-nodal-image-integrality). -/
def nodalLogGenericHomSection {Y Z : Scheme.{u}} (q : Z ⟶ Y) (F G : Y.Modules)
    (c : (Scheme.Modules.tensorPullback q).obj F ≅
      (Scheme.Modules.tensorPullback q).obj G) :
    Γ(Scheme.Modules.homObj F
      ((Scheme.Modules.pushforward q).obj ((Scheme.Modules.tensorPullback q).obj G)), ⊤) :=
  Scheme.Modules.homToΓHomObj F _
    ((Scheme.Modules.tensorPullbackSectionAdjunction q).unit.app F ≫
      (Scheme.Modules.pushforward q).map c.hom)

/-- The canonically normalized generic logarithmic pullback is integral at a
special-fibre component generic point with nonsmooth image. The differential equation
fixes the generic comparison, including its scalar, using the original fundamental
classes and Cartier twists. The displayed stalk image is literally the localization
image of M = (p^*L_X)^dual tensor L_Y under its canonical Hom identification.

Source: Stacks, curves.tex, Tag 0CBY; duality.tex, fundamental-class-lci and
shriek-etale; the agent branch and faithfully flat pole-quotient argument
(blueprint: lem-sfb-log-pullback-nodal-image-integrality).

Proof plan, following the nine steps of the DAG:
1. Finite type over a DVR gives Noetherian models. Generic-fibre-points-smooth
   makes eta relatively smooth. Remove the markings: eta is a component generic
   point and its nonsmooth image cannot meet a smooth marking.
2. The smooth-trait local-properties and fibre-stalk quotient lemmas make the total
   stalk A a local domain with maximal ideal pi A. The principal-ideal DVR criterion
   makes A a DVR, and the differential-stalk formula identifies the target line with
   the free rank-one module of relative differentials.
3. The trait nodal etale DVR model gives uv=h with h=0 or a uniformizer power.
   Pull back its etale chart along p, and choose a point above eta and the chart point.
4. Etale base change and smooth relative-dimension permanence make the chart stalk
   B a local domain. Its closed fibre is reduced and zero-dimensional, hence a field.
   Thus B is a DVR with uniformizer pi and is faithfully flat over A.
5. Regular affine presentations and the lci fundamental class give an integral
   adjunction frame lambda with alpha(du)=u lambda and alpha(dv)=-v lambda.
   Etale-source and base-change comparisons retain the original normalization.
6. At least one pullback coordinate is nonzero in B[1/pi]. Otherwise the nodal
   relation gives differential dimension two, contradicting smooth relative dimension
   one via the generic isomorphism and formally etale differential base change.
7. Write the nonzero coordinate as pi^m w. Differentiation kills pi, so da/a=dw/w
   is integral; use -db/b if a=0. This includes the persistent equation uv=0.
8. Differential stalks and etale adjunction comparisons identify this integral map
   with the scalar extension of the original generic section of the Hom line.
9. Trivialize M_eta and write its element c/pi^N. Its image lies in B, hence c is
   in pi^N B. Faithful-flat injectivity for A/(pi^N) gives c in pi^N A. Therefore
   the original generic germ lies in the displayed image, before chart choices.
-/
theorem nodal_log_pullback_nodal_image_integrality
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (π : R) (hπ : IsLocalRing.maximalIdeal R = Ideal.span {π})
    (j : Spec (.of K) ⟶ Spec (.of R))
    (hj : j = Spec.map (CommRingCat.ofHom (algebraMap R K)))
    (P Q : MultipointedCurve (Spec (.of R))) [IsHProjective P.x] [IsHProjective Q.x]
    (n : ℕ) (a : (∐ fun _ : Fin n ↦ Spec (.of R)) ≅ P.D)
    (b : (∐ fun _ : Fin n ↦ Spec (.of R)) ≅ Q.D)
    (ha : a.hom ≫ P.d = Sigma.desc (fun _ : Fin n ↦ 𝟙 (Spec (.of R))))
    (hb : b.hom ≫ Q.d = Sigma.desc (fun _ : Fin n ↦ 𝟙 (Spec (.of R))))
    (hsmoothP : ∀ z : P.D, P.i z ∈ P.x.smoothLocus)
    (hsmoothQ : ∀ z : Q.D, Q.i z ∈ Q.x.smoothLocus)
    (hnodalP : HasNodalGeometricFibres P.x) (hnodalQ : HasNodalGeometricFibres Q.x)
    (hgeometricP : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (t : Spec (.of Ω) ⟶ Spec (.of R)),
      IsReduced (pullback P.x t) ∧ (pullback P.x t).IsPureDimension 1)
    (hgeometricQ : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (t : Spec (.of Ω) ⟶ Spec (.of R)),
      IsReduced (pullback Q.x t) ∧ (pullback Q.x t).IsPureDimension 1)
    (DP : MarkedNodalDualizingDegreesData P) (DQ : MarkedNodalDualizingDegreesData Q)
    (p : Q.X ⟶ P.X) (hp : p ≫ P.x = Q.x)
    (hmarks : ∀ i : Fin n,
      Sigma.ι (fun _ : Fin n ↦ Spec (.of R)) i ≫ b.hom ≫ Q.i ≫ p =
        Sigma.ι (fun _ : Fin n ↦ Spec (.of R)) i ≫ a.hom ≫ P.i)
    (hiso : IsIso (pullback.map Q.x j P.x j p (𝟙 (Spec (.of K)))
      (𝟙 (Spec (.of R))) ((Category.comp_id _).trans hp.symm)
      ((Category.comp_id _).trans (Category.id_comp _).symm)))
    (c : (Scheme.Modules.tensorPullback (pullback.fst Q.x j)).obj
        ((Scheme.Modules.tensorPullback p).obj (markedNodalLine P DP.omega)) ≅
      (Scheme.Modules.tensorPullback (pullback.fst Q.x j)).obj
        (markedNodalLine Q DQ.omega))
    (hcanonical : ∀ (W : P.X.Opens) (s : Γ(P.X, W)),
      c.hom.app (pullback.fst Q.x j ⁻¹ᵁ (p ⁻¹ᵁ W))
        (Scheme.Modules.tensorPullbackSection (pullback.fst Q.x j)
          ((Scheme.Modules.tensorPullback p).obj (markedNodalLine P DP.omega)) (p ⁻¹ᵁ W)
          (((Scheme.Modules.tensorPullback p).map
            (nodalLogFundamental P DP.omega DP.dualizing)).app (p ⁻¹ᵁ W)
            (P.x.relativeDifferentialsPullbackGenerator p W s))) =
      Scheme.Modules.tensorPullbackSection (pullback.fst Q.x j)
        (markedNodalLine Q DQ.omega) (p ⁻¹ᵁ W)
        ((nodalLogFundamental Q DQ.omega DQ.dualizing).app (p ⁻¹ᵁ W)
          (Q.x.relativeDifferentialsDerivation.d (X := op (p ⁻¹ᵁ W)) (p.app W s))))
    (η : Q.X) (ηk : Q.x.fiber (IsLocalRing.closedPoint R))
    (hη : Q.x.fiberι (IsLocalRing.closedPoint R) ηk = η)
    (hηk : closure ({ηk} : Set (Q.x.fiber (IsLocalRing.closedPoint R))) ∈
      irreducibleComponents (Q.x.fiber (IsLocalRing.closedPoint R)))
    (hx : p η ∉ P.x.smoothLocus) :
    (Scheme.Modules.homObj
      ((Scheme.Modules.tensorPullback p).obj (markedNodalLine P DP.omega))
      ((Scheme.Modules.pushforward (pullback.fst Q.x j)).obj
        ((Scheme.Modules.tensorPullback (pullback.fst Q.x j)).obj
          (markedNodalLine Q DQ.omega)))).presheaf.germ ⊤ η True.intro
        (nodalLogGenericHomSection (pullback.fst Q.x j)
          ((Scheme.Modules.tensorPullback p).obj (markedNodalLine P DP.omega))
          (markedNodalLine Q DQ.omega) c) ∈
      Set.range ((TopCat.Presheaf.stalkFunctor AddCommGrpCat η).map
        ((PresheafOfModules.toPresheaf Q.X.ringCatSheaf.obj).map
          (nodalLogGenericHomMap (pullback.fst Q.x j)
            ((Scheme.Modules.tensorPullback p).obj (markedNodalLine P DP.omega))
            (markedNodalLine Q DQ.omega)).val)) := by
  sorry

end AlgebraicGeometry
