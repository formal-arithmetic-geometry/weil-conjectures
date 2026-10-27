/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Sheaf.AlgebraicGeometry.NodalLogCanonicalReconstruction
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.AlgebraicGeometry.EffectiveCartier
public import WeilConjectures.AlgebraicGeometry.InvertibleSectionRing

import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import WeilConjectures.RingTheory.Depth
import WeilConjectures.AlgebraicGeometry.Morphisms.DepthTwoHartogsRestriction
import Sheaf.AlgebraicGeometry.FibreStalkQuotient
import Mathlib.RingTheory.Flat.Basic
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.RingTheory.FlatLocalDepthFormula
import WeilConjectures.RingTheory.NonzerodivisorIfMaximalNotAssociated

/-!
# Log pluricanonical lattices of semistable marked models

Source: the agent common-model comparison motivated by Stacks, Moduli of Curves,
Tag 0E97, and de Jong (1997), section 3.8. Tag 0E97 itself treats smooth unmarked
curves; the marked and persistently nodal extension is the prerequisite stated here
(blueprint: lem-sfb-semistable-log-pluricanonical-lattices).

The comparison is normalized by the existing log fundamental classes, so cannot be
rescaled. Homogeneous operations below are the operations of the existing section ring.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

/-- Restriction of a tensor-power section is the actual tensor-unit pullback followed
by the canonical comparison of tensor powers, including the structure module in degree zero.
Source: Stacks, Properties, Tag 01PZ, and Sheaves, Tag 0096
(blueprint: lem-sfb-semistable-log-pluricanonical-lattices). -/
def nodalLogPowerRestriction {X Y : Scheme.{u}} (g : X ⟶ Y) (L : Y.Modules)
    (m : ℕ) : Scheme.Modules.SectionRingComponent L m →
      Scheme.Modules.SectionRingComponent ((Scheme.Modules.tensorPullback g).obj L) m :=
  nodalLogPullbackSection g L ((Scheme.Modules.tensorPullback g).obj L) (Iso.refl _) m ⊤

/-- The explicit homogeneous algebra laws. Scalar multiplication uses the actual
structure map on global functions, so these are laws of R-algebras, including degree zero.
Source: Stacks, Properties, Tag 01PZ and Constructions, Tag 01N8
(blueprint: lem-sfb-semistable-log-pluricanonical-lattices). -/
def NodalLogSectionAlgebraLaws (R : Type u) [CommRing R]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (.of R)) (g : Y ⟶ Spec (.of R))
    (L : X.Modules) (M : Y.Modules)
    (F : ∀ m : ℕ, Scheme.Modules.SectionRingComponent L m →
      Scheme.Modules.SectionRingComponent M m) : Prop :=
  (∀ (m : ℕ) (a b : Scheme.Modules.SectionRingComponent L m),
    F m (a + b) = F m a + F m b) ∧
  (∀ (m : ℕ) (r : R) (a : Scheme.Modules.SectionRingComponent L m),
    F m ((f.appTop ((Scheme.ΓSpecIso (.of R)).inv r)) • a) =
      (g.appTop ((Scheme.ΓSpecIso (.of R)).inv r)) • F m a) ∧
  (∀ (i j : ℕ) (a : Scheme.Modules.SectionRingComponent L i)
      (b : Scheme.Modules.SectionRingComponent L j),
    F (i + j) (GradedMonoid.GMul.mul a b) =
      GradedMonoid.GMul.mul (F i a) (F j b)) ∧
  F 0 (GradedMonoid.GOne.one : Scheme.Modules.SectionRingComponent L 0) =
    (GradedMonoid.GOne.one : Scheme.Modules.SectionRingComponent M 0)

/-- Normalization of the generic line comparison by differential pullback. Both
fundamental classes factor through relative differentials on the common generic curve;
the two factors agree on every `da`. This states equality under the canonical differential
identification without a transport hidden in the type. Since the generic base map is a
localization, these factors exist. On the smooth unmarked dense locus they are the usual
differential isomorphism; reducedness then determines the comparison on the whole curve,
including persistent nodes. Thus an arbitrary scalar multiple cannot satisfy this condition.
Source: the canonical adjunction normalization in the node and de Jong (1997), section 3.8
(blueprint: lem-sfb-semistable-log-pluricanonical-lattices). -/
def IsNodalLogGenericComparison {S T : Scheme.{u}}
    (P Q : MultipointedCurve S)
    (D : MarkedNodalDualizingDegreesData P) (E : MarkedNodalDualizingDegreesData Q)
    (η : T ⟶ S) (v : pullback P.x η ≅ pullback Q.x η)
    (c : (Scheme.Modules.tensorPullback v.hom).obj
        ((Scheme.Modules.tensorPullback (pullback.fst Q.x η)).obj
          (markedNodalLine Q E.omega)) ≅
      (Scheme.Modules.tensorPullback (pullback.fst P.x η)).obj
        (markedNodalLine P D.omega)) : Prop :=
  ∃ (a : (pullback.fst P.x η ≫ P.x).relativeDifferentials ⟶
        (Scheme.Modules.tensorPullback (pullback.fst P.x η)).obj
          (markedNodalLine P D.omega))
    (b : ((v.hom ≫ pullback.fst Q.x η) ≫ Q.x).relativeDifferentials ⟶
        (Scheme.Modules.tensorPullback (pullback.fst P.x η)).obj
          (markedNodalLine P D.omega)),
    (Scheme.Modules.tensorPullback (pullback.fst P.x η)).map
        (nodalLogFundamental P D.omega D.dualizing) =
      P.x.relativeDifferentialsPullbackMap (pullback.fst P.x η) ≫ a ∧
    (Scheme.Modules.tensorPullback (v.hom ≫ pullback.fst Q.x η)).map
        (nodalLogFundamental Q E.omega E.dualizing) ≫
        (Scheme.Modules.tensorPullbackSectionComp v.hom (pullback.fst Q.x η)).hom.app
          (markedNodalLine Q E.omega) ≫ c.hom =
      Q.x.relativeDifferentialsPullbackMap (v.hom ≫ pullback.fst Q.x η) ≫ b ∧
    ∀ (U : (pullback P.x η).Opens) (s : Γ(pullback P.x η, U)),
      a.app U ((pullback.fst P.x η ≫ P.x).relativeDifferentialsDerivation.d
        (X := op U) s) =
      b.app U (((v.hom ≫ pullback.fst Q.x η) ≫ Q.x).relativeDifferentialsDerivation.d
        (X := op U) s)

/-- Generic pointed isomorphisms identify all integral log pluricanonical lattices of
semistable models. The parameter η is fixed by its displayed equation to the fraction-field
map. A finite splitting of each marking is exactly a list of disjoint sections; the generic
marking isomorphism is equivalently a permutation of that list. D and E are arbitrary
representatives of the canonical normalized dualizing data supplied by reconstruction,
without its positivity assumption. The conclusion supplies the normalized line comparison,
injective restrictions, equality of their images in every degree, and the homogeneous
R-algebra laws for both restrictions and for generic pullback.

Source: the agent logarithmic section-lattice formulation motivated by Stacks, Moduli of
Curves, Tag 0E97, and de Jong (1997), section 3.8; the source tag itself is smooth and unmarked
(blueprint: lem-sfb-semistable-log-pluricanonical-lattices).

Proof plan, following all seven steps of the DAG node:
1. A DVR is Noetherian, and finite type makes the models Noetherian. Flatness and local
   freeness make each tensor power uniformizer-torsion-free. A section restricting to zero
   is locally killed by a power of the uniformizer, hence is zero. This proves injectivity.
2. At a closed special-fibre point, the fibre-stalk quotient is reduced of dimension one.
   Its maximal ideal is not associated: a hypothetical annihilator gives either a field
   or a nonzero square-zero element. The nonzerodivisor lemma gives depth at least one;
   the flat local depth formula gives depth at least two on the total model and the line.
3. Relabel markings and apply lem-sfb-common-nodal-model to obtain a common marked model
   Y with projections, isomorphic away from finite closed special-fibre sets, inducing v.
4. Lem-sfb-nodal-log-dualizing-pullback gives the normalized logarithmic line maps from
   each pulled-back model line to the Y line. Tensor powers pull integral sections forward,
   with the identity in degree zero. This gives the forward lattice inclusions.
5. Conversely restrict a section on Y to the common open. Depth-two Hartogs restriction
   extends it uniquely over the omitted points of each model. The whole generic fibre
   lies in that open, giving reverse inclusions, also for m=0.
6. The two pullbacks identify their model lattices with Y's lattice. Their generic maps
   compose by v, so cancellation gives the stated equality of images in each degree.
   Fundamental-class normalization fixes precisely the canonical comparison c.
7. Restriction and pullback commute with addition, coefficients, tensor multiplication
   and the degree-zero unit. Thus these equalities identify the graded R-subalgebras,
   without a choice of generator or rescaling in any degree. -/
theorem semistable_log_pluricanonical_lattices
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (η : Spec (.of K) ⟶ Spec (.of R))
    (hη : η = Spec.map (CommRingCat.ofHom (algebraMap R K)))
    (P Q : MultipointedCurve (Spec (.of R))) [IsHProjective P.x] [IsHProjective Q.x]
    (n : ℕ) (p : (∐ fun _ : Fin n ↦ Spec (.of R)) ≅ P.D)
    (q : (∐ fun _ : Fin n ↦ Spec (.of R)) ≅ Q.D)
    (hp : p.hom ≫ P.d = Sigma.desc (fun _ : Fin n ↦ 𝟙 (Spec (.of R))))
    (hq : q.hom ≫ Q.d = Sigma.desc (fun _ : Fin n ↦ 𝟙 (Spec (.of R))))
    (hPsmooth : ∀ z : P.D, P.i z ∈ P.x.smoothLocus)
    (hQsmooth : ∀ z : Q.D, Q.i z ∈ Q.x.smoothLocus)
    (hPnodal : HasNodalGeometricFibres P.x) (hQnodal : HasNodalGeometricFibres Q.x)
    (hPgeom : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ Spec (.of R)),
      IsReduced (pullback P.x t) ∧ (pullback P.x t).IsPureDimension 1)
    (hQgeom : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ Spec (.of R)),
      IsReduced (pullback Q.x t) ∧ (pullback Q.x t).IsPureDimension 1)
    (D : MarkedNodalDualizingDegreesData P) (E : MarkedNodalDualizingDegreesData Q)
    (v : pullback P.x η ≅ pullback Q.x η)
    (hv : v.hom ≫ pullback.snd Q.x η = pullback.snd P.x η)
    (d : pullback P.d η ≅ pullback Q.d η)
    (hd : d.hom ≫ pullback.snd Q.d η = pullback.snd P.d η)
    (hmarks : P.markingBaseChange η ≫ v.hom = d.hom ≫ Q.markingBaseChange η) :
    ∃ c : (Scheme.Modules.tensorPullback v.hom).obj
        ((Scheme.Modules.tensorPullback (pullback.fst Q.x η)).obj
          (markedNodalLine Q E.omega)) ≅
      (Scheme.Modules.tensorPullback (pullback.fst P.x η)).obj (markedNodalLine P D.omega),
      IsNodalLogGenericComparison P Q D E η v c ∧
      (∀ m : ℕ,
        Function.Injective (nodalLogPowerRestriction (pullback.fst P.x η)
          (markedNodalLine P D.omega) m) ∧
        Function.Injective (nodalLogPowerRestriction (pullback.fst Q.x η)
          (markedNodalLine Q E.omega) m) ∧
        (nodalLogPullbackSection v.hom
            ((Scheme.Modules.tensorPullback (pullback.fst Q.x η)).obj
              (markedNodalLine Q E.omega))
            ((Scheme.Modules.tensorPullback (pullback.fst P.x η)).obj
              (markedNodalLine P D.omega)) c m ⊤) ''
          Set.range (nodalLogPowerRestriction (pullback.fst Q.x η)
            (markedNodalLine Q E.omega) m) =
          Set.range (nodalLogPowerRestriction (pullback.fst P.x η)
            (markedNodalLine P D.omega) m)) ∧
      NodalLogSectionAlgebraLaws R P.x (pullback.fst P.x η ≫ P.x)
        (markedNodalLine P D.omega)
        ((Scheme.Modules.tensorPullback (pullback.fst P.x η)).obj
          (markedNodalLine P D.omega))
        (nodalLogPowerRestriction (pullback.fst P.x η) (markedNodalLine P D.omega)) ∧
      NodalLogSectionAlgebraLaws R Q.x (pullback.fst Q.x η ≫ Q.x)
        (markedNodalLine Q E.omega)
        ((Scheme.Modules.tensorPullback (pullback.fst Q.x η)).obj
          (markedNodalLine Q E.omega))
        (nodalLogPowerRestriction (pullback.fst Q.x η) (markedNodalLine Q E.omega)) ∧
      NodalLogSectionAlgebraLaws R (pullback.fst Q.x η ≫ Q.x)
        (pullback.fst P.x η ≫ P.x)
        ((Scheme.Modules.tensorPullback (pullback.fst Q.x η)).obj
          (markedNodalLine Q E.omega))
        ((Scheme.Modules.tensorPullback (pullback.fst P.x η)).obj
          (markedNodalLine P D.omega))
        (fun m ↦ nodalLogPullbackSection v.hom
          ((Scheme.Modules.tensorPullback (pullback.fst Q.x η)).obj
            (markedNodalLine Q E.omega))
          ((Scheme.Modules.tensorPullback (pullback.fst P.x η)).obj
            (markedNodalLine P D.omega)) c m ⊤) := by
  sorry

end AlgebraicGeometry
