/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N8
-/
module

public import Sheaf.AlgebraicGeometry.NodalLogCanonicalReconstruction
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

import Sheaf.TraceFormula.GenericFibrePointsSmooth
import Sheaf.SixFunctors.TraceFormula.NodalFamilyEtaleLocalModel
import Sheaf.AlgebraicGeometry.SmoothSectionAffineCoordinates
import WeilConjectures.RingTheory.SerreCriterionReduced
import WeilConjectures.RingTheory.FlatLocalDepthFormula
import WeilConjectures.AlgebraicGeometry.Morphisms.DepthTwoHartogsRestriction
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.RingTheory.Filtration
import Mathlib.AlgebraicGeometry.Sites.MorphismProperty
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# Regular pullback of logarithmic dualizing lines on nodal models

Source: Stacks Project, models.tex, Tag 0CDC (`example-blowup`), motivation only;
curves.tex, Tag 0CBY, nodal charts; divisors.tex, Tag 0E9I (`lemma-depth-2-hartog`).
The logarithmic discrepancy argument is the agent proof in the DAG; the requested
Knudsen II, sections 1--2 reference remains wanted
(blueprint: lem-sfb-nodal-log-dualizing-pullback).

The lines, marking ideals, fundamental classes and tensor pullback are the existing
ones. The equation on `1 ⊗ da` fixes the canonical comparison on the isomorphism open,
including its normalization at markings and persistent nodes. Generic-fibre restriction
uses the actual base-change projection from the fibre over the specified fraction field.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

/-- The canonical logarithmic-dualizing comparison on the isomorphism open extends
as a morphism of line bundles on the entire source. The equation on pullback differential
sections says that its restriction is the canonical comparison, rather than an unspecified
isomorphism. Since the generic fibre lies in this open, the same equation normalizes its
explicitly asserted generic-fibre isomorphism. `P` is X and `Q` is Y; their splittings of
one finite coproduct encode the ordered, disjoint smooth sections, including the empty list.
The supplied dualizing data are the canonical data furnished without positivity by
`exists_nodal_log_canonical_reconstruction`.

Source: Stacks Project, models.tex, Tag 0CDC (`example-blowup`), motivation only;
curves.tex, Tag 0CBY; divisors.tex, Tag 0E9I (`lemma-depth-2-hartog`); the ten-step
agent logarithmic discrepancy proof in the DAG
(blueprint: lem-sfb-nodal-log-dualizing-pullback).

Proof plan:
1. Finite type over the Noetherian DVR makes both models Noetherian. The Hom line
   M = (p* L_X)^dual tensor L_Y is coherent. Flatness makes a uniformizer pi regular,
   so restriction of its sections to the generic fibre is injective on every open.
2. At a generic point eta of the reduced special fibre, the fibre stalk is a field
   by minimal-prime localization. The maximal ideal of the total stalk A is pi A.
   Krull intersection gives a finite order for every nonzero a, hence a = pi^m w
   with w a unit. Pi-regularity makes A a domain. Thus da/a = dw/w is regular.
   The generic-fibre-points-smooth theorem makes eta relatively smooth and unmarked.
3. At a nonsmooth image of eta, use the nodal-family etale model uv=h and pull its
   covering back along p. The chosen chart stalk A' is faithfully flat over A, with
   field special fibre, by the etale-over-field and flat-local faithful-flatness lemmas.
   The etale-source-adjunction-line lemma and canonical base change identify the
   chart lines with the original normalized dualizing lines.
4. At a smooth unmarked image the map of relative differentials is already integral.
5. At a marked image, centred smooth-section coordinates give one equation t=0.
   The Cartier twist and lci fundamental class give the frame dt/t. Its pullback
   a is nonzero generically; factor a = pi^m w, so its pullback is dw/w, regular.
6. At a node the lci Jacobian determinants are -u and v. A dualizing frame is
   du/u = -dv/v up to a fixed sign. At least one pullback a,b is nonzero, since
   the generic point maps to the smooth locus under the generic isomorphism.
   Factor that nonzero element as pi^m w to obtain a regular logarithmic differential.
   This includes h=0, the horizontally persistent node, without normality.
7. Faithful flatness injects the pole quotient M_eta[1/pi]/M_eta into its tensor
   extension over A'. Thus the chart regularity descends to A.
8. Spread these integral germs to neighbourhoods of all special-fibre generic points.
   Generic-fibre injectivity from Step 1 makes them agree with the prescribed map
   and with one another. Glue on their union with the isomorphism open.
9. A remaining point has a reduced one-dimensional fibre local ring of depth at
   least one by the reduced Serre criterion. The flat local depth formula adds the
   base depth one, giving depth at least two for the total stalk and the Hom line.
10. Depth-two Hartogs extends its section to all of Y. Interpret this section as
    alpha. It has the prescribed restriction, and hence the usual generic pullback.
    No positivity, stability, smooth generic fibre or normal total space was used;
    for n=0 Step 5 is absent.
-/
theorem exists_nodal_log_dualizing_pullback
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
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
    (p : Q.X ⟶ P.X) [IsProper p] (hp : p ≫ P.x = Q.x)
    (hmarks : ∀ j : Fin n,
      Sigma.ι (fun _ : Fin n ↦ Spec (.of R)) j ≫ b.hom ≫ Q.i ≫ p =
        Sigma.ι (fun _ : Fin n ↦ Spec (.of R)) j ≫ a.hom ≫ P.i)
    (Z : Set P.X) (hfinite : Z.Finite)
    (hclosed : ∀ z ∈ Z, IsClosed ({z} : Set P.X))
    (hspecial : ∀ z ∈ Z, P.x z = IsLocalRing.closedPoint R)
    (U : P.X.Opens) (hU : (U : Set P.X) = Zᶜ)
    (hiso : IsIso (pullback.snd p U.ι)) :
    ∃ α : (Scheme.Modules.tensorPullback p).obj (markedNodalLine P DP.omega) ⟶
        markedNodalLine Q DQ.omega,
      IsIso ((Scheme.Modules.tensorPullback (p ⁻¹ᵁ U).ι).map α) ∧
      (∀ (W : P.X.Opens), W ≤ U → ∀ s : Γ(P.X, W),
        (((Scheme.Modules.tensorPullback p).map
            (nodalLogFundamental P DP.omega DP.dualizing)) ≫ α).app (p ⁻¹ᵁ W)
            (P.x.relativeDifferentialsPullbackGenerator p W s) =
          (nodalLogFundamental Q DQ.omega DQ.dualizing).app (p ⁻¹ᵁ W)
            (Q.x.relativeDifferentialsDerivation.d (X := op (p ⁻¹ᵁ W)) (p.app W s))) ∧
      IsIso ((Scheme.Modules.tensorPullback
        (pullback.fst Q.x (Spec.map (CommRingCat.ofHom (algebraMap R K))))).map α) := by
  sorry

end AlgebraicGeometry
