module

public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.AlgebraicGeometry.NormalCrossingsDivisor
public import Sheaf.AlgebraicGeometry.UnionOfIrreducibleComponents
public import Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary
public import Sheaf.AlgebraicGeometry.PermissibleCenter
public import Sheaf.AlgebraicGeometry.PermissibleCoordinateChart
public import Sheaf.AlgebraicGeometry.MarkedIdealOrder
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.Blowup.Gluing
public import WeilConjectures.Compactification.StrictTransform
public import WeilConjectures.RingTheory.IsRegularSystemOfParameters
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.RingTheory.Flat.Localization
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible
import Sheaf.TraceFormula.EtaleComponentCoordinateIdentification
import Sheaf.RingTheory.RegularLocalUFDBoundaryFactorization
import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import WeilConjectures.Blowup.FiniteDegree.Algebra

/-! # Actual étale charts of a permissible blowup

Source: ILO, Travaux de Gabber, Exposé VIII 4.1.2--4.1.4(i), Remark 4.2.2(i),
and Lemma 4.2.9, printed pp. 117--121
(blueprint: lem-trf-permissible-boundary-etale-charts).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.PermissibleBoundaryEtaleCharts

/-- The inclusion of the reduced irreducible component, followed by the boundary inclusion.
Source: ILO VIII Remark 4.2.2(i)
(blueprint: lem-trf-permissible-boundary-etale-charts). -/
abbrev componentMap {X : Scheme.{u}} (H : X.IdealSheafData)
    (a : irreducibleComponents H.subscheme) :=
  (Scheme.IdealSheafData.vanishingIdeal
    ⟨a.1, isClosed_of_mem_irreducibleComponents a.1 a.2⟩).subschemeι ≫ H.subschemeι

variable {X W : Scheme.{u}} (M : X.IdealSheafData) (e : W ⟶ X)
    (U : W.affineOpens) (V : (pullback M.blowupMap (U.1.ι ≫ e)).Opens)

/-- The actual chart projection to the blowup. Source: ILO VIII Lemma 4.2.9
(blueprint: lem-trf-permissible-boundary-etale-charts). -/
abbrev projection : V.toScheme ⟶ M.blowup :=
  V.ι ≫ pullback.fst M.blowupMap (U.1.ι ≫ e)

/-- The actual chart projection to the étale neighbourhood. Source: ILO VIII Lemma 4.2.9
(blueprint: lem-trf-permissible-boundary-etale-charts). -/
abbrev baseProjection : V.toScheme ⟶ W :=
  V.ι ≫ pullback.snd M.blowupMap (U.1.ι ≫ e) ≫ U.1.ι

/-- The point of the étale neighbourhood under the chosen chart point.
Source: ILO VIII Lemma 4.2.9
(blueprint: lem-trf-permissible-boundary-etale-charts). -/
abbrev basePoint (z : V.toScheme) : W := baseProjection M e U V z

/-- The germ map from sections on the chosen affine neighbourhood to its chart base point.
Source: ILO VIII Lemma 4.2.9
(blueprint: lem-trf-permissible-boundary-etale-charts). -/
abbrev baseGerm (z : V.toScheme) : Γ(W, U.1) →+* W.presheaf.stalk (basePoint M e U V z) :=
  (W.presheaf.germ U.1 (basePoint M e U V z)
    (pullback.snd M.blowupMap (U.1.ι ≫ e) (V.ι z)).property).hom

/-- The actual étale lift has the quotient chart presentation, labelled strict transforms,
reduced total transforms, and regular coordinate intersections, all as closed-subscheme germs.
Source: ILO VIII 4.1.2--4.1.4(i), Remark 4.2.2(i), Lemma 4.2.9, pp. 117--121
(blueprint: lem-trf-permissible-boundary-etale-charts).

Proof:
1. At x=b(y) in M, permissibility supplies an actual étale neighbourhood and parameter
sections. The regular parameter quotient is a domain, so containment M⊆B forces the
centre index set J to meet the boundary indices (regular-sequence and UFD lemmas).
2. The reduced Cartier ideal of H factors in the regular local UFD as a squarefree
subproduct. Finitely many components and finite germ spreading give common affine
representatives. Étale component-coordinate identification labels precisely the original
components through x by this subproduct and removes components missing x.
3. A prime of the nonzero tensor product of the two residue fields gives a point above
both y and w. Flat blowup base change and the standard affine chart cover choose a
pivot j and an actual open chart V. Its projection to Y is étale.
4. Localize the coefficients at w. The chart ring becomes the quotient by
`t_i-t_j*u_i`; localizing at the prime induced by z gives the actual stalk at z.
The permissible-coordinate-chart lemma gives regularity and parameter positions.
5. Strict transforms are scheme-theoretic closures off the centre. The finite-centre
open-closure uniqueness and schematic density under flat pullback compare these
closures after étale base change, coefficient localization, and localization at z.
6. The pivot component disappears; other selected components have equation u_i or t_i.
The strict transform of a finite coordinate union is the union of these closures:
in the localized UFD its product ideal is the intersection of the distinct prime ideals.
7. Étale pullback preserves reductions. Substitution t_i=t_j*u_i shows that the reduced
inverse images of B and H∪M are the exceptional hyperplane together with precisely the
surviving full or selected boundary hyperplanes. Their parameter ideals are radical.
8. All assertions concern the same actual chart point. Finite germ spreading on the
locally Noetherian chart makes the finitely many ideal equalities hold after one common
shrinking. The regular-parameter quotient theorem gives regular intersections and the
stated dimension drops. Empty H and empty surviving strict transforms use empty unions.
-/
theorem permissible_boundary_etale_charts
    (X : Scheme.{u}) [IsNoetherian X] (hX : IsRegularScheme X)
    (B H M : X.IdealSheafData) (hB : B.IsNormalCrossingsDivisor)
    (hH : IsStrictNormalCrossingsBoundary H)
    (hHB : IsUnionOfIrreducibleComponents H B) (hM : IsPermissibleCenter B M)
    (y : M.blowup) (hy : y ∈ (M.comap M.blowupMap).radical.support) :
    ∃ (W : Scheme.{u}) (e : W ⟶ X), Etale e ∧
      ∃ (U : W.affineOpens) (V : (pullback M.blowupMap (U.1.ι ≫ e)).Opens)
        (z : V.toScheme),
        projection M e U V z = y ∧
        e (basePoint M e U V z) = M.blowupMap y ∧
        Etale (projection M e U V) ∧
        ∃ (d r : ℕ) (f : Fin d → Γ(W, U.1))
          (t : Fin d → W.presheaf.stalk (basePoint M e U V z))
          (hN : IsNoetherianRing (W.presheaf.stalk (basePoint M e U V z)))
          (J I : Finset (Fin d)),
          r ≤ d ∧
          @IsLocalRing.IsRegularSystemOfParameters _ _ _ hN (List.ofFn t) ∧
          (∀ i, baseGerm M e U V z (f i) = t i) ∧
          I ⊆ Finset.univ.filter (fun i : Fin d ↦ i.val < r) ∧
          J.Nonempty ∧
          (J ∩ Finset.univ.filter (fun i : Fin d ↦ i.val < r)).Nonempty ∧
          (B.comap e).ideal U =
            Ideal.span {∏ i ∈ Finset.univ.filter (fun i : Fin d ↦ i.val < r), f i} ∧
          (H.comap e).ideal U = Ideal.span {∏ i ∈ I, f i} ∧
          (M.comap e).ideal U = Ideal.span (f '' (J : Set (Fin d))) ∧
          ∃ label : {a : irreducibleComponents H.subscheme //
              M.blowupMap y ∈ Set.range (componentMap H a)} ≃ ↥I,
            (∀ a, ((componentMap H a.1).ker.comap e).ideal U =
              Ideal.span {f (label a)}) ∧
            (∀ a : irreducibleComponents H.subscheme,
              M.blowupMap y ∉ Set.range (componentMap H a) →
                ((componentMap H a).ker.comap e).ideal U = ⊤) ∧
            ∃ (j : Fin d) (_hj : j ∈ J)
              (p : PrimeSpectrum (PermissibleCoordinateChart.Chart t J j))
              (φ : Localization.AtPrime p.asIdeal ≃+* V.toScheme.presheaf.stalk z)
              (hNZ : IsNoetherianRing (V.toScheme.presheaf.stalk z)),
              (∀ a, φ (algebraMap _ _ (algebraMap _
                (PermissibleCoordinateChart.Chart t J j) a)) =
                  (baseProjection M e U V).stalkMap z a) ∧
              IsRegularLocalRing (V.toScheme.presheaf.stalk z) ∧
              (∃ s : List (V.toScheme.presheaf.stalk z),
                @IsLocalRing.IsRegularSystemOfParameters _ _ _ hNZ s ∧
                ∃ positions : {k : Option (Fin d) //
                    k ∈ PermissibleCoordinateChart.labels
                      (Finset.univ.filter (fun i : Fin d ↦ i.val < r)) j ∧
                    φ (algebraMap _ _ (PermissibleCoordinateChart.equation t J j k)) ∈
                      IsLocalRing.maximalIdeal (V.toScheme.presheaf.stalk z)} → Fin s.length,
                  Function.Injective positions ∧ ∀ k, s.get (positions k) =
                    φ (algebraMap _ _ (PermissibleCoordinateChart.equation t J j k))) ∧
              HilbertSamuel.stalkIdeal
                ((M.comap M.blowupMap).radical.comap (projection M e U V)) z =
                (Ideal.span {PermissibleCoordinateChart.equation t J j none}).map
                  (φ.toRingHom.comp (algebraMap _ _)) ∧
              (∀ a, HilbertSamuel.stalkIdeal
                ((strictTransformMap (componentMap H a.1) M.blowupMap
                  M.support.compl).ker.comap (projection M e U V)) z =
                    (Ideal.span {PermissibleCoordinateChart.strictEquation t J j
                      (label a)}).map (φ.toRingHom.comp (algebraMap _ _))) ∧
              (∀ a : irreducibleComponents H.subscheme,
                M.blowupMap y ∉ Set.range (componentMap H a) →
                HilbertSamuel.stalkIdeal
                  ((strictTransformMap (componentMap H a) M.blowupMap
                    M.support.compl).ker.comap (projection M e U V)) z = ⊤) ∧
              HilbertSamuel.stalkIdeal
                ((B.comap M.blowupMap).radical.comap (projection M e U V)) z =
                (PermissibleCoordinateChart.unionIdeal t J j
                  (PermissibleCoordinateChart.labels
                    (Finset.univ.filter (fun i : Fin d ↦ i.val < r)) j)).map
                      (φ.toRingHom.comp (algebraMap _ _)) ∧
              HilbertSamuel.stalkIdeal
                (((H ⊓ M).comap M.blowupMap).radical.comap (projection M e U V)) z =
                (PermissibleCoordinateChart.unionIdeal t J j
                  (PermissibleCoordinateChart.labels I j)).map
                    (φ.toRingHom.comp (algebraMap _ _)) ∧
              (∀ (Z : X.IdealSheafData) (L : Finset (Fin d)),
                (Z = B ∧ L = Finset.univ.filter (fun i : Fin d ↦ i.val < r)) ∨
                  (Z = H ∧ L = I) →
                HilbertSamuel.stalkIdeal
                  ((strictTransformMap Z.subschemeι M.blowupMap M.support.compl).ker.comap
                    (projection M e U V)) z =
                  (PermissibleCoordinateChart.unionIdeal t J j
                    ((L.erase j).image some)).map (φ.toRingHom.comp (algebraMap _ _))) ∧
              (∀ S : Finset (Option (Fin d)),
                S ⊆ PermissibleCoordinateChart.labels
                  (Finset.univ.filter (fun i : Fin d ↦ i.val < r)) j →
                (Subsingleton (V.toScheme.presheaf.stalk z ⧸
                  (PermissibleCoordinateChart.intersection t J j S).map
                    (φ.toRingHom.comp (algebraMap _ _))) ∨
                  IsRegularLocalRing (V.toScheme.presheaf.stalk z ⧸
                    (PermissibleCoordinateChart.intersection t J j S).map
                      (φ.toRingHom.comp (algebraMap _ _)))) ∧
                ((PermissibleCoordinateChart.intersection t J j S).map
                  (φ.toRingHom.comp (algebraMap _ _)) ≠ ⊤ →
                  ringKrullDim (V.toScheme.presheaf.stalk z) =
                    ringKrullDim (V.toScheme.presheaf.stalk z ⧸
                      (PermissibleCoordinateChart.intersection t J j S).map
                        (φ.toRingHom.comp (algebraMap _ _))) + (S.card : WithBot ℕ∞))) := by
  sorry

end AlgebraicGeometry.PermissibleBoundaryEtaleCharts
