/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Sheaf.AlgebraicGeometry.FSLogSmoothEtale
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.RingTheory.ExcellentRing
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.LogRegularSharpChart
import Sheaf.AlgebraicGeometry.MonoidalResolutionTower
import Sheaf.AlgebraicGeometry.LogBlowupNormalization
import Sheaf.TraceFormula.LogRegularDivisorialStructure
import Sheaf.AlgebraicGeometry.FreeCharacteristicRegularBoundary
import Sheaf.AlgebraicGeometry.CoherentLogIdealChartConstruction
import Sheaf.AlgebraicGeometry.Morphisms.HProjectiveComposition

/-!
# Projective log resolution of log regular schemes

Source: ILO, Exposé VIII 3.4.6(i), 3.4.8--3.4.9, pp.111--112; VI 1.7--1.8,
p.70; XVI 3.7, pp.254--255 (blueprint: lem-per-log-regular-projective-log-resolution).

The cumulative maps `p` specify the actual tower composite using the published `CompEq`
relation. Their initial map is the identity on schemes and on log sections. `HEq` transports
only the endpoint from `T.level 0` to the equal log scheme `V`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- An integral log regular fs scheme of finite type, quasi-projective over an excellent
Noetherian affine base, admits a projective birational saturated log blowup tower with
integral regular source. The tower is log étale and preserves every log-smooth map out of V.
Source: ILO VIII 3.4.6(i), 3.4.8--3.4.9; VI 1.7--1.8; XVI 3.7
(blueprint: lem-per-log-regular-projective-log-resolution).

Proof:
1. Finite type over the Noetherian affine base makes V Noetherian by
   lem-weil-pbc-finite-type-over-noetherian. Sharp saturated characteristic charts from
   lem-trf-log-regular-sharp-chart have torsion-free group completions: if n h = 0,
   saturation puts h and -h in the monoid, and sharpness then forces h = 0.
   Apply lem-trf-monoidal-resolution-tower to obtain a finite saturated blowup tower
   with free final characteristic monoids.
2. The triviality locus U is open dense by lem-trf-log-regular-divisorial-structure.
   Induct along the tower: each level is integral, quasi-projective of finite type over
   Spec A, log regular, and isomorphic to U over its triviality locus. The induction step
   uses lem-trf-log-blowup-normalization to identify the next level with the normalized
   ordinary blowup of a nonzero finite-type quasi-coherent ideal. Apply
   lem-per-excellent-quasiprojective-normalized-blowup to retain the induction hypotheses
   and obtain H-projectivity of that step.
3. The final free characteristics give regularity by
   lem-trf-free-characteristic-regular-boundary. The identified dense triviality loci give
   birationality. Compose projective steps using lem-trf-h-projective-composition; for
   length zero use the identity embedding into P^0. Take p to be the successive composites.
4. The saturated charts of lem-trf-coherent-log-ideal-chart-construction have the same
   group completion as the original chart. Their group kernel and cokernel vanish, their
   orders are 1, and their scheme comparison is the identity. Thus every step is log étale
   in the sense of def-per-fs-log-smooth-etale.
5. The finite-tower clause of lem-per-log-smooth-composition-strict-base-change makes b
   log étale, including length zero. Its mixed-composition clause makes g after b log
   smooth for every log-smooth g to every locally Noetherian fs D. This uses the same tower
   independently of D and g. CompEq specifies that composite including its log map. -/
theorem exists_logRegular_projective_log_resolution
    (A : Type u) [CommRing A] [IsNoetherianRing A] (hA : IsExcellent A)
    (V : FineSaturatedLogScheme.{u}) [IsIntegral V.scheme]
    (hV : V.IsLogRegular) (s : V.scheme ⟶ Spec (.of A))
    [LocallyOfFiniteType s] [QuasiCompact s]
    (hquasi : ∃ (n : ℕ) (i : V.scheme ⟶ ℙ(ULift.{u} (Fin (n + 1)); Spec (.of A))),
      IsImmersion i ∧ i ≫ ℙ(ULift.{u} (Fin (n + 1)); Spec (.of A)) ↘ Spec (.of A) = s) :
    ∃ T : SaturatedLogBlowupTower.{u}, T.level 0 = V ∧
      ∃ p : ∀ i : Fin (T.length + 1), EtaleLogHom (T.level i) (T.level 0),
        ∃ hId : (p 0).base = 𝟙 (T.level 0).scheme,
        (∀ (W U : (T.level 0).scheme.Etale) (k : U.left ⟶ W.left)
          (hk : k ≫ W.hom = U.hom ≫ (p 0).base),
          (p 0).sectionMap W U k hk =
            ((T.level 0).logStructure.monoidSheaf.obj.map
              (MorphismProperty.Over.homMk k (by
                exact hk.trans ((congrArg (fun f ↦ U.hom ≫ f) hId).trans
                  (Category.comp_id U.hom)))).op).hom) ∧
        (∀ i : Fin T.length, (T.arrow i).CompEq (p i.castSucc) (p i.succ)) ∧
        ∃ b : EtaleLogHom (T.level ⟨T.length, Nat.lt_succ_self T.length⟩) V,
          HEq (p ⟨T.length, Nat.lt_succ_self T.length⟩) b ∧
          IsHProjective b.base ∧
          IsIntegral (T.level ⟨T.length, Nat.lt_succ_self T.length⟩).scheme ∧
          IsRegularScheme (T.level ⟨T.length, Nat.lt_succ_self T.length⟩).scheme ∧
          (∃ (U : V.scheme.Opens)
            (W : (T.level ⟨T.length, Nat.lt_succ_self T.length⟩).scheme.Opens)
            (e : W.toScheme ≅ U.toScheme),
            Dense (U : Set V.scheme) ∧
            Dense (W : Set (T.level ⟨T.length, Nat.lt_succ_self T.length⟩).scheme) ∧
            e.hom ≫ U.ι = W.ι ≫ b.base) ∧
          b.IsLogEtale ∧
          ∀ (D : FineSaturatedLogScheme.{u}) (g : EtaleLogHom V D), g.IsLogSmooth →
            ∃ c : EtaleLogHom (T.level ⟨T.length, Nat.lt_succ_self T.length⟩) D,
              b.CompEq g c ∧ c.IsLogSmooth := by
  sorry

end AlgebraicGeometry
