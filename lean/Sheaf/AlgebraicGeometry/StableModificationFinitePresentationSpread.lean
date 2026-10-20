/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q52
-/
module

public import Sheaf.TraceFormula.MultipointedCurve
public import Sheaf.AlgebraicGeometry.RiemannZariskiFiniteRefinement
import WeilConjectures.AlgebraicGeometry.DescendClosedImmersion
import WeilConjectures.AlgebraicGeometry.DescendFlatFinitePresentation
import WeilConjectures.AlgebraicGeometry.EventuallyProper
import WeilConjectures.AlgebraicGeometry.ProperLimitNoetherian
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Sheaf.TraceFormula.PureRelativeDimensionFiniteStage

/-! # Finite-presentation spreading of a prescribed marked modification

Source: Temkin, *Stable modification of relative curves*, §3.1, Remark 3.1.1(ii),
and the second paragraph of the proof of Theorem 1.5, pp. 34--36
(blueprint: lem-trf-stable-modification-finite-presentation-spread).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A proper compatible pair over a centred valuation ring, generically an isomorphism,
spreads to an integral separated finite-type quasi-model, with the prescribed base change.
No semistability or stability is imposed on the descended multipointed curve.
Source: Temkin, §3.1, Remark 3.1.1(ii), and proof of Theorem 1.5, second paragraph
(blueprint: lem-trf-stable-modification-finite-presentation-spread).

Proof:
1. Apply `lem-weil-pbc-proper-limit-noetherian` to the identity of `Spec V` and its
   affine clause to express it as a directed affine limit of finite-type integer schemes.
   Use the morphism clause of `thm-pd-spreading-out` on the section into the product
   with `T` to descend the centre. Descend the two source schemes, the target base
   changes, both maps, the marking and the finite compatibility equations at one stage.
2. Use `lem-weil-pbc-descend-closed-immersion` for the marking and
   `lem-weil-pbc-descend-flat-finite-presentation` for both structural maps. Apply
   `lem-trf-pure-relative-dimension-finite-stage` in dimensions one and zero.
   Flat base change and `lem-weil-pbc-proper-fp-permanence` preserve these properties
   at later stages; the final reduced closed generic closure has the same fibres.
3. Apply `lem-weil-pbc-eventually-proper` to both descended maps and pass to a common
   stage. If the affine stage ring is `Aᵢ`, put `Bᵢ = image(Aᵢ → V)` and
   `Kᵢ = Frac(Bᵢ)`. Their directed unions are `V` and `L`, respectively. Apply the
   morphism and equality clauses of `thm-pd-spreading-out` to the field system `Kᵢ`
   to descend the two generic inverses and their inverse identities. At the final
   stage take the reduced closure of the image of `Spec L`. Integrality of `Spec V`
   makes the centre factor through it. It is affine, integral, finite type and
   separated over `T`, by `lem-weil-pbc-proper-fp-permanence`,
   `lem-weil-pbc-qcqs-morphism-permanence` and
   `lem-weil-pbc-affine-source-morphism-separated`, hence is the required quasi-model
   in `lem-trf-riemann-zariski-finite-refinement`.
4. The limit identifications give the two displayed isomorphisms over `Spec V`.
   Fibre-product associativity and the descended equations identify the markings
   and recover both original maps. Nothing in the construction requires stability.
-/
theorem exists_stable_modification_finite_presentation_spread
    (T : Scheme.{u}) [IsIntegral T]
    (t : T ⟶ Spec (.of (ULift.{u} ℤ))) [LocallyOfFiniteType t] [QuasiCompact t]
    (L : Type u) [Field L] [Algebra T.functionField L] [IsSepClosure T.functionField L]
    (v : RiemannZariski.ValuationPoint T L
      (Spec.map (CommRingCat.ofHom (algebraMap T.functionField L)) ≫
        T.fromSpecStalk (genericPoint T)))
    (P : MultipointedCurve T) (Y : MultipointedCurve (Spec (.of v.V)))
    (fX : Y.X ⟶ pullback P.x v.centre) (fD : Y.D ⟶ pullback P.d v.centre)
    [IsProper fX] [IsProper fD]
    (hX : fX ≫ pullback.snd P.x v.centre = Y.x)
    (hD : fD ≫ pullback.snd P.d v.centre = Y.d)
    (hmark : fD ≫ pullback.fst P.d v.centre ≫ P.i =
      Y.i ≫ fX ≫ pullback.fst P.x v.centre)
    (hXη : IsIso (pullback.map Y.x (Spec.map (CommRingCat.ofHom v.V.subtype))
      (pullback.snd P.x v.centre) (Spec.map (CommRingCat.ofHom v.V.subtype))
      fX (𝟙 _) (𝟙 _)
      ((Category.comp_id _).trans hX.symm)
      ((Category.comp_id _).trans (Category.id_comp _).symm)))
    (hDη : IsIso (pullback.map Y.d (Spec.map (CommRingCat.ofHom v.V.subtype))
      (pullback.snd P.d v.centre) (Spec.map (CommRingCat.ofHom v.V.subtype))
      fD (𝟙 _) (𝟙 _)
      ((Category.comp_id _).trans hD.symm)
      ((Category.comp_id _).trans (Category.id_comp _).symm))) :
    ∃ (U : RiemannZariski.QuasiModel T L
        (Spec.map (CommRingCat.ofHom (algebraMap T.functionField L)) ≫
          T.fromSpecStalk (genericPoint T)))
      (l : Spec (.of v.V) ⟶ U.X),
      l ≫ U.map = v.centre ∧
      Spec.map (CommRingCat.ofHom v.V.subtype) ≫ l = U.generic ∧
      ∃ (Y₀ : MultipointedCurve U.X)
        (gX : Y₀.X ⟶ pullback P.x U.map) (gD : Y₀.D ⟶ pullback P.d U.map),
        IsProper gX ∧ IsProper gD ∧
        ∃ (hgX : gX ≫ pullback.snd P.x U.map = Y₀.x)
          (hgD : gD ≫ pullback.snd P.d U.map = Y₀.d),
          gD ≫ pullback.fst P.d U.map ≫ P.i =
            Y₀.i ≫ gX ≫ pullback.fst P.x U.map ∧
          IsIso (pullback.map Y₀.x (U.X.fromSpecResidueField (genericPoint U.X))
            (pullback.snd P.x U.map) (U.X.fromSpecResidueField (genericPoint U.X))
            gX (𝟙 _) (𝟙 _)
            ((Category.comp_id _).trans hgX.symm)
            ((Category.comp_id _).trans (Category.id_comp _).symm)) ∧
          IsIso (pullback.map Y₀.d (U.X.fromSpecResidueField (genericPoint U.X))
            (pullback.snd P.d U.map) (U.X.fromSpecResidueField (genericPoint U.X))
            gD (𝟙 _) (𝟙 _)
            ((Category.comp_id _).trans hgD.symm)
            ((Category.comp_id _).trans (Category.id_comp _).symm)) ∧
          ∃ (eX : pullback Y₀.x l ≅ Y.X) (eD : pullback Y₀.d l ≅ Y.D),
            eX.hom ≫ Y.x = pullback.snd Y₀.x l ∧
            eD.hom ≫ Y.d = pullback.snd Y₀.d l ∧
            eD.hom ≫ Y.i ≫ eX.inv ≫ pullback.fst Y₀.x l =
              pullback.fst Y₀.d l ≫ Y₀.i ∧
            eX.hom ≫ fX ≫ pullback.fst P.x v.centre =
              pullback.fst Y₀.x l ≫ gX ≫ pullback.fst P.x U.map ∧
            eD.hom ≫ fD ≫ pullback.fst P.d v.centre =
              pullback.fst Y₀.d l ≫ gD ≫ pullback.fst P.d U.map := by
  sorry

end AlgebraicGeometry
