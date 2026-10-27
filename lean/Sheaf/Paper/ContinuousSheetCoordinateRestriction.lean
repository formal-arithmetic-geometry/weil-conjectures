/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.ContinuousLatticeSumFree
public import Sheaf.Paper.FiniteEtaleLatticeSheetMaps

/-! # Restricting the forward coordinate equation to an open subscheme

Source: blueprint, stratified lattice trace proof, Local computation, paragraphs 1--2.
(blueprint: lem-sfb-continuous-sheet-coordinate-restriction)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor Matrix

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- A global coordinate equation for normalized sheet maps persists on every open.
The matrices are arbitrary; freeness and invertibility are not assumed.
Source: blueprint, stratified lattice trace proof, Local computation, paragraphs 1--2;
Bhatt--Scholze, Section 6.8, restriction of continuous coefficients.
(blueprint: lem-sfb-continuous-sheet-coordinate-restriction)

Proof. Restrict the two given continuous-function presentations along W → Y.
The continuous module encoding identifies inverse image along this open immersion
with restriction of its module presheaf, so the restricted coordinate maps are
the same maps on each pro-etale test object B over W, now regarded as an object
over Y. For the rational presentation first use comapUpperStarIso to commute
restriction of scalars with inverse image; then upperStarComp identifies the
rational target with the pullback along W.ι ≫ g. Similarly upperStarComp for
integral coefficients identifies each source with pullback along W.ι ≫ t j.
These transports preserve linearity and the coordinate restriction identities.
The equation (W.ι ≫ t j) ≫ p = W.ι ≫ g follows by associativity and w j.
Naturality of comapUpperStarIso and associativity of upperStarComp identify
the transported global sheet map with finiteEtaleLatticeSheetEmbedding for
these composite arrows. Apply the assumed global equation to B regarded over Y.
Its point is W.ι (B.hom z), giving the displayed formula. On an empty W there
are no points z; the same restriction construction still gives the presentations.
No matrix-continuity, invertibility, rank or scalar-extension claim is needed. -/
theorem continuousSheet_coordinate_restriction
    (l : ℕ) [Fact l.Prime] (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [TotallyDisconnectedSpace E] {X U Y : Scheme.{u}}
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))
    (p : U ⟶ X)
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj (integralCoeff l E) U))
    (e : (Mod.extendScalars (coefficientMap (integralScalarMap l E) U)).obj M ≅
      (upperStar (Profinite.continuousMapRingObj E) p).obj P)
    (g : Y ⟶ X) (d : ℕ) (t : Fin d → (Y ⟶ U)) (w : ∀ j, t j ≫ p = g)
    (r : ℕ)
    (c : ContinuousFunctionPresentation Y (continuousIntegers l E)
        (Fin r → E) ((Mod.comap (coefficientMap (integralScalarMap l E) Y)).obj
          ((upperStar (Profinite.continuousMapRingObj E) g).obj P)))
    (b : ∀ j, ContinuousFunctionPresentation Y (continuousIntegers l E)
        (Fin r → continuousIntegers l E) ((upperStar (integralCoeff l E) (t j)).obj M))
    (G : Fin d → Y → Matrix (Fin r) (Fin r) E)
    (h : ∀ (j : Fin d) (B : Y.ProEt)
      (x : ((continuousRingModuleEquivalence Y (continuousIntegers l E)).functor.obj
          ((upperStar (integralCoeff l E) (t j)).obj M)).val.obj (op B)) (z : B.left),
      c.sections B
        (((continuousRingModuleEquivalence Y (continuousIntegers l E)).functor.map
            (finiteEtaleLatticeSheetEmbedding (integralScalarMap l E) P p M e
              g (t j) (w j))).val.app (op B) x) z =
        G j (B.hom z) *ᵥ (fun i ↦ ((b j).sections B x z i : E))) :
      ∀ W : Y.Opens, ∃ w' : ∀ j, (W.ι ≫ t j) ≫ p = W.ι ≫ g,
        ∃ c : ContinuousFunctionPresentation W.toScheme (continuousIntegers l E)
            (Fin r → E) ((Mod.comap
              (coefficientMap (integralScalarMap l E) W.toScheme)).obj
              ((upperStar (Profinite.continuousMapRingObj E) (W.ι ≫ g)).obj P)),
        ∃ b : ∀ j, ContinuousFunctionPresentation W.toScheme (continuousIntegers l E)
            (Fin r → continuousIntegers l E)
            ((upperStar (integralCoeff l E) (W.ι ≫ t j)).obj M),
        ∀ (j : Fin d) (B : W.toScheme.ProEt)
          (x : ((continuousRingModuleEquivalence W.toScheme
            (continuousIntegers l E)).functor.obj
            ((upperStar (integralCoeff l E) (W.ι ≫ t j)).obj M)).val.obj (op B))
          (z : B.left),
          c.sections B
            (((continuousRingModuleEquivalence W.toScheme
              (continuousIntegers l E)).functor.map
              (finiteEtaleLatticeSheetEmbedding (integralScalarMap l E) P p M e
                (W.ι ≫ g) (W.ι ≫ t j) (w' j))).val.app (op B) x) z =
            G j (W.ι (B.hom z)) *ᵥ
              (fun i ↦ ((b j).sections B x z i : E)) := by sorry

end AlgebraicGeometry.ProEtale.CondensedRing
