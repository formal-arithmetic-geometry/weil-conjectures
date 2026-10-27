/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.ContinuousLatticeSumFree
public import Sheaf.Paper.FiniteEtaleLatticeSheetMaps

/-! # Global scalar-compatible frames with independent ranks

Source: blueprint, stratified lattice trace proof, Local computation, paragraphs 1--2.
(blueprint: lem-sfb-continuous-free-sheet-global-coordinates)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor Matrix

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Include integral continuous vector coordinates in rational continuous coordinates.
Source: the coefficient inclusion in the blueprint local computation.
(blueprint: lem-sfb-continuous-free-sheet-global-coordinates) -/
def continuousIntegralVector {E : Type} [NormedField E] (A : Subring E)
    {Z : Type u} [TopologicalSpace Z] {r : ℕ} (x : C(Z, Fin r → A)) :
    C(Z, Fin r → E) :=
  ⟨fun z i ↦ (x z i : E), continuous_pi fun i ↦
    continuous_subtype_val.comp ((continuous_apply i).comp x.continuous)⟩

/-- Global free frames give natural rational coordinate changes before extracting matrices.
This assertion concerns the base Y itself, with no restriction to open subschemes.
Source: blueprint, stratified lattice trace proof, Local computation, paragraphs 1--2;
Bhatt--Scholze, Section 6.8.
(blueprint: lem-sfb-continuous-free-sheet-global-coordinates)

Proof. Choose a finite free rational frame and integral frames for the finitely
many pulled-back modules. Extend each integral frame to E and compare it with the
rational frame as follows. The component of pullIso on M identifies the extension
of t_j*M with t_j*Ext(M); follow by t_j*e, then by the inverse of upperStarComp
normalized by w j, obtaining an isomorphism q_j from Ext(t_j*M) to g*P.
The continuous coefficient encoding takes these finite biproducts to finite products
of the continuous coefficient sheaf. Keep the rank r of the rational frame and
the independent ranks n j of the integral frames. No rank identification or
pointwise evaluation is needed.
The encoded rational coordinate changes are the E-linear equivalences F on every
test object. Their naturality is that of the encoded frame isomorphisms.
Restriction of the rational frame
along the coefficient inclusion gives c, while the integral frames give b.
In rational coordinates F is the rational frame map, composed with q_j and
with the inverse of the rationalized integral frame map. The regular-module
scalar-extension unit equation sends integral coordinates to the same vector in E.
The one-map mate equation for comapUpperStarIso identifies the adjoint of q_j with
the specified normalized sheet map, after the composition normalization by w j. This proves the
global equation; no matrix or open restriction
assertion is being assumed here. -/
theorem continuousFreeSheet_globalCoordinates
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
    (hP : Mod.IsFree (condensedRingObj (Profinite.continuousMapRingObj E) Y)
      ((upperStar (Profinite.continuousMapRingObj E) g).obj P))
    (hM : ∀ j, Mod.IsFree (condensedRingObj (integralCoeff l E) Y)
      ((upperStar (integralCoeff l E) (t j)).obj M)) :
    ∃ (r : ℕ) (n : Fin d → ℕ) (c : ContinuousFunctionPresentation Y (continuousIntegers l E)
        (Fin r → E) ((Mod.comap (coefficientMap (integralScalarMap l E) Y)).obj
          ((upperStar (Profinite.continuousMapRingObj E) g).obj P)))
      (b : ∀ j, ContinuousFunctionPresentation Y (continuousIntegers l E)
        (Fin (n j) → continuousIntegers l E) ((upperStar (integralCoeff l E) (t j)).obj M))
      (F : ∀ (j : Fin d) (B : Y.ProEt),
        C(B.left, Fin (n j) → E) ≃ₗ[C(B.left, E)] C(B.left, Fin r → E)),
      (∀ (j : Fin d) (B D : Y.ProEt) (a : D ⟶ B) (x : C(B.left, Fin (n j) → E)),
        F j D (x.comp a.left.base.hom) = (F j B x).comp a.left.base.hom) ∧
      ∀ (j : Fin d) (B : Y.ProEt)
        (x : ((continuousRingModuleEquivalence Y (continuousIntegers l E)).functor.obj
          ((upperStar (integralCoeff l E) (t j)).obj M)).val.obj (op B)),
        c.sections B
          (((continuousRingModuleEquivalence Y (continuousIntegers l E)).functor.map
            (finiteEtaleLatticeSheetEmbedding (integralScalarMap l E) P p M e
              g (t j) (w j))).val.app (op B) x) =
          F j B (continuousIntegralVector (continuousIntegers l E) ((b j).sections B x)) := by sorry

end AlgebraicGeometry.ProEtale.CondensedRing
