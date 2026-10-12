/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.BaseChangeCurve
public import Sheaf.AlgebraicGeometry.GenusInvariant
public import Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundary
public import WeilConjectures.AlgebraicGeometry.Curve.Compactification
public import WeilConjectures.AlgebraicGeometry.Curve.Picard
public import WeilConjectures.AlgebraicGeometry.Picard.Jacobian
public import Mathlib.GroupTheory.QuotientGroup.Basic
import WeilConjectures.AlgebraicGeometry.Curve.Affine
import WeilConjectures.AlgebraicGeometry.EffectiveCartier
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected

/-! # Compatibility of the affine Picard quotient with field extension

Source: `literature/stacks-project/etale-cohomology.tex`, Tags 03RQ and 01JF
(blueprint: lem-sc-pic-affine-base-change-compatibility).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The affine Picard quotient description is compatible with extension of algebraically closed
fields.  The proof uses base change of the compactification, the boundary restriction theorem,
and the Jacobian base-change compatibility.

Source: Stacks Tags 03RQ and 01JF, and the affine case of
`thm-sc-constant-invariance` (blueprint: lem-sc-pic-affine-base-change-compatibility).
-/
theorem pic_affine_base_change_compatibility
    {k k' : Type u} [Field k] [Field k'] [Algebra k k'] [IsAlgClosed k] [IsAlgClosed k']
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] [IsAffine C]
    (c : Compactification f) [IsConnectedCurve c.g] [Smooth c.g]
    [hsm : SmoothOfRelativeDimension 1 c.g]
    [hsm' : SmoothOfRelativeDimension 1
      (Compactification.baseChange c
        (Spec.map (CommRingCat.ofHom (algebraMap k k')))).g]
    (P₀ : closedPoints c.Z) (hP₀ : P₀.val ∉ Set.range c.i.base) :
    IsConnectedCurve (CategoryTheory.Limits.pullback.snd f
      (Spec.map (CommRingCat.ofHom (algebraMap k k')))) ∧
      Smooth (CategoryTheory.Limits.pullback.snd f
        (Spec.map (CommRingCat.ofHom (algebraMap k k')))) ∧
      IsConnectedCurve (Compactification.baseChange c
        (Spec.map (CommRingCat.ofHom (algebraMap k k')))).g ∧
      Smooth (Compactification.baseChange c
        (Spec.map (CommRingCat.ofHom (algebraMap k k')))).g ∧
      IsProper (Compactification.baseChange c
        (Spec.map (CommRingCat.ofHom (algebraMap k k')))).g ∧
      IsOpenImmersion (Compactification.baseChange c
        (Spec.map (CommRingCat.ofHom (algebraMap k k')))).i ∧
      (Set.range (Compactification.baseChange c
        (Spec.map (CommRingCat.ofHom (algebraMap k k')))).i.base)ᶜ.Finite ∧
      Function.Surjective (Scheme.Pic.mapHom c.i) ∧
      (Scheme.Pic.mapHom c.i).ker = Subgroup.closure
        {L | ∃ P : closedPoints c.Z, P.val ∉ Set.range c.i.base ∧
          L = @Scheme.Pic.ofClosedPoint k _ c.Z ⟨c.g⟩ hsm P} ∧
      Function.Surjective (Scheme.Pic.mapHom
        (Compactification.baseChange c
          (Spec.map (CommRingCat.ofHom (algebraMap k k')))).i) ∧
      (Scheme.Pic.mapHom (Compactification.baseChange c
        (Spec.map (CommRingCat.ofHom (algebraMap k k')))).i).ker = Subgroup.closure
        {L | ∃ P : closedPoints (Compactification.baseChange c
            (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Z,
          P.val ∉ Set.range (Compactification.baseChange c
            (Spec.map (CommRingCat.ofHom (algebraMap k k')))).i.base ∧
          L = @Scheme.Pic.ofClosedPoint k' _
            (Compactification.baseChange c
              (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Z
            ⟨(Compactification.baseChange c
              (Spec.map (CommRingCat.ofHom (algebraMap k k')))).g⟩ hsm' P} ∧
      ∃ (G : Subgroup c.Z.Pic) (_ : (G : Set c.Z.Pic) = c.g.picZero)
        (Λ : Subgroup G) (e : (G ⧸ Λ) ≃* C.Pic)
        (G' : Subgroup (Compactification.baseChange c
          (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Z.Pic)
        (_ : (G' : Set (Compactification.baseChange c
          (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Z.Pic) =
          (Compactification.baseChange c
            (Spec.map (CommRingCat.ofHom (algebraMap k k')))).g.picZero)
        (Λ' : Subgroup G')
        (e' : (G' ⧸ Λ') ≃* (CategoryTheory.Limits.pullback f
          (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Pic)
        (j : c.Z.Pic →* (Compactification.baseChange c
          (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Z.Pic)
        (hj : ∀ L : G, j L.val ∈ G'),
        Subgroup.map G.subtype Λ = Subgroup.closure
          {L | ∃ P : closedPoints c.Z, P.val ∉ Set.range c.i.base ∧
            L = @Scheme.Pic.ofClosedPoint k _ c.Z ⟨c.g⟩ hsm P /
              @Scheme.Pic.ofClosedPoint k _ c.Z ⟨c.g⟩ hsm P₀} ∧
        ∀ L : G, e (QuotientGroup.mk L) = Scheme.Pic.mapHom c.i L.val ∧
        Subgroup.map G'.subtype Λ' = Subgroup.closure
          {L | ∃ P Q : closedPoints (Compactification.baseChange c
              (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Z,
            P.val ∉ Set.range (Compactification.baseChange c
              (Spec.map (CommRingCat.ofHom (algebraMap k k')))).i.base ∧
            Q.val ∉ Set.range (Compactification.baseChange c
              (Spec.map (CommRingCat.ofHom (algebraMap k k')))).i.base ∧
            L = @Scheme.Pic.ofClosedPoint k' _
              (Compactification.baseChange c
                (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Z
              ⟨(Compactification.baseChange c
                (Spec.map (CommRingCat.ofHom (algebraMap k k')))).g⟩ hsm' P /
              @Scheme.Pic.ofClosedPoint k' _
                (Compactification.baseChange c
                  (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Z
                ⟨(Compactification.baseChange c
                  (Spec.map (CommRingCat.ofHom (algebraMap k k')))).g⟩ hsm' Q} ∧
        ∀ L : G', e' (QuotientGroup.mk L) = Scheme.Pic.mapHom
          (Compactification.baseChange c
            (Spec.map (CommRingCat.ofHom (algebraMap k k')))).i L.val ∧
        (∃ ej : Λ ≃* Λ', ∀ L : Λ, (ej L : _) = j L.val) ∧
        ∀ L : c.Z.Pic, j L = Scheme.Pic.mapHom
          (CategoryTheory.Limits.pullback.fst c.g
            (Spec.map (CommRingCat.ofHom (algebraMap k k')))) L ∧
        ∀ L : G, e' (QuotientGroup.mk ⟨j L.val, hj L⟩) =
          Scheme.Pic.mapHom (CategoryTheory.Limits.pullback.fst f
            (Spec.map (CommRingCat.ofHom (algebraMap k k'))))
            (e (QuotientGroup.mk L)) := by
  sorry

end AlgebraicGeometry
