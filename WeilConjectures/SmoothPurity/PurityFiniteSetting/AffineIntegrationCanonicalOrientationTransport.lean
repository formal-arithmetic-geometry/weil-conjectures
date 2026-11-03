/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Model.ModelAffineIntegrationOrientationNormalized

/-! # Canonical transport for the total affine orientation -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

private theorem diagonal_orientation_transport
    (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}} (r : ℕ) (f g : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension r f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension r g]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (w : f = g) :
    letI := Dnc.compactifiable P f aY
    letI := Dnc.compactifiable P g aY
    eqToIso (by subst g; rfl) ≪≫ P.diagonalDualizingObject r g aY =
      P.diagonalDualizingObject r f aY := by
  subst g
  simp only [eqToIso_refl, Iso.refl_trans]

/-- Transport the canonical affine total orientation to the pasted model orientation.
Source: latest blueprint, composition proof Step 1 (canonical affine comparison).
(blueprint: new-pur-affine-integration-canonical-orientation-transport).

Proof: unfold `modelAffineTotalOrientation` and the canonical affine gamma.  The
coordinate identity `q d e B ≫ pr e B = pr (d + e) B` identifies their diagonal
objects, and the equality transport for the chosen dualizing objects cancels the
resulting `eqToHom`. Prove the transport first for arbitrary equal morphisms by
substituting one for the other; all the geometric instances are propositions.
Then compose with the unchanged `modelOrientationUnit` and take the hom. This also
covers zero ranks and the empty affine base.
-/
theorem modelAffineTotalOrientation_canonical_transport
    (P : PurityFiniteSetting.{u}) (B : Scheme.{u}) [IsAffine B] (d e : ℕ)
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB] :
    letI := (DiagonalPasting.affineGeometry d e B).2.2.2.2.1
    letI := (DiagonalPasting.affineGeometry d e B).2.2.2.2.2.1
    letI := (DiagonalPasting.affineGeometry d e B).2.2.2.2.2.2.1
    letI := (DiagonalPasting.affineGeometry d e B).2.2.2.2.2.2.2.1
    letI := DiagonalPasting.affineDimension e B
    letI := DiagonalPasting.affineDimension (d + e) B
    letI : SmoothOfRelativeDimension (d + e)
        (DiagonalPasting.q d e B ≫ DiagonalPasting.pr e B) :=
      smoothOfRelativeDimension_comp (n := d) (m := e)
        (DiagonalPasting.q d e B) (DiagonalPasting.pr e B)
    letI := Dnc.compactifiable P (DiagonalPasting.pr e B) aB
    letI := Dnc.compactifiable P (DiagonalPasting.q d e B)
      (DiagonalPasting.pr e B ≫ aB)
    (P.modelAffineTotalOrientation P.modelAffineCanonicalGamma B d e aB).hom =
      (P.modelOrientation (d + e)
        (DiagonalPasting.q d e B ≫ DiagonalPasting.pr e B) aB).hom := by
  let := (DiagonalPasting.affineGeometry d e B).2.2.2.2.1
  let := (DiagonalPasting.affineGeometry d e B).2.2.2.2.2.1
  let := (DiagonalPasting.affineGeometry d e B).2.2.2.2.2.2.1
  let := (DiagonalPasting.affineGeometry d e B).2.2.2.2.2.2.2.1
  let := DiagonalPasting.affineDimension e B
  let := DiagonalPasting.affineDimension (d + e) B
  let : SmoothOfRelativeDimension (d + e)
      (DiagonalPasting.q d e B ≫ DiagonalPasting.pr e B) :=
    smoothOfRelativeDimension_comp (n := d) (m := e)
      (DiagonalPasting.q d e B) (DiagonalPasting.pr e B)
  unfold modelAffineTotalOrientation modelAffineCanonicalGamma modelOrientation
  simp only [Iso.symm_symm_eq]
  rw [diagonal_orientation_transport P (d + e)
    (DiagonalPasting.q d e B ≫ DiagonalPasting.pr e B)
    (DiagonalPasting.pr (d + e) B) aB
    (DiagonalPasting.affineGeometry d e B).2.2.2.1]

end WeilConjectures.PurityFiniteSetting
