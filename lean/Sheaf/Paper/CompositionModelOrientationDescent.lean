/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V3
-/
module

public import Sheaf.Paper.CompositionModelOrientationDefinitions
import Sheaf.Paper.ModelAffineIntegrationOrientation
import Sheaf.Paper.ModelOrientationSourceNaturality
import Sheaf.Paper.ModelOrientationTateDetection
import Sheaf.Paper.ModelChartOrientationAssembly
import Sheaf.Paper.ModelOrientationChartDescent

/-! # Assembly of affine model orientations and their global descent -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

/-- Global comparison of the specified diagonal orientations, including empty X.
Source: composition proof Steps 1--2
(blueprint: lem-pur-composition-model-orientation-descent).

Proof: (1) concatenate the ordinary Tate powers and their even shifts; the Tate line
is locally free of rank one, so ordinary powers compute derived powers. (2) Ordered
integration transposes identify the affine comparisons at every positive coefficient
level, and coefficient-counit normalization writes Gamma as theta(1 tensor G).
(3) Integration-normalized vector-bundle direct sums, transported through the proper/open
site comparisons and mate pasting, give G_h mu = sigma(G_q tensor q*G_g).
(4) Cancel the invertible G maps. Rank-zero factors reduce to the tensor-unit laws.
(5) Pull along the total zero section to obtain b_(d+e) nu = mu(b_d tensor b_e).
(6) In the compatible affine DNC charts these are precisely the normal orientations;
substitute their three identity-coordinate DNC maps to obtain the beta-delta equation.
(7) Substitute theta = beta delta alpha inverse and cancel the invertible tensor of alphas.
(8) Remove the common even shift of the Tate line and apply degree-zero derived-map
gluing to the compatible-chart cover. Restriction is injective on endomorphisms and
hence on automorphisms. (9) The quotient of the two orientations is locally the identity,
so it is globally the identity. The empty cover proves the same assertion for empty X.
-/
theorem composition_model_orientation_descent (P : PurityFiniteSetting.{u})
    {X Y Z : Scheme.{u}}
    (d e : ℕ) (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    (aZ : Z ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aZ] [QuasiCompact aZ] :
    CompositionModelOrientationConclusion.{u, w} P d e f g aZ := by
  let : Y.Over (Spec (.of P.field.k)) := ⟨g ≫ aZ⟩
  obtain ⟨G, hG, hGzero, haffine, hbeta⟩ := model_affine_integration_orientation P d e
  have hsource : ModelOrientationSourceNaturality P d e f g := by
    constructor
    · intro K _
      exact (Classical.choose_spec (P.existsUnique_compositionSourceFixed f g d e K)).1
    · intro K L _ _ a
      exact model_orientation_source_naturality P d e f g K L a
  have hsign : (-1 : ℤ) ^ ((2 * d) * (2 * e)) = 1 := by
    rw [Nat.mul_assoc, pow_mul]
    norm_num
  have hchart (U V T : Scheme.{u}) [IsAffine U] [IsAffine V] [IsAffine T]
      (f' : U ⟶ V) (g' : V ⟶ T)
      [IsSeparated f'] [LocallyOfFiniteType f'] [QuasiCompact f']
      [IsSeparated g'] [LocallyOfFiniteType g'] [QuasiCompact g']
      [SmoothOfRelativeDimension d f'] [SmoothOfRelativeDimension e g']
      (aT : T ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aT] [QuasiCompact aT] :
      ModelChartOrientationEquation P d e f' g' aT :=
    model_chart_orientation_assembly P G d e f' g' aT
      (fun B _ aB _ _ ↦ (haffine B aB).2) hbeta
  have hdetect := model_orientation_tate_detection.{u, w} P X (f ≫ g ≫ aZ) (d + e)
  have hglobal : ModelOrientationEquation P d e f g aZ := by
    let := P.noetherian aZ
    let := P.noetherian (g ≫ aZ)
    let := Dnc.compactifiable P f (g ≫ aZ)
    let := Dnc.compactifiable P g aZ
    let := Dnc.compactifiable P (f ≫ g) aZ
    let := (DiagonalPasting.geometryProperties d e f g).2.2.2.2
    let : IsNoetherianRing P.Coefficient := isNoetherian_of_finite _ _
    let := ProEtale.upperStarPreservesFlat_moduleCat P.Coefficient
    have heq := model_orientation_chart_descent P d e f g aZ hchart hdetect
    constructor
    · exact heq
    · rw [heq]
      simp only [Iso.inv_hom_id_assoc, Iso.inv_hom_id]
      rfl
  exact ⟨G, hG, hGzero, hsource, hsign, haffine,
    fun U V T _ _ _ f' g' _ _ _ _ _ _ _ _ aT _ _ ↦
      ⟨hchart U V T f' g' aT, hbeta U V T f' g' aT⟩,
    hdetect, hglobal⟩

end WeilConjectures.PurityFiniteSetting
