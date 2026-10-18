/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import Sheaf.Paper.PuritySectionInvariant
public import WeilConjectures.AlgebraicGeometry.DeformationToNormalCone

/-! # The deformation family and its finite section invariant

Source: blueprint sec-smooth-purity/sk-def-purity-conv/def-pur-dnc-section-family.md
(blueprint: def-pur-dnc-section-family).

The total space and its maps are the constructed extended-Rees relative spectrum,
equivalently the specified blowup open. The family object uses the recorded actual
finite section invariant. No deformation datum is selected by existence.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- The affine line over B, as a scheme over the fixed field.
Source: blueprint deformation family (blueprint: def-pur-dnc-section-family). -/
noncomputable def purityDncBase (P : PurityFiniteSetting.{u}) {B : Scheme.{u}}
    (aB : B ⟶ Spec (.of P.field.k)) : Over (Spec (.of P.field.k)) :=
  Over.mk ((AffineSpace (ULift.{u} (Fin 1)) B ↘ B) ≫ aB)

/-- The constructed DNC as a scheme over the fixed field.
Source: blueprint deformation family (blueprint: def-pur-dnc-section-family). -/
noncomputable def purityDncSource (P : PurityFiniteSetting.{u}) {V B : Scheme.{u}}
    (g : V ⟶ B) (aB : B ⟶ Spec (.of P.field.k)) (s : B ⟶ V) :
    Over (Spec (.of P.field.k)) :=
  Over.mk (Scheme.Hom.deformationSpaceProj g s ≫ (purityDncBase P aB).hom)

/-- The DNC projection, with its fixed k-structure.
Source: blueprint deformation family (blueprint: def-pur-dnc-section-family). -/
noncomputable def purityDncMap (P : PurityFiniteSetting.{u}) {V B : Scheme.{u}}
    (g : V ⟶ B) (aB : B ⟶ Spec (.of P.field.k)) (s : B ⟶ V) :
    purityDncSource P g aB s ⟶ purityDncBase P aB :=
  Over.homMk (Scheme.Hom.deformationSpaceProj g s) rfl

/-- The Rees augmentation section is a k-morphism.
Source: blueprint deformation family (blueprint: def-pur-dnc-section-family).
Proof: its composite with the projection is the identity by the polynomial
augmentation, hence its composite with the k-structure is the given base structure. -/
theorem purityDncSection_over (P : PurityFiniteSetting.{u}) {V B : Scheme.{u}}
    (g : V ⟶ B) (aB : B ⟶ Spec (.of P.field.k)) (s : B ⟶ V)
    (hs : s ≫ g = 𝟙 B) :
    s.deformationSpaceSection ≫ (purityDncSource P g aB s).hom =
      (purityDncBase P aB).hom := by
  sorry

/-- The actual Rees augmentation section, with its k-structure.
Source: blueprint deformation family (blueprint: def-pur-dnc-section-family). -/
noncomputable def purityDncSection (P : PurityFiniteSetting.{u}) {V B : Scheme.{u}}
    (g : V ⟶ B) (aB : B ⟶ Spec (.of P.field.k)) (s : B ⟶ V)
    (hs : s ≫ g = 𝟙 B) : purityDncBase P aB ⟶ purityDncSource P g aB s :=
  Over.homMk s.deformationSpaceSection (purityDncSection_over P g aB s hs)

/-- The DNC augmentation is a section over k.
Source: blueprint deformation family (blueprint: def-pur-dnc-section-family).
Proof: Over morphism extensionality reduces to the published section/projection
identity, proved on extended-Rees affine charts by t mapping to t. -/
theorem purityDncSection_comp_map (P : PurityFiniteSetting.{u}) {V B : Scheme.{u}}
    (g : V ⟶ B) (aB : B ⟶ Spec (.of P.field.k)) (s : B ⟶ V)
    (hs : s ≫ g = 𝟙 B) :
    purityDncSection P g aB s hs ≫ purityDncMap P g aB s = 𝟙 _ := by
  sorry

/-- All required domains and geometric properties of the DNC of a smooth section.
Source: blueprint sk-lem-geometry and the finite-type domain check in sk-thm-dnc
(blueprint: def-pur-dnc-section-family).
Proof: etale-locally along the section the extended-Rees chart is x_i=t*u_i,
so its projection is smooth of the locally constant relative dimension of g.
Away from the section it is the product with Gm. The affine Rees projection
and separatedness of g give separatedness. Its affine centre ideal is finitely
generated on the Noetherian finite-type source, so the Rees chart is finite type.
The affine line is finite type over B and the DNC is quasi-compact over that line.
The displayed section is closed because the projection is separated. -/
theorem purityDncDomain (P : PurityFiniteSetting.{u}) {V B : Scheme.{u}}
    (g : V ⟶ B) [Smooth g] [IsSeparated g] [QuasiCompact g]
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    (s : B ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 B) :
    LocallyOfFiniteType (purityDncBase P aB).hom ∧
    QuasiCompact (purityDncBase P aB).hom ∧
    LocallyOfFiniteType (purityDncSource P g aB s).hom ∧
    QuasiCompact (purityDncSource P g aB s).hom ∧
    Smooth (purityDncMap P g aB s).left ∧
    IsClosedImmersion (purityDncSection P g aB s hs).left := by
  sorry

/-- Compactifiability of the actual DNC projection in the finite-type domain.
Source: blueprint sk-thm-dnc, opening domain check
(blueprint: def-pur-dnc-section-family).
Proof: the blowup is proper over V times A1. Its defining open is quasi-compact
because this product is Noetherian, so the open immersion is finite type. Hence
the DNC projection is separated finite type. Its base is Noetherian and Nagata
provides a compactification. -/
theorem purityDncCompactifiable (P : PurityFiniteSetting.{u}) {V B : Scheme.{u}}
    (g : V ⟶ B) [Smooth g] [IsSeparated g] [QuasiCompact g]
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    (s : B ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 B) :
    HasCompactification (Scheme.Hom.deformationSpaceProj g s) := by
  sorry

/-- The finite family F = Ls~* Rg~! A. The total space, projection and section
are the actual extended-Rees construction, equivalently the specified blowup open.
Source: blueprint def-pur-dnc-section-family, displayed definition
(blueprint: def-pur-dnc-section-family). -/
noncomputable def purityDncFamily (P : PurityFiniteSetting.{u}) {V B : Scheme.{u}}
    (g : V ⟶ B) [Smooth g] [IsSeparated g] [QuasiCompact g]
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    (s : B ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 B) :=
  letI := (purityDncDomain P g aB s hs).1
  letI := (purityDncDomain P g aB s hs).2.1
  letI := purityDncCompactifiable P g aB s hs
  P.sectionInvariant (Scheme.Hom.deformationSpaceProj g s) (purityDncBase P aB).hom
    s.deformationSpaceSection

end WeilConjectures
