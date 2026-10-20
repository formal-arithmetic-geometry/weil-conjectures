/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q28
-/
module

public import Sheaf.Paper.PuritySectionInvariantIntrinsic
public import Sheaf.Paper.PurityDncFamily
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
noncomputable def purityDncIntrinsicBase (P : PurityFiniteSetting.{u}) {B : Scheme.{u}}
    (aB : B ⟶ Spec (.of P.field.k)) : Over (Spec (.of P.field.k)) :=
  Over.mk ((AffineSpace (ULift.{u} (Fin 1)) B ↘ B) ≫ aB)

/-- The constructed DNC as a scheme over the fixed field.
Source: blueprint deformation family (blueprint: def-pur-dnc-section-family). -/
noncomputable def purityDncIntrinsicSource (P : PurityFiniteSetting.{u}) {V B : Scheme.{u}}
    (g : V ⟶ B) (aB : B ⟶ Spec (.of P.field.k)) (s : B ⟶ V) :
    Over (Spec (.of P.field.k)) :=
  Over.mk (Scheme.Hom.deformationSpaceProj g s ≫ (purityDncIntrinsicBase P aB).hom)

/-- The DNC projection, with its fixed k-structure.
Source: blueprint deformation family (blueprint: def-pur-dnc-section-family). -/
noncomputable def purityDncIntrinsicMap (P : PurityFiniteSetting.{u}) {V B : Scheme.{u}}
    (g : V ⟶ B) (aB : B ⟶ Spec (.of P.field.k)) (s : B ⟶ V) :
    purityDncIntrinsicSource P g aB s ⟶ purityDncIntrinsicBase P aB :=
  Over.homMk (Scheme.Hom.deformationSpaceProj g s) rfl

/-- The Rees augmentation section is a k-morphism.
Source: blueprint deformation family (blueprint: def-pur-dnc-section-family).
Proof: its composite with the projection is the identity by the polynomial
augmentation, hence its composite with the k-structure is the given base structure. -/
theorem purityDncIntrinsicSection_over (P : PurityFiniteSetting.{u}) {V B : Scheme.{u}}
    (g : V ⟶ B) (aB : B ⟶ Spec (.of P.field.k)) (s : B ⟶ V)
    (hs : s ≫ g = 𝟙 B) :
    s.deformationSpaceSection ≫ (purityDncIntrinsicSource P g aB s).hom =
      (purityDncIntrinsicBase P aB).hom := by
  change s.deformationSpaceSection ≫
      (Scheme.Hom.deformationSpaceProj g s ≫ (purityDncIntrinsicBase P aB).hom) = _
  rw [← Category.assoc, Scheme.Hom.deformationSpaceSection_deformationSpaceProj hs,
    Category.id_comp]

/-- The actual Rees augmentation section, with its k-structure.
Source: blueprint deformation family (blueprint: def-pur-dnc-section-family). -/
noncomputable def purityDncIntrinsicSection (P : PurityFiniteSetting.{u}) {V B : Scheme.{u}}
    (g : V ⟶ B) (aB : B ⟶ Spec (.of P.field.k)) (s : B ⟶ V)
    (hs : s ≫ g = 𝟙 B) : purityDncIntrinsicBase P aB ⟶ purityDncIntrinsicSource P g aB s :=
  Over.homMk s.deformationSpaceSection (purityDncIntrinsicSection_over P g aB s hs)

/-- The DNC augmentation is a section over k.
Source: blueprint deformation family (blueprint: def-pur-dnc-section-family).
Proof: Over morphism extensionality reduces to the published section/projection
identity, proved on extended-Rees affine charts by t mapping to t. -/
theorem purityDncIntrinsicSection_comp_map (P : PurityFiniteSetting.{u}) {V B : Scheme.{u}}
    (g : V ⟶ B) (aB : B ⟶ Spec (.of P.field.k)) (s : B ⟶ V)
    (hs : s ≫ g = 𝟙 B) :
    purityDncIntrinsicSection P g aB s hs ≫ purityDncIntrinsicMap P g aB s = 𝟙 _ := by
  apply Over.OverMorphism.ext
  exact Scheme.Hom.deformationSpaceSection_deformationSpaceProj hs

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
theorem purityDncIntrinsicDomain (P : PurityFiniteSetting.{u}) {V B : Scheme.{u}}
    (g : V ⟶ B) [Smooth g] [IsSeparated g] [QuasiCompact g]
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    (s : B ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 B) :
    LocallyOfFiniteType (purityDncIntrinsicBase P aB).hom ∧
    QuasiCompact (purityDncIntrinsicBase P aB).hom ∧
    LocallyOfFiniteType (purityDncIntrinsicSource P g aB s).hom ∧
    QuasiCompact (purityDncIntrinsicSource P g aB s).hom ∧
    Smooth (purityDncIntrinsicMap P g aB s).left ∧
    IsClosedImmersion (purityDncIntrinsicSection P g aB s hs).left := by
  exact purityDncDomain P g aB s hs

/-- The finite family F = Ls~* Rg~! A. The total space, projection and section
are the actual extended-Rees construction, equivalently the specified blowup open.
Source: blueprint def-pur-dnc-section-family, displayed definition
(blueprint: def-pur-dnc-section-family). -/
noncomputable def purityDncIntrinsicFamily (P : PurityFiniteSetting.{u}) {V B : Scheme.{u}}
    (g : V ⟶ B) [Smooth g] [IsSeparated g] [QuasiCompact g]
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    (s : B ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 B) :=
  letI := (purityDncIntrinsicDomain P g aB s hs).1
  letI := (purityDncIntrinsicDomain P g aB s hs).2.1
  letI := purityDncCompactifiable P g aB s hs
  P.sectionInvariantIntrinsic (Scheme.Hom.deformationSpaceProj g s)
    s.deformationSpaceSection

/-- The actual deformation family belongs to Pic(Dctf), expressed as membership and
an actual two-sided tensor inverse without an orientation.
Source: blueprint sk-def-purity-conv, last displayed formula
(blueprint: def-pur-dnc-section-family).
Proof: purityDncIntrinsicDomain gives the smooth finite-type deformation projection,
its finite-type base and closed augmentation section. The projection is separated
because it is the Rees open of the blowup of a separated finite-type scheme over
the affine line. The section/projection identity is the Rees augmentation identity.
Apply section-invariant invertibility to this projection and section, using the
published `purityDncCompactifiable` theorem for its compactification. The resulting object is
exactly purityDncIntrinsicFamily, so its finite-Tor membership, inverse and both
tensor isomorphisms give the assertion. This also covers empty bases and varying
relative dimension by the clopen dimension argument for the section invariant. -/
theorem purityDncIntrinsicFamily_pic (P : PurityFiniteSetting.{u}) {V B : Scheme.{u}}
    (g : V ⟶ B) [Smooth g] [IsSeparated g] [QuasiCompact g]
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    (s : B ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 B) :
    finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos
        (purityDncIntrinsicBase P aB).left (purityDncIntrinsicFamily P g aB s hs) ∧
      ∃ Q : Scheme.proEtaleDerivedCategory (purityDncIntrinsicBase P aB).left P.Ring,
        finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos
          (purityDncIntrinsicBase P aB).left Q ∧
        Nonempty ((P.intrinsicCoefficientTensor (purityDncIntrinsicBase P aB).left).obj
          (purityDncIntrinsicFamily P g aB s hs, Q) ≅
            P.intrinsicCoefficientUnit (purityDncIntrinsicBase P aB).left) ∧
        Nonempty ((P.intrinsicCoefficientTensor (purityDncIntrinsicBase P aB).left).obj
          (Q, purityDncIntrinsicFamily P g aB s hs) ≅
            P.intrinsicCoefficientUnit (purityDncIntrinsicBase P aB).left) := by
  have hdomain := purityDncIntrinsicDomain P g aB s hs
  let := hdomain.1
  let := hdomain.2.1
  let : HasCompactification (Scheme.Hom.deformationSpaceProj g s) :=
    purityDncCompactifiable P g aB s hs
  let : Smooth (Scheme.Hom.deformationSpaceProj g s) := hdomain.2.2.2.2.1
  let : IsClosedImmersion s.deformationSpaceSection := hdomain.2.2.2.2.2
  exact P.sectionInvariantIntrinsic_invertible (Scheme.Hom.deformationSpaceProj g s)
    (purityDncIntrinsicBase P aB).hom s.deformationSpaceSection
    (Scheme.Hom.deformationSpaceSection_deformationSpaceProj hs)

end WeilConjectures
