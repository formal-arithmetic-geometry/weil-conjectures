/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSectionInvariant
public import WeilConjectures.AlgebraicGeometry.DeformationToNormalCone
import WeilConjectures.AlgebraicGeometry.DeformationSpace.SmoothProj

/-! # The deformation family with the native exceptional inverse image

Source: latest blueprint sec-smooth-purity/sk-lem-geometry/
def-pur-dnc-section-family.md, displayed family definition
(blueprint: def-pur-dnc-section-family).

The geometry is the published extended-Rees construction, equivalently the blowup
minus the scheme-theoretic strict transform. The family is the recorded condensed
section invariant of its actual projection and augmentation section.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (D : WeilConjectures.FiniteFieldDatum.{u})
  (B V : Over (Spec (.of D.k))) (g : V ⟶ B) (s : B ⟶ V)

/-- The affine-line base of the deformation, with its given field structure.
Source: latest blueprint, deformation base (blueprint: def-pur-dnc-section-family). -/
def condensedDncBase : Over (Spec (.of D.k)) :=
  Over.mk ((AffineSpace (ULift.{u} (Fin 1)) B.left ↘ B.left) ≫ B.hom)

/-- The actual extended-Rees deformation space, with its field structure.
Source: latest blueprint, blowup complement (blueprint: def-pur-dnc-section-family). -/
def condensedDncSource : Over (Spec (.of D.k)) :=
  Over.mk (Scheme.Hom.deformationSpaceProj g.left s.left ≫ (condensedDncBase D B).hom)

/-- The projection of the constructed deformation to its affine-line base.
Source: latest blueprint, g tilde (blueprint: def-pur-dnc-section-family). -/
def condensedDncMap : condensedDncSource D B V g s ⟶ condensedDncBase D B :=
  Over.homMk (Scheme.Hom.deformationSpaceProj g.left s.left) rfl

/-- The Rees augmentation section respects the fixed field structure.
Source: latest blueprint, s tilde (blueprint: def-pur-dnc-section-family).
Proof: the augmentation sends t to t and every f/t to zero; its composite with
projection is the identity. Compose that identity with the affine-line field map.
This uses the geometric section identity of the extended-Rees construction. -/
theorem condensedDncSection_over (hs : s ≫ g = 𝟙 B) :
    s.left.deformationSpaceSection ≫ (condensedDncSource D B V g s).hom =
      (condensedDncBase D B).hom := by
  have hs' : s.left ≫ g.left = 𝟙 B.left := congrArg (fun f ↦ f.left) hs
  change s.left.deformationSpaceSection ≫
      (Scheme.Hom.deformationSpaceProj g.left s.left ≫ (condensedDncBase D B).hom) = _
  rw [← Category.assoc, Scheme.Hom.deformationSpaceSection_deformationSpaceProj hs',
    Category.id_comp]

/-- The actual augmentation section, as a morphism over the fixed field.
Source: latest blueprint, s tilde (blueprint: def-pur-dnc-section-family). -/
def condensedDncSection (hs : s ≫ g = 𝟙 B) :
    condensedDncBase D B ⟶ condensedDncSource D B V g s :=
  Over.homMk s.left.deformationSpaceSection (condensedDncSection_over D B V g s hs)

variable [hBft : LocallyOfFiniteType B.hom] [hBqc : QuasiCompact B.hom]
  [hBsep : IsSeparated B.hom]
  [hVft : LocallyOfFiniteType V.hom] [hVqc : QuasiCompact V.hom]
  [hVsep : IsSeparated V.hom]
  [hgsm : Smooth g.left] [hgsep : IsSeparated g.left]
  [hgft : LocallyOfFiniteType g.left] [hgqc : QuasiCompact g.left]
  [hsclosed : IsClosedImmersion s.left]

include hBft hBqc hBsep hVft hVqc hVsep hgsm hgsep hgft hgqc hsclosed

/-- The geometric domain of the smooth deformation family, including its section law.
Source: latest blueprint, deformation family and sk-lem-geometry
(blueprint: def-pur-dnc-section-family).
Proof: near the section choose smooth etale coordinates, and write the Rees chart
as x_i=t*u_i. Projection to t is smooth. Away from the section it is the product
with Gm. These charts include varying relative dimension and the empty base.
Finite type follows from the finitely generated centre on the Noetherian source;
separatedness follows from the blowup of the separated product. The section is
closed since the projection is separated. The augmentation gives the section law.
The affine line is separated finite type over B, so both field structures have
the displayed properties. These are the geometric clauses of the dependency node. -/
theorem condensedDncDomain (hs : s ≫ g = 𝟙 B) :
    LocallyOfFiniteType (condensedDncBase D B).hom ∧
    QuasiCompact (condensedDncBase D B).hom ∧
    IsSeparated (condensedDncBase D B).hom ∧
    LocallyOfFiniteType (condensedDncSource D B V g s).hom ∧
    QuasiCompact (condensedDncSource D B V g s).hom ∧
    IsSeparated (condensedDncSource D B V g s).hom ∧
    Smooth (condensedDncMap D B V g s).left ∧
    IsSeparated (condensedDncMap D B V g s).left ∧
    LocallyOfFiniteType (condensedDncMap D B V g s).left ∧
    QuasiCompact (condensedDncMap D B V g s).left ∧
    IsClosedImmersion (condensedDncSection D B V g s hs).left ∧
    condensedDncSection D B V g s hs ≫ condensedDncMap D B V g s = 𝟙 _ := by
  have _ := hVft
  have _ := hVqc
  have _ := hVsep
  have _ := hgft
  have hs' : s.left ≫ g.left = 𝟙 B.left := congrArg (fun f ↦ f.left) hs
  have hsection := Scheme.Hom.deformationSpaceSection_deformationSpaceProj hs'
  have : Smooth (Scheme.Hom.deformationSpaceProj g.left s.left) :=
    Scheme.Hom.smooth_deformationSpaceProj g.left s.left hs'
  have : IsClosedImmersion (s.left.deformationSpaceSection ≫
      Scheme.Hom.deformationSpaceProj g.left s.left) := hsection ▸ inferInstance
  have : IsClosedImmersion s.left.deformationSpaceSection :=
    IsClosedImmersion.of_comp _ (Scheme.Hom.deformationSpaceProj g.left s.left)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change LocallyOfFiniteType ((AffineSpace (ULift.{u} (Fin 1)) B.left ↘ B.left) ≫ B.hom)
    infer_instance
  · change QuasiCompact ((AffineSpace (ULift.{u} (Fin 1)) B.left ↘ B.left) ≫ B.hom)
    infer_instance
  · change IsSeparated ((AffineSpace (ULift.{u} (Fin 1)) B.left ↘ B.left) ≫ B.hom)
    infer_instance
  · change LocallyOfFiniteType (Scheme.Hom.deformationSpaceProj g.left s.left ≫
        (AffineSpace (ULift.{u} (Fin 1)) B.left ↘ B.left) ≫ B.hom)
    infer_instance
  · change QuasiCompact (Scheme.Hom.deformationSpaceProj g.left s.left ≫
        (AffineSpace (ULift.{u} (Fin 1)) B.left ↘ B.left) ≫ B.hom)
    infer_instance
  · change IsSeparated (Scheme.Hom.deformationSpaceProj g.left s.left ≫
        (AffineSpace (ULift.{u} (Fin 1)) B.left ↘ B.left) ≫ B.hom)
    infer_instance
  · exact inferInstanceAs (Smooth (Scheme.Hom.deformationSpaceProj g.left s.left))
  · exact inferInstanceAs (IsSeparated (Scheme.Hom.deformationSpaceProj g.left s.left))
  · exact inferInstanceAs (LocallyOfFiniteType (Scheme.Hom.deformationSpaceProj g.left s.left))
  · exact inferInstanceAs (QuasiCompact (Scheme.Hom.deformationSpaceProj g.left s.left))
  · exact inferInstanceAs (IsClosedImmersion s.left.deformationSpaceSection)
  · apply Over.OverMorphism.ext
    exact hsection

variable (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
  (E : PadicAlgCl.FiniteIntermediateField ell) (n : ℕ) (hn : 1 ≤ n)
  (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  (hcoeff :
    Nonempty (Mon.mk Λ ≅ Mon.mk (IntegralModelsEmbedded.discreteObj
      (Padic.coefficientExtensionRing ell E n))) ∨
    Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ell E)) ∨
    Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E)) ∨
    Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ell)))

/-- The family F = Ls tilde* Rg tilde! Lambda, using the native condensed functor.
Only geometric proofs from condensedDncDomain are used to type the expression;
its objects and arrows are the actual Rees construction, never an existence choice.
Source: latest blueprint, family formula (blueprint: def-pur-dnc-section-family). -/
def condensedDncFamily (hs : s ≫ g = 𝟙 B) :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (condensedDncBase D B).left)
      Ab.{u + 1}) (condensedRingObj Λ (condensedDncBase D B).left)) :=
  let H := condensedDncDomain D B V g s hs
  letI := H.1
  letI := H.2.1
  letI := H.2.2.1
  letI := H.2.2.2.1
  letI := H.2.2.2.2.1
  letI := H.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.2.2.2.2.1
  condensedSectionInvariant D ell hell E n hn Λ hcoeff
    (condensedDncBase D B) (condensedDncSource D B V g s)
    (condensedDncMap D B V g s) (condensedDncSection D B V g s hs)
    H.2.2.2.2.2.2.2.2.2.2.2

end AlgebraicGeometry.ProEtale.CondensedRing
