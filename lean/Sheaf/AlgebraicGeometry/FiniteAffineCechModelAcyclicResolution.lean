/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.AlgebraicGeometry.FiniteAffineCechModel
public import Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-! # An acyclic resolution representing the specified section complex

Source: Stacks Project, Tags 01XB, 01XD, 01FK and 01FM.
(blueprint: lem-pc-finite-affine-cech-model-acyclic-resolution).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- The finite section model is the termwise pushforward of an acyclic resolution.
This assertion concerns complexes and ordinary direct image, without a derived
localization or a total derived comparison.
Source: Stacks Project, Tags 01XB, 01XD, 01FK and 01FM.
(blueprint: lem-pc-finite-affine-cech-model-acyclic-resolution).

Proof: In degree p form the finite product of j_J,*(F restricted to U_J), where J
runs over the increasing (p+1)-tuples of the cover and U_J is their intersection.
For each deleted entry use the restriction morphism between these open direct
images, with sign (-1)^j. The two orders of deleting entries cancel, so the signed
sum squares to zero. The restriction maps from F augment this complex. On V_i,
insert i into a tuple, sort it with its sign, and put repeated-index contributions
to zero. The signed face calculation gives a contraction of the augmentation;
thus it is locally, and hence globally, a quasi-isomorphism. Equivalently this is
the ordered version of the usual sheaf Cech resolution, via Tags 01FK and 01FM.
Separatedness over the affine target makes each U_J affine. Its inclusion in X
is affine, as its inverse image on any affine chart is an intersection of affine
opens. Both j_J and f composed with j_J have vanishing positive direct images on
F restricted to U_J by affine quasi-coherent acyclicity (01XB). The open inclusion
has exact restriction as its left adjoint and therefore preserves injectives.
Pushing an injective resolution along j_J gives an injective resolution of its
ordinary direct image; composition of pushforwards then proves f_*-acyclicity of
that factor. Finite products of acyclic objects are acyclic. Finally identify
f_*j_J,*(F restricted to U_J) on the affine target with the associated module of
sections of F on U_J. Naturality of the tilde-Gamma identification intertwines
every restriction and therefore the signed differentials. The canonical chart
T to Spec Gamma(T,O) and GammaSpecIso give exactly the scalar restriction and
pullback in finiteAffineCechModel, so these identifications assemble into the
asserted chain isomorphism after extension by zero. For r=0 the covering condition
forces X empty, and the zero complex and unique augmentation give the claim.
When p+1 exceeds r the product is empty and zero; F=0 and empty affine intersections
are also covered by the same construction. Existential witnesses are consumed only
in proofs and never used here to define an arbitrary object. -/
theorem exists_finiteAffineCechModel_acyclic_resolution
    {X T : Scheme.{u}} (f : X ⟶ T) [IsAffine T] [IsSeparated f] [QuasiCompact f]
    (F : X.Modules) [F.IsQuasicoherent]
    {r : ℕ} (V : Fin r → X.Opens) (hV : ∀ i, IsAffineOpen (V i))
    (hcover : iSup V = ⊤) :
    ∃ (D : CochainComplex X.Modules ℕ)
      (ε : (CochainComplex.single₀ X.Modules).obj F ⟶ D),
      QuasiIso ε ∧
      (∀ p, (RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightAcyclic (D.X p)) ∧
      Nonempty (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (D.extend ComplexShape.embeddingUpNat) ≅
          finiteAffineCechModel f F V) := by sorry

end AlgebraicGeometry.Scheme.Modules
