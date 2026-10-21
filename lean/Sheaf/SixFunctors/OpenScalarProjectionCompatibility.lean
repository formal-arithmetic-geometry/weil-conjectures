/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C6
-/
module

public import Sheaf.SixFunctors.OpenScalarTensorData

/-! # Open projection and scalar restriction 

Source: Stacks Project, sites-cohomology.tex, Tags 07A4, 07A6, 0D6D and 0GL1;
sites-modules.tex, Tag 0E8I
(blueprint: lem-sp-open-projection-scalar-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme SheafOfModules WeilConjectures
namespace AlgebraicGeometry.ProEtale.OpenScalarTensor

/-- The scalar-restriction interpretation of any normalized open projection.
Source: Stacks 0GL1 and 0E8I
(blueprint: lem-sp-open-projection-scalar-comparison). -/
structure ProjectionCompatibility (m : Models.{u}) (c : Choices m)
    (projection : ∀ (A : Type u) [CommRing A] [Finite A]
      {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j], Projection m A j) where
  restriction_open_isIso : ∀ {A B : Type u} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j], IsIso (restrictionOpen φ j)
  restricted_beta : ∀ {A B : Type u} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (K : proEtaleDerivedCategory U A),
    scalarProjection m c φ X ((openExtension (A := A) j).obj K) ≫
        (scalarRestriction φ X).map ((beta m φ j).hom.app K) =
      (projection A j).iso.hom.app (K, coefficient m φ X) ≫
        (openExtension (A := A) j).map
          ((tensor m A U).map (Prod.mkHom (𝟙 K) (coefficientPullback m c φ j).hom) ≫
            scalarProjection m c φ U K) ≫
        (restrictionOpen φ j).app ((scalar m φ U).obj K)

/-- The restriction interpretation of a projection with its specified open adjunct,
and invertibility of the restriction/open comparison.
Source: Stacks, sites-modules.tex, Tags 03CY, 03DI and 0E8I;
sites-cohomology.tex, Tags 0GL1, 07A4 and 07A6.
(blueprint: lem-sp-open-projection-scalar-comparison).

Proof: the supplied projection has its inverse fixed by the open Hom bijection,
so it is the canonical unit-normalized projection, independent of its presentation.
Restriction of scalars commutes with the extension presheaf and its sheafification:
it changes only the scalar action. The same identity on sections is therefore an
isomorphism and is the mate `restrictionOpen`, by the open-unit equation.
For `restricted_beta`, take inverse open adjuncts. Scalar extension and tensoring
by the restricted B unit are computed by the same balanced tensor. The normalized
scalar unit inserts 1; the comparison with pullback retains the B factor. Thus
the scalar adjunct defining `scalarProjection` identifies the restricted inverse
beta with the inverse projection at that coefficient, followed by inverse
coefficient pullback. The two adjuncts coincide on the resolving complexes;
descent and injectivity of the open Hom bijection give the equality. Invert it
to obtain the displayed forward equation. This argument imposes no boundedness,
quasi-compactness of the open, or flatness on the coefficient map. -/
theorem open_scalar_projection_compatibility (m : Models.{u}) (c : Choices m)
    (projection : ∀ (A : Type u) [CommRing A] [Finite A]
      {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j], Projection m A j) :
    Nonempty (ProjectionCompatibility m c projection) := by
  sorry

end AlgebraicGeometry.ProEtale.OpenScalarTensor
