/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E3
-/
module

public import Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryDifferential

/-! # Naturality forced by componentwise uncurrying

Source: Stacks Project, sites-cohomology.tex, Tag 0A90, and cohomology.tex, Tag 08DJ.
(blueprint: lem-pc-tensor-hom-uncurry-descent-naturality).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u w
open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace
namespace AlgebraicGeometry

/-- The representative localization equation forces three-variable naturality.
Assume also transport along isomorphisms; this is essential when the chosen
derived category has objects which are not literally images of complexes.
No existence of a family, or existence of chain representatives, is asserted here.
Source: Stacks Project, cohomology.tex, Tag 08DJ, naturality of evaluation;
sites-cohomology.tex, Tags 0A90 and 0A96.
(blueprint: lem-pc-tensor-hom-uncurry-descent-naturality).

Proof: Choose K-flat representatives for the four source objects K,K',L,L',
and the functorial K-injective models for M and M'. Represent maps between them
by roofs, using common K-flat resolutions for source denominators. Maps to a
K-injective complex are actual chain maps modulo homotopy. On these models,
restrict the two uncurried chain maps to every total tensor summand. Naturality
of the sheaf tensor-Hom adjunction and of the Hom product projections identifies
both sides with evaluation after precomposition in P and L and postcomposition
in I(M). The coproduct universal property proves equality of the chain maps.
Apply Q and the assumed representative equation to these chain maps. Naturality
of Q's lax tensor map, of the derived Hom localization factorization, and of the
functorial resolution map gives the claimed equality on representatives.
Use the assumed isomorphism transport to cancel the localized quasi-isomorphisms
in the roofs and the representative isomorphisms to obtain the equation for
arbitrary derived maps a,b,c. Homotopy invariance ensures that none of the roof
choices affects the calculation. The identity and zero-map cases obey the same
component equation, without boundedness assumptions. -/
theorem tensorHomUncurry_descent_natural (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (t : ∀ K L M : schemeDerivedCategory X,
      (K ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op L, M)) → (K ⊗ L ⟶ M))
    (ht : ∀ (P L M : CochainComplex
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ),
        P.IsKFlat →
        ∀ φ : P ⟶ homComplex (R := X.sheaf) L
            ((schemeHomKInjectiveResolution X).obj M),
          t (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj M)
              (DerivedCategory.Q.map φ ≫
                (schemeDerivedInternalHomResolutionIso X L M).inv) =
            pullbackTensorModelMap X P L ≫
              DerivedCategory.Q.map (schemeTensorHomUncurry X P L M φ) ≫
                schemeHomResolutionInverse X M)
    (hi : letI := schemeDerivedTensorMonoidal X
    ∀ (K K' L L' M M' : schemeDerivedCategory X)
      (a : K' ≅ K) (b : L' ≅ L) (c : M ≅ M')
      (f : K ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op L, M)),
      t K' L' M' (a.hom ≫ f ≫
        (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
          X.toRingedSpace.sheaf).map (b.hom.op, c.hom)) =
        (a.hom ⊗ₘ b.hom) ≫ t K L M f ≫ c.hom) :
    letI := schemeDerivedTensorMonoidal X
    ∀ (K K' L L' M M' : schemeDerivedCategory X)
      (a : K' ⟶ K) (b : L' ⟶ L) (c : M ⟶ M')
      (f : K ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op L, M)),
      t K' L' M' (a ≫ f ≫
        (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
          X.toRingedSpace.sheaf).map (b.op, c)) =
        (a ⊗ₘ b) ≫ t K L M f ≫ c := by sorry

end AlgebraicGeometry
