/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W3
-/
module

public import Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryDifferential

/-! # Naturality on localized chain maps

Source: Stacks Project, sites-cohomology.tex, Tag 0A90, and cohomology.tex, Tag 08DJ.
(blueprint: lem-pc-tensor-hom-uncurry-chain-naturality).
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

/-- Componentwise uncurrying is natural on the images of actual chain maps.
The input `f` is an arbitrary derived morphism; the three variable maps are chain maps.
Source: Stacks Project, cohomology.tex, Tag 08DJ, and sites-cohomology.tex,
Tags 0A90 and 0A96.
(blueprint: lem-pc-tensor-hom-uncurry-chain-naturality).

Proof: Choose K-flat replacements of P and P', and use a common K-flat replacement
of the roof representing the map between them. Replace M and M' by the fixed functorial
K-injective resolutions. The Hom complex from L into I(M) is K-injective after
replacing L by a K-flat complex, so f is represented by an actual chain map into that
Hom complex, modulo homotopy. Transport t along the localized replacement isomorphisms
using hi. On the K-flat models use ht to identify each value of t with the localization
of schemeTensorHomUncurry. Precomposition in P, precomposition in L, and postcomposition
in I(M) commute with this chain map: restrict both sides to each total tensor summand,
use naturality of the Hom projections and of the sheaf tensor-Hom adjunction, and then
use coproduct extensionality. The homotopy between two chosen lifts gives a homotopy
between their uncurried maps by the same component calculation. Apply Q to this identity;
naturality of the tensor comparison, the internal-Hom factorization isomorphism and the
resolution augmentation yields the displayed equality. Cancel replacement isomorphisms
using hi. No boundedness, flatness of the original complexes, or nonzero-map assumption
is used; identities and zero maps satisfy the same summand calculation. The extension
from localized chain maps to arbitrary derived arrows is deliberately not asserted here. -/
theorem tensorHomUncurry_chain_natural (X : Scheme.{u})
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
    ∀ (P P' L L' M M' : CochainComplex
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
      (a : P' ⟶ P) (b : L' ⟶ L) (c : M ⟶ M')
      (f : DerivedCategory.Q.obj P ⟶
        (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
          X.toRingedSpace.sheaf).obj (op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj M)),
      t (DerivedCategory.Q.obj P') (DerivedCategory.Q.obj L') (DerivedCategory.Q.obj M')
          (DerivedCategory.Q.map a ≫ f ≫
            (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
              X.toRingedSpace.sheaf).map ((DerivedCategory.Q.map b).op,
                DerivedCategory.Q.map c)) =
        (DerivedCategory.Q.map a ⊗ₘ DerivedCategory.Q.map b) ≫
          t (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj M) f ≫
            DerivedCategory.Q.map c := by sorry

end AlgebraicGeometry
