/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryDifferential

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u w
open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace
namespace AlgebraicGeometry

/-- Existence of representative-normalized values, without isomorphism transport.
Source: Stacks Project, cohomology.tex, Tag 08DJ; sites-cohomology.tex,
Tags 0A90 and 0A96.
(blueprint: lem-pc-tensor-hom-uncurry-descent-representative).

Proof: First take K-flat Lc and the fixed K-injective resolution I(M).
Hom(Lc,I(M)) is K-injective by Tag 0A96. Thus maps in the derived category into
this complex lift uniquely to homotopy classes of chain maps. Choose a chain
map in that class, uncurry by the sheaf tensor-Hom adjunction on every tensor
summand, and localize the explicit coproduct extension. A chain homotopy gives
an uncurried homotopy: apply the same evaluation to its degree-minus-one
components. The differential calculation of Tag 0A90 identifies its boundary
with the difference of the uncurried maps. Hence the result is independent of
the lift. Tensor model comparisons and the inverse map to I(M) put it in the
stated derived Hom set. For arbitrary L, choose a K-flat resolution Lc to L.
Hom(-,I(M)) and P tensor - invert its quasi-isomorphism, and evaluation commutes
with that map. Cancel the localized comparison to obtain the required formula
for L itself. Common K-flat resolutions show that the values assigned by two
such descriptions of the same literal derived input agree. This defines the
required values on all inputs covered by the displayed equation; assign zero
to other inputs. No compatibility on those other inputs is claimed. Zero inputs
and zero complexes give zero, and the argument uses no boundedness. -/
theorem exists_tensorHomUncurry_descent_representative (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] :
    letI := schemeDerivedTensorMonoidal X
    ∃ t : ∀ K L M : schemeDerivedCategory X,
      (K ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op L, M)) → (K ⊗ L ⟶ M),
      ∀ (P L M : CochainComplex
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ),
        P.IsKFlat →
        ∀ φ : P ⟶ homComplex (R := X.sheaf) L
            ((schemeHomKInjectiveResolution X).obj M),
          t (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj M)
              (DerivedCategory.Q.map φ ≫
                (schemeDerivedInternalHomResolutionIso X L M).inv) =
            pullbackTensorModelMap X P L ≫
              DerivedCategory.Q.map (schemeTensorHomUncurry X P L M φ) ≫
                schemeHomResolutionInverse X M := by
  sorry

end AlgebraicGeometry
