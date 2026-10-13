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

/-- Extend representative-normalized values to an isomorphism-compatible family.
The new family agrees with the given one only on the specified chain inputs;
the given family need not be compatible on arbitrary derived objects.
Source: Stacks Project, cohomology.tex, Tag 08DJ (functoriality on representatives),
and sites-cohomology.tex, Tags 0A90 and 0A96.
(blueprint: lem-pc-tensor-hom-uncurry-descent-extension).

Proof: Choose complex representatives of the three derived objects and K-flat
resolutions of the first two. Maps into Hom(Lc,I(M)) lift to chain maps modulo
homotopy because that Hom complex is K-injective. Evaluate t on these chain
inputs and transport the answer along the chosen representative isomorphisms.
The normalization hypothesis expresses every value used here as localized
componentwise evaluation, so it supplies homotopy invariance and compatibility
under changes of the chain lift. For changes of representatives, compute roofs
on common K-flat resolutions and K-injective targets. On each tensor summand,
the sheaf tensor-Hom adjunction and the Hom projections commute with pre- and
postcomposition. The coproduct universal property gives the comparison identity
for evaluation. Localize it, use the naturality of the tensor model map, Hom
resolution comparison and resolution augmentation, and cancel the invertible
quasi-isomorphisms. This proves independence of representatives and the asserted
transport identity for arbitrary derived isomorphisms. If the input already has
the form in the agreement clause, use its given K-flat P. Resolve its possibly
non-K-flat L; both P tensor - and Hom(-,I(M)) invert this resolution and evaluation
commutes with it. Cancellation and ht give precisely agreement with t on that
input. The construction does not retain arbitrary values of t elsewhere. Identity
isomorphisms, zero inputs and zero complexes satisfy the same comparison; no
boundedness or naturality of the given t outside its normalized inputs is used. -/
theorem exists_tensorHomUncurry_descent_extension (X : Scheme.{u})
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
                schemeHomResolutionInverse X M) :
    letI := schemeDerivedTensorMonoidal X
    ∃ s : ∀ K L M : schemeDerivedCategory X,
      (K ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op L, M)) → (K ⊗ L ⟶ M),
      (∀ (P L M : CochainComplex
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ),
        P.IsKFlat →
        ∀ φ : P ⟶ homComplex (R := X.sheaf) L
            ((schemeHomKInjectiveResolution X).obj M),
          s (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj M)
              (DerivedCategory.Q.map φ ≫
                (schemeDerivedInternalHomResolutionIso X L M).inv) =
            t (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj M)
              (DerivedCategory.Q.map φ ≫
                (schemeDerivedInternalHomResolutionIso X L M).inv)) ∧
    ∀ (K K' L L' M M' : schemeDerivedCategory X)
      (a : K' ≅ K) (b : L' ≅ L) (c : M ≅ M')
      (f : K ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op L, M)),
      s K' L' M' (a.hom ≫ f ≫
        (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
          X.toRingedSpace.sheaf).map (b.hom.op, c.hom)) =
        (a.hom ⊗ₘ b.hom) ≫ s K L M f ≫ c.hom := by
  sorry

end AlgebraicGeometry
