/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q14
-/
module

public import Sheaf.AlgebraicGeometry.NormalProductSquareDescent
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses

/-! # Square difference after a finite field extension

Source: Guo, Divisors on coherent schemes and homogeneous spaces, Section 5.1,
Proposition 5.2(ii), Claim 5.2.1 and its proof, printed pages 11--13,
March 31, 2026 version (blueprint: lem-sfb-field-square-after-finite-extension).

The existing square coordinates are base changed by `Over.pullback`; no rational
points, separability, or properness assumptions are imposed.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- The square difference on the base change of the original product, using the
base changes of its four recorded coordinate maps. The argument is a module on
`C_T`, so in the theorem it is precisely the tensor pullback `A_K`. The two negative
factors are internal Homs into the structure sheaf on `(P ×[S] X₃)_T`.

Source: Guo, Section 5.1 and Claim 5.2.1
(blueprint: lem-sfb-field-square-after-finite-extension). -/
noncomputable def squareDifferenceAfterBaseChange {S T : Scheme.{u}}
    (X₁ X₂ X₃ : Over S) (g : T ⟶ S)
    (A : (Limits.pullback ((X₁ ⨯ X₂) ⨯ X₃).hom g).Modules) :
    (Limits.pullback (squareParameter X₁ X₂ ⨯ X₃).hom g).Modules :=
  (tensorPullback ((Over.pullback g).map
    (squareCoordinate X₁ X₂ X₃ false false)).left).obj A ⊗
    (tensorPullback ((Over.pullback g).map
      (squareCoordinate X₁ X₂ X₃ true true)).left).obj A ⊗
    SheafOfModules.homObj (R := (Limits.pullback (squareParameter X₁ X₂ ⨯ X₃).hom g).sheaf)
      ((tensorPullback ((Over.pullback g).map
        (squareCoordinate X₁ X₂ X₃ false true)).left).obj A) (𝟙_ _) ⊗
    SheafOfModules.homObj (R := (Limits.pullback (squareParameter X₁ X₂ ⨯ X₃).hom g).sheaf)
      ((tensorPullback ((Over.pullback g).map
        (squareCoordinate X₁ X₂ X₃ true false)).left).obj A) (𝟙_ _)

/-- After a finite field extension, the square difference of an invertible module
on the three-factor product is pulled back from the doubled first two factors.
The products in `Over (Spec k)` are fibre products. Finite presentation is local
finite presentation and quasi-compactness, since separatedness implies
quasi-separatedness. Base change identifies `(P ×[k] X₃)_K` with `P_K ×[K] X₃,K`.
The conclusion uses the base-changed coordinate maps and `A_K` itself.

Source: Guo, Proposition 5.2(ii), Claim 5.2.1, printed pages 11--13,
March 31, 2026 version (blueprint: lem-sfb-field-square-after-finite-extension).

Proof plan (the seven steps of the node):
1. Smooth base change and composition (lem-pc-proper-base-change,
   lem-trf-smooth-composition), geometric irreducibility of products
   (lem-sc-geometrically-irreducible-product), and geometric normality
   (lem-trf-smooth-geometrically-normal) make all products geometrically integral
   and normal. Use pqf-lem-locnoeth-lft for local Noetherianity,
   lem-pc-smooth-flat for flat projections, and
   lem-sfb-finite-type-composition-base-change and
   lem-weil-pbc-proper-fp-permanence for finite type and separatedness.
2. Apply lem-sfb-finite-closed-set-rational-lifts to the disjoint union of the
   three factors over three copies of Spec k. Obtain one finite extension with
   rational points x*, y*, z*, and choose affine neighbourhoods U, V of x*, y*.
3. Rigidify A' on U × V × X₃ as B = A' ⊗ a*A'⁻¹ ⊗ b*A'⁻¹ ⊗ c*A', where a
   replaces x by x*, b replaces y by y*, and c replaces both. Both coordinate
   slices are trivial by cancellation (lem-weil-pbc-invertible-pullback-tensor).
4. On U × V × Z, Z = X₃ × X₃, put H = q₀*B ⊗ (q₁*B)⁻¹. Apply
   lem-sfb-birigidified-affine-triviality-locus, enlarging the finite extension
   if necessary. The diagonal point (z*,z*) belongs to the clopen triviality
   locus; connectedness of Z makes it all of Z. The generic fibre is trivial.
5. Apply lem-sfb-normal-noetherian-generic-line-pullback to H. The section
   (x*,y*,id) trivializes the descended module, so H is trivial everywhere.
6. Restrict along (x,y,z) ↦ (x,y,z,z*), obtaining B pulled back from U × V.
   Expand its four-term square. Every rigidifying correction omits x or y,
   so its square factors cancel in pairs. Thus D(A_K) descends over
   Q = U × U × V × V, by lem-weil-pbc-invertible-pullback-tensor.
7. The open Q contains the generic point of the integral scheme P_K. Its
   descended line is a one-dimensional vector space there and is trivial.
   Apply lem-sfb-normal-noetherian-generic-line-pullback to π_K to obtain
   the invertible N_K on all of P_K and the required isomorphism.
-/
theorem exists_fieldSquare_after_finite_extension (k : Type u) [Field k]
    (X₁ X₂ X₃ : Over (Spec (CommRingCat.of k)))
    [Smooth X₁.hom] [IsSeparated X₁.hom] [LocallyOfFinitePresentation X₁.hom]
    [QuasiCompact X₁.hom] [GeometricallyIntegral X₁.hom]
    [Smooth X₂.hom] [IsSeparated X₂.hom] [LocallyOfFinitePresentation X₂.hom]
    [QuasiCompact X₂.hom] [GeometricallyIntegral X₂.hom]
    [Smooth X₃.hom] [IsSeparated X₃.hom] [LocallyOfFinitePresentation X₃.hom]
    [QuasiCompact X₃.hom] [GeometricallyIntegral X₃.hom]
    (A : ((X₁ ⨯ X₂) ⨯ X₃).left.Modules) [IsInvertible A] :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K) (_ : Module.Finite k K),
      ∃ N : (Limits.pullback (squareParameter X₁ X₂).hom
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))).Modules,
        IsInvertible N ∧
          Nonempty
            (squareDifferenceAfterBaseChange X₁ X₂ X₃
                (Spec.map (CommRingCat.ofHom (algebraMap k K)))
                ((tensorPullback (pullback.fst ((X₁ ⨯ X₂) ⨯ X₃).hom
                  (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj A) ≅
              (tensorPullback
                (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map
                  (squareProjection X₁ X₂ X₃)).left)).obj N) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
