/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q16
-/
module

public import Sheaf.AlgebraicGeometry.GroupScheme.RelativeSL2Presheaf
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Gabber splitting of relative SL2 central extensions

Source: Conrad, Reductive group schemes, Proposition 4.3.1 and proof, printed pp.126--131
(blueprint: lem-sfb-relative-sl2-central-extension-splitting).

The auxiliary coefficient universe is arbitrary. The standard group universe-lift
functor permits extensions valued in groups larger than the scheme Hom sets.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite
open scoped MonObj

namespace AlgebraicGeometry

/-- A central fppf extension of relative SL2 by a separated commutative S-group
has a unique splitting, the canonical product map is an isomorphism, and the middle
sheaf is representable. Under any group-scheme representations of the source and target,
the splitting is represented by a group-scheme morphism.

Source: Conrad, Proposition 4.3.1, printed pp.126--131
(blueprint: lem-sfb-relative-sl2-central-extension-splitting).

Proof (the seven steps of the DAG node):
1. The commutator pairing on the preimage D' of the diagonal torus descends to a
   bimultiplicative map D x D to Z. Use lem-sfb-relative-torus-bimultiplicative-vanishing
   and lem-sfb-sl2-lifted-root-gauss-relations to see that D' is commutative.
2. Centrality descends conjugation to an SL2 action on E. The diagonal torus acts
   on the upper and lower root groups with weights 2 and -2. Apply
   lem-sfb-weighted-additive-central-extension to obtain equivariant lifts x',y'.
3. Set g'(t)=y'(-1/t)x'(t)y'(-1/t) and h'(t)=g'(t)g'(1) inverse. The hypotheses
   of lem-sfb-sl2-lifted-root-gauss-relations now hold. It supplies the lifted torus
   homomorphism and both Gauss relations, including zero and nonunit parameters.
4. On the open cell define sigma(x(u)h(s)y(v))=x'(u)h'(s)y'(v). If w=1+va is
   invertible, the inverse Gauss relation rewrites the product with coordinates
   (u+s squared a/w, st/w, b+t squared v/w). These are also the matrix product
   coordinates downstairs. Thus sigma is partially multiplicative and lifts the cell.
5. Use lem-sfb-sl2-open-cell-sheaf-extension to extend sigma to s. Its uniqueness
   applied downstairs gives p s = id.
6. Two splittings differ by a homomorphism SL2 to Z. Conjugation invariance and
   the final assertion of lem-sfb-weighted-additive-central-extension kill both root
   restrictions, hence the torus and open cell. Uniqueness in
   lem-sfb-sl2-open-cell-sheaf-extension makes the ratio trivial everywhere.
7. Centrality makes (z,g) mapping to i(z)s(g) a group map. Its inverse sends e to
   (z,p(e)), where i(z)=e s(p(e)) inverse; the kernel identification determines z
   uniquely and naturally. Therefore the product map is a natural group isomorphism.
   The product S-scheme represents E. Yoneda represents the splitting under any
   chosen group-scheme representations, and its group identities give IsMonHom.
   Neither smoothness nor invertibility of 2 was used. -/
theorem relativeSL2_central_extension_splitting
    {S : Scheme.{u}} (Z : Grp (Over S)) [IsCommMonObj Z.X]
    [IsClosedImmersion (pullback.diagonal Z.X.hom)]
    (E : Sheaf (Scheme.fppfTopology.over S) GrpCat.{max u v})
    (i : (yonedaGrp.obj Z ⋙ GrpCat.uliftFunctor.{v, u}) ⟶ E.obj)
    (p : E.obj ⟶ relativeSL2Presheaf S ⋙ GrpCat.uliftFunctor.{v, u})
    (hi : ∀ U : (Over S)ᵒᵖ, Function.Injective (i.app U))
    (hker : ∀ (U : (Over S)ᵒᵖ) (e : E.obj.obj U),
      p.app U e = 1 ↔ ∃ z, i.app U z = e)
    (hp : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) p)
    (hcentral : ∀ (U : (Over S)ᵒᵖ)
      (z : (yonedaGrp.obj Z ⋙ GrpCat.uliftFunctor.{v, u}).obj U) (e : E.obj.obj U),
      i.app U z * e = e * i.app U z) :
    ∃ s : (relativeSL2Presheaf S ⋙ GrpCat.uliftFunctor.{v, u}) ⟶ E.obj,
      s ≫ p = 𝟙 _ ∧
      (∀ s' : (relativeSL2Presheaf S ⋙ GrpCat.uliftFunctor.{v, u}) ⟶ E.obj,
        s' ≫ p = 𝟙 _ → s' = s) ∧
      (∀ U : (Over S)ᵒᵖ,
        ∃ e : ((yonedaGrp.obj Z ⋙ GrpCat.uliftFunctor.{v, u}).obj U ×
            (relativeSL2Presheaf S ⋙ GrpCat.uliftFunctor.{v, u}).obj U) ≃* E.obj.obj U,
          ∀ z g, e (z, g) = i.app U z * s.app U g) ∧
      (E.obj ⋙ forget GrpCat).IsRepresentable ∧
      (∀ (G H : Grp (Over S))
        (α : (yonedaGrp.obj G ⋙ GrpCat.uliftFunctor.{v, u}) ≅
          relativeSL2Presheaf S ⋙ GrpCat.uliftFunctor.{v, u})
        (β : (yonedaGrp.obj H ⋙ GrpCat.uliftFunctor.{v, u}) ≅ E.obj),
        ∃ t : G ⟶ H,
          Functor.whiskerRight (yonedaGrp.map t) GrpCat.uliftFunctor.{v, u} ≫ β.hom =
            α.hom ≫ s) := by
  sorry

end AlgebraicGeometry
