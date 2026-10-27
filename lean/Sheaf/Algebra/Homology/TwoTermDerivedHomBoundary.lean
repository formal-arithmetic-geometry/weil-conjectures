/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q72
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-! # Derived Hom and the boundary of a two-term complex

Source: Stacks Project, Derived Categories, Tags 0149 and 06XS(1)
(blueprint: lem-sfb-two-term-derived-hom-boundary).

The complex `[M → F]` in degrees `-1,0` is Mathlib's cone of the degree-zero
single-complex map. The quotient is the negative of the cone triangle's last map;
this retains the positive projection onto `M[1]` with the prescribed cone signs.
All maps below are explicit compositions of Mathlib's canonical maps.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The canonical chain projection to the degree-zero cokernel of the differential.
It is zero on the shifted source summand and the cokernel projection on the target.
Source: Stacks Project, Tags 014E and 06XS(1)
(blueprint: lem-sfb-two-term-derived-hom-boundary). -/
noncomputable def twoTermCokernelProjection {M F : A} (d : M ⟶ F) :
    CochainComplex.mappingCone ((CochainComplex.singleFunctor A 0).map d) ⟶
      (CochainComplex.singleFunctor A 0).obj (cokernel d) :=
  CochainComplex.mappingCone.descShortComplex
    ((ShortComplex.mk d (cokernel.π d) (cokernel.condition d)).map
      (CochainComplex.singleFunctor A 0))

/-- The chain map with components `a,b` induced by a square of differentials.
Source: Stacks Project, Tag 014E, functoriality of the cone
(blueprint: lem-sfb-two-term-derived-hom-boundary). -/
noncomputable def twoTermSquareMap {M F M' F' : A} (d : M ⟶ F) (d' : M' ⟶ F')
    (a : M ⟶ M') (b : F ⟶ F') (h : d ≫ b = a ≫ d') :
    CochainComplex.mappingCone ((CochainComplex.singleFunctor A 0).map d) ⟶
      CochainComplex.mappingCone ((CochainComplex.singleFunctor A 0).map d') :=
  CochainComplex.mappingCone.map _ _
    ((CochainComplex.singleFunctor A 0).map a)
    ((CochainComplex.singleFunctor A 0).map b)
    (((CochainComplex.singleFunctor A 0).map_comp d b).symm.trans
      ((congrArg (CochainComplex.singleFunctor A 0).map h).trans
        ((CochainComplex.singleFunctor A 0).map_comp a d')))

variable [HasDerivedCategory.{w} A]

/-- The specified positive quotient `q : [M → F] → M[1]` in the derived category.
The cone triangle has last arrow `-q`, hence the explicit negation.
Source: Stacks Project, Tags 014E and 0149
(blueprint: lem-sfb-two-term-derived-hom-boundary). -/
noncomputable def twoTermQuotient {M F : A} (d : M ⟶ F) :
    Q.obj (CochainComplex.mappingCone ((CochainComplex.singleFunctor A 0).map d)) ⟶
      ((singleFunctor A 0).obj M)⟦(1 : ℤ)⟧ :=
  Q.map (-(CochainComplex.mappingCone.triangle
    ((CochainComplex.singleFunctor A 0).map d)).mor₃) ≫
      (Q.commShiftIso (1 : ℤ)).hom.app ((CochainComplex.singleFunctor A 0).obj M)

/-- The additive boundary `δ ↦ δ[1] ∘ q`, with target `Ext¹([M → F],G)`.
Source: Stacks Project, Tag 0149
(blueprint: lem-sfb-two-term-derived-hom-boundary). -/
noncomputable def twoTermBoundary {M F : A} (d : M ⟶ F) (G : A) :
    (M ⟶ G) →+
      (Q.obj (CochainComplex.mappingCone ((CochainComplex.singleFunctor A 0).map d)) ⟶
        ((singleFunctor A 0).obj G)⟦(1 : ℤ)⟧) :=
  (Preadditive.leftComp _ (twoTermQuotient d)).comp
    (((shiftFunctor (DerivedCategory A) (1 : ℤ)).mapAddHom).comp
      (singleFunctor A 0).mapAddHom)

/-- Precomposition with the canonical chain map to `coker(d)[0]`, after the single
embedding; the target is `Ext⁰([M → F],G)`, written as unshifted derived Hom.
Source: Stacks Project, Tag 06XS(1)
(blueprint: lem-sfb-two-term-derived-hom-boundary). -/
noncomputable def twoTermCokernelHom {M F : A} (d : M ⟶ F) (G : A) :
    (cokernel d ⟶ G) →+
      (Q.obj (CochainComplex.mappingCone ((CochainComplex.singleFunctor A 0).map d)) ⟶
        (singleFunctor A 0).obj G) :=
  (Preadditive.leftComp _ (Q.map (twoTermCokernelProjection d))).comp
    (singleFunctor A 0).mapAddHom

/-- The boundary sequence is exact at `Hom(M,G)` without any projectivity or
injectivity assumptions.
Source: Stacks Project, Tag 0149
(blueprint: lem-sfb-two-term-derived-hom-boundary).

Proof: the cone triangle of `d[0]` has arrows `d,i,-q`. Rotate it, and change sign
on its third vertex to obtain the distinguished triangle `F[0] → K → M[1] → F[1]`
with maps `i,q,d[1]` (def-weil-abstract-derived-category and
 def-weil-triangulated-category). Apply clause (ii) of
lem-weil-pbc-hom-out-of-triangle-exact with target `G[1]`. A boundary-zero `δ` then
factors through `d[1]`; undo the shift and use
lem-weil-pbc-derived-single-fully-faithful to obtain `δ = θ ∘ d`. Conversely,
`d[1] ∘ q` is null-homotopic with sole nonzero homotopy component `h⁰ = 1_F`, so
it vanishes after localization, and every `θ ∘ d` has zero boundary. -/
theorem twoTermBoundary_exact {M F : A} (d : M ⟶ F) (G : A) :
    Function.Exact (Preadditive.leftComp G d) (twoTermBoundary d G) := by
  sorry

/-- The canonical cokernel-induced additive map on degree-zero derived Hom is bijective.
Source: Stacks Project, Tag 06XS(1)
(blueprint: lem-sfb-two-term-derived-hom-boundary).

Proof: put `I = im(d)` and `L = [M ↠ I]`. The kernel of `K → coker(d)[0]` is `L`:
in degree `-1` its sequence is `0 → M → M → 0`, and in degree zero it is
`0 → I → F → coker(d) → 0` (def-sp-abelian). Apply
lem-weil-pbc-complex-ses-triangle. Since `M → I` is epic, `Hʲ(L)=0` for `j ≥ 0`;
thus `L` lies in `D^{≤-1}` and `L[1]` in `D^{≤-2}`. The standard t-structure
(def-sbc-standard-tstructure-derived-category and def-weil-t-structure) gives
`Hom(L,G[0]) = Hom(L[1],G[0]) = 0`. Clause (i) of
lem-weil-pbc-hom-out-of-triangle-exact gives existence of a factorization through
the cokernel projection, and clause (ii), applied to the difference of two
factorizations, gives uniqueness. Finally use
lem-weil-pbc-derived-single-fully-faithful to identify maps from `coker(d)[0]` with
actual maps from `coker(d)`. All compositions are additive. -/
theorem twoTermCokernelHom_bijective {M F : A} (d : M ⟶ F) (G : A) :
    Function.Bijective (twoTermCokernelHom d G) := by
  sorry

/-- The additive isomorphism induced by the specified cokernel chain projection.
Its inverse is the unique factorization established by `twoTermCokernelHom_bijective`.
Source: Stacks Project, Tag 06XS(1)
(blueprint: lem-sfb-two-term-derived-hom-boundary). -/
noncomputable def twoTermCokernelHomEquiv {M F : A} (d : M ⟶ F) (G : A) :
    (cokernel d ⟶ G) ≃+
      (Q.obj (CochainComplex.mappingCone ((CochainComplex.singleFunctor A 0).map d)) ⟶
        (singleFunctor A 0).obj G) :=
  AddEquiv.ofBijective (twoTermCokernelHom d G) (twoTermCokernelHom_bijective d G)

/-- All three arrows commute with postcomposition in the coefficient object.
Source: Stacks Project, Tags 0149 and 06XS(1)
(blueprint: lem-sfb-two-term-derived-hom-boundary).

Proof: the first identity is associativity. For the second, functoriality of the
single embedding and of shift identifies `(g ∘ δ)[1]` with `g[1] ∘ δ[1]`, and
associativity moves `q` to the front. For the third, the equivalence's forward map
is the single embedding followed by precomposition with the fixed cokernel chain
projection; functoriality and associativity again apply. Naturality of the inverse
follows from uniqueness of the cokernel factorization. This is step 6 of the node. -/
theorem twoTermDerivedHom_postcomp {M F G G' : A} (d : M ⟶ F) (g : G ⟶ G') :
    (∀ θ : F ⟶ G, (d ≫ θ) ≫ g = d ≫ (θ ≫ g)) ∧
    (∀ δ : M ⟶ G, twoTermBoundary d G' (δ ≫ g) =
      twoTermBoundary d G δ ≫ ((singleFunctor A 0).map g)⟦(1 : ℤ)⟧') ∧
    (∀ γ : cokernel d ⟶ G, twoTermCokernelHomEquiv d G' (γ ≫ g) =
      twoTermCokernelHomEquiv d G γ ≫ (singleFunctor A 0).map g) := by
  sorry

/-- All arrows commute with a commutative square of differentials; the chain map
is the canonical cone map with components `a,b`, and the map on cokernels is canonical.
Source: Stacks Project, Tags 014E, 0149 and 06XS(1)
(blueprint: lem-sfb-two-term-derived-hom-boundary).

Proof: for the first arrow, substitute `d ≫ b = a ≫ d'` and associate. The cone map
`u` has components `a,b`, so its positive quotient satisfies `u ≫ q' = q ≫ a[1]`.
Apply the single embedding, shift functoriality and associativity to obtain the
boundary identity. The cokernel universal property gives `π ≫ c = b ≫ π'`.
The chain projections consequently satisfy `u ≫ p' = p ≫ c[0]`, checked on both
summands of the cone. Precompose `γ[0]` to obtain the last identity. The forward
map of the equivalence is precisely precomposition by `p`; uniqueness then gives
naturality of its inverse too. This is step 6 of the node. -/
theorem twoTermDerivedHom_square {M F M' F' : A} (d : M ⟶ F) (d' : M' ⟶ F')
    (a : M ⟶ M') (b : F ⟶ F') (h : d ≫ b = a ≫ d') (G : A) :
    (∀ θ : F' ⟶ G, d ≫ (b ≫ θ) = a ≫ (d' ≫ θ)) ∧
    (∀ δ : M' ⟶ G, twoTermBoundary d G (a ≫ δ) =
      Q.map (twoTermSquareMap d d' a b h) ≫ twoTermBoundary d' G δ) ∧
    (∀ γ : cokernel d' ⟶ G,
      twoTermCokernelHomEquiv d G (cokernel.map d d' a b h ≫ γ) =
        Q.map (twoTermSquareMap d d' a b h) ≫ twoTermCokernelHomEquiv d' G γ) := by
  sorry

end DerivedCategory
