module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
import Mathlib.CategoryTheory.Yoneda
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.IsFiniteOfFpqcCover
import WeilConjectures.AlgebraicGeometry.FlatOfFpqcCover
import WeilConjectures.AlgebraicGeometry.LocallyOfFinitePresentationFpqcDescent

/-!
# Finite locally free maps in diagrams of group extensions

Source: Stacks Project, Descent, Tag 02VO; the group-extension consequence is the
fppf-local lifting and translation argument recorded in the DAG.
(blueprint: lem-sfb-finite-flat-homomorphism-extensions)
-/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry

/-- In a morphism of two fppf-exact extensions of commutative group schemes over `B`,
finite locally free surjections on the kernels and quotients imply the same for the middle map.
The indices `0, 1 : Fin 2` label the two rows. The multiplicative identity `1` on sections
is the zero section in the additive notation of the source. No geometric regularity or
characteristic assumption is made.

Source: Stacks Project, Descent, Tag 02VO, and the group-extension argument in the DAG
(blueprint: lem-sfb-finite-flat-homomorphism-extensions).

Proof:
1. Form `P = Q₁ ×[Q₂] E₂` (`def-pc-fibre-product`). The second square gives
   `h = (q₁, v) : E₁ ⟶ P` and factors `v` as `h` followed by the base change of `w`.
2. Lift the identity section of `Q₁` fppf locally using the first row's local lifting
   hypothesis. Pull that cover back to `P` (`lem-trf-fppf-covering-base-change`).
3. On a member of the pulled-back cover, choose a lift `e` in `E₁`. Exactness of the
   second row gives the unique `k₂` with `j₂(k₂) = y - v(e)`. Translation by `e`
   identifies the pullback of `h` with the pullback of `u` along `k₂`: the inverse
   subtracts `e` and uses exactness of the first row. Injectivity of `j₂` verifies
   the remaining equation. The formulas commute with restriction, so Yoneda
   (`lem-galois-yoneda-fully-faithful`) gives an isomorphism of schemes over the cover.
4. The local models of `h` and the second projection of `P` are finite locally free
   surjections by base change (`lem-weil-pbc-finite-morphism-permanence`,
   `lem-weil-pbc-flat-morphism-base-change`, `lem-weil-pbc-qcqs-morphism-permanence`,
   `lem-weil-pbc-surjective-base-change`).
5. The fppf cover is fpqc (`lem-trf-fppf-covering-is-fpqc`). Descend finiteness,
   flatness and local finite presentation (`lem-weil-pbc-fpqc-descend-finite`,
   `lem-weil-pbc-fpqc-descend-flat`,
   `lem-weil-pbc-fpqc-descend-locally-finite-presentation`) to `h`. For any point of
   `P`, choose a point of the cover above it and then a point of the local model
   above that point. Projection gives a point of `E₁`, proving surjectivity of `h`.
6. Compose the two finite locally free maps
   (`lem-trf-finite-locally-free-composition`) and compose their surjections. -/
theorem finiteLocallyFree_surjective_of_extension_diagram
    (B : Scheme.{u}) (K E Q : Fin 2 → Over B)
    [∀ i : Fin 2, GrpObj (K i)] [∀ i : Fin 2, IsCommMonObj (K i)]
    [∀ i : Fin 2, GrpObj (E i)] [∀ i : Fin 2, IsCommMonObj (E i)]
    [∀ i : Fin 2, GrpObj (Q i)] [∀ i : Fin 2, IsCommMonObj (Q i)]
    (j : ∀ i : Fin 2, K i ⟶ E i) (q : ∀ i : Fin 2, E i ⟶ Q i)
    [∀ i : Fin 2, IsMonHom (j i)] [∀ i : Fin 2, IsMonHom (q i)]
    (hkernel : ∀ (i : Fin 2) (U : Over B),
      Function.Injective (fun k : U ⟶ K i ↦ k ≫ j i) ∧
        ∀ e : U ⟶ E i, e ≫ q i = 1 ↔ ∃ k : U ⟶ K i, k ≫ j i = e)
    (hlift : ∀ (i : Fin 2) (U : Over B) (x : U ⟶ Q i),
      ∃ (I : Type u) (V : I → Over B) (p : ∀ a : I, V a ⟶ U),
        Presieve.ofArrows (fun a ↦ (V a).left) (fun a ↦ (p a).left) ∈
          Scheme.fppfPrecoverage U.left ∧
        ∀ a : I, ∃ e : V a ⟶ E i, e ≫ q i = p a ≫ x)
    (u : K 0 ⟶ K 1) (v : E 0 ⟶ E 1) (w : Q 0 ⟶ Q 1)
    [IsMonHom u] [IsMonHom v] [IsMonHom w]
    (hleft : j 0 ≫ v = u ≫ j 1) (hright : v ≫ q 1 = q 0 ≫ w)
    (hu : Scheme.Hom.IsFiniteLocallyFree u.left) (hsu : Surjective u.left)
    (hw : Scheme.Hom.IsFiniteLocallyFree w.left) (hsw : Surjective w.left) :
    Scheme.Hom.IsFiniteLocallyFree v.left ∧ Surjective v.left := by
  sorry

end AlgebraicGeometry
