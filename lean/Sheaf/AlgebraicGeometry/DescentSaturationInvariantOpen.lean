module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
import Mathlib.AlgebraicGeometry.PullbackCarrier
import WeilConjectures.AlgebraicGeometry.DescentOrbitSaturated
import WeilConjectures.AlgebraicGeometry.EffectiveDescent.Invariant

/-!
# Restriction of descent to a saturated open

Source: Stacks Project, Tag 02W8, second paragraph of the proof.
(blueprint: lem-trf-descent-saturation-invariant-open).

The existing transport presentation of descent data includes the isomorphism over the
double base and its cocycle. The restricted datum is required to intertwine every transport
with the inclusion of the saturated open.
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Over.DescentDatum

/-- Restriction of a descent datum to the open saturation of an affine open.

Source: Stacks Project, Tag 02W8, second paragraph of the proof.
(blueprint: lem-trf-descent-saturation-invariant-open).

Proof:
1. Write R = V ×_B A, s = pr_V, and t = D.toHom. The transport laws of
   def-pd-descent-datum give identity, inverse and composition for this relation.
2. The map C ×_B A → R is the pullback of C.ι along s. By
   lem-weil-pbc-base-change-image its image is s⁻¹(C). Hence the given image W
   is the union of the orbits t(s⁻¹({c})) for c in C.
3. Apply lem-pd-descent-orbit-saturated to every c. Taking unions yields
   s⁻¹(W) = t⁻¹(W), for all scheme points, without residue-field restrictions.
4. By lem-weil-pbc-open-immersion-base-change the maps W ×_B A → V ×_B A and
   A ×_B W → A ×_B V are open immersions. Their images are the corresponding
   inverse images of W by lem-weil-pbc-base-change-image. The equality of step 3
   allows the descent isomorphism and its inverse to factor through these opens,
   using lem-weil-pbc-morphism-factors-through-open-subscheme.
5. Cancel these inclusions using lem-weil-pbc-open-immersion-monomorphism to see
   that the factors are inverse and over A ×_B A. Evaluate the factorization on
   every test scheme to obtain the asserted transport equality. Apply it twice
   and cancel W.ι to inherit the cocycle, giving the stated descent datum.
-/
theorem exists_descentDatum_saturation_open
    {A B : Scheme.{u}} [IsAffine A] [IsAffine B]
    (p : A ⟶ B) [Flat p] [Surjective p] [LocallyOfFinitePresentation p]
    [QuasiCompact p] [QuasiSeparated p] {V : Over A}
    (D : Over.DescentDatum p V) (C : V.left.Opens) (_hC : IsAffineOpen C)
    (W : V.left.Opens)
    (_hW : (W : Set V.left) = Set.range
      (pullback.map (C.ι ≫ V.hom ≫ p) p (V.hom ≫ p) p C.ι (𝟙 A) (𝟙 B)
        (by simp) (by simp) ≫ D.toHom)) :
    ∃ E : Over.DescentDatum p (Over.mk (W.ι ≫ V.hom)),
      ∀ (Z : Scheme.{u}) (a b : Z ⟶ A) (h : a ≫ p = b ≫ p)
        (v : Over.mk a ⟶ Over.mk (W.ι ≫ V.hom)),
        (E.transport a b h v).left ≫ W.ι =
          (D.transport a b h (v ≫ Over.homMk W.ι rfl)).left := by
  let m := pullback.map (C.ι ≫ V.hom ≫ p) p (V.hom ≫ p) p C.ι (𝟙 A) (𝟙 B)
    (by simp) (by simp)
  have hm : Set.range m = pullback.fst (V.hom ≫ p) p ⁻¹' (C : Set V.left) := by
    dsimp [m]
    rw [Scheme.Pullback.range_map]
    simp
  have hW : (W : Set V.left) =
      D.toHom '' (pullback.fst (V.hom ≫ p) p ⁻¹' (C : Set V.left)) := by
    rw [_hW]
    change Set.range (D.toHom ∘ m) = _
    rw [Set.range_comp, hm]
  have hInv : D.IsInvariant W := by
    rw [D.isInvariant_iff]
    intro r hr
    change D.toHom r ∈ (W : Set V.left)
    change pullback.fst (V.hom ≫ p) p r ∈ (W : Set V.left) at hr
    rw [hW] at hr ⊢
    obtain ⟨r₀, hr₀, he⟩ := hr
    have hs := D.descent_orbit_saturated (pullback.fst (V.hom ≫ p) p)
      (pullback.snd (V.hom ≫ p) p) D.toHom (IsPullback.of_hasPullback _ _) rfl
      (pullback.fst (V.hom ≫ p) p r₀)
    have horbit : pullback.fst (V.hom ≫ p) p r ∈
        D.toHom '' (pullback.fst (V.hom ≫ p) p ⁻¹'
          {pullback.fst (V.hom ≫ p) p r₀}) := ⟨r₀, rfl, he⟩
    have ht : D.toHom r ∈ D.toHom '' (pullback.fst (V.hom ≫ p) p ⁻¹'
        {pullback.fst (V.hom ≫ p) p r₀}) := by
      exact (Set.ext_iff.mp hs r).mp horbit
    obtain ⟨r₁, hr₁, ht₁⟩ := ht
    refine ⟨r₁, ?_, ht₁⟩
    change pullback.fst (V.hom ≫ p) p r₁ ∈ C
    change pullback.fst (V.hom ≫ p) p r₁ = pullback.fst (V.hom ≫ p) p r₀ at hr₁
    rw [hr₁]
    exact hr₀
  refine ⟨D.restrict W hInv, ?_⟩
  intro Z a b h v
  exact D.restrict_transport_left_ι W hInv a b h v

end CategoryTheory.Over.DescentDatum
