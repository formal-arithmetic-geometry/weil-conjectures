/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import WeilConjectures.AlgebraicGeometry.FlatTelescopeStageMap
public import Sheaf.AlgebraicGeometry.BoundedFlatShiftRepresentative
import Sheaf.AlgebraicGeometry.FlatTelescopeSumModels
import Sheaf.AlgebraicGeometry.FlatComparisonPreservesCountableCoproducts

/-! # The normalized comparison on sums of bounded-flat stages

Source: the finite-partial-sum argument of step 1 of
lem-sc-flat-telescope-normalization-unshifted-is-iso, expanding Stacks Tags 06YS and 06YJ.
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
namespace AlgebraicGeometry

/-- The sum of bounded-flat stages has a literal telescope representative on which
the comparison is invertible.
This concerns the sum of the stages, not the cone of their transition map.
No transition maps, normalized shifted-unit isomorphism, or shift equation are inputs.

Source: step 1 of lem-sc-flat-telescope-normalization-unshifted-is-iso;
Stacks Tags 06YS and 06YJ, the sum part of the telescope argument, expanded by the agent.

Proof. Let B_n be the finite sum of E_0,...,E_n and let its transition be the split
inclusion. The finite maximum of the upper bounds bounds B_n, and finite sums of
flat modules are flat. Define R to be the cone of one minus transition on the sum
of the B_n. The split telescope augmentation R -> sum E is a homotopy equivalence:
on each E_j summand the tail of the partial-sum tower is the constant identity tower;
write D_j = sum over n >= j of E_j. The augmentation D_j -> E_j sums
the coordinates and has a section into the first coordinate. One minus successor
is an isomorphism from D_j to the augmentation kernel: its inverse takes finite
partial sums, whose tail vanishes because the input coordinates sum to zero.
All these maps commute with the differentials. The split sequence therefore
identifies its cone with E_j plus a contractible cone of an identity. Taking
the direct sum of these splittings gives the required cochain homotopy equivalence.
Thus the homotopy quotient of sum E is isomorphic to qR.
Represent each bounded E_j by its constant identity telescope. Its terms and cone
remain bounded above and flat, since countable sums preserve flatness and a cone's
terms are finite sums. It satisfies the bounded normalization hypothesis. Its augmentation
is a homotopy equivalence to E_j. Transport alpha through these isomorphisms.
Naturality makes this transport independent of the presentation and intertwines every inclusion.
The functors Qh, derived pullback, and termwise tensor pullback preserve the relevant
countable coproducts: localization uses exact coproducts, derived pullback is a left
adjoint, and tensor pullback is a left adjoint. The coproduct universal property
therefore identifies the transported alpha on sum E with the direct sum of its
invertible stage components. Transfer the resulting isomorphism along the split telescope
augmentation to alpha at qR. The construction also covers the zero tower
and the empty scheme. No uniform upper bound on all E_n is used.
(blueprint: lem-sc-flat-telescope-sum-comparison-is-iso). -/
theorem exists_flat_telescope_sum_comparison_isIso
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (f : Z ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [Functor.Monoidal (derivedPullback f)]
    [(Scheme.Modules.tensorPullback f).Additive]
    (α : ∀ X : HomotopyCategory
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ),
        flatTelescopeShiftRepresentative Y X →
          ((DerivedCategory.Qh ⋙ derivedPullback f).obj X ⟶
            ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
              (DerivedCategory.Qh : HomotopyCategory
                (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
                schemeDerivedCategory Z)).obj X))
    (hαnat : (∀ (X X' : HomotopyCategory
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ))
          (hX : flatTelescopeShiftRepresentative Y X) (hX' : flatTelescopeShiftRepresentative Y X')
          (s : X ⟶ X'),
          (DerivedCategory.Qh ⋙ derivedPullback f).map s ≫ (α X' hX') =
            (α X hX) ≫
              ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
                (DerivedCategory.Qh : HomotopyCategory
                  (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
                  schemeDerivedCategory Z)).map s))
    (hαbounded : ∀ (X : HomotopyCategory
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ))
      (hX : flatTelescopeShiftRepresentative Y X),
      boundedFlatShiftRepresentative Y X → IsIso (α X hX))
    (E : ℕ → CochainComplex
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (hb : ∀ n : ℕ, ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero ((E n).X i))
    (hf : ∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((E n).X i)) :
    ∃ (R : CochainComplex
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
      (hR : isFlatTelescope Y R),
      Nonempty ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj (∐ E) ≅
        (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj R) ∧
      IsIso (α ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj R)
        ⟨R, hR, Or.inl rfl⟩) := by
  classical
  obtain ⟨R, hR, T, hT, s, e, hTb, hc⟩ := exists_flat_telescope_sum_models Y E hb hf
  let q := HomotopyCategory.quotient
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ)
  let L := DerivedCategory.Qh ⋙ derivedPullback f
  let G := (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    (DerivedCategory.Qh : HomotopyCategory
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
      schemeDerivedCategory Z)
  let hR' : flatTelescopeShiftRepresentative Y (q.obj R) := ⟨R, hR, Or.inl rfl⟩
  let hT' (n : ℕ) : flatTelescopeShiftRepresentative Y (q.obj (T n)) :=
    ⟨T n, hT n, Or.inl rfl⟩
  obtain ⟨hL, hG⟩ := flat_comparison_preserves_countable_coproducts f
  let : PreservesColimitsOfShape (Discrete ℕ) L := hL
  let : PreservesColimitsOfShape (Discrete ℕ) G := hG
  have cL : IsColimit (Cofan.mk (L.obj (q.obj R)) (fun n ↦ L.map (s n))) :=
    isColimitCofanMkObjOfIsColimit L _ _ hc.some
  have cG : IsColimit (Cofan.mk (G.obj (q.obj R)) (fun n ↦ G.map (s n))) :=
    isColimitCofanMkObjOfIsColimit G _ _ hc.some
  let a := α (q.obj R) hR'
  let b (n : ℕ) := α (q.obj (T n)) (hT' n)
  have (n : ℕ) : IsIso (b n) := hαbounded _ (hT' n) (hTb n)
  have hn (n : ℕ) : L.map (s n) ≫ a = b n ≫ G.map (s n) :=
    hαnat _ _ (hT' n) hR' (s n)
  let d : G.obj (q.obj R) ⟶ L.obj (q.obj R) :=
    Cofan.IsColimit.desc cG (fun n ↦ inv (b n) ≫ L.map (s n))
  have hd (n : ℕ) : G.map (s n) ≫ d = inv (b n) ≫ L.map (s n) :=
    Cofan.IsColimit.fac cG _ n
  have had : a ≫ d = 𝟙 _ := by
    apply Cofan.IsColimit.hom_ext cL
    intro n
    change L.map (s n) ≫ (a ≫ d) = L.map (s n) ≫ 𝟙 _
    rw [← Category.assoc, hn, Category.assoc, hd]
    simp
  have hda : d ≫ a = 𝟙 _ := by
    apply Cofan.IsColimit.hom_ext cG
    intro n
    change G.map (s n) ≫ (d ≫ a) = G.map (s n) ≫ 𝟙 _
    rw [← Category.assoc, hd, Category.assoc, hn]
    simp
  refine ⟨R, hR, e, ?_⟩
  exact ⟨⟨d, had, hda⟩⟩

end AlgebraicGeometry
