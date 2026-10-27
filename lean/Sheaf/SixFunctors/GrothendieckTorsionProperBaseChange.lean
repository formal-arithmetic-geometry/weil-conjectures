/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B9
-/
module

public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Sheaf.SixFunctors.GrothendieckTorsionSheafProperBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Generators
import WeilConjectures.CategoryTheory.DerivedCategory.BoundedEssentiallySmall
import WeilConjectures.SixFunctors.Etale.Derived.Triangulated

/-! # Proper base change with Grothendieck abelian torsion coefficients -/

@[expose] public section

set_option autoImplicit false

universe u' u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
  [HasSmallSiteSheafify A]

/-- Proper base change on bounded complexes whose geometric homology stalks have finite
exponent. Source: the finite truncation argument in SGA 4 XVII, 4.3.2(ii), after the
sheaf-level proper-base-change comparison.

Proof: finite exponent of every geometric stalk is invariant under sheaf isomorphisms.
The sheaf-level theorem gives the comparison for a sheaf in degree zero, and compatibility
of the exchange transformation with shifts gives it in every single degree. Use the
library Postnikov decomposition of a bounded object into finite extensions of its single
homology objects. This decomposition is proved by induction on a finite cohomological
interval using truncation triangles. The isomorphism locus of the exchange is a strictly
full triangulated property, by the triangulated five lemma, so it contains those finite
extensions. No boundedness of the direct image is required.
(blueprint: lem-sf-grothendieck-torsion-proper-base-change). -/
theorem isIso_derivedBaseChangeMap_of_bounded_stalkwise_finite_exponent
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} [IsProper f]
    (sq : IsPullback g' f' f g)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (hK : _root_.DerivedCategory.TStructure.t.bounded K)
    (hT : ∀ (n : ℤ) (Ω : Type u) [Field Ω] [IsSepClosed Ω]
      (s : Spec (.of Ω) ⟶ X), ∃ N : ℕ, 0 < N ∧
        N • (𝟙 ((Scheme.pointSmallEtale s).sheafFiber.obj
          ((_root_.DerivedCategory.homologyFunctor _ n).obj K))) = 0) :
    IsIso ((derivedBaseChangeMap A sq.toCommSq).app K) := by
  let P : ObjectProperty (Sheaf X.smallEtaleTopology A) := fun F ↦
    ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X),
      ∃ N : ℕ, 0 < N ∧ N • (𝟙 ((Scheme.pointSmallEtale s).sheafFiber.obj F)) = 0
  have : P.IsClosedUnderIsomorphisms := by
    constructor
    intro F G e h Ω _ _ s
    obtain ⟨N, hN, hN₀⟩ := h Ω s
    refine ⟨N, hN, ?_⟩
    let i := (Scheme.pointSmallEtale s).sheafFiber.mapIso e
    apply (cancel_epi i.hom).1
    calc
      i.hom ≫ (N • 𝟙 _) = (N • 𝟙 _) ≫ i.hom := by simp
      _ = i.hom ≫ 0 := by rw [hN₀]; simp
  have hP : ∀ F, P F → IsIso ((derivedBaseChangeMap A sq.toCommSq).app
      ((_root_.DerivedCategory.singleFunctor _ 0).obj F)) :=
    fun F hF ↦ isIso_derivedBaseChangeMap_single_of_stalkwise_finite_exponent A sq F hF
  let τ := derivedBaseChangeMap A sq.toCommSq
  obtain ⟨d, hd⟩ := _root_.DerivedCategory.exists_iteratedExtensions_of_bounded P K hK hT
  apply _root_.DerivedCategory.iteratedExtensions_le P (Q := τ.isoLocus) ?_ d K hd
  rintro Z ⟨n, F, hF, ⟨e⟩⟩
  rw [NatTrans.isoLocus_iff, NatTrans.isIso_app_iff_of_iso τ e]
  rw [← NatTrans.isIso_app_iff_of_iso τ
    (((_root_.DerivedCategory.singleFunctors _).shiftIso (-n) n 0 (by omega)).app F)]
  change IsIso (τ.app (((_root_.DerivedCategory.singleFunctor _ 0).obj F)⟦-n⟧))
  rw [NatTrans.app_shift τ]
  have := hP F hF
  infer_instance

end AlgebraicGeometry.Etale
