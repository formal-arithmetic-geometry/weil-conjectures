/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.AlgebraicGeometry.CoherentThickeningSystem
public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.ClosedImmersionUnitQuotient

/-! # Completion comparison from a normalized restriction functor

Source: Stacks Project, Remark 088F, Lemma 087T and equation 0880.
(blueprint: lem-weil-pbc-completion-from-restriction).
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

noncomputable section

set_option autoImplicit false

/-- A restriction functor with unit-normalized pullback comparisons induces the
canonical comparison with completion.
Source: Stacks Project, Remark 088F, Lemma 087T and equation 0880.
(blueprint: lem-weil-pbc-completion-from-restriction).

Proof:
For each coherent F and n, closedImmersion_unit_quotient applied to j_n identifies
F/J^(n+1)F with j_(n,*)j_n^*F. Identify the iterated ideal-module product defining
formalModuleQuotient with multiplication by J^(n+1), by induction on n using
associativity of multiplication (equivalently its affine tensor calculation).
Transport the quotient identification from the canonical tensor-pullback adjunction
to aj_n by the unit-normalized uniqueness isomorphism of left adjoints. Compose
with the inverse of j_(n,*)(r_n,F) and then the inverse of beta_n,R(F).
These are isomorphisms from the terms of completion(F) to the terms of Phi(R(F)).
The transition hypothesis for Phi, the comparison equation hr for R, and the unit
equation hc imply that adjacent transition squares commute after precomposition
with the quotient projection F -> F/J^(n+2)F. This map is epi, so the squares commute.
Every order map of natural numbers factors into adjacent maps, so the termwise
maps and their inverses define an isomorphism of inverse systems. Naturality in F
follows from naturality of quotient maps, adjunction units, beta and r, again
canceling the quotient projections. Lift this natural isomorphism through the full
subcategory of coherent formal modules. The definition of its terms gives the
asserted quotient-projection equation. No arbitrary existence witness is used to
define an object: R is supplied, and all quotient maps are uniquely determined.
-/
theorem completion_from_restriction {A : Type v} [CommRing A] [IsNoetherianRing A]
    {X : Scheme.{v}} (f : X ⟶ Spec (CommRingCat.of A))
    [LocallyOfFiniteType f] [QuasiCompact f] (I : Ideal A)
    (i : ∀ n : ℕ, pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))) ⟶
        pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))
    (hi : ∀ n : ℕ,
      i n ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1))))) =
          pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))
    (hi₂ : ∀ n : ℕ,
      i n ≫ pullback.snd f
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1))))) =
      pullback.snd f
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))) ≫
          Spec.map (CommRingCat.ofHom
            (Ideal.Quotient.factor (Ideal.pow_le_pow_right (I := I) (Nat.le_succ (n + 1))))))
    (ai : ∀ n : ℕ, Scheme.Modules.tensorPullback (i n) ⊣ Scheme.Modules.pushforward (i n))
    (aj : ∀ n : ℕ, Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (I ^ (n + 1)))))) ⊣
      Scheme.Modules.pushforward (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (I ^ (n + 1)))))))
    [hX : IsNoetherian X]
    (hgeom : (∀ n : ℕ, IsClosedImmersion (pullback.fst f
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (I ^ (n + 1)))))) ∧
        (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))).ker =
            (Scheme.IdealSheafData.ofIdealTop (I.map (Scheme.ΓSpecIso (CommRingCat.of
            A)).inv.hom)).comap f ^ (n + 1)))
    (Φ : CoherentThickeningSystem (fun n ↦ pullback f (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (I ^ (n + 1)))))) i ⥤
          @CoherentFormalModule X hX ((Scheme.IdealSheafData.ofIdealTop (I.map (Scheme.ΓSpecIso
              (CommRingCat.of A)).inv.hom)).comap f))
        (β : ∀ n : ℕ,
          Φ ⋙ ObjectProperty.ι (IsCoherentFormalModule ((Scheme.IdealSheafData.ofIdealTop (I.map
              (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f)) ⋙
            (CategoryTheory.evaluation ℕᵒᵖ X.Modules).obj (op n) ≅
          CoherentThickeningSystem.evaluation (fun n ↦ pullback f (Spec.map (CommRingCat.ofHom
              (Ideal.Quotient.mk (I ^ (n + 1)))))) i n ⋙
            Scheme.Modules.pushforward (pullback.fst f (Spec.map (CommRingCat.ofHom
                (Ideal.Quotient.mk (I ^ (n + 1)))))))
    (htransition : (∀ (M : CoherentThickeningSystem (fun n ↦ pullback f (Spec.map (CommRingCat.ofHom
            (Ideal.Quotient.mk (I ^ (n + 1)))))) i) (n : ℕ),
          (((Φ.obj M).obj).map (homOfLE (Nat.le_succ n)).op) ≫ (β n).hom.app M =
          (β (n + 1)).hom.app M ≫
            (Scheme.Modules.pushforward (pullback.fst f (Spec.map (CommRingCat.ofHom
                (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))).map
              ((ai n).homEquiv _ _ (M.comparison n).hom) ≫
            (Scheme.Modules.pushforwardComp (i n) (pullback.fst f (Spec.map (CommRingCat.ofHom
                (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))).hom.app
              (M.term n) ≫
            (Scheme.Modules.pushforwardCongr (hi n)).hom.app (M.term n)))
    (c : ∀ n : ℕ,
            Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
                (Ideal.Quotient.mk (I ^ (n + 1 + 1)))))) ⋙
              Scheme.Modules.tensorPullback (i n) ≅
            Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
                (Ideal.Quotient.mk (I ^ (n + 1)))))))
    (R : CoherentModules X ⥤ CoherentThickeningSystem (fun n ↦ pullback f (Spec.map
              (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))) i)
          (r : ∀ n : ℕ, R ⋙ CoherentThickeningSystem.evaluation (fun n ↦ pullback f (Spec.map
              (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))) i n ≅
            ObjectProperty.ι (RingedSpace.IsCoherent X.toRingedSpace) ⋙
              Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
                  (Ideal.Quotient.mk (I ^ (n + 1)))))))
    (hc : ∀ (F : X.Modules) (n : ℕ),
            (aj (n + 1)).unit.app F ≫
              (Scheme.Modules.pushforward (pullback.fst f (Spec.map (CommRingCat.ofHom
                  (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))).map
                ((ai n).unit.app
                  ((Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
                      (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))).obj F)) ≫
              (Scheme.Modules.pushforwardComp (i n) (pullback.fst f (Spec.map (CommRingCat.ofHom
                  (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))).hom.app
                ((Scheme.Modules.tensorPullback (i n)).obj
                  ((Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
                      (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))).obj F)) ≫
              (Scheme.Modules.pushforwardCongr (hi n)).hom.app
                ((Scheme.Modules.tensorPullback (i n)).obj
                  ((Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
                      (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))).obj F)) ≫
              (Scheme.Modules.pushforward (pullback.fst f (Spec.map (CommRingCat.ofHom
                  (Ideal.Quotient.mk (I ^ (n + 1))))))).map ((c n).hom.app F) =
            (aj n).unit.app F)
    (hr : ∀ (F : CoherentModules X) (n : ℕ),
            ((R.obj F).comparison n).hom ≫ (r n).hom.app F =
              (Scheme.Modules.tensorPullback (i n)).map ((r (n + 1)).hom.app F) ≫
                (c n).hom.app F.obj) :
    ∃ (ρ : @completion X hX ((Scheme.IdealSheafData.ofIdealTop (I.map (Scheme.ΓSpecIso
              (CommRingCat.of A)).inv.hom)).comap f) ≅ R ⋙ Φ),
          (∀ (F : CoherentModules X) (n : ℕ),
            formalModuleQuotientπ ((Scheme.IdealSheafData.ofIdealTop (I.map (Scheme.ΓSpecIso
                (CommRingCat.of A)).inv.hom)).comap f) (n + 1) F.obj ≫
              (ρ.hom.app F).hom.app (op n) ≫ (β n).hom.app (R.obj F) ≫
                (Scheme.Modules.pushforward (pullback.fst f (Spec.map (CommRingCat.ofHom
                    (Ideal.Quotient.mk (I ^ (n + 1))))))).map ((r n).hom.app F) =
            (aj n).unit.app F.obj) := by sorry

end
end AlgebraicGeometry
