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
import Sheaf.AlgebraicGeometry.ClosedImmersionCoherentEquivalence
import Sheaf.AlgebraicGeometry.ClosedImmersionPushforwardFullyFaithful
import Sheaf.AlgebraicGeometry.ClosedImmersionPushforwardIdealPowers
import Sheaf.AlgebraicGeometry.ClosedImmersionUnitQuotient
import Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBase
import Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties
import Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Sheaf.AlgebraicGeometry.FiniteTypeModuleSupportClosed
import Sheaf.AlgebraicGeometry.FiniteTypeModuleSupportPullback
import Sheaf.AlgebraicGeometry.QuotientBaseChangeIdeal
import Sheaf.AlgebraicGeometry.TensorPullback
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # The dictionary for coherent systems on infinitesimal thickenings

Source: Stacks Project, Cohomology of Schemes, Remark 088F and Lemma 087T
(blueprint: lem-weil-pbc-thickening-systems-dictionary).

The natural evaluation isomorphisms specify the dictionary on both objects and morphisms.
The unit equations specify its transitions and the canonical restriction comparisons.
The indexing starts with X_0 = X × Spec(A/I).
X_n is spelled `pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))`,
j_n its `pullback.fst`, and I O_X `(Scheme.IdealSheafData.ofIdealTop (I.map
(Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f`, as in the landed
`quotientBaseChange_closedImmersion_ideal` and `grothendieck_existence`.
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

noncomputable section

set_option autoImplicit false

/-- The dictionary, including its naturality and proper-support restriction.
Source: Stacks, Remark 088F, Lemma 087T, equation 0880 and Lemma 0CYL
(blueprint: lem-weil-pbc-thickening-systems-dictionary).

Proof, in the node's twelve steps:
1. A finite-type scheme over a Noetherian affine scheme is Noetherian (01T6).
2. Quotient base change gives j_n closed with ideal I^(n+1)O_X; extension commutes
with powers. Each thickening is Noetherian and its coherent modules are quasi-coherent
of finite type (quotient-base-change-closed-immersion-ideal, coherent-ft-locnoeth).
3. The pullback unit for a closed immersion is the quotient by its defining ideal
(closed-immersion-unit-quotient).
4. Push the adjoints of the comparisons forward. Ideal-power pushforward identifies
these transitions with the required quotient isomorphisms, giving formal coherent objects.
5. Adjunction and fully faithful closed-immersion pushforward identify compatible
families on the two sides, hence give full faithfulness.
6. The coherent closed-immersion equivalence lifts each formal term to its thickening.
Lift transitions uniquely by full faithfulness, take their adjoints, and reflect
isomorphisms after identifying the quotient by the unit. This gives essential surjectivity.
7. Pullback preserves quasi-coherence and finite type, so restrictions are coherent.
Uniqueness of left adjoints gives the canonical comparison isomorphisms.
8. The j_n units identify the pushed restrictions with F/I^(n+1)F. The composite
adjunction unit identity gives compatibility of these isomorphisms with transitions.
9. Full faithfulness and this natural completion comparison give the stated bijections
on morphisms and isomorphisms; naturality sends restricted v to its completion.
10. Coherent supports are closed; the coherent closed-immersion equivalence identifies
Supp(j_0,*F_0) with j_0(Supp F_0).
11. Choose a closed subscheme with that support. Its map to S is proper iff its map
to S_0 is proper: the closed immersion S_0 → S is proper and separated, so use
composition of proper maps and properness over a separated base.
12. Formal proper support is the level-one support. Step 11 and invariance of
support under isomorphism restrict the equivalence to the two full subcategories.

The binders i and hi specify the canonical transition maps by their two projections;
a_i and a_j are choices of the recorded tensor-pullback adjunctions. Thus no completeness
or separatedness assumption is used by this dictionary.
-/
theorem thickeningSystems_dictionary {A : Type v} [CommRing A] [IsNoetherianRing A]
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
          (I ^ (n + 1))))))) :
    ∃ hX : IsNoetherian X,
      (∀ n : ℕ, IsClosedImmersion (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (I ^ (n + 1)))))) ∧
        (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))).ker =
            (Scheme.IdealSheafData.ofIdealTop (I.map (Scheme.ΓSpecIso (CommRingCat.of
            A)).inv.hom)).comap f ^ (n + 1)) ∧
      ∃ (Φ : CoherentThickeningSystem (fun n ↦ pullback f (Spec.map (CommRingCat.ofHom
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
                (Ideal.Quotient.mk (I ^ (n + 1))))))),
        Φ.IsEquivalence ∧
        (∀ (M : CoherentThickeningSystem (fun n ↦ pullback f (Spec.map (CommRingCat.ofHom
            (Ideal.Quotient.mk (I ^ (n + 1)))))) i) (n : ℕ),
          (((Φ.obj M).obj).map (homOfLE (Nat.le_succ n)).op) ≫ (β n).hom.app M =
          (β (n + 1)).hom.app M ≫
            (Scheme.Modules.pushforward (pullback.fst f (Spec.map (CommRingCat.ofHom
                (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))).map
              ((ai n).homEquiv _ _ (M.comparison n).hom) ≫
            (Scheme.Modules.pushforwardComp (i n) (pullback.fst f (Spec.map (CommRingCat.ofHom
                (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))).hom.app
              (M.term n) ≫
            (Scheme.Modules.pushforwardCongr (hi n)).hom.app (M.term n)) ∧
        ∃ (c : ∀ n : ℕ,
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
          (ρ : @completion X hX ((Scheme.IdealSheafData.ofIdealTop (I.map (Scheme.ΓSpecIso
              (CommRingCat.of A)).inv.hom)).comap f) ≅ R ⋙ Φ),
          (∀ (F : X.Modules) (n : ℕ),
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
            (aj n).unit.app F) ∧
          (∀ (F : CoherentModules X) (n : ℕ),
            ((R.obj F).comparison n).hom ≫ (r n).hom.app F =
              (Scheme.Modules.tensorPullback (i n)).map ((r (n + 1)).hom.app F) ≫
                (c n).hom.app F.obj) ∧
          (∀ (F : CoherentModules X) (n : ℕ),
            formalModuleQuotientπ ((Scheme.IdealSheafData.ofIdealTop (I.map (Scheme.ΓSpecIso
                (CommRingCat.of A)).inv.hom)).comap f) (n + 1) F.obj ≫
              (ρ.hom.app F).hom.app (op n) ≫ (β n).hom.app (R.obj F) ≫
                (Scheme.Modules.pushforward (pullback.fst f (Spec.map (CommRingCat.ofHom
                    (Ideal.Quotient.mk (I ^ (n + 1))))))).map ((r n).hom.app F) =
            (aj n).unit.app F.obj) ∧
          (∀ F G : CoherentModules X,
            Function.Bijective (fun v : R.obj G ⟶ R.obj F ↦
              (ρ.hom.app G) ≫ Φ.map v ≫ (ρ.inv.app F))) ∧
          (∀ (F G : CoherentModules X) (v : G ⟶ F),
            (ρ.hom.app G) ≫ Φ.map (R.map v) ≫ (ρ.inv.app F) =
              (@completion X hX ((Scheme.IdealSheafData.ofIdealTop (I.map (Scheme.ΓSpecIso
                  (CommRingCat.of A)).inv.hom)).comap f)).map v) ∧
          (∀ (F : CoherentModules X)
            (M : CoherentThickeningSystem (fun n ↦ pullback f (Spec.map (CommRingCat.ofHom
                (Ideal.Quotient.mk (I ^ (n + 1)))))) i),
            ∃ b : (R.obj F ≅ M) ≃
              ((@completion X hX ((Scheme.IdealSheafData.ofIdealTop (I.map (Scheme.ΓSpecIso
                  (CommRingCat.of A)).inv.hom)).comap f)).obj F ≅ Φ.obj M),
              ∀ e, b e = (ρ.app F) ≪≫ Φ.mapIso e) ∧
          (∀ F₀ : CoherentModules (pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^
              (0 + 1)))))),
            {x : X | ¬ Subsingleton
              (((Scheme.Modules.pushforward (pullback.fst f (Spec.map (CommRingCat.ofHom
                  (Ideal.Quotient.mk (I ^ (0 + 1))))))).obj
                F₀.obj).presheaf.stalk x)} =
              (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (0 + 1)))))) ''
                {x : ↥(pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (0 +
                    1)))))) | ¬ Subsingleton (F₀.obj.presheaf.stalk x)} ∧
            (Scheme.Modules.HasSupportProperOver
              (pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (0 + 1))))))
              F₀.obj ↔
            Scheme.Modules.HasSupportProperOver f
              ((Scheme.Modules.pushforward (pullback.fst f (Spec.map (CommRingCat.ofHom
                  (Ideal.Quotient.mk (I ^ (0 + 1))))))).obj F₀.obj))) ∧
          (∀ M : CoherentThickeningSystem (fun n ↦ pullback f (Spec.map (CommRingCat.ofHom
              (Ideal.Quotient.mk (I ^ (n + 1)))))) i,
            Scheme.Modules.HasSupportProperOver
              (pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (0 + 1))))))
              (M.term 0) ↔
            Scheme.Modules.HasSupportProperOver f ((Φ.obj M).obj.obj (op 0))) := by
  sorry

end
end AlgebraicGeometry
