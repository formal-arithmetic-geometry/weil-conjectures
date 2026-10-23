/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionUpperShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition
public import WeilConjectures.SmoothPurity.Adjunction

/-!

# Smooth purity for `ℚ̄_ℓ`-coefficients on the pro-étale site

Let `ℓ` be a prime and `k` a field of characteristic `p > 0` with `p ≠ ℓ`. As in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`, all schemes are
objects `X : Over (Spec (.of k))`, separated and of finite type over `Spec k`, and all morphisms
are morphisms `f : X ⟶ Y` of `Over (Spec (.of k))`; in particular `ℓ` is invertible on every
scheme considered. In the documentation, `X` also stands for the underlying scheme `X.left`.

Let `f : X ⟶ Y` be a morphism whose underlying morphism of schemes `f.left` is smooth of pure
relative dimension `d`. *Smooth purity* (SGA 4, Exposé XVIII, Théorème 3.2.5, and Bhatt–Scholze,
*The pro-étale topology for schemes*, Section 6.8, for `ℚ̄_ℓ`-coefficients) identifies the
exceptional inverse image of the constant coefficient object with a shifted Tate twist:
```
pur_f : Rf^! ℚ̄_ℓ,Y ≅ ℚ̄_ℓ,X(d)[2d]
```
in the derived category `D(Mod_{ℚ̄_ℓ,X})` of module objects over `ℚ̄_ℓ,X = p_X^* ℚ̲̄_ℓ`, the
pullback of the condensed ring `ℚ̲̄_ℓ` (`Profinite.padicAlgClRingObj ℓ`). Here `Rf^!` is
`AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleUpperShriek` on the bounded
constructible derived categories `Dᵇc(-)⟦ℚ̲̄_ℓ⟧` (the right adjoint of `Rf_!`, built from the
compactification of `f` chosen by Nagata's theorem), `ℚ̄_ℓ,Y` is the tensor unit of the
monoidal category `Dᵇc(Y)⟦ℚ̲̄_ℓ⟧`
(`AlgebraicGeometry.ProEtale.CondensedRing.isMonoidal_boundedConstructible`), whose underlying
complex is the tensor unit of `D(Mod_{ℚ̄_ℓ,Y})`, and `ℚ̄_ℓ,X(d)` is the Tate twist of
`WeilConjectures.TateTwist.ProEtale`, a bounded constructible complex
(`AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleTateTwist`).

## Construction

The purity isomorphism is the value at the unit `ℚ̄_ℓ,Y` of the purity isomorphism of functors
`γ_f : Lf^*(-)(d)[2d] ≅ Rf^!` of blueprint `sk-thm-purity-transport`
(`AlgebraicGeometry.ProEtale.CondensedRing.smoothPurityNatIso`,
`WeilConjectures.SmoothPurity.Adjunction`), composed with `Lf^* ℚ̄_ℓ,Y ⊗ ℚ̄_ℓ,X(d)[2d] ≅
ℚ̄_ℓ,X(d)[2d]` (`AlgebraicGeometry.ProEtale.CondensedRing.smoothPurityUnitIso`). The trace map
`Tr_f : Rf_! ℚ̄_ℓ,X(d)[2d] ⟶ ℚ̄_ℓ,Y` (`AlgebraicGeometry.ProEtale.CondensedRing.smoothTrace`) is
then *defined* as in `def-pur-smooth-trace`: `Rf_!` of the purity isomorphism followed by the
counit of `Rf_! ⊣ Rf^!`. Its adjoint `smoothPurityMap` is therefore an isomorphism
(`AlgebraicGeometry.ProEtale.CondensedRing.isIso_smoothPurityMap`).

## Sorried normalizations

The purity isomorphism of functors is the counit-compatible isomorphism for a chosen adjunction
`Rf_! ⊣ Lf^*(-)(d)[2d]` (`det-sp-qbar-adjunction`), whose counit is not normalized by
integration on the affine line in the formalization. The following normalizations of the trace
are therefore `sorry`ed:

- `AlgebraicGeometry.ProEtale.CondensedRing.smoothPurityIso_zero_of_isOpenImmersion`: in
  relative dimension zero, for an open immersion `j`, the purity isomorphism is the canonical
  identification `Rj^! ℚ̄_ℓ ≅ j^* ℚ̄_ℓ ≅ ℚ̄_ℓ`
  (`AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleUpperShriekUnitIso_padicAlgCl`);
- `AlgebraicGeometry.ProEtale.CondensedRing.smoothPurityIso_comp_openImmersion`: compatibility
  with composition with an open immersion `j` on the target, through the composition
  isomorphism `R(f ≫ j)^! ≅ Rj^! ⋙ Rf^!`.

These normalizations pin the trace down far more than an arbitrary isomorphism
`Rf^! ℚ̄_ℓ ≅ ℚ̄_ℓ(d)[2d]`, but not completely: the compatibility with general composition and
with base change, and the identification of the trace of a smooth curve with the classical
trace on `H²_c`, need the comparison isomorphisms of Tate twists along pullbacks and tensor
products, which are not available yet.

-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### Smooth purity -/

section Purity

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y) (d : ℕ) [SmoothOfRelativeDimension d f.left]

/-- The purity isomorphism `Rf^! ℚ̄_ℓ,Y ≅ ℚ̄_ℓ,X(d)[2d]` in `Dᵇc(X)⟦ℚ̲̄_ℓ⟧`: the inverse of the
purity isomorphism `γ_f : Lf^* ℚ̄_ℓ,Y (d)[2d] ≅ Rf^! ℚ̄_ℓ,Y` at the unit (`smoothPurityNatIso`),
followed by `Lf^* ℚ̄_ℓ,Y ⊗ ℚ̄_ℓ,X(d)[2d] ≅ ℚ̄_ℓ,Y ⊗ ℚ̄_ℓ,X(d)[2d] ≅ ℚ̄_ℓ,X(d)[2d]`, the unit
isomorphism of the monoidal functor `Lf^*` and the left unitor. -/
noncomputable def smoothPurityUnitIso :
    (boundedConstructibleUpperShriek (Profinite.padicAlgClRingObj ℓ) ℓ f).obj (𝟙_ _) ≅
      boundedConstructibleTateTwist (Profinite.padicIntRingObjToPadicAlgCl ℓ) X d (2 * d) :=
  ((smoothPurityNatIso (Profinite.padicIntRingObjToPadicAlgCl ℓ) f d).app (𝟙_ _)).symm ≪≫
    whiskerRightIso (Functor.Monoidal.εIso
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f)).symm _ ≪≫
    λ_ _

/-- Blueprint `sk-def-sp-trace`: the **trace map** `Tr_f : Rf_! ℚ̄_ℓ,X(d)[2d] ⟶ ℚ̄_ℓ,Y` of a
morphism `f` smooth of pure relative dimension `d` (SGA 4, Exposé XVIII, Théorème 2.9), at the
constant coefficient object: `Rf_!` of the purity isomorphism `ℚ̄_ℓ,X(d)[2d] ≅ Rf^! ℚ̄_ℓ,Y`
(`smoothPurityUnitIso`) followed by the counit of `Rf_! ⊣ Rf^!`, the transpose of the purity
isomorphism. -/
noncomputable def smoothTrace :
    (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ f).obj
      (boundedConstructibleTateTwist (Profinite.padicIntRingObjToPadicAlgCl ℓ) X d (2 * d)) ⟶
      𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :=
  ((boundedConstructibleUpperShriekAdjunction _ ℓ f).homEquiv _ _).symm
    (smoothPurityUnitIso ℓ f d).inv

/-- The trace is `Rf_!` of the purity isomorphism followed by the counit of `Rf_! ⊣ Rf^!`. -/
lemma smoothTrace_eq :
    smoothTrace ℓ f d =
      (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ f).map
          (smoothPurityUnitIso ℓ f d).inv ≫
        (boundedConstructibleUpperShriekAdjunction _ ℓ f).counit.app _ :=
  Adjunction.homEquiv_counit _ _ _ _

/-- The **purity map** `ℚ̄_ℓ,X(d)[2d] ⟶ Rf^! ℚ̄_ℓ,Y`: the adjoint of the trace `Tr_f` for
`Rf_! ⊣ Rf^!`. -/
noncomputable def smoothPurityMap :
    boundedConstructibleTateTwist (Profinite.padicIntRingObjToPadicAlgCl ℓ) X d (2 * d) ⟶
      (boundedConstructibleUpperShriek (Profinite.padicAlgClRingObj ℓ) ℓ f).obj
        (𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)) :=
  (boundedConstructibleUpperShriekAdjunction _ ℓ f).homEquiv _ _ (smoothTrace ℓ f d)

/-- The purity map is the inverse of the purity isomorphism `smoothPurityUnitIso`. -/
lemma smoothPurityMap_eq : smoothPurityMap ℓ f d = (smoothPurityUnitIso ℓ f d).inv :=
  Equiv.apply_symm_apply _ _

/-- Blueprint `sk-thm-sp-qbar`: **smooth purity** (SGA 4, Exposé XVIII, Théorème 3.2.5): the
adjoint of the trace, `ℚ̄_ℓ,X(d)[2d] ⟶ Rf^! ℚ̄_ℓ,Y`, is an isomorphism. It is the inverse of the
purity isomorphism `smoothPurityUnitIso`, the value at the unit of the purity isomorphism of
functors given by the adjunction `Rf_! ⊣ Lf^*(-)(d)[2d]` of `det-sp-qbar-adjunction`. -/
instance isIso_smoothPurityMap : IsIso (smoothPurityMap ℓ f d) := by
  rw [smoothPurityMap_eq]
  infer_instance

/-- **Smooth purity**: for a morphism `f : X ⟶ Y` of separated `k`-schemes of finite type
which is smooth of pure relative dimension `d`, the exceptional inverse image of the constant
coefficient object is the shifted Tate twist, `Rf^! ℚ̄_ℓ,Y ≅ ℚ̄_ℓ,X(d)[2d]`. It is the inverse of
the adjoint of the trace (`smoothPurityMap`), after the inclusion
`Dᵇc(X)⟦ℚ̲̄_ℓ⟧ ⥤ D(Mod_{ℚ̄_ℓ,X})`. -/
noncomputable def smoothPurityIso :
    ((boundedConstructibleUpperShriek (Profinite.padicAlgClRingObj ℓ) ℓ f).obj
      (𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧))).obj ≅
      (shiftFunctor _ (2 * d : ℤ)).obj
        (tateTwistDerived X.left (Profinite.padicIntRingObjToPadicAlgCl ℓ) d) :=
  (ObjectProperty.ι _).mapIso (asIso (smoothPurityMap ℓ f d)).symm

/-- Blueprint `det-sp-trace-basic`, clause (3), in the étale form of smooth purity for all
admissible coefficients (`f^! ≃ f^*` for étale `f`, `γ_f` the identity): **normalization
of purity in relative dimension zero**: for an open immersion `j`, the purity isomorphism
`Rj^! ℚ̄_ℓ ≅ ℚ̄_ℓ(0)[0]` is the canonical identification `Rj^! ℚ̄_ℓ ≅ j^* ℚ̄_ℓ ≅ ℚ̄_ℓ`
(`boundedConstructibleUpperShriekUnitIso_padicAlgCl`); equivalently, the trace of `j` is the
counit `Rj_! Rj^! ℚ̄_ℓ ⟶ ℚ̄_ℓ` read through it. This is a normalization of the counit of the
adjunction `Rj_! ⊣ j^*(-)(0)[0]` of `det-sp-qbar-adjunction`, which only records its existence;
it is not implied by the statements formalized here. -/
theorem smoothPurityIso_zero_of_isOpenImmersion (j : X ⟶ Y) [IsOpenImmersion j.left] :
    smoothPurityIso ℓ j 0 =
      (ObjectProperty.ι _).mapIso (boundedConstructibleUpperShriekUnitIso_padicAlgCl ℓ j) ≪≫
        (tateTwistDerivedZeroIso X.left (Profinite.padicIntRingObjToPadicAlgCl ℓ)).symm ≪≫
        ((shiftFunctorZero' _ (2 * ((0 : ℕ) : ℤ)) (by simp)).app _).symm :=
  sorry

/-- Blueprint `sk-prop-sp-composition`, case of an open immersion: **compatibility of purity
with composition with an open immersion**: for `f` smooth of pure relative dimension `d` and an
open immersion `j` on its target, the purity isomorphism of `f ≫ j` is that of `f` precomposed with
`R(f ≫ j)^! ℚ̄_ℓ ≅ Rf^! Rj^! ℚ̄_ℓ ≅ Rf^! ℚ̄_ℓ`, the composition isomorphism of the exceptional
inverse images followed by purity for `j` (`boundedConstructibleUpperShriekUnitIso_padicAlgCl`). -/
theorem smoothPurityIso_comp_openImmersion {Z : Over (Spec (.of k))} [LocallyOfFiniteType Z.hom]
    [QuasiCompact Z.hom] [IsSeparated Z.hom] (j : Y ⟶ Z) [IsOpenImmersion j.left]
    [SmoothOfRelativeDimension d (f ≫ j).left] :
    smoothPurityIso ℓ (f ≫ j) d =
      (ObjectProperty.ι _).mapIso
          ((boundedConstructibleUpperShriekComp_padicAlgCl ℓ f j).app _ ≪≫
            (boundedConstructibleUpperShriek _ ℓ f).mapIso
              (boundedConstructibleUpperShriekUnitIso_padicAlgCl ℓ j)) ≪≫
        smoothPurityIso ℓ f d :=
  sorry

end Purity

end AlgebraicGeometry.ProEtale.CondensedRing
