/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleAdditive
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarUnitCoherence
public import WeilConjectures.SmoothPurity.Defs
public import WeilConjectures.TraceFormula.Slop.Basic

/-!

# Dualizing complexes, Borel–Moore sections and integration

Let `ℓ` be a prime, `k` a field of characteristic `p ≠ ℓ` and `X` a separated `k`-scheme of
finite type with structure morphism `a_X : X ⟶ s = Spec k`. The *dualizing complex* of `X` is
```
ω_X = Ra_X^! ℚ̄_ℓ ∈ Dᵇc(X)⟦ℚ̲̄_ℓ⟧
```
(`ProEtale.CondensedRing.dualizingComplex`), for the exceptional inverse image
`boundedConstructibleUpperShriek` of the chosen compactification. It is transported along
morphisms by the composition isomorphism `Rf^! ω_Y ≅ ω_X`
(`ProEtale.CondensedRing.dualizingComplexComp`, blueprint `thm-trf-dualizing-complex-composition`),
the conjugate of the composition isomorphism of the lower shriek.

## Smooth purity

The dualizing complexes of smooth schemes are computed by smooth purity
(`ProEtale.CondensedRing.smoothPurityIso`, `WeilConjectures.SmoothPurity.Defs`): for `X` smooth
of pure dimension `d` over `s`,
```
ω_X = Ra_X^! ℚ̄_ℓ ≅ ℚ̄_ℓ,X(d)[2d]
```
(`ProEtale.CondensedRing.dualizingComplexSmoothIso`); in particular `ω_C ≅ ℚ̄_ℓ,C(1)[2]` for a
smooth curve `C`, which is what makes the local terms of the Frobenius correspondence on a curve
computable (`WeilConjectures.TraceFormula.Correspondence`). In relative dimension zero, for an
étale morphism `j : U ⟶ X` such as the inclusion of an open and closed subscheme, purity is the
identification `Rj^! ℚ̄_ℓ,X ≅ ℚ̄_ℓ,U` (`ProEtale.CondensedRing.etalePurityIso`).

For the base point no purity is needed: `a_s` is the identity of `s`, and
`ω_s = R(𝟙 s)^! ℚ̄_ℓ,s ≅ ℚ̄_ℓ,s` is the identity isomorphism of the exceptional inverse image
(`ProEtale.CondensedRing.dualizingComplexPointIso`).

## Borel–Moore sections and integration

A *Borel–Moore section* of `X` is a morphism `α : ℚ̄_ℓ,X ⟶ ω_X`
(`ProEtale.CondensedRing.BorelMooreSection`, blueprint `sk-d-integral`). Along an étale morphism
`j : U ⟶ X` it restricts to
```
j^* α : ℚ̄_ℓ,U ≅ Rj^! ℚ̄_ℓ,X --Rj^! α--> Rj^! ω_X ≅ ω_U
```
by étale purity (`ProEtale.CondensedRing.BorelMooreSection.restrict`). For `X` proper over `s`
its *integral* is
```
∫_X α : ℚ̄_ℓ,s ⟶ Ra_{X*} La_X^* ℚ̄_ℓ,s ≅ Ra_{X*} ℚ̄_ℓ,X ≅ Ra_{X!} ℚ̄_ℓ,X --α^♭--> ℚ̄_ℓ,s,
```
an element of `End (ℚ̄_ℓ,s)`, where `α^♭` is the adjoint of `α` for `Ra_{X!} ⊣ Ra_X^!`
(`ProEtale.CondensedRing.BorelMooreSection.integral`, blueprint `def-trf-integration`). The
*local term* of `α` along an open and closed subscheme `j : B ⟶ X` proper over `s` is the
integral of its restriction, `LT_B(α) = ∫_B j^* α`
(`ProEtale.CondensedRing.BorelMooreSection.localTerm`, blueprint `def-trf-local-term`), and the
integral over a finite disjoint union of open and closed pieces is the sum of the local terms
(`ProEtale.CondensedRing.BorelMooreSection.integral_eq_sum_localTerm`, blueprint
`lem-trf-integration-component-sum`). Over the base point the integral of `α` is `α` itself,
read through `ω_s ≅ ℚ̄_ℓ,s` (`ProEtale.CondensedRing.BorelMooreSection.integral_point`): the
identity isomorphisms of the six functors for `𝟙 s` are compatible with the unit comparison of
the monoidal pullback `L(𝟙 s)^*`
(`ProEtale.CondensedRing.boundedConstructibleLowerStarId_inv_app_unit`).

## Main definitions

- `ProEtale.CondensedRing.boundedConstructibleUpperShriekId`,
  `ProEtale.CondensedRing.boundedConstructibleUpperShriekComp`: the identity and composition
  isomorphisms of the exceptional inverse image.
- `ProEtale.CondensedRing.dualizingComplex`, `ProEtale.CondensedRing.dualizingComplexComp`.
- `ProEtale.CondensedRing.etalePurityIso`, `ProEtale.CondensedRing.dualizingComplexSmoothIso`:
  smooth purity for the dualizing complexes.
- `ProEtale.CondensedRing.dualizingComplexPointIso`: `ω_s ≅ ℚ̄_ℓ,s`.
- `ProEtale.CondensedRing.BorelMooreSection`, `BorelMooreSection.restrict`,
  `BorelMooreSection.integral`, `BorelMooreSection.localTerm`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

namespace Slop
end Slop
open Slop


open Scheme

/-! ### The identity and composition isomorphisms of the exceptional functors -/

section Comparison

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-- The identity isomorphism `R(𝟙 X)_! ≅ 𝟭` of the derived lower shriek on bounded constructible
`ℚ̄_ℓ`-sheaves: the identification `R(𝟙 X)_! ≅ R(𝟙 X)_*` of the lower shriek of a proper morphism
with its pushforward, followed by `R(𝟙 X)_* ≅ 𝟭`. -/
noncomputable def Slop.boundedConstructibleLowerShriekId (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] :
    boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (𝟙 X) ≅
      𝟭 (Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :=
  boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (𝟙 X) ≪≫
    boundedConstructibleLowerStarId _ ℓ X

/-- The identity isomorphism `R(𝟙 X)^! ≅ 𝟭` of the exceptional inverse image: the conjugate of
`boundedConstructibleLowerShriekId` for the adjunctions `R(𝟙 X)_! ⊣ R(𝟙 X)^!` and `𝟭 ⊣ 𝟭`. -/
noncomputable def Slop.boundedConstructibleUpperShriekId (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] :
    boundedConstructibleUpperShriek (Profinite.padicAlgClRingObj ℓ) ℓ (𝟙 X) ≅
      𝟭 (Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :=
  conjugateIsoEquiv
    (boundedConstructibleUpperShriekAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ (𝟙 X))
    Adjunction.id (boundedConstructibleLowerShriekId ℓ X).symm

variable {X Y Z : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
  [IsSeparated Z.hom]

/-- The composition isomorphism `R(f ≫ g)^! ≅ Rg^! ⋙ Rf^!` of the exceptional inverse image: the
conjugate of the composition isomorphism `boundedConstructibleLowerShriekComp` of the lower
shriek. -/
noncomputable def Slop.boundedConstructibleUpperShriekComp (f : X ⟶ Y) (g : Y ⟶ Z) :
    boundedConstructibleUpperShriek (Profinite.padicAlgClRingObj ℓ) ℓ (f ≫ g) ≅
      boundedConstructibleUpperShriek (Profinite.padicAlgClRingObj ℓ) ℓ g ⋙
        boundedConstructibleUpperShriek (Profinite.padicAlgClRingObj ℓ) ℓ f :=
  conjugateIsoEquiv
    (boundedConstructibleUpperShriekAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ (f ≫ g))
    ((boundedConstructibleUpperShriekAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ f).comp
      (boundedConstructibleUpperShriekAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ g))
    (boundedConstructibleLowerShriekComp (Profinite.padicAlgClRingObj ℓ) ℓ f g).symm

end Comparison

/-! ### Dualizing complexes -/

section Dualizing

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-- The *dualizing complex* `ω_X = Ra_X^! ℚ̄_ℓ` of a separated `k`-scheme of finite type
(blueprint `def-trf-dualizing-complex`). -/
noncomputable abbrev Slop.dualizingComplex (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom] : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  (boundedConstructibleUpperShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).obj (𝟙_ _)

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- The composition isomorphism `Rf^! ω_Y ≅ ω_X` of the dualizing complexes (blueprint
`thm-trf-dualizing-complex-composition`). -/
noncomputable def Slop.dualizingComplexComp (f : X ⟶ Y) :
    (boundedConstructibleUpperShriek (Profinite.padicAlgClRingObj ℓ) ℓ f).obj
        (dualizingComplex ℓ Y) ≅ dualizingComplex ℓ X :=
  ((boundedConstructibleUpperShriekComp ℓ f (toPoint Y)).app (𝟙_ _)).symm ≪≫
    eqToIso (by rw [comp_toPoint])

/-- The Tate twist `ℚ̄_ℓ,X(0)`, placed in degree `0`, is the unit of `D(Mod_{ℚ̄_ℓ,X})`. -/
noncomputable def Slop.tateTwistDerivedZeroIso (T : Scheme.{u}) :
    tateTwistDerived T ℓ 0 ≅ 𝟙_ _ :=
  DerivedCategory.singleFunctorObjUnitIso _

/-- **Étale purity**, smooth purity in relative dimension zero: for a morphism `f` smooth of
relative dimension `0`, that is étale, `Rf^! ℚ̄_ℓ,Y ≅ ℚ̄_ℓ,X`. This is
`ProEtale.CondensedRing.smoothPurityIso` for `d = 0`, lifted along the fully faithful inclusion
`Dᵇc(X)⟦ℚ̲̄_ℓ⟧ ⥤ D(Mod_{ℚ̄_ℓ,X})`. -/
noncomputable def Slop.etalePurityIso (f : X ⟶ Y) [SmoothOfRelativeDimension 0 f.left] :
    (boundedConstructibleUpperShriek (Profinite.padicAlgClRingObj ℓ) ℓ f).obj
        (𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)) ≅
      𝟙_ (Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :=
  (ObjectProperty.fullyFaithfulι _).preimageIso
    (smoothPurityIso ℓ f 0 ≪≫
      (shiftFunctorZero' _ (2 * ((0 : ℕ) : ℤ)) (by simp)).app _ ≪≫
      tateTwistDerivedZeroIso ℓ X.left)

variable (X) in
/-- **Smooth purity for the dualizing complex**: for `X` smooth of pure dimension `d` over `s`,
`ω_X ≅ ℚ̄_ℓ,X(d)[2d]`, after the inclusion `Dᵇc(X)⟦ℚ̲̄_ℓ⟧ ⥤ D(Mod_{ℚ̄_ℓ,X})`. This is
`ProEtale.CondensedRing.smoothPurityIso` for the structure morphism `a_X`. -/
noncomputable def Slop.dualizingComplexSmoothIso (d : ℕ) [SmoothOfRelativeDimension d X.hom] :
    (dualizingComplex ℓ X).obj ≅
      (shiftFunctor _ (2 * d : ℤ)).obj (tateTwistDerived X.left ℓ d) :=
  haveI : SmoothOfRelativeDimension d (toPoint X).left :=
    inferInstanceAs (SmoothOfRelativeDimension d X.hom)
  smoothPurityIso ℓ (toPoint X) d

variable (k) in
/-- The dualizing complex of the base point is the unit, `ω_s ≅ ℚ̄_ℓ,s`: the structure morphism
`a_s = toPoint s` is the identity of `s`, and this is the identity isomorphism
`R(𝟙 s)^! ≅ 𝟭` of the exceptional inverse image (`boundedConstructibleUpperShriekId`) at the
unit. -/
noncomputable def Slop.dualizingComplexPointIso :
    dualizingComplex ℓ (point k) ≅ 𝟙_ (Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧) :=
  (boundedConstructibleUpperShriekId ℓ (point k)).app (𝟙_ _)

end Dualizing

/-! ### Borel–Moore sections -/

section BorelMoore

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-- The *Borel–Moore sections* of `X`: the morphisms `ℚ̄_ℓ,X ⟶ ω_X` (blueprint `sk-d-integral`). -/
abbrev Slop.BorelMooreSection (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom] : Type _ :=
  𝟙_ (Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) ⟶ dualizingComplex ℓ X

variable {ℓ} {X U : Over (Spec (.of k))} [QuasiCompact X.hom] [QuasiCompact U.hom]

namespace Slop.BorelMooreSection

variable [LocallyOfFiniteType X.hom] [IsSeparated X.hom] [LocallyOfFiniteType U.hom]
  [IsSeparated U.hom] in
/-- The *restriction* of a Borel–Moore section along an étale morphism `j : U ⟶ X`, for
instance the inclusion of an open and closed subscheme:
```
j^* α : ℚ̄_ℓ,U ≅ Rj^! ℚ̄_ℓ,X --Rj^! α--> Rj^! ω_X ≅ ω_U,
```
through étale purity `etalePurityIso` and `dualizingComplexComp` (blueprint `def-trf-local-term`,
restricted sections). -/
noncomputable def restrict (j : U ⟶ X) [SmoothOfRelativeDimension 0 j.left]
    (α : BorelMooreSection ℓ X) : BorelMooreSection ℓ U :=
  (etalePurityIso ℓ j).inv ≫
    (boundedConstructibleUpperShriek (Profinite.padicAlgClRingObj ℓ) ℓ j).map α ≫
    (dualizingComplexComp ℓ j).hom

/-- The *integral* `∫_X α ∈ End ℚ̄_ℓ,s` of a Borel–Moore section of a scheme proper over `s`:
```
ℚ̄_ℓ,s ⟶ Ra_{X*} La_X^* ℚ̄_ℓ,s ≅ Ra_{X*} ℚ̄_ℓ,X ≅ Ra_{X!} ℚ̄_ℓ,X --α^♭--> ℚ̄_ℓ,s,
```
the unit of `La_X^* ⊣ Ra_{X*}`, the unit isomorphism of the monoidal functor `La_X^*`, the
identification `Ra_{X!} ≅ Ra_{X*}` for the proper `a_X`, and the adjoint `α^♭` of `α` for
`Ra_{X!} ⊣ Ra_X^!` (blueprint `def-trf-integration`). -/
noncomputable def integral [IsProper X.hom] (α : BorelMooreSection ℓ X) :
    End (𝟙_ (Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧)) :=
  haveI : IsProper (toPoint X).left := inferInstanceAs (IsProper X.hom)
  (boundedConstructibleUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ
      (toPoint X)).unit.app (𝟙_ _) ≫
    (boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).map
      (Functor.Monoidal.εIso
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X))).inv ≫
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ
      (toPoint X)).inv.app (𝟙_ _) ≫
    ((boundedConstructibleUpperShriekAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ
      (toPoint X)).homEquiv _ _).symm α

/-- The integral is additive (blueprint `lem-trf-integration-linear`). -/
lemma integral_add [IsProper X.hom] (α β : BorelMooreSection ℓ X) :
    (α + β).integral = α.integral + β.integral :=
  by
  simp only [integral, Adjunction.homEquiv_counit, Functor.map_add, Preadditive.add_comp,
    Preadditive.comp_add]

variable [LocallyOfFiniteType X.hom] [IsSeparated X.hom] in
/-- The *local term* `LT_B(α) = ∫_B j^* α` of a Borel–Moore section along an open and closed
subscheme `j : B ⟶ X` proper over `s` (blueprint `def-trf-local-term`). -/
noncomputable def localTerm (j : U ⟶ X) [IsOpenImmersion j.left] [IsClosedImmersion j.left]
    [IsProper U.hom] (α : BorelMooreSection ℓ X) :
    End (𝟙_ (Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧)) :=
  (α.restrict j).integral

/-- **Decomposition of the integral into local terms** (blueprint
`lem-trf-integration-component-sum`, `prop-trf-pairing-local-decomposition`): if a scheme `X`
proper over `s` is the disjoint union of finitely many open and closed subschemes
`j_β : B_β ⟶ X`, the integral of a Borel–Moore section is the sum of its local terms,
`∫_X α = ∑_β LT_{B_β}(α)`. -/
theorem integral_eq_sum_localTerm [IsProper X.hom] {ι : Type*} [Fintype ι]
    (B : ι → Over (Spec (.of k))) [∀ i, QuasiCompact (B i).hom] [∀ i, IsProper (B i).hom]
    (j : ∀ i, B i ⟶ X) [∀ i, IsOpenImmersion (j i).left] [∀ i, IsClosedImmersion (j i).left]
    (hdisj : Pairwise fun i i' ↦ Disjoint (Set.range (j i).left.base)
      (Set.range (j i').left.base))
    (hcover : ⋃ i, Set.range (j i).left.base = Set.univ) (α : BorelMooreSection ℓ X) :
    α.integral = ∑ i, α.localTerm (j i) :=
  sorry

instance Slop.instDualizing7 : IsProper (point k).hom :=
  inferInstanceAs (IsProper (𝟙 (Spec (.of k))))

/-- **Point normalization of the integral**: over the base point, where `ω_s ≅ ℚ̄_ℓ,s`
(`dualizingComplexPointIso`), the integral of a Borel–Moore section is the section itself. -/
theorem integral_point (α : BorelMooreSection ℓ (point k)) :
    α.integral = α ≫ (dualizingComplexPointIso ℓ k).hom := by
  have h := homEquiv_comp_conjugateEquiv_app
    (boundedConstructibleUpperShriekAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ (𝟙 (point k)))
    Adjunction.id (boundedConstructibleLowerShriekId ℓ (point k)).inv
    (((boundedConstructibleUpperShriekAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ
      (𝟙 (point k))).homEquiv _ _).symm α)
  rw [Equiv.apply_symm_apply, Adjunction.id_homEquiv_apply, ← Iso.symm_hom,
    ← conjugateIsoEquiv_apply_hom] at h
  rw [dualizingComplexPointIso, Iso.app_hom, boundedConstructibleUpperShriekId]
  erw [h]
  have hL : (boundedConstructibleLowerShriekId ℓ (point k)).inv.app (𝟙_ _) =
      (boundedConstructibleUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ
        (𝟙 (point k))).unit.app (𝟙_ _) ≫
        (boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ (𝟙 (point k))).map
          (Functor.Monoidal.εIso (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
            (𝟙 (point k)))).inv ≫
        (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (𝟙 (point k))).inv.app
          (𝟙_ _) := by
    rw [boundedConstructibleLowerShriekId, Iso.trans_inv, NatTrans.comp_app,
      boundedConstructibleLowerStarId_inv_app_unit, Category.assoc]
  refine Eq.trans ?_ (congrArg (· ≫ ((boundedConstructibleUpperShriekAdjunction
    (Profinite.padicAlgClRingObj ℓ) ℓ (𝟙 (point k))).homEquiv _ _).symm α) hL).symm
  simp only [Category.assoc]
  rfl

end Slop.BorelMooreSection

end BorelMoore

end AlgebraicGeometry.ProEtale.CondensedRing
