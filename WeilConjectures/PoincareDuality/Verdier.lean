/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.PoincareDuality.ProjectionFormula
public import WeilConjectures.PoincareDuality.VerdierBiduality
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleMonoidalComp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructiblePullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionIhom
public import WeilConjectures.SixFunctors.Etale.Derived.DoubleDual

/-!

# Verdier duality on bounded constructible complexes on the pro-étale site

Let `k` be a field of characteristic `≠ ℓ` and `f : X ⟶ Y` a morphism of separated `k`-schemes
of finite type, a morphism of `Over (Spec (.of k))`. This file specializes the abstract
constructions of `WeilConjectures.PoincareDuality.Abstract` to the six functors on the bounded
constructible derived categories `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` with coefficients in the condensed ring `ℚ̲̄_ℓ`
(`Profinite.padicAlgClRingObj ℓ`): the adjunctions `Lf^* ⊣ Rf_*` and `Rf_! ⊣ Rf^!`, the internal
hom `RHom` and the derived exceptional projection morphism `PF^!` of
`WeilConjectures.PoincareDuality.ProjectionFormula`.

The exceptional inverse image `Rf^!` only exists on `Dᵇc`
(`ProEtale.CondensedRing.boundedConstructibleUpperShriek`), and requires `Rg_*` along the proper
half of the chosen compactification to be a left adjoint. This is why the coefficients are
`ℚ̲̄_ℓ` rather than a general condensed ring: for `ℚ̲̄_ℓ` it is the instance
`ProEtale.CondensedRing.isLeftAdjoint_boundedConstructibleLowerStar_padicAlgClRingObj`. The
monoidal closed structure on `Dᵇc` is that of
`ProEtale.CondensedRing.isMonoidal_boundedConstructible` and
`ProEtale.CondensedRing.isMonoidalClosed_boundedConstructible`, and its braiding, used in the
double-dual morphism, is the Koszul braiding `ProEtale.CondensedRing.boundedConstructibleBraiding`,
made a local instance.

## Main definitions

- `ProEtale.CondensedRing.verdierExchange`: the Verdier exchange morphism
  `Φ_{f,K,L} : Rf_* RHom(K, Rf^! L) ⟶ RHom(Rf_! K, L)`.
- `ProEtale.CondensedRing.dualizingComplex`: for a structure morphism `a : X ⟶ S`, the
  dualizing complex `ω_X = Ra^! ℚ̄_ℓ,S`, and `ProEtale.CondensedRing.verdierDual`: the Verdier
  dual `𝔻_X K = RHom(K, ω_X)`.
- `ProEtale.CondensedRing.verdierBiduality`: the double-dual morphism `δ_K : K ⟶ 𝔻_X 𝔻_X K`.
- `ProEtale.CondensedRing.upperShriekDualizingComplexIso`: for `f : X ⟶ Y` and `a_Y : Y ⟶ S`,
  the identification `γ : Rf^! ω_Y ≅ ω_X` with `ω_X` relative to `f ≫ a_Y`, the composition
  isomorphism `R(f ≫ a_Y)^! ≅ Ra_Y^! ⋙ Rf^!`
  (`ProEtale.CondensedRing.boundedConstructibleUpperShriekComp_padicAlgCl`) at the unit.
- `ProEtale.CondensedRing.absoluteVerdierExchange` and
  `ProEtale.CondensedRing.dualVerdierExchange`: the absolute exchange
  `Rf_* 𝔻_X K ⟶ 𝔻_Y Rf_! K` and the opposite exchange `Θ_K : Rf_! 𝔻_X K ⟶ 𝔻_Y Rf_* K`, built
  with `γ`.

The isomorphism `γ` is the conjugate of the composition isomorphism of lower shrieks
`R(f ≫ a_Y)_! ≅ Rf_! ⋙ Ra_Y_!`
(`ProEtale.CondensedRing.boundedConstructibleLowerShriekComp_padicAlgCl`).

## Main results

- `ProEtale.CondensedRing.isIso_verdierExchange`: **Verdier duality**, the exchange morphism
  is an isomorphism, deduced from the derived projection formula
  (`isIso_boundedConstructibleExceptionalProjectionMorphism`) by the Yoneda argument.
- `ProEtale.CondensedRing.isIso_verdierBiduality_of_isDualizable` and
  `ProEtale.CondensedRing.isIso_verdierBiduality_of_isCompl`: the lisse and open–closed steps of
  biduality.
- `ProEtale.CondensedRing.dualizingComplexIsoUpperStar`: `Lj^* ω_X ≅ ω_U` for an open immersion
  `j`, and `ProEtale.CondensedRing.isIso_map_verdierBiduality_iff_of_isOpenImmersion`:
  `Lj^* δ_K` is an isomorphism iff `δ_{Lj^* K}` is.

## Sorried input

- `ProEtale.CondensedRing.isIso_verdierBiduality`: **constructible biduality**, `δ_K` is an
  isomorphism for `K` bounded constructible and `ω_X` the dualizing complex relative to the
  structure morphism `X ⟶ Spec k` (Input 3.3 of the specification).

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-! ### The Verdier exchange morphism -/

section Exchange

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

/-- The **Verdier exchange morphism** `Φ_{f,K,L} : Rf_* RHom(K, Rf^! L) ⟶ RHom(Rf_! K, L)` on
bounded constructible complexes: the transpose of the pairing
```
Rf_! K ⊗ᴸ Rf_* RHom(K, Rf^! L) ⟶ Rf_! (K ⊗ᴸ Lf^* Rf_* RHom(K, Rf^! L))
  ⟶ Rf_! (K ⊗ᴸ RHom(K, Rf^! L)) ⟶ Rf_! Rf^! L ⟶ L,
```
see `CategoryTheory.Verdier.exchange`. -/
noncomputable def verdierExchange (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (L : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerStar _ ℓ f).obj
        ((ihom K).obj ((boundedConstructibleUpperShriek _ ℓ f).obj L)) ⟶
      (ihom ((boundedConstructibleLowerShriek _ ℓ f).obj K)).obj L :=
  Verdier.exchange (boundedConstructibleUpperStarLowerStarAdjunction _ ℓ f)
    (boundedConstructibleUpperShriekAdjunction _ ℓ f)
    (boundedConstructibleExceptionalProjection _ ℓ f) K L

/-- **Verdier duality**: the exchange morphism `Φ_{f,K,L}` is an isomorphism, by the derived
projection formula and the Yoneda lemma. -/
theorem isIso_verdierExchange (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (L : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso (verdierExchange ℓ f K L) := by
  have := isIso_boundedConstructibleExceptionalProjection_app_app ℓ f K
  exact Verdier.isIso_exchange_of_isIso _ _ _ K L

end Exchange

/-! ### The dualizing complex and the double-dual morphism -/

section Dualizing

variable {X S : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType S.hom]
  [QuasiCompact S.hom] [IsSeparated S.hom]
  (a : X ⟶ S)

/-- The **dualizing complex** `ω_X = Ra^! ℚ̄_ℓ,S` of `X` relative to the structure morphism
`a : X ⟶ S`. -/
noncomputable def dualizingComplex : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  (boundedConstructibleUpperShriek _ ℓ a).obj (𝟙_ _)

/-- The **Verdier dual** `𝔻_X K = RHom(K, ω_X)` relative to the structure morphism `a : X ⟶ S`. -/
noncomputable def verdierDual (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  (ihom K).obj (dualizingComplex ℓ a)

/-- The **double-dual morphism** `δ_K : K ⟶ 𝔻_X 𝔻_X K`: the transpose of the evaluation pairing
`𝔻_X K ⊗ᴸ K ⟶ K ⊗ᴸ 𝔻_X K ⟶ ω_X`. -/
noncomputable def verdierBiduality (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    K ⟶ verdierDual ℓ a (verdierDual ℓ a K) :=
  Verdier.bidualityMap (dualizingComplex ℓ a) K

/-- **Biduality for dualizable complexes** (the lisse step of the blueprint theorem
`thm-coef-qbar-verdier`): if the dualizing complex `ω_X` relative to `a` is isomorphic to an
invertible object (as `ℚ̄_ℓ(d)[2d]` is, for `a` smooth of relative dimension `d`), the double-dual
morphism `δ_K : K ⟶ 𝔻_X 𝔻_X K` is an isomorphism for every dualizable `K`. -/
theorem isIso_verdierBiduality_of_isDualizable {T : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (γ : T ≅ dualizingComplex ℓ a) (hT : IsInvertible T)
    {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (hK : IsDualizable K) :
    IsIso (verdierBiduality ℓ a K) :=
  Verdier.isIso_bidualityMap_of_isDualizable γ hT hK

/-- **Open–closed dévissage of biduality**: for a quasi-compact open immersion `j : U ⟶ X` and a
closed immersion `i : Z ⟶ X` onto its complement, the double-dual morphism `δ_K` is an
isomorphism as soon as its restrictions `Lj^* δ_K` and `Li^* δ_K` are. -/
theorem isIso_verdierBiduality_of_isCompl {Z U : Over (Spec (.of k))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
    (i : Z ⟶ X) [IsClosedImmersion i.left] (j : U ⟶ X) [QuasiCompact j.left]
    (hij : IsCompl (Set.range i.left.base) (Set.range j.left.base))
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hj : IsIso ((boundedConstructibleUpperStar _ ℓ j).map (verdierBiduality ℓ a K)))
    (hi : IsIso ((boundedConstructibleUpperStar _ ℓ i).map (verdierBiduality ℓ a K))) :
    IsIso (verdierBiduality ℓ a K) :=
  isIso_of_isIso_boundedConstructibleUpperStar_map_of_isCompl _ ℓ i j hij _ hj hi

end Dualizing

/-! ### Biduality over the base field -/

section Biduality

instance : LocallyOfFiniteType (Over.mk (𝟙 (Spec (.of k)))).hom :=
  inferInstanceAs (LocallyOfFiniteType (𝟙 _))

instance : QuasiCompact (Over.mk (𝟙 (Spec (.of k)))).hom :=
  inferInstanceAs (QuasiCompact (𝟙 _))

instance : IsSeparated (Over.mk (𝟙 (Spec (.of k)))).hom :=
  inferInstanceAs (IsSeparated (𝟙 _))

variable {X : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-- **Constructible Verdier biduality**: for the structure morphism `a : X ⟶ Spec k` of a
separated `k`-scheme of finite type, the double-dual morphism `δ_K` for the dualizing complex
`ω_X = Ra^! ℚ̄_ℓ` is an isomorphism for `K` bounded constructible. See the module docstring.

The base must be `Spec k` (or at least regular): for `a = 𝟙` on a nodal curve and `K` the
skyscraper `ℚ̄_ℓ` at the node, `𝔻𝔻K` has rank `9`. -/
theorem isIso_verdierBiduality (a : X ⟶ Over.mk (𝟙 (Spec (.of k))))
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso (verdierBiduality ℓ a K) :=
  sorry

end Biduality

/-! ### The absolute and opposite exchange morphisms -/

section Absolute

variable {X Y S : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
  [IsSeparated S.hom]
  (f : X ⟶ Y) (aY : Y ⟶ S)

/-- The identification `γ : Rf^! ω_Y ≅ ω_X` of the dualizing complexes `ω_Y = Ra_Y^! ℚ̄_ℓ,S` and
`ω_X = R(f ≫ a_Y)^! ℚ̄_ℓ,S`: the composition isomorphism `R(f ≫ a_Y)^! ≅ Ra_Y^! ⋙ Rf^!` of
`ProEtale.CondensedRing.boundedConstructibleUpperShriekComp_padicAlgCl` at the unit. -/
noncomputable def upperShriekDualizingComplexIso :
    (boundedConstructibleUpperShriek _ ℓ f).obj (dualizingComplex ℓ aY) ≅
      dualizingComplex ℓ (f ≫ aY) :=
  ((boundedConstructibleUpperShriekComp_padicAlgCl ℓ f aY).app (𝟙_ _)).symm

/-- The **absolute Verdier exchange morphism** `Rf_* 𝔻_X K ⟶ 𝔻_Y Rf_! K`, with `𝔻_X` relative to
`f ≫ a_Y` and `𝔻_Y` relative to `a_Y`: the exchange morphism `Φ_{f,K,ω_Y}` precomposed with the
inverse of `γ = upperShriekDualizingComplexIso`. -/
noncomputable def absoluteVerdierExchange (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerStar _ ℓ f).obj (verdierDual ℓ (f ≫ aY) K) ⟶
      verdierDual ℓ aY ((boundedConstructibleLowerShriek _ ℓ f).obj K) :=
  Verdier.absoluteExchange (boundedConstructibleUpperStarLowerStarAdjunction _ ℓ f)
    (boundedConstructibleUpperShriekAdjunction _ ℓ f)
    (boundedConstructibleExceptionalProjection _ ℓ f)
    (dualizingComplex ℓ (f ≫ aY)) (dualizingComplex ℓ aY)
    (upperShriekDualizingComplexIso ℓ f aY) K

/-- The **opposite Verdier exchange morphism** `Θ_K : Rf_! 𝔻_X K ⟶ 𝔻_Y Rf_* K`, with `𝔻_X`
relative to `f ≫ a_Y` and `𝔻_Y` relative to `a_Y`: the double-dual morphism of `Rf_! 𝔻_X K`,
followed by the dual of `Rf_* K ⟶ Rf_* 𝔻_X 𝔻_X K ⟶ 𝔻_Y Rf_! 𝔻_X K`. The familiar
`𝔻_Y Rf_* K ≅ Rf_! 𝔻_X K` is its inverse, when it is invertible. -/
noncomputable def dualVerdierExchange (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriek _ ℓ f).obj (verdierDual ℓ (f ≫ aY) K) ⟶
      verdierDual ℓ aY ((boundedConstructibleLowerStar _ ℓ f).obj K) :=
  Verdier.dualExchange (boundedConstructibleUpperStarLowerStarAdjunction _ ℓ f)
    (boundedConstructibleUpperShriekAdjunction _ ℓ f)
    (boundedConstructibleExceptionalProjection _ ℓ f)
    (dualizingComplex ℓ (f ≫ aY)) (dualizingComplex ℓ aY)
    (upperShriekDualizingComplexIso ℓ f aY) K

end Absolute

/-! ### Restriction of the dualizing complex to an open subscheme -/

section OpenImmersion

variable {U X S : Over (Spec (.of k))}
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom] [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
  [IsSeparated S.hom]
  (j : U ⟶ X) [IsOpenImmersion j.left] (a : X ⟶ S)

/-- For an open immersion `j`, the lower shriek `Rj_!` on bounded constructible `ℚ̄_ℓ`-complexes
is the extension by zero `j_!`: the independence of the compactification, comparing the chosen
compactification of `j` with the compactification `X ⟶ X` by the identity, along which the
derived pushforward is the identity. -/
noncomputable def boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek :
    boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j ≅
      boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j :=
  boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl ℓ (compactificationOverField j)
      (Compactification.ofIsOpenImmersion j.left) ≪≫
    (Iso.refl _ : _ ≅ boundedConstructibleOpenImmersionLowerShriek _ ℓ j ⋙
      boundedConstructibleLowerStar _ ℓ (𝟙 X)) ≪≫
    Functor.isoWhiskerLeft _ (boundedConstructibleLowerStarId _ ℓ X) ≪≫ Functor.rightUnitor _

/-- For an open immersion `j`, the exceptional inverse image `Rj^!` on bounded constructible
`ℚ̄_ℓ`-complexes is the pullback `Lj^*`: the conjugate of
`boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek`. -/
noncomputable def boundedConstructibleUpperShriekIsoUpperStar :
    boundedConstructibleUpperShriek (Profinite.padicAlgClRingObj ℓ) ℓ j ≅
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j :=
  conjugateIsoEquiv (boundedConstructibleUpperShriekAdjunction _ ℓ j)
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ j)
    (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek ℓ j).symm

/-- **The dualizing complex restricts to open subschemes**: for an open immersion `j : U ⟶ X` and
`a : X ⟶ S`, the dualizing complex of `U` relative to `j ≫ a` is the restriction
`Lj^* ω_X` of the dualizing complex of `X` relative to `a`. -/
noncomputable def dualizingComplexIsoUpperStar :
    dualizingComplex ℓ (j ≫ a) ≅
      (boundedConstructibleUpperStar _ ℓ j).obj (dualizingComplex ℓ a) :=
  (upperShriekDualizingComplexIso ℓ j a).symm ≪≫
    (boundedConstructibleUpperShriekIsoUpperStar ℓ j).app _

/-- **Restriction of biduality to an open subscheme**: for an open immersion `j : U ⟶ X` and
`a : X ⟶ S`, the restriction `Lj^* δ_K` of the double-dual morphism of `K` relative to `a` is an
isomorphism if and only if the double-dual morphism `δ_{Lj^* K}` relative to `j ≫ a` is, under
the identification `Lj^* ω_X ≅ ω_U` (`dualizingComplexIsoUpperStar`) and the
commutation of `Lj^*` with internal homs
(`isIso_ihomComparison_boundedConstructibleUpperStar_of_isOpenImmersion`). The compatibility of
`Lj^*` with the Koszul braidings is `boundedConstructibleUpperStar_map_braiding_hom_δ`. -/
theorem isIso_map_verdierBiduality_iff_of_isOpenImmersion
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso ((boundedConstructibleUpperStar _ ℓ j).map (verdierBiduality ℓ a K)) ↔
      IsIso (verdierBiduality ℓ (j ≫ a) ((boundedConstructibleUpperStar _ ℓ j).obj K)) := by
  have hbr : ∀ K M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧,
      Functor.LaxMonoidal.μ (boundedConstructibleUpperStar _ ℓ j) K M ≫
          (boundedConstructibleUpperStar _ ℓ j).map (β_ K M).hom =
        (β_ ((boundedConstructibleUpperStar _ ℓ j).obj K)
            ((boundedConstructibleUpperStar _ ℓ j).obj M)).hom ≫
          Functor.LaxMonoidal.μ (boundedConstructibleUpperStar _ ℓ j) M K := fun K M ↦ by
    rw [← cancel_mono (Functor.OplaxMonoidal.δ (boundedConstructibleUpperStar _ ℓ j) M K),
      Category.assoc, Category.assoc, boundedConstructibleUpperStar_map_braiding_hom_δ,
      Functor.Monoidal.μ_δ, Category.comp_id, Functor.Monoidal.μ_δ_assoc]
  let : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).LaxBraided :=
    { (inferInstance : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        j).LaxMonoidal) with braided := hbr }
  have := isIso_ihomComparison_boundedConstructibleUpperStar_of_isOpenImmersion _ ℓ j K
  have := isIso_ihomComparison_boundedConstructibleUpperStar_of_isOpenImmersion _ ℓ j
    ((ihom K).obj (dualizingComplex ℓ a))
  have : IsIso (MonoidalClosed.dualComparison (boundedConstructibleUpperStar _ ℓ j)
      (dualizingComplexIsoUpperStar ℓ j a).inv K) := by
    rw [MonoidalClosed.dualComparison]
    infer_instance
  have : IsIso (MonoidalClosed.dualComparison (boundedConstructibleUpperStar _ ℓ j)
      (dualizingComplexIsoUpperStar ℓ j a).inv
      ((ihom K).obj (dualizingComplex ℓ a))) := by
    rw [MonoidalClosed.dualComparison]
    infer_instance
  exact MonoidalClosed.isIso_map_toIhomIhom_iff (boundedConstructibleUpperStar _ ℓ j)
    (dualizingComplexIsoUpperStar ℓ j a).inv K

end OpenImmersion

end AlgebraicGeometry.ProEtale.CondensedRing
