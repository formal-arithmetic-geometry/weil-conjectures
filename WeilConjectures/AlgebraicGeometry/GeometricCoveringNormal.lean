/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import WeilConjectures.AlgebraicGeometry.DetWrpCoverOpenImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian

/-!
# Geometric coverings of a normal scheme

Let `X` be a nonempty connected normal scheme of finite type over a field and let `p : Y ⟶ X` be
separated and étale. If `p` satisfies the existence part of the valuative criterion, then every
connected component of `Y` is finite étale and surjective over `X`.

## Main statements

- `AlgebraicGeometry.isFinite_and_surjective_of_valuativeCriterion_existence`: the case of a
  connected `Y`.
- `AlgebraicGeometry.exists_connectedComponent_isFinite_etale_surjective`: every connected
  component of `Y` is an open subscheme which is finite, étale and surjective over `X`.

## Implementation details

A connected component `Y₁` of `Y` is open (`Y` is locally noetherian), and it embeds over `X` as
an open subscheme of a finite normalization `N` of `X`
(`AlgebraicGeometry.det_wrp_cover_open_immersion`). As `N` is noetherian, `Y₁ ⟶ X` is
quasi-compact, so the valuative criterion makes it proper; being also quasi-finite it is finite
(Zariski's main theorem, `AlgebraicGeometry.IsFinite.of_isProper_of_locallyQuasiFinite`). Its
image is then open and closed, hence all of `X`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}} [ConnectedSpace X]
  (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
  (hX : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x))

include aX hX in
/-- Let `X` be a connected normal scheme of finite type over a field and let `p : Y ⟶ X` be a
separated étale morphism from a connected scheme which satisfies the existence part of the
valuative criterion. Then `p` is finite and surjective. -/
theorem isFinite_and_surjective_of_valuativeCriterion_existence {Y : Scheme.{u}}
    [ConnectedSpace Y] (p : Y ⟶ X) [IsSeparated p] [Etale p]
    (hp : ValuativeCriterion.Existence p) : IsFinite p ∧ Surjective p := by
  obtain ⟨_, -, -, L, _, _, -, -, -, -, hfin, f, hf, hfo⟩ :=
    det_wrp_cover_open_immersion aX hX p
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType aX
  have : IsNoetherian (X.normalizationIn L) :=
    isNoetherian_of_locallyOfFiniteType (X.fromNormalizationIn L)
  have : QuasiCompact p := hf ▸ inferInstance
  have : UniversallyClosed p := UniversallyClosed.of_valuativeCriterion p hp
  have : IsProper p := {}
  have : IsFinite p := IsFinite.of_isProper_of_locallyQuasiFinite p
  refine ⟨this, ⟨?_⟩⟩
  have h : Set.range p = Set.univ :=
    IsClopen.eq_univ ⟨p.isClosedMap.isClosed_range, p.isOpenMap.isOpen_range⟩
      (Set.range_nonempty p)
  exact Set.range_eq_univ.mp h

include aX hX in
/-- **Geometric coverings of a normal scheme.** Let `X` be a nonempty connected normal scheme of
finite type over a field `k`, and let `p : Y ⟶ X` be separated and étale. Suppose that every
commutative square
```
Spec K ⟶ Y
  |       |
  v       v
Spec V ⟶ X
```
with `V` a valuation ring with fraction field `K` has a lift `Spec V ⟶ Y`. Then every connected
component of `Y` is (an open subscheme) finite étale and surjective over `X`. -/
theorem exists_connectedComponent_isFinite_etale_surjective {Y : Scheme.{u}} (p : Y ⟶ X)
    [IsSeparated p] [Etale p] (hp : ValuativeCriterion.Existence p) (y : Y) :
    ∃ U : Y.Opens, (U : Set Y) = connectedComponent y ∧
      IsFinite (U.ι ≫ p) ∧ Etale (U.ι ≫ p) ∧ Surjective (U.ι ≫ p) := by
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType aX
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian p
  let U : Y.Opens := ⟨connectedComponent y, isOpen_connectedComponent⟩
  have : ConnectedSpace U := Subtype.connectedSpace isConnected_connectedComponent
  have hU : ValuativeCriterion.Existence (U.ι ≫ p) := by
    intro S
    obtain ⟨⟨l, hl₁, hl₂⟩⟩ := hp ⟨S.R, S.K, S.i₁ ≫ U.ι, S.i₂,
      ⟨by rw [Category.assoc, S.commSq.w]⟩⟩
    -- the image of the connected `Spec V` meets, hence lies in, the component `U`
    have hrange : Set.range l ⊆ (U : Set Y) := by
      let z : Spec (.of S.K) := IsLocalRing.closedPoint S.K
      have hz : l (Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) z) ∈ (U : Set Y) := by
        rw [← Scheme.Hom.comp_apply, hl₁, Scheme.Hom.comp_apply]
        exact (S.i₁ z).2
      rw [show (U : Set Y) = connectedComponent y from rfl, connectedComponent_eq hz]
      exact (isPreconnected_range l.continuous).subset_connectedComponent ⟨_, rfl⟩
    let l' : Spec (.of S.R) ⟶ U := IsOpenImmersion.lift U.ι l (by rwa [U.range_ι])
    refine ⟨⟨⟨l', ?_, ?_⟩⟩⟩
    · rw [← cancel_mono U.ι, Category.assoc, IsOpenImmersion.lift_fac]
      exact hl₁
    · rw [← Category.assoc, IsOpenImmersion.lift_fac]
      exact hl₂
  obtain ⟨hfin, hsurj⟩ :=
    isFinite_and_surjective_of_valuativeCriterion_existence aX hX (U.ι ≫ p) hU
  exact ⟨U, rfl, hfin, inferInstance, hsurj⟩

end AlgebraicGeometry
