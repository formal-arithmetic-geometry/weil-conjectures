/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorSpreading.Limit
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorSpreading.Noetherian

/-!
# Spreading a finite étale Galois cover out from the generic fibre

Let `S` be a qcqs integral normal scheme with generic point `η`, let `c : C ⟶ S` be a qcqs
smooth morphism with geometrically connected fibres, and fix a section `σ` of `c`. An
`M`-torsor on the generic fibre `C_η`, for `M` a finite abelian group of order invertible on
`S`, carrying a `κ(η)`-rational point above `σ(η)`, extends to an `M`-torsor on `C`. This is
[Stacks 0EZJ]; the statement is the input taken by the induction in the proof of smooth base
change.

A finite étale Galois cover with abelian group `M` is the same thing as an `M`-torsor, so
the covers are recorded as `AlgebraicGeometry.Scheme.EtaleTorsor` of
`WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor`.

## Implementation notes

The statement takes the constructions it speaks about as explicit data rather than building
them, so that it is a statement and not a construction:

- the generic fibre `C_η` is a scheme `Cη` together with a cartesian square over
  `Spec S.functionField ⟶ S`, the latter being `AlgebraicGeometry.Scheme.fromSpecStalk` at
  the generic point;
- the generic point of the section is a morphism `sη : Spec S.functionField ⟶ Cη` which is a
  section of the generic fibre and lies over `σ`;
- the restriction of the produced torsor to the generic fibre is expressed by asking for a
  morphism `ψ` from the given torsor to the produced one which makes a cartesian square over
  `j : Cη ⟶ C` and commutes with the `M`-actions.

Normality of `S` is spelled out as integral closedness of all the stalks, there being no
`IsNormal` predicate on schemes; qcqs-ness of `S` is `CompactSpace` together with
`QuasiSeparatedSpace`.

Stacks `0EZJ` itself, for an arbitrary finite group `G`, is recorded as
`AlgebraicGeometry.Scheme.GaloisCover.exists_isPullback_of_genericFibre`, for Galois covers in
the sense of `AlgebraicGeometry.Scheme.GaloisCover` (finite étale `G`-torsors, following the
blueprint definition `def-sbc-normal-dominant-galois`). The extension is the relative
normalization of `C` in the cover; its proof is assembled in the files
`WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorSpreading.*` from separately stated
steps (limit reduction, generic point, trait case, depth at least two). Only the
abelian case is used by smooth base change; it is the statement
`AlgebraicGeometry.Scheme.EtaleTorsor.exists_isPullback_of_genericFibre` about `M`-torsors,
deduced by viewing an `M`-torsor as a Galois cover with group `Multiplicative M`.

The uniqueness of the extension is not asserted. Connectedness of the torsor is deliberately
*not* assumed: the torsors that the vanishing theorem `sk-thm-vanishing` spreads are those
attached to an arbitrary class in `H^1`, which need not be connected.

## Main statements

- `AlgebraicGeometry.Scheme.GaloisCover.exists_isPullback_of_genericFibre`: spreading a finite
  étale Galois cover with group `G` (blueprint `sbc-thm-spreading-finite-etale-galois`).
- `AlgebraicGeometry.Scheme.EtaleTorsor.exists_isPullback_of_genericFibre`: the spreading
  statement for torsors under a finite abelian group (blueprint `sk-prop-input-spreading`).

## References

- Stacks Project, Tag `0EZJ`, <https://stacks.math.columbia.edu/tag/0EZJ>
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The deep step of blueprint `sbc-thm-spreading-finite-etale-galois` ([Stacks 0EZJ]): in the
situation of `AlgebraicGeometry.Scheme.GaloisCover.exists_isPullback_of_genericFibre`, the total
space `Z.P ⟶ C_η` of the Galois cover is the restriction to the generic fibre of a finite étale
`C`-scheme `p : Y ⟶ C`, that is, there is `ψ : Z.P ⟶ Y` making the square over `j : C_η ⟶ C`
cartesian.

The extension is the relative normalization of `C` in `Z.P`. The statement is reduced to a
Noetherian base by a limit argument
(`AlgebraicGeometry.Scheme.SpreadingDatum.exists_isFinite_etale_isPullback_of_isNoetherian`),
where it is [Stacks 0EYJ]
(`AlgebraicGeometry.Scheme.SpreadingDatum.exists_isFinite_etale_isPullback`): an induction over
the points of the base through the trait case (tame ramification, Abhyankar's lemma and purity)
and the case of depth at least two (the formal neighbourhood of the section). The equivariance
and torsor structure of the extension are then formal:
`AlgebraicGeometry.Scheme.GaloisCover.exists_of_isPullback_isFinite_etale`. -/
@[stacks 0EZJ]
theorem GaloisCover.exists_isFinite_etale_isPullback_of_genericFibre {S C : Scheme.{u}}
    [CompactSpace S] [QuasiSeparatedSpace S] [IsIntegral S]
    (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (c : C ⟶ S) [QuasiCompact c] [QuasiSeparated c] [Smooth c] [GeometricallyConnected c]
    (σ : S ⟶ C) (hσ : σ ≫ c = 𝟙 S)
    (G : Type (u + 1)) [Group G] [Finite G]
    (hG : IsUnit (Nat.card G : Γ(S, ⊤)))
    {Cη : Scheme.{u}} (q : Cη ⟶ Spec S.functionField) (j : Cη ⟶ C)
    (hCη : IsPullback q j (S.fromSpecStalk (genericPoint S)) c)
    (sη : Spec S.functionField ⟶ Cη) (hsq : sη ≫ q = 𝟙 _)
    (hsj : sη ≫ j = S.fromSpecStalk (genericPoint S) ≫ σ)
    (Z : GaloisCover G Cη) (hZ : ∃ z : Spec S.functionField ⟶ Z.P, z ≫ Z.π = sη) :
    ∃ (Y : Scheme.{u}) (p : Y ⟶ C) (_ : IsFinite p) (_ : Etale p) (ψ : Z.P ⟶ Y),
      IsPullback ψ Z.π p j :=
  SpreadingDatum.exists_isFinite_etale_isPullback_of_isNoetherian
    (fun D _ ↦ D.exists_isFinite_etale_isPullback)
    { S := S, isIntegrallyClosed_stalk := hS, C := C, c := c, σ := σ, σ_c := hσ,
      isUnit_card := hG, Cη := Cη, q := q, j := j, isPullback := hCη, sη := sη, sη_q := hsq,
      sη_j := hsj, Z := Z, exists_point := hZ }

/-- Blueprint `sbc-thm-spreading-finite-etale-galois`: Spreading a finite étale Galois cover

Let `S` be a qcqs integral normal scheme with generic point `η` and function field
`κ(η) = S.functionField`, let `c : C ⟶ S` be a qcqs smooth morphism with geometrically
connected fibres, and let `σ` be a section of `c`. Let `G` be a finite group whose order is
invertible on `S`, let `Cη` be the generic fibre of `c`, given by the cartesian square
`hCη`, and let `Z` be a finite étale Galois cover of `Cη` with group `G` carrying a
`κ(η)`-rational point above the generic point `sη` of the section. Then there is a finite
étale Galois cover `T` of `C` with group `G` and a `G`-equivariant morphism `ψ : Z.P ⟶ T.P`
making `Z` the restriction of `T` to `Cη`, that is, making the square over `j : Cη ⟶ C`
cartesian.

This is [Stacks 0EZJ], recorded as a classical input. Galois covers are taken in the sense
of `AlgebraicGeometry.Scheme.GaloisCover`, following the blueprint definition
`def-sbc-normal-dominant-galois`: their total space need not be connected. -/
@[stacks 0EZJ]
theorem GaloisCover.exists_isPullback_of_genericFibre {S C : Scheme.{u}} [CompactSpace S]
    [QuasiSeparatedSpace S] [IsIntegral S]
    (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (c : C ⟶ S) [QuasiCompact c] [QuasiSeparated c] [Smooth c] [GeometricallyConnected c]
    (σ : S ⟶ C) (hσ : σ ≫ c = 𝟙 S)
    (G : Type (u + 1)) [Group G] [Finite G]
    (hG : IsUnit (Nat.card G : Γ(S, ⊤)))
    {Cη : Scheme.{u}} (q : Cη ⟶ Spec S.functionField) (j : Cη ⟶ C)
    (hCη : IsPullback q j (S.fromSpecStalk (genericPoint S)) c)
    (sη : Spec S.functionField ⟶ Cη) (hsq : sη ≫ q = 𝟙 _)
    (hsj : sη ≫ j = S.fromSpecStalk (genericPoint S) ≫ σ)
    (Z : GaloisCover G Cη) (hZ : ∃ z : Spec S.functionField ⟶ Z.P, z ≫ Z.π = sη) :
    ∃ (T : GaloisCover G C) (ψ : Z.P ⟶ T.P), IsPullback ψ Z.π T.π j ∧
      ∀ g : G, Z.smul g ≫ ψ = ψ ≫ T.smul g := by
  obtain ⟨Y, p, _, _, ψ, hψ⟩ := exists_isFinite_etale_isPullback_of_genericFibre hS c σ hσ G hG
    q j hCη sη hsq hsj Z hZ
  have : Nonempty Cη := ⟨sη (IsLocalRing.closedPoint S.functionField)⟩
  exact exists_of_isPullback_isFinite_etale hS c q j hCη Z p ψ hψ

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.EtaleTorsor

/-- Blueprint `sk-prop-input-spreading`: Spreading a finite étale Galois cover

Let `S` be a qcqs integral normal scheme with generic point `η` and function field
`κ(η) = S.functionField`, let `c : C ⟶ S` be a qcqs smooth morphism with geometrically
connected fibres, and let `σ` be a section of `c`. Let `M` be a finite abelian group whose
order is invertible on `S`, let `Cη` be the generic fibre of `c`, that is, the left column of
the cartesian square

```
Cη ---j---> C
|           |
q           c
v           v
Spec κ(η) -> S
```

and let `Z` be an `M`-torsor on `Cη` — a finite étale Galois cover of `Cη` with group `M` —
carrying a `κ(η)`-rational point above the generic point `sη` of the section. Then `Z`
extends to an `M`-torsor on `C`: there is an `M`-torsor `T` on `C` and an `M`-equivariant
morphism `ψ : Z.P ⟶ T.P` making the square

```
Z.P --ψ--> T.P
 |          |
Z.π        T.π
 v          v
 Cη --j---> C
```

cartesian, so that the restriction of `T` to the generic fibre is `Z`.

This is [Stacks 0EZJ]: it is the case `G = Multiplicative M` of
`AlgebraicGeometry.Scheme.GaloisCover.exists_isPullback_of_genericFibre`. -/
@[stacks 0EZJ]
theorem exists_isPullback_of_genericFibre {S C : Scheme.{u}} [CompactSpace S]
    [QuasiSeparatedSpace S] [IsIntegral S]
    (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (c : C ⟶ S) [QuasiCompact c] [QuasiSeparated c] [Smooth c] [GeometricallyConnected c]
    (σ : S ⟶ C) (hσ : σ ≫ c = 𝟙 S)
    (M : Type (u + 1)) [AddCommGroup M] [Finite M]
    (hM : IsUnit (Nat.card M : Γ(S, ⊤)))
    {Cη : Scheme.{u}} (q : Cη ⟶ Spec S.functionField) (j : Cη ⟶ C)
    (hCη : IsPullback q j (S.fromSpecStalk (genericPoint S)) c)
    (sη : Spec S.functionField ⟶ Cη) (hsq : sη ≫ q = 𝟙 _)
    (hsj : sη ≫ j = S.fromSpecStalk (genericPoint S) ≫ σ)
    (Z : EtaleTorsor M Cη) (hZ : ∃ z : Spec S.functionField ⟶ Z.P, z ≫ Z.π = sη) :
    ∃ (T : EtaleTorsor M C) (ψ : Z.P ⟶ T.P), IsPullback ψ Z.π T.π j ∧
      ∀ m : M, Z.vadd m ≫ ψ = ψ ≫ T.vadd m := by
  obtain ⟨T, ψ, hψ, hψM⟩ := GaloisCover.exists_isPullback_of_genericFibre hS c σ hσ
    (Multiplicative M) hM q j hCη sη hsq hsj Z.toGaloisCover hZ
  exact ⟨T.toEtaleTorsor, ψ, hψ, fun m ↦ hψM (.ofAdd m)⟩

end AlgebraicGeometry.Scheme.EtaleTorsor
