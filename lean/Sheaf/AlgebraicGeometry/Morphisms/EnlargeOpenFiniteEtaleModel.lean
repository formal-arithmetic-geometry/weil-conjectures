/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A3
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor

import Sheaf.AlgebraicGeometry.Morphisms.LocalFiniteEtaleModelOverlap
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Gluing

/-!
# Enlarging an open carrying a generic finite étale cover

Source: Stacks Project, Tag 0EYJ.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- An extension over a proper open containing the generic point extends over a strictly
larger open. This is the local extension step, before Noetherian induction.

Source: Stacks Project, Tag 0EYJ, proof of Lemma 58.31.8, the local claim and its spreading.
(blueprint: lem-sbc-enlarge-open-finite-etale-model)

Proof:
Let s be a generic point of an irreducible component of S minus U. The inverse image
of U in Spec O(S,s) is the punctured spectrum. Normality of the smooth total space
implies full faithfulness of restriction of finite étale covers to the generic fibre,
so the action on Z extends uniquely to the given model over c⁻¹(U). The torsor identities
and surjectivity follow from generic comparison on this normal integral family.
If the local base has dimension one it is a trait. Tameness follows because the
ramification index divides the invertible group order. The tame normalization and
trait test, using the split section fibre, give étaleness near the section. The special
fibre is irreducible, so purity extends the cover across it (0EYG, 0EYH, 0EYI, 0EYE).
In higher dimension normality gives depth two on the local base, and flatness transfers
it to the total space. Extend the finite algebra by 0EY6; this extension is unique among
depth-two extensions and commutes with flat base change. Complete a smooth affine
neighbourhood of the section: it is a power series ring over the local base. The
restriction to the punctured section is split, since it is finite étale over a normal
integral base and split generically. By 0EY9 the cover on the punctured completion is
split, so its depth-two extension is split. Flat descent and 0EYB imply étaleness on the
missing fibre. Spread this local extension and glue it to the original one by 0BQ5
and 0EY3. The resulting open V contains U and s, hence U < V, and still contains the
generic point. For a disconnected torsor apply the connected argument to each component
and its stabilizer. Stabilizer orders divide the invertible group order; the split
section fibre meets every component. Induce and take the finite disjoint union to
recover Z, and retain only the underlying finite étale cover and comparison. -/
theorem GaloisCover.exists_larger_open_finiteEtale_model {S C : Scheme.{u}} [IsNoetherian S]
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
    (Z : GaloisCover G Cη) (hZ : ∃ z : Spec S.functionField ⟶ Z.P, z ≫ Z.π = sη)
    (U : S.Opens) (hηU : genericPoint S ∈ U) (hU : U ≠ ⊤)
    (jU : Cη ⟶ (c ⁻¹ᵁ U).toScheme) (P : Scheme.{u})
    (π : P ⟶ (c ⁻¹ᵁ U).toScheme) (ψ : Z.P ⟶ P)
    (hjU : jU ≫ (c ⁻¹ᵁ U).ι = j) (hπ : IsFinite π) (hEt : Etale π)
    (hψ : IsPullback ψ Z.π π jU) :
    ∃ V : S.Opens, U < V ∧ genericPoint S ∈ V ∧
      ∃ (jV : Cη ⟶ (c ⁻¹ᵁ V).toScheme) (P' : Scheme.{u})
        (π' : P' ⟶ (c ⁻¹ᵁ V).toScheme) (ψ' : Z.P ⟶ P'),
        jV ≫ (c ⁻¹ᵁ V).ι = j ∧ IsFinite π' ∧ Etale π' ∧
          IsPullback ψ' Z.π π' jV := by
  classical
  let PA : (c ⁻¹ᵁ U).toScheme.FiniteEtale :=
    ⟨MorphismProperty.Over.mk ⊤ π hEt, hπ⟩
  obtain ⟨W, s, hsU, hsW, Q, ⟨e⟩⟩ :=
    GaloisCover.exists_local_finiteEtale_model_overlap hS c σ hσ G hG
      q j hCη sη hsq hsj Z hZ U hηU hU jU PA ψ hjU hψ
  let V := U ⊔ W
  have hUV : U < V := by
    apply lt_of_le_not_ge le_sup_left
    intro hVU
    exact hsU (hVU (show s ∈ V from Or.inr hsW))
  have hηV : genericPoint S ∈ V := Or.inl hηU
  have hA : c ⁻¹ᵁ U ≤ c ⁻¹ᵁ V := fun x hx ↦ Or.inl hx
  have hB : c ⁻¹ᵁ W ≤ c ⁻¹ᵁ V := fun x hx ↦ Or.inr hx
  let iA := C.homOfLE hA
  let iB := C.homOfLE hB
  let dA := C.homOfLE (inf_le_left : (c ⁻¹ᵁ U) ⊓ (c ⁻¹ᵁ W) ≤ c ⁻¹ᵁ U)
  let dB := C.homOfLE (inf_le_right : (c ⁻¹ᵁ U) ⊓ (c ⁻¹ᵁ W) ≤ c ⁻¹ᵁ W)
  have H : IsPullback dA dB iA iB := isPullback_opens_inf_le hA hB
  have hcov : ∀ x, x ∈ Set.range iA ∨ x ∈ Set.range iB := by
    intro x
    obtain hx | hx := x.2
    · left
      exact ⟨⟨x.1, hx⟩, Subtype.ext (by simp [iA])⟩
    · right
      exact ⟨⟨x.1, hx⟩, Subtype.ext (by simp [iB])⟩
  obtain ⟨PV, ⟨eA⟩⟩ :=
    FiniteEtale.exists_pullback_iso_of_isPullback dA dB iA iB H hcov PA Q e
  let a := eA.inv.hom.left
  let f := a ≫ Limits.pullback.fst PV.obj.hom iA
  have ha : a ≫ Limits.pullback.snd PV.obj.hom iA = π := FiniteEtale.hom_left_comp eA.inv
  have hf : IsPullback f π PV.obj.hom iA := by
    have haIso : IsIso a := by
      let eL := (ObjectProperty.ι _ ⋙ MorphismProperty.Over.forget _ _ _ ⋙
        Over.forget _).mapIso eA.symm
      change IsIso eL.hom
      infer_instance
    have hleft : IsPullback a π (Limits.pullback.snd PV.obj.hom iA) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by simpa using ha⟩
    simpa only [Category.id_comp] using
      hleft.paste_horiz (IsPullback.of_hasPullback PV.obj.hom iA)
  let jV := jU ≫ iA
  have hjV : jV ≫ (c ⁻¹ᵁ V).ι = j := by
    simpa [jV, iA] using hjU
  exact ⟨V, hUV, hηV, jV, PV.obj.left, PV.obj.hom, ψ ≫ f, hjV,
    PV.property, PV.obj.prop, hψ.paste_horiz hf⟩


end AlgebraicGeometry.Scheme
