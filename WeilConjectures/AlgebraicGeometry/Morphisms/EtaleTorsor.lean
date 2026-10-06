/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.CategoryTheory.Sites.Torsor

/-!
# Torsors and étale `H^1`

Let `Y` be a scheme and `M` a finite abelian group. An `M`-torsor on the small étale site of
`Y` is the same thing as a finite étale surjective `Y`-scheme `P` carrying a simply
transitive action of `M` over `Y`; that is the form in which the notion is recorded here, as
`AlgebraicGeometry.Scheme.EtaleTorsor`. Simple transitivity is the statement that the
canonical morphism `∐_{m ∈ M} P ⟶ P ×_Y P` sending the `m`-th summand by `(m +ᵥ -, id)` is an
isomorphism, which is available because `M` is finite, hence `Small.{u}`.

Isomorphism of torsors is an equivalence relation
(`AlgebraicGeometry.Scheme.EtaleTorsor.setoid`), and the proposition of the blueprint
subsection `sk-prop-input-torsors` is that the quotient by it is in canonical bijection with
`H^1(Y_ét, M)`, the first sheaf cohomology of the constant sheaf with value `M`. The
statement below records that bijection together with the one further property of it that the
smooth base change proof uses: a torsor has class `0` exactly when its structure morphism
admits a section.

## Implementation notes

Two refinements of Stacks `02NE` recorded in the sketch are not part of the statement.

The first is the naturality of the bijection in the pair `(Y, M)`. The proof of the vanishing
theorem `sk-thm-vanishing` uses naturality in `Y`: it pulls a torsor back along a morphism
`Y' ⟶ Y` and concludes that its class dies. Stating it needs a pullback map
`H^1(Y_ét, M) ⟶ H^1(Y'_ét, M)` on sheaf cohomology along a morphism of schemes, which neither
Mathlib nor this repository has; recording that map is what a file completing this subsection
needs first.

The second is the criterion, for `Y` connected and `M = ℤ/dℤ`, that the torsor attached to a
class be connected — a Galois cover with group `ℤ/dℤ`, which is the input of
`sk-prop-input-spreading` — exactly when the corresponding homomorphism out of the étale
fundamental group is surjective. Mathlib has no étale fundamental group, so this is left to
the prose.

## Main definitions

- `AlgebraicGeometry.Scheme.EtaleTorsor`: an `M`-torsor over a scheme `Y`.
- `AlgebraicGeometry.Scheme.GaloisCover`: a finite étale Galois cover with group `G`, that is,
  a finite étale `G`-torsor, for a finite group `G` acting on the left.
- `AlgebraicGeometry.Scheme.EtaleTorsor.IsIsomorphic` and
  `AlgebraicGeometry.Scheme.EtaleTorsor.setoid`: the isomorphism relation on torsors, and
  the fact that it is an equivalence relation.

## Main statements

- `AlgebraicGeometry.Scheme.EtaleTorsor.exists_sheafTorsor`: `M`-torsors in the above sense
  are the same, up to isomorphism, as torsors under the constant sheaf `M` on the small étale
  site, sections of the structure morphism corresponding to global sections. The proof, by
  étale descent, is `sorry`.
- `AlgebraicGeometry.Scheme.EtaleTorsor.exists_quotientEquivSheafH`: the bijection between
  isomorphism classes of `M`-torsors on `Y` and `H^1(Y_ét, M)`, under which the class of a
  torsor vanishes exactly when the torsor has a section. It follows from the previous statement
  and the classification of torsors under an abelian sheaf by `H¹`,
  `CategoryTheory.Sheaf.Torsor.exists_quotientEquiv_H_one`.

## References

- Stacks Project, Tag `02NE`, <https://stacks.math.columbia.edu/tag/02NE>
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

variable (M : Type (u + 1)) [AddCommGroup M] [Finite M]

/-- An `M`-torsor over a scheme `Y`: a finite étale surjective `Y`-scheme with a simply
transitive action of the finite abelian group `M`.

Simple transitivity is expressed by the isomorphism `M × P ≅ P ×_Y P`, in the form that the
morphism `∐_{m ∈ M} P ⟶ P ×_Y P` whose `m`-th component is `(m +ᵥ -, id)` is an isomorphism:

```
∐_{m ∈ M} P --≅--> P ×_Y P --pr₁--> P
                                    |
                                    π
                                    v
                                    Y
```

The coproduct exists because `M` is finite, hence small. -/
structure Scheme.EtaleTorsor (Y : Scheme.{u}) where
  /-- the total space of the torsor -/
  P : Scheme.{u}
  /-- the structure morphism to the base -/
  π : P ⟶ Y
  [isFinite : IsFinite π]
  [etale : Etale π]
  [surjective : Surjective π]
  /-- the action of `M` on `P` over `Y` -/
  vadd : M → (P ⟶ P)
  /-- the action is by morphisms over `Y` -/
  vadd_π (m : M) : vadd m ≫ π = π
  /-- the zero of `M` acts as the identity -/
  zero_vadd : vadd 0 = 𝟙 P
  /-- the action is additive in the acting variable -/
  add_vadd (m n : M) : vadd (m + n) = vadd m ≫ vadd n
  /-- the action is simply transitive: `∐_{m ∈ M} P ≅ P ×_Y P` -/
  isIso_sigmaDesc : IsIso (Sigma.desc
    fun m : M ↦ pullback.lift (f := π) (g := π) (vadd m) (𝟙 P) (by simp [vadd_π]))

namespace Scheme.EtaleTorsor

variable {M} {Y : Scheme.{u}}

/-- Two `M`-torsors over `Y` are isomorphic when their total spaces are isomorphic over `Y`
by an isomorphism commuting with the `M`-actions. -/
def IsIsomorphic (t₁ t₂ : EtaleTorsor M Y) : Prop :=
  ∃ φ : t₁.P ≅ t₂.P, φ.hom ≫ t₂.π = t₁.π ∧
    ∀ m : M, t₁.vadd m ≫ φ.hom = φ.hom ≫ t₂.vadd m

lemma isIsomorphic_refl (t : EtaleTorsor M Y) : t.IsIsomorphic t :=
  ⟨Iso.refl _, by simp, by simp⟩

lemma IsIsomorphic.symm {t₁ t₂ : EtaleTorsor M Y} (h : t₁.IsIsomorphic t₂) :
    t₂.IsIsomorphic t₁ := by
  obtain ⟨φ, hπ, hv⟩ := h
  refine ⟨φ.symm, ?_, fun m ↦ ?_⟩
  · rw [Iso.symm_hom, ← hπ, Iso.inv_hom_id_assoc]
  · rw [Iso.symm_hom, Iso.comp_inv_eq, Category.assoc, hv, Iso.inv_hom_id_assoc]

lemma IsIsomorphic.trans {t₁ t₂ t₃ : EtaleTorsor M Y} (h₁ : t₁.IsIsomorphic t₂)
    (h₂ : t₂.IsIsomorphic t₃) : t₁.IsIsomorphic t₃ := by
  obtain ⟨φ, hπ, hv⟩ := h₁
  obtain ⟨ψ, hπ', hv'⟩ := h₂
  refine ⟨φ ≪≫ ψ, ?_, fun m ↦ ?_⟩
  · rw [Iso.trans_hom, Category.assoc, hπ', hπ]
  · simp only [Iso.trans_hom, ← Category.assoc, hv]
    simp only [Category.assoc, hv']

lemma isIsomorphic_equivalence : Equivalence (IsIsomorphic (M := M) (Y := Y)) :=
  ⟨isIsomorphic_refl, IsIsomorphic.symm, IsIsomorphic.trans⟩

variable (M Y) in
/-- Isomorphism of `M`-torsors over `Y` as a setoid, so that the isomorphism classes are
the quotient `Quotient (EtaleTorsor.setoid M Y)`. -/
instance setoid : Setoid (EtaleTorsor M Y) := ⟨IsIsomorphic, isIsomorphic_equivalence⟩

variable (M Y) in
/-- Blueprint `sbc-prop-torsors-h1`, the finite étale clause: an `M`-torsor on the small étale
site of `Y` is the same thing as a finite étale `Y`-scheme with a simply transitive
`M`-action.

The functor of points `P ↦ Hom_Y(-, P)`, with the action of the constant sheaf `M` induced by
the action of `M` on `P`, sends an `M`-torsor `t` in the sense of
`AlgebraicGeometry.Scheme.EtaleTorsor` to a torsor `F t` under the constant sheaf `M` in the
sense of `CategoryTheory.Sheaf.Torsor`. It induces a bijection on isomorphism classes, and the
global sections of `F t` are the sections of the structure morphism of `t`. Fully faithfulness
is étale descent of morphisms; essential surjectivity is effective étale descent of finite étale
morphisms (blueprint `thm-galois-lc-etale`, Stacks `03HC`).

Only the existence of such an assignment `F` is recorded. The proof is `sorry`: neither the
étale descent of finite étale morphisms nor the comparison of sections of the constant sheaf
with locally constant functions is available yet. -/
theorem exists_sheafTorsor :
    ∃ F : EtaleTorsor M Y → Sheaf.Torsor
        ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of M)),
      (∀ t₁ t₂, t₁ ≈ t₂ ↔ F t₁ ≈ F t₂) ∧ (∀ P, ∃ t, F t ≈ P) ∧
      ∀ t, (∃ s : Y ⟶ t.P, s ≫ t.π = 𝟙 Y) ↔ Nonempty ((F t).sheaf.obj.obj (op (⊤_ Y.Etale))) :=
  sorry

variable (M Y) in
/-- Blueprint `sk-prop-input-torsors`: Torsors and étale H^1

For a scheme `Y` and a finite abelian group `M` the isomorphism classes of `M`-torsors on
the small étale site of `Y` are in canonical bijection with the first sheaf cohomology
group `H^1(Y_ét, M)` of the constant sheaf with value `M`, under which the class of a
torsor vanishes exactly when its structure morphism admits a section, that is, exactly
when the torsor is trivial.

An `M`-torsor is, by `AlgebraicGeometry.Scheme.EtaleTorsor`, the same thing as a finite
étale surjective `Y`-scheme with a simply transitive `M`-action; the naturality of the
bijection in `(Y, M)` and the connectedness criterion of the sketch are not part of this
statement, see the implementation notes of this file.

The proof combines the classification of torsors under an abelian sheaf by `H¹`
(`CategoryTheory.Sheaf.Torsor.exists_quotientEquiv_H_one`, blueprint `thm-galois-torsor-h1`)
with the comparison of étale torsors and sheaf torsors
(`AlgebraicGeometry.Scheme.EtaleTorsor.exists_sheafTorsor`, blueprint `sbc-prop-torsors-h1`). -/
@[stacks 02NE]
theorem exists_quotientEquivSheafH :
    ∃ c : Quotient (EtaleTorsor.setoid M Y) ≃ Sheaf.H
      ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of M)) 1,
      ∀ t : EtaleTorsor M Y, c ⟦t⟧ = 0 ↔ ∃ s : Y ⟶ t.P, s ≫ t.π = 𝟙 Y := by
  obtain ⟨F, hF, hFsurj, hFsec⟩ := exists_sheafTorsor M Y
  obtain ⟨c, hc⟩ := Sheaf.Torsor.exists_quotientEquiv_H_one
    ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of M))
    terminalIsTerminal
  let Φ : Quotient (EtaleTorsor.setoid M Y) → Quotient (Sheaf.Torsor.setoid (G := _)) :=
    Quotient.map F fun t₁ t₂ h ↦ (hF t₁ t₂).1 h
  have hΦ : Function.Bijective Φ := by
    refine ⟨fun t₁ t₂ h ↦ ?_, fun P ↦ ?_⟩
    · induction t₁ using Quotient.inductionOn
      induction t₂ using Quotient.inductionOn
      exact Quotient.sound ((hF _ _).2 (Quotient.exact h))
    · induction P using Quotient.inductionOn with | h P => ?_
      obtain ⟨t, ht⟩ := hFsurj P
      exact ⟨⟦t⟧, Quotient.sound ht⟩
  exact ⟨(Equiv.ofBijective Φ hΦ).trans c, fun t ↦ (hc (F t)).trans (hFsec t).symm⟩

end Scheme.EtaleTorsor

section GaloisCover

variable (G : Type (u + 1)) [Group G] [Finite G]

/-- A finite étale Galois cover of a scheme `Y` with group `G`: a finite étale surjective
`Y`-scheme `P` on which the finite group `G` acts on the left over `Y`, simply transitively,
that is, such that the morphism `∐_{g ∈ G} P ⟶ P ×_Y P` whose `g`-th component is
`(g • -, id)` is an isomorphism. In other words, `P` is a finite étale `G`-torsor over `Y`.

This is the notion of a Galois cover with group `G` of the blueprint definition
`def-sbc-normal-dominant-galois`; as there, the total space is not required to be connected.
The quotient `P / G ≅ Y` of that definition is a consequence of the torsor condition and is
not recorded. For an abelian group written additively this is
`AlgebraicGeometry.Scheme.EtaleTorsor`, see `AlgebraicGeometry.Scheme.EtaleTorsor.toGaloisCover`
and `AlgebraicGeometry.Scheme.GaloisCover.toEtaleTorsor`. -/
structure Scheme.GaloisCover (Y : Scheme.{u}) where
  /-- the total space of the cover -/
  P : Scheme.{u}
  /-- the structure morphism to the base -/
  π : P ⟶ Y
  [isFinite : IsFinite π]
  [etale : Etale π]
  [surjective : Surjective π]
  /-- the left action of `G` on `P` over `Y` -/
  smul : G → (P ⟶ P)
  /-- the action is by morphisms over `Y` -/
  smul_π (g : G) : smul g ≫ π = π
  /-- the unit of `G` acts as the identity -/
  one_smul : smul 1 = 𝟙 P
  /-- the action is a left action: `(g * h) • x = g • (h • x)` -/
  mul_smul (g h : G) : smul (g * h) = smul h ≫ smul g
  /-- the action is simply transitive: `∐_{g ∈ G} P ≅ P ×_Y P` -/
  isIso_sigmaDesc : IsIso (Sigma.desc
    fun g : G ↦ pullback.lift (f := π) (g := π) (smul g) (𝟙 P) (by simp [smul_π]))

end GaloisCover

namespace Scheme

variable {M : Type (u + 1)} [AddCommGroup M] [Finite M] {Y : Scheme.{u}}

/-- An `M`-torsor, for `M` a finite abelian group, as a Galois cover with group
`Multiplicative M`. -/
@[simps]
def EtaleTorsor.toGaloisCover (t : EtaleTorsor M Y) : GaloisCover (Multiplicative M) Y where
  P := t.P
  π := t.π
  isFinite := t.isFinite
  etale := t.etale
  surjective := t.surjective
  smul g := t.vadd g.toAdd
  smul_π g := t.vadd_π _
  one_smul := t.zero_vadd
  mul_smul g h := by rw [toAdd_mul, add_comm, t.add_vadd]
  isIso_sigmaDesc := t.isIso_sigmaDesc

/-- A Galois cover with group `Multiplicative M`, for `M` a finite abelian group, as an
`M`-torsor. -/
@[simps]
def GaloisCover.toEtaleTorsor (t : GaloisCover (Multiplicative M) Y) : EtaleTorsor M Y where
  P := t.P
  π := t.π
  isFinite := t.isFinite
  etale := t.etale
  surjective := t.surjective
  vadd m := t.smul (.ofAdd m)
  vadd_π m := t.smul_π _
  zero_vadd := t.one_smul
  add_vadd m n := by rw [add_comm, ofAdd_add, t.mul_smul]
  isIso_sigmaDesc := t.isIso_sigmaDesc

end Scheme

end AlgebraicGeometry
