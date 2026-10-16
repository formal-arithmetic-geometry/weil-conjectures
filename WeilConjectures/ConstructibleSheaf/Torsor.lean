/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Sites.Torsor
public import WeilConjectures.ConstructibleSheaf.KernelCokernel

/-!
# Torsors on the small étale site are trivial on an étale cover

Let `G` be a sheaf of abelian groups on the small étale site of a scheme `X` and let `P` be a
`G`-torsor (`CategoryTheory.Sheaf.Torsor`). Then there is an étale cover `(Uᵢ ⟶ X)ᵢ` and
sections `sᵢ ∈ P(Uᵢ)` trivialising `P` over `Uᵢ`: for every `V ⟶ Uᵢ` the map `a ↦ a • sᵢ|_V`
is a bijection `G(V) ≃ P(V)`.

This is blueprint `lemma-constructible-torsor-trivialises` (where `G` is finite locally
constant). In the formalisation a torsor has sections locally by definition
(`CategoryTheory.Sheaf.Torsor.nonemptySieve_mem`), as in SGA 4; the blueprint's argument via
representability of `G_X`-torsors by finite étale `X`-schemes shows that the sheaf-theoretic
torsors of the blueprint have this property. So the lemma reduces to turning a covering sieve of
the small étale site into an étale cover, and needs no hypothesis on `G`.

-/

@[expose] public section

universe w u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} {G : Sheaf X.smallEtaleTopology AddCommGrpCat.{w}}

/-- Blueprint `lemma-constructible-torsor-trivialises`: Torsors under finite locally constant
sheaves.

A torsor `P` under a sheaf `G` of abelian groups on the small étale site of `X` (in particular
under a finite locally constant one) is trivial on an étale cover of `X`: there are an étale
cover `(Uᵢ ⟶ X)ᵢ` and sections `sᵢ ∈ P(Uᵢ)` such that, for every `V ⟶ Uᵢ` in the small étale
site, `a ↦ a • sᵢ|_V` is a bijection `G(V) ≃ P(V)`, i.e. `P|_{Uᵢ} ≅ G|_{Uᵢ}`. -/
theorem exists_cover_torsor_trivial (P : Sheaf.Torsor G) :
    ∃ 𝒰 : Cover.{u} etalePrecoverage X, ∀ i, ∃ s : P.sheaf.obj.obj (op (Etale.mk (𝒰.f i))),
      ∀ ⦃V : X.Etale⦄ (h : V ⟶ Etale.mk (𝒰.f i)),
        Function.Bijective fun a : G.obj.obj (op V) ↦ P.vadd (op V) a (P.sheaf.obj.map h.op s) := by
  let S := Sheaf.nonemptySieve P.sheaf.obj (Etale.mk (𝟙 X))
  have hS : S ∈ X.smallEtaleTopology _ := P.nonemptySieve_mem _
  refine ⟨Cover.ofSieve S hS, fun y ↦ ?_⟩
  obtain ⟨s₀⟩ := Cover.ofSieveHom_mem S hS y
  let φ : Etale.mk ((Cover.ofSieve S hS).f y) ⟶ Cover.ofSieveObj S hS y :=
    MorphismProperty.Over.homMk (𝟙 _) (by simp [Cover.ofSieve_f, Cover.ofSieveHom_left])
  exact ⟨P.sheaf.obj.map φ.op s₀, fun V h ↦ P.bijective_vadd (op V) _⟩

end AlgebraicGeometry.Scheme
