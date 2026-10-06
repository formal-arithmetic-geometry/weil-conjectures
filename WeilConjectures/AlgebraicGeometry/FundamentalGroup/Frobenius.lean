/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Topology.Instances.ZMod
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor
public import WeilConjectures.AlgebraicGeometry.GeometricFrobenius

/-!
# Transport of torsors along automorphisms and the Frobenius action on `H¹`

Let `Y` be a connected scheme with a geometric point `s` and fundamental group `G = π₁(Y, s)`,
and let `e : Y ≅ Y` be an automorphism, for instance the geometric Galois Frobenius of the
geometric fibre of a curve over a finite field. Transporting a finite étale `Y`-scheme
`P ⟶ Y` along `e`, i.e. replacing its structure morphism by `P ⟶ Y ⟶ Y`, is an autoequivalence
of `FÉt(Y)` (`AlgebraicGeometry.Scheme.FiniteEtale.mapIso`), and the same construction on
torsors (`AlgebraicGeometry.Scheme.EtaleTorsor.mapIso`) is the action of `e` on
`H¹(Y_ét, M)`, in the torsor model of `H¹`.

A *transport* `τ : F_s ∘ e_* ≅ F_s` of the fibre functor, together with the induced map
`σ : G → G` with `τ (g • x) = σ g • τ x`, describes how `e` acts on monodromy:
the monodromy character of the transported torsor is that of the torsor precomposed with `σ`
(`AlgebraicGeometry.Scheme.EtaleTorsor.monodromy_mapIso`). For the Frobenius of a curve over a
finite field and the Weil group, `σ` is conjugation by a lift of Frobenius, which is the
Weil-descent clause of blueprint `lem-wf-finite-constant-h1-pi1`.

The last section states the cohomological input of the purity of rank-one sheaves
(blueprint `prop-wf-open-curve-h1-no-frobenius-fixed`): on the geometric fibre of a smooth
geometrically connected curve over `𝔽_q`, a compatible system of `ℤ / ℓⁿ`-torsors which are
all fixed by the Frobenius is trivial.

## Main definitions

- `AlgebraicGeometry.Scheme.FiniteEtale.mapIso`: transport of finite étale schemes along an
  isomorphism of the base.
- `AlgebraicGeometry.Scheme.EtaleTorsor.mapIso`: transport of torsors along an isomorphism of
  the base.

## Main statements

- `AlgebraicGeometry.Scheme.EtaleTorsor.monodromy_mapIso`: the monodromy of a transported
  torsor.
- `AlgebraicGeometry.Scheme.EtaleTorsor.monodromy_eq_one_of_section`: a torsor with a section
  has trivial monodromy.
- `AlgebraicGeometry.Scheme.EtaleTorsor.exists_section_of_isIsomorphic_mapIso`: Frobenius-fixed
  compatible systems of `ℤ / ℓⁿ`-torsors on a curve over `𝔽̄_q` are trivial.
-/

@[expose] public section

universe u

open CategoryTheory Limits PreGaloisCategory

namespace AlgebraicGeometry.Scheme

namespace FiniteEtale

variable {Y Y' : Scheme.{u}} (e : Y ≅ Y')

/-- The transport `P ↦ (P ⟶ Y ⟶ Y')` of finite étale schemes along an isomorphism
`e : Y ≅ Y'`. For an automorphism `e` of `Y` this is the push-forward `e_*`, i.e. the pullback
along `e⁻¹`. -/
noncomputable def mapIso : Y.FiniteEtale ⥤ Y'.FiniteEtale where
  obj P := ⟨MorphismProperty.Over.mk ⊤ (P.obj.hom ≫ e.hom)
    (by have : Etale P.obj.hom := P.obj.prop; infer_instance),
    by have := P.property; exact inferInstanceAs (IsFinite (P.obj.hom ≫ e.hom))⟩
  map {P Q} f := ObjectProperty.homMk
    (MorphismProperty.Over.homMk f.hom.left (by simp))
  map_id _ := rfl
  map_comp _ _ := rfl

end FiniteEtale

namespace EtaleTorsor

variable {M : Type (u + 1)} [AddCommGroup M] [Finite M] {Y Y' : Scheme.{u}}

/-- The transport of an `M`-torsor `t` along an isomorphism `e : Y ≅ Y'`: the same total space
and `M`-action, with structure morphism `t.π ≫ e.hom`. For an automorphism `e` of `Y` this is
the action of `e` on `H¹(Y_ét, M)` in the torsor model. -/
noncomputable def mapIso (t : EtaleTorsor M Y) (e : Y ≅ Y') : EtaleTorsor M Y' where
  P := t.P
  π := t.π ≫ e.hom
  isFinite := by have := t.isFinite; infer_instance
  etale := by have := t.etale; infer_instance
  surjective := by have := t.surjective; infer_instance
  vadd := t.vadd
  vadd_π m := by rw [← Category.assoc, t.vadd_π]
  zero_vadd := t.zero_vadd
  add_vadd := t.add_vadd
  isIso_sigmaDesc := by
    have := t.isIso_sigmaDesc
    let i := pullback.map t.π t.π (t.π ≫ e.hom) (t.π ≫ e.hom) (𝟙 t.P) (𝟙 t.P) e.hom
      (by simp) (by simp)
    convert (inferInstance : IsIso ((Sigma.desc fun m : M ↦ pullback.lift (f := t.π)
      (g := t.π) (t.vadd m) (𝟙 t.P) (by simp [t.vadd_π])) ≫ i)) using 1
    refine Sigma.hom_ext _ _ fun m ↦ ?_
    apply pullback.hom_ext <;> simp [i]

@[simp]
lemma mapIso_P (t : EtaleTorsor M Y) (e : Y ≅ Y') : (t.mapIso e).P = t.P := rfl

@[simp]
lemma mapIso_π (t : EtaleTorsor M Y) (e : Y ≅ Y') : (t.mapIso e).π = t.π ≫ e.hom := rfl

lemma toFiniteEtale_mapIso (t : EtaleTorsor M Y) (e : Y ≅ Y') :
    (t.mapIso e).toFiniteEtale = (FiniteEtale.mapIso e).obj t.toFiniteEtale := rfl

lemma vaddHom_mapIso (t : EtaleTorsor M Y) (e : Y ≅ Y') (m : M) :
    (t.mapIso e).vaddHom m = (FiniteEtale.mapIso e).map (t.vaddHom m) := rfl

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω]

section Monodromy

open FiniteEtale

open scoped FintypeCatDiscrete

variable [ConnectedSpace Y] (s : Spec (.of Ω) ⟶ Y) (G : Type u) [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [∀ P, MulAction G ((fiber s).obj P)]
  [IsFundamentalGroup (fiber s) G] [TopologicalSpace M] [DiscreteTopology M]

/-- Blueprint `lem-wf-finite-constant-h1-pi1`: Finite constant torsors and the etale
fundamental group, the Weil-descent clause.

Let `e` be an automorphism of `Y` and `τ : F_s ∘ e_* ≅ F_s` a transport of the fibre functor,
with `σ : G → G` the induced map, `τ (g • x) = σ g • τ x`. Then the monodromy character of the
transported torsor `e_* P` is `g ↦ f_P (σ g)`. For the Frobenius of a curve over a finite field
and a lift `γ` of Frobenius to the Weil group, `σ` is conjugation by `γ`, so the Frobenius acts
on `H¹(Y, M) = Hom_cont(π₁(Y, s), M)` by `f ↦ (g ↦ f (γ⁻¹ g γ))`, up to the convention for
`γ`. -/
lemma monodromy_mapIso (e : Y ≅ Y) (τ : FiniteEtale.mapIso e ⋙ fiber s ≅ fiber s) (σ : G → G)
    (hσ : ∀ P (g : G) (x : (fiber s).obj ((FiniteEtale.mapIso e).obj P)),
      τ.hom.app P (g • x) = σ g • τ.hom.app P x)
    (t : EtaleTorsor M Y) (g : G) :
    (t.mapIso e).monodromy s G g = t.monodromy s G (σ g) := by
  let P := t.toFiniteEtale
  let x := ((t.mapIso e).nonempty_fiber s).some
  refine ((t.mapIso e).monodromy_eq_iff s G g x _).mpr ?_
  have hinj : Function.Injective (τ.hom.app P) :=
    (ConcreteCategory.bijective_of_isIso (τ.hom.app P)).1
  have h1 := ConcreteCategory.congr_hom
    (τ.hom.naturality (t.vaddHom (t.monodromy s G (σ g)).toAdd))
    (x : (FiniteEtale.mapIso e ⋙ fiber s).obj P)
  simp only [Functor.comp_map, ConcreteCategory.comp_apply] at h1
  refine hinj (h1.trans ?_)
  rw [t.fiber_map_vaddHom_monodromy s G (σ g)]
  exact (hσ P g x).symm

/-- A torsor with a section has trivial monodromy: the point of the geometric fibre through the
section is the image of the unique point of the geometric fibre of `Y` itself, which is fixed by
`G`. -/
lemma monodromy_eq_one_of_section (t : EtaleTorsor M Y) {σ : Y ⟶ t.P} (hσ : σ ≫ t.π = 𝟙 Y) :
    t.monodromy s G = 1 := by
  let T : Y.FiniteEtale := ⟨MorphismProperty.Over.mk ⊤ (𝟙 Y) inferInstance,
    inferInstanceAs (IsFinite (𝟙 Y))⟩
  let S : T ⟶ t.toFiniteEtale := ObjectProperty.homMk (MorphismProperty.Over.homMk σ hσ)
  let x₀ : (fiber s).obj T := Over.homMk s (Category.comp_id s)
  have hx₀ (g : G) : g • x₀ = x₀ := fiber_ext s <| by
    rw [← Category.comp_id (g • x₀).left, ← Category.comp_id x₀.left]
    exact (fiber_left_comp s (g • x₀)).trans (fiber_left_comp s x₀).symm
  ext g
  let x := (fiber s).map S x₀
  refine congrArg Multiplicative.toAdd ((t.monodromy_eq_iff s G g x 0).mpr ?_)
  rw [t.fiber_map_vaddHom_zero s, ← IsNaturalSMul.naturality g S x₀, hx₀]

end Monodromy

section Curve

open FiniteEtale

/-- Blueprint `prop-wf-open-curve-h1-no-frobenius-fixed`: No Frobenius-fixed compatible class
on an open normal curve.

Let `U₀` be a smooth geometrically connected curve over a finite field `K = 𝔽_q`, let
`U = U₀ ×_K K̄` be its geometric fibre with geometric point `s` and fundamental group
`G = π₁(U, s)`, and let `ℓ ≠ char K`. In the torsor model of `H¹(U, ℤ / ℓⁿ)`, the geometric
Frobenius acts by transport along the geometric Galois Frobenius `g_U`. A compatible system of
classes `(z_n) ∈ lim_n H¹(U, ℤ / ℓⁿ)` — torsors `t n` whose monodromy characters are
compatible under reduction — all of which are fixed by the Frobenius is zero: every `t n` has
a section.

The proof compares `U` with its smooth compactification `C`: the residue sequence
`0 → H¹(C) → H¹(U) → ⊕_{x ∈ C - U} ℤ_ℓ(-1)` (blueprint `lem-wf-open-curve-residue-sequence`)
reduces to the proper case, where `lim_n H¹(C, ℤ / ℓⁿ)` is the dual of the Tate module of the
Jacobian by Poincaré duality and Kummer theory (blueprints `lem-wf-curve-finite-level-pd`,
`lem-wf-curve-h1-dual-tate-module`), on which Frobenius has no fixed vector because
`J₀(𝔽_q)` is finite (blueprints `lem-wf-finite-field-tate-no-fixed`,
`lem-wf-proper-curve-compatible-h1-no-fixed`). None of these inputs (cup products, purity for
`C - U ⊆ C`, the Jacobian and its Tate module as a Galois module) is available, so the
statement is recorded without proof. -/
theorem exists_section_of_isIsomorphic_mapIso {K : Type u} [Field K] [Finite K]
    {U : Scheme.{u}} (p : U ⟶ Spec (.of K)) [IsCurve p] [SmoothOfRelativeDimension 1 p]
    [GeometricallyConnected p] (l : ℕ) [Fact l.Prime] [Fact (ringChar K ≠ l)]
    [ConnectedSpace p.geometricFiber] (s : Spec (.of (AlgebraicClosure K)) ⟶ p.geometricFiber)
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [∀ P, MulAction G ((fiber s).obj P)] [IsFundamentalGroup (fiber s) G]
    (t : ∀ n : ℕ, EtaleTorsor (ULift.{u + 1} (ZMod (l ^ n))) p.geometricFiber)
    (ht : ∀ n g, ZMod.castHom (pow_dvd_pow l (Nat.le_add_right n 1)) (ZMod (l ^ n))
      ((t (n + 1)).monodromy s G g).toAdd.down = ((t n).monodromy s G g).toAdd.down)
    (hfix : ∀ n, ((t n).mapIso p.geometricGaloisFrobenius).IsIsomorphic (t n)) (n : ℕ) :
    ∃ σ : p.geometricFiber ⟶ (t n).P, σ ≫ (t n).π = 𝟙 _ := by
  sorry

end Curve

end EtaleTorsor

end AlgebraicGeometry.Scheme
