/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Topology.Instances.ZMod
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.GeometricPoints
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Curve.Compactification
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Functoriality
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor
public import WeilConjectures.AlgebraicGeometry.GeometricFrobenius
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian
public import WeilConjectures.GroupTheory.TorsionCharacter

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

The last section proves the cohomological input of the purity of rank-one sheaves
(blueprint `prop-wf-open-curve-h1-no-frobenius-fixed`): on the geometric fibre of a smooth
geometrically connected curve over `𝔽_q`, a compatible system of `ℤ / ℓⁿ`-torsors which are
all fixed by the Frobenius is trivial. The open case reduces to the proper case through the
smooth compactification and the residue sequence
(`AlgebraicGeometry.Scheme.EtaleTorsor.exists_extension_of_isIsomorphic_mapIso`). In the proper
case, the duality between `H¹(C, ℤ / ℓⁿ)` and `Pic(C)[ℓⁿ] = J₀(K̄)[ℓⁿ]`
(`AlgebraicGeometry.Scheme.EtaleTorsor.exists_picTorsionPairing`) turns the system into a
compatible system of Frobenius-invariant characters of `J₀(K̄)[ℓⁿ]`, which vanishes because the
Frobenius has finitely many fixed points `J₀(𝔽_q)`
(`AddSubgroup.eq_zero_of_forall_map_eq_of_finite_fixedPoints`).

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
- `AlgebraicGeometry.Scheme.EtaleTorsor.exists_section_of_isIsomorphic_mapIso_of_isProper`: the
  same for a proper curve.
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

open FiniteEtale MonoidalCategory CartesianMonoidalCategory MonObj

variable {K : Type u} [Field K] [Finite K]

/-- The geometric Galois Frobenius of the geometric fibre `C = C₀ ×_K K̄` is the action
`𝟙 × Spec σ` of the geometric Frobenius `σ ∈ Gal(K̄ / K)`. -/
lemma _root_.AlgebraicGeometry.Scheme.Hom.geometricGaloisFrobenius_hom_eq_geometricFiberGaloisMap
    [Fintype K] {C : Scheme.{u}} (p : C ⟶ Spec (.of K)) :
    p.geometricGaloisFrobenius.hom = p.geometricFiberGaloisMap
      (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K)).toAlgHom := by
  rw [Scheme.Hom.geometricGaloisFrobenius, asIso_hom, Scheme.Hom.geometricFiberGaloisMap]
  congr 1
  rw [Scheme.specAlgebraicClosureMap_left, specGeometricFrobenius_hom]
  rfl

/-- Blueprint `lem-wf-curve-h1-dual-tate-module`: Untwisted integral classes form the dual Tate
module, at finite level (the isomorphisms (4.3) with `J[ℓⁿ](K̄) = Pic(C)[ℓⁿ]`).

Let `C₀` be a proper smooth geometrically connected curve over a finite field `K`, `C` its
geometric fibre and `ℓ ≠ char K`. The cup product followed by the trace
`H¹(C, ℤ / ℓⁿ) × H¹(C, μ_{ℓⁿ}) ⟶ H²(C, μ_{ℓⁿ}) = ℤ / ℓⁿ` is perfect (blueprint
`lem-wf-curve-finite-level-pd`), and Kummer theory identifies `H¹(C, μ_{ℓⁿ})` with the
`ℓⁿ`-torsion of `Pic(C)` (blueprint `lem-wf-curve-kummer-jacobian-tate-module`). In the torsor
model of `H¹(C, ℤ / ℓⁿ)` this gives maps `Ψ n` from `ℤ / ℓⁿ`-torsors to characters of
`Pic(C)[ℓⁿ]` such that

* a torsor with zero character has a section (nondegeneracy);
* isomorphic torsors have the same character;
* the transport along the geometric Galois Frobenius `g` corresponds to pulling back line
  bundles along `g` (invariance of cup product and trace under the automorphism `g` of `C`);
* the reduction `ℤ / ℓⁿ⁺¹ → ℤ / ℓⁿ` of torsors corresponds to the `ℓ`-th power map
  `Pic(C)[ℓⁿ⁺¹] → Pic(C)[ℓⁿ]` (the compatibility of the Kummer sequences and traces). -/
theorem exists_picTorsionPairing {C : Scheme.{u}}
    (p : C ⟶ Spec (.of K)) [IsCurve p] [SmoothOfRelativeDimension 1 p] [IsProper p]
    [GeometricallyConnected p] (l : ℕ) [Fact l.Prime] [Fact (ringChar K ≠ l)]
    [ConnectedSpace p.geometricFiber] (s : Spec (.of (AlgebraicClosure K)) ⟶ p.geometricFiber)
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [∀ P, MulAction G ((fiber s).obj P)] [IsFundamentalGroup (fiber s) G] :
    ∃ Ψ : ∀ n : ℕ, EtaleTorsor (ULift.{u + 1} (ZMod (l ^ n))) p.geometricFiber →
        (AddSubgroup.torsionBy (Additive p.geometricFiber.Pic) ((l : ℤ) ^ n) →+ ZMod (l ^ n)),
      (∀ n t, Ψ n t = 0 → ∃ σ : p.geometricFiber ⟶ t.P, σ ≫ t.π = 𝟙 _) ∧
      (∀ n t₁ t₂, t₁.IsIsomorphic t₂ → Ψ n t₁ = Ψ n t₂) ∧
      (∀ n t y, Ψ n (t.mapIso p.geometricGaloisFrobenius) y =
        Ψ n t ⟨(Scheme.Pic.mapHom p.geometricGaloisFrobenius.hom).toAdditive y,
          AddSubgroup.apply_mem_torsionBy _ y.2⟩) ∧
      ∀ n (t : EtaleTorsor (ULift.{u + 1} (ZMod (l ^ n))) p.geometricFiber)
        (t' : EtaleTorsor (ULift.{u + 1} (ZMod (l ^ (n + 1)))) p.geometricFiber),
        (∀ g, ZMod.castHom (pow_dvd_pow l (Nat.le_add_right n 1)) (ZMod (l ^ n))
          (t'.monodromy s G g).toAdd.down = (t.monodromy s G g).toAdd.down) →
        ∀ y : AddSubgroup.torsionBy (Additive p.geometricFiber.Pic) ((l : ℤ) ^ (n + 1)),
          Ψ n t ⟨(l : ℤ) • (y : Additive p.geometricFiber.Pic),
            AddSubgroup.zsmul_mem_torsionBy_pow y.2⟩ =
          ZMod.castHom (pow_dvd_pow l (Nat.le_add_right n 1)) (ZMod (l ^ n)) (Ψ (n + 1) t' y) := by
  sorry

/-- Blueprint `lem-wf-proper-curve-compatible-h1-no-fixed`: No fixed compatible `H¹`-system on a
proper curve.

The proper case of
`AlgebraicGeometry.Scheme.EtaleTorsor.exists_section_of_isIsomorphic_mapIso`: on the geometric
fibre `C` of a proper smooth geometrically connected curve over `𝔽_q`, a compatible system of
`ℤ / ℓⁿ`-torsors all fixed by the Frobenius is trivial.

Through the pairings `AlgebraicGeometry.Scheme.EtaleTorsor.exists_picTorsionPairing` and the
Jacobian `J₀` (`AlgebraicGeometry.JacobianTorsionDatum.nonempty`), such a system is a compatible
system of Frobenius-invariant characters of `J₀(K̄)[ℓⁿ]`. Since the Frobenius has only finitely
many fixed points on `J₀(K̄)`, namely `J₀(𝔽_q)`, such a system vanishes
(`AddSubgroup.eq_zero_of_forall_map_eq_of_finite_fixedPoints`). -/
theorem exists_section_of_isIsomorphic_mapIso_of_isProper
    {U : Scheme.{u}} (p : U ⟶ Spec (.of K)) [IsCurve p] [SmoothOfRelativeDimension 1 p]
    [IsProper p] [GeometricallyConnected p] (l : ℕ) [Fact l.Prime] [Fact (ringChar K ≠ l)]
    [ConnectedSpace p.geometricFiber] (s : Spec (.of (AlgebraicClosure K)) ⟶ p.geometricFiber)
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [∀ P, MulAction G ((fiber s).obj P)] [IsFundamentalGroup (fiber s) G]
    (t : ∀ n : ℕ, EtaleTorsor (ULift.{u + 1} (ZMod (l ^ n))) p.geometricFiber)
    (ht : ∀ n g, ZMod.castHom (pow_dvd_pow l (Nat.le_add_right n 1)) (ZMod (l ^ n))
      ((t (n + 1)).monodromy s G g).toAdd.down = ((t n).monodromy s G g).toAdd.down)
    (hfix : ∀ n, ((t n).mapIso p.geometricGaloisFrobenius).IsIsomorphic (t n)) (n : ℕ) :
    ∃ σ : p.geometricFiber ⟶ (t n).P, σ ≫ (t n).π = 𝟙 _ := by
  have hl : l.Prime := Fact.out
  let _ : Fintype K := Fintype.ofFinite K
  have : Smooth p := SmoothOfRelativeDimension.smooth 1 p
  have := GeometricallyIrreducible.of_smooth_of_geometricallyConnected p
  have : GeometricallyIntegral p := .of_geometricallyReduced_of_geometricallyIrreducible _
  obtain ⟨d⟩ := JacobianTorsionDatum.nonempty p l
  obtain ⟨Ψ, h0, hiso, hfrob, hcompat⟩ := exists_picTorsionPairing p l s G
  set σ₀ := FiniteField.geometricFrobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K)
  let A := Additive (Scheme.specAlgebraicClosure K ⟶ d.J)
  let e := IsAbelianVariety.geometricPointsAddEquiv (A := d.J) σ₀
  let ψ (m : ℕ) : AddSubgroup.torsionBy A ((l : ℤ) ^ m) →+ ZMod (l ^ m) :=
    (Ψ m (t m)).comp (d.equivTorsion m).toAddMonoidHom
  have hfixfin : {a | e.toAddMonoidHom a = a}.Finite := by
    refine (IsAbelianVariety.finite_setOf_frobenius_fixed d.J).subset fun a (ha : e a = a) ↦ ?_
    change IsAbelianVariety.geometricPointsAddEquiv _ a = a
    rw [← inv_inv (FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K)),
      IsAbelianVariety.geometricPointsAddEquiv_inv,
      ← FiniteField.geometricFrobeniusAlgEquivOfAlgebraic_eq_inv]
    exact (AddEquiv.symm_apply_eq _).2 ha.symm
  have hσ (m : ℕ) (y : AddSubgroup.torsionBy A ((l : ℤ) ^ m)) :
      ψ m ⟨e.toAddMonoidHom y, AddSubgroup.apply_mem_torsionBy _ y.2⟩ = ψ m y := by
    have hg := d.equivTorsion_galois m σ₀ y
    rw [← Scheme.Hom.geometricGaloisFrobenius_hom_eq_geometricFiberGaloisMap] at hg
    change Ψ m (t m) (d.equivTorsion m ⟨e y, _⟩) = Ψ m (t m) (d.equivTorsion m y)
    rw [show d.equivTorsion m ⟨e y, _⟩ =
        ⟨(Scheme.Pic.mapHom p.geometricGaloisFrobenius.hom).toAdditive (d.equivTorsion m y),
          AddSubgroup.apply_mem_torsionBy _ (d.equivTorsion m y).2⟩ from
      Subtype.ext hg, ← hfrob, hiso m _ _ (hfix m)]
  have hψ (m : ℕ) (y : AddSubgroup.torsionBy A ((l : ℤ) ^ (m + 1))) :
      ψ m ⟨(l : ℤ) • (y : A), AddSubgroup.zsmul_mem_torsionBy_pow y.2⟩ =
        ZMod.castHom (pow_dvd_pow l (Nat.le_succ m)) _ (ψ (m + 1) y) := by
    change Ψ m (t m) (d.equivTorsion m ⟨_, _⟩) = ZMod.castHom (pow_dvd_pow l (Nat.le_succ m)) _
      (Ψ (m + 1) (t (m + 1)) (d.equivTorsion (m + 1) y))
    rw [show d.equivTorsion m ⟨(l : ℤ) • (y : A), AddSubgroup.zsmul_mem_torsionBy_pow y.2⟩ =
        ⟨(l : ℤ) • (d.equivTorsion (m + 1) y : Additive p.geometricFiber.Pic),
          AddSubgroup.zsmul_mem_torsionBy_pow (d.equivTorsion (m + 1) y).2⟩ from
      Subtype.ext (d.equivTorsion_zsmul m y)]
    exact hcompat m (t m) (t (m + 1)) (ht m) _
  have hψ0 := AddSubgroup.eq_zero_of_forall_map_eq_of_finite_fixedPoints hl e.toAddMonoidHom
    hfixfin (IsAbelianVariety.finite_torsionBy_geometricPoints d.J l)
    (IsAbelianVariety.exists_zsmul_eq_geometricPoints d.J l hl.pos) ψ hσ hψ n
  refine h0 n (t n) (AddMonoidHom.ext fun y ↦ ?_)
  obtain ⟨x, rfl⟩ := (d.equivTorsion n).surjective y
  exact DFunLike.congr_fun hψ0 x

/-- Blueprint `lem-wf-open-curve-residue-sequence`: Finite-level residue sequences on an open
curve, the consequence used for compatible Frobenius-fixed systems.

Let `U₀ ⊆ C₀` be a smooth geometrically connected curve over `K = 𝔽_q` in a smooth proper
compactification `c`, with geometric fibres `U ⊆ C` and `j : U ⟶ C`. A compatible system of
`ℤ / ℓⁿ`-torsors on `U` all fixed by the Frobenius extends to a compatible system of
Frobenius-fixed torsors on `C`. Indeed, by purity the residues of the system at the finitely many
boundary points form a compatible system in `lim_n H⁰(D, ℤ / ℓⁿ(-1))`, fixed by a power
`Φ_Q`, `Q = q ^ m`, of the Frobenius which fixes every boundary point and acts there as
multiplication by `Q`; so the residues vanish, and the exact sequence
`0 → H¹(C) → H¹(U) → H⁰(D, ℤ / ℓⁿ(-1))` gives the unique extensions, which are compatible and
Frobenius-fixed by uniqueness. -/
theorem exists_extension_of_isIsomorphic_mapIso
    {U : Scheme.{u}} (p : U ⟶ Spec (.of K)) [IsCurve p] [SmoothOfRelativeDimension 1 p]
    [GeometricallyConnected p] (c : Compactification p) [IsCurve c.g]
    [SmoothOfRelativeDimension 1 c.g] [GeometricallyConnected c.g] (l : ℕ) [Fact l.Prime]
    [Fact (ringChar K ≠ l)] [ConnectedSpace p.geometricFiber]
    [ConnectedSpace c.g.geometricFiber] (s : Spec (.of (AlgebraicClosure K)) ⟶ p.geometricFiber)
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [∀ P, MulAction G ((fiber s).obj P)] [IsFundamentalGroup (fiber s) G]
    (t : ∀ n : ℕ, EtaleTorsor (ULift.{u + 1} (ZMod (l ^ n))) p.geometricFiber)
    (ht : ∀ n g, ZMod.castHom (pow_dvd_pow l (Nat.le_add_right n 1)) (ZMod (l ^ n))
      ((t (n + 1)).monodromy s G g).toAdd.down = ((t n).monodromy s G g).toAdd.down)
    (hfix : ∀ n, ((t n).mapIso p.geometricGaloisFrobenius).IsIsomorphic (t n)) :
    ∃ t' : ∀ n : ℕ, EtaleTorsor (ULift.{u + 1} (ZMod (l ^ n))) c.g.geometricFiber,
      (∀ n, Nonempty ((FiniteEtale.pullback (p.geometricFiberMap c.i c.comm.symm)).obj
        (t' n).toFiniteEtale ≅ (t n).toFiniteEtale)) ∧
      (∀ n, ((t' n).mapIso c.g.geometricGaloisFrobenius).IsIsomorphic (t' n)) ∧
      ∀ (s' : Spec (.of (AlgebraicClosure K)) ⟶ c.g.geometricFiber) (G' : Type u) [Group G']
        [TopologicalSpace G'] [IsTopologicalGroup G'] [CompactSpace G']
        [∀ P, MulAction G' ((fiber s').obj P)] [IsFundamentalGroup (fiber s') G'] (n : ℕ) (g : G'),
        ZMod.castHom (pow_dvd_pow l (Nat.le_add_right n 1)) (ZMod (l ^ n))
          ((t' (n + 1)).monodromy s' G' g).toAdd.down = ((t' n).monodromy s' G' g).toAdd.down := by
  sorry
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
`lem-wf-proper-curve-compatible-h1-no-fixed`). Here the residue step is
`AlgebraicGeometry.Scheme.EtaleTorsor.exists_extension_of_isIsomorphic_mapIso` and the proper
case is `AlgebraicGeometry.Scheme.EtaleTorsor.exists_section_of_isIsomorphic_mapIso_of_isProper`;
a section of the extended torsor over `C` restricts to a section over `U`. -/
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
  -- Reduce to the smooth proper compactification `C₀` of `U₀`.
  obtain ⟨c, hcurve, hsm, hconn, -, -⟩ := exists_smooth_properCompactification p
  have := c.isProper
  have : ConnectedSpace c.g.geometricFiber :=
    pullback_of_geometrically (GeometricallyConnected.geometrically_connectedSpace (f := c.g)) _ _
  obtain ⟨t', ht'U, ht'fix, ht'compat⟩ :=
    exists_extension_of_isIsomorphic_mapIso p c l s G t ht hfix
  let j := p.geometricFiberMap c.i c.comm.symm
  obtain ⟨G', _, _⟩ := exists_isFundamentalGroup (s ≫ j)
  obtain ⟨σ', hσ'⟩ := exists_section_of_isIsomorphic_mapIso_of_isProper c.g l (s ≫ j) G' t'
    (ht'compat (s ≫ j) G') ht'fix n
  -- The section of the extended torsor restricts to a section over `U`.
  obtain ⟨e⟩ := ht'U n
  refine ⟨pullback.lift (j ≫ σ') (𝟙 _)
    (by change j ≫ σ' ≫ (t' n).π = 𝟙 _ ≫ j; rw [hσ', Category.comp_id, Category.id_comp]) ≫
      e.hom.hom.left, ?_⟩
  have he : e.hom.hom.left ≫ (t n).π = pullback.snd (t' n).π j :=
    MorphismProperty.Over.w e.hom.hom
  rw [Category.assoc, he]
  exact pullback.lift_snd _ _ _

end Curve

end EtaleTorsor

end AlgebraicGeometry.Scheme
