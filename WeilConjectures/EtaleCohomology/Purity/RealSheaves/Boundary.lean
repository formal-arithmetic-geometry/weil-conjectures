/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RepresentationTheory.Invariants
public import WeilConjectures.ConstructibleSheaf.OpenClosed
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Weights
public import WeilConjectures.Mathlib.Topology.JacobsonSpace
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FullyFaithful
public import WeilConjectures.SixFunctors.OpenClosed.Conservative

/-!
# Boundary extension of a lisse Weil sheaf on a curve

Let `j : U₀ ↪ C₀` be a nonempty open of a curve with finite complement `S₀` and let `ℱ` be
lisse Weil on `U₀`. The ordinary direct image `J = j_* ℱ` is constructible, its stalk at a
boundary point `s` is the inertia invariants `V^{I_s}` of the local generic stalk, and a
residue Frobenius lift acts on those invariants.

Neither the henselization of a local ring of a scheme nor the inertia subgroup of a boundary
point exists in Mathlib, so a *boundary datum* (`AlgebraicGeometry.BoundaryDatum`) records
them as data on top of a `AlgebraicGeometry.WeilGroup.Restriction`: the finiteness of the
boundary, and at every boundary point an inertia subgroup of the geometric fundamental group
of `U` together with a residue Frobenius lift normalising it and restricting into the
Frobenius class of that point.

Inertia and the residue Frobenius are indexed by the boundary `S₀ = C₀ \ U₀` alone: they carry
no meaning at a point of `U₀`, and `deg_residueFrobenius` would be a statement about the junk
value of `AlgebraicGeometry.Scheme.Hom.degreeOver` at a non-closed point. The field
`boundary_subset_finitePoints` records that the boundary of an open subcurve consists of closed
points, which is what makes the residue degree `e_s` meaningful.

## Main definitions

- `AlgebraicGeometry.BoundaryDatum` : the boundary extension datum of `sk-d-real-boundary`.
- `AlgebraicGeometry.BoundaryDatum.boundaryStalk` : the boundary stalk `V^{I_s}`.
- `AlgebraicGeometry.BoundaryDatum.boundaryFrobenius` : the residue Frobenius acting on it.
- `AlgebraicGeometry.Etale.middleExtension` : the middle extension `j_* ℱ`.

## Main statements

- `AlgebraicGeometry.Scheme.isConstructibleSheaf_lowerStar` : `j_* ℱ` is constructible.
- `AlgebraicGeometry.Scheme.isIso_unit_upperStarLowerStarAdjunction` : a finite locally
  constant sheaf on a smooth curve is the direct image of its restriction to a dense open.

Both are proved from two auxiliary pointwise inputs at the boundary,
`AlgebraicGeometry.Scheme.isFiniteLocallyConstantSheaf_upperStar_middleExtension`
(the restriction of `j_* ℱ` to a boundary point is finite locally constant, a consequence of
the blueprint's identification of the boundary stalk with the inertia invariants) and
`AlgebraicGeometry.Scheme.isIso_sheafFiber_map_unit_upperStarLowerStarAdjunction` (inertia acts
trivially on the stalks of a sheaf lisse at the boundary point), which need the strict
henselization of a curve at a point and are not yet proved. The inertia-invariants
identification `lem-wf-boundary-stalk-invariants` itself is not formalised here.
-/

@[expose] public section

universe u u'

open CategoryTheory

namespace AlgebraicGeometry

open Scheme Etale

variable {K : Type u} [Field K] [Finite K] {C U : Scheme.{u}}
  {p : C ⟶ Spec (.of K)} [IsCurve p] {pU : U ⟶ Spec (.of K)} [IsCurve pU]

/-- Blueprint `sk-d-real-boundary`: Boundary extension and inertia.

A *boundary datum* for a nonempty open `j : U₀ ↪ C₀` of a curve: a restriction
`AlgebraicGeometry.WeilGroup.Restriction` of Weil groups along `j`, the finiteness of the
boundary `S₀ = C₀ \ U₀`, and, at every boundary point `s`, the inertia subgroup
`I_s = ker (Gal(K̄_s / K_s) → Gal(k(s)‾ / k(s)))` inside the geometric fundamental group of `U`,
together with a residue Frobenius lift of degree `e_s` normalising it and lying, after
restriction to `W(C₀)`, in the Frobenius conjugacy class at `s`.

The henselization `𝒪_{C₀, s}^h`, its fraction field `K_s` and the inertia subgroup are not
available in Mathlib, so they are recorded as data here. -/
structure BoundaryDatum (j : U ⟶ C) [IsOpenImmersion j] [Nonempty U] (WU : WeilGroup pU)
    (WC : WeilGroup p) extends WeilGroup.Restriction j WU WC where
  /-- The boundary `S₀ = C₀ \ U₀` is finite. -/
  finite_boundary : (Set.range j.base)ᶜ.Finite
  /-- Every boundary point is a closed point of `C₀`, so its residue degree `e_s` is
  meaningful. -/
  boundary_subset_finitePoints : (Set.range j.base)ᶜ ⊆ C.finitePoints
  /-- The inertia subgroup `I_s` at a boundary point `s`. -/
  inertia : ↥((Set.range j.base)ᶜ) → Subgroup WU.carrier
  /-- Inertia is contained in the geometric fundamental group `π₁(U)`. -/
  inertia_le (s : ↥((Set.range j.base)ᶜ)) : inertia s ≤ WU.geometric
  /-- Inertia at `s` dies in `W(C₀)`: the decomposition homomorphism at `s` factors through the
  fundamental group of the strict henselization of `C₀` at `s`, which is trivial, so a sheaf
  which is lisse on all of `C₀` is unramified at `s`. -/
  inertia_le_ker_restrict (s : ↥((Set.range j.base)ᶜ)) : inertia s ≤ restrict.ker
  /-- A residue Frobenius lift at a boundary point `s`. -/
  residueFrobenius : ↥((Set.range j.base)ᶜ) → WU.carrier
  /-- The residue Frobenius lift at `s` has degree `e_s = [k(s) : 𝔽_q]`. -/
  deg_residueFrobenius (s : ↥((Set.range j.base)ᶜ)) :
    WU.deg (residueFrobenius s) = Multiplicative.ofAdd (p.degreeOver s.1 : ℤ)
  /-- The residue Frobenius lift at `s` restricts into the Frobenius conjugacy class at `s`;
  this is what makes `V ^ (I_s)` with its residue-Frobenius action compute the stalk of
  `j_* ℱ`. -/
  restrict_residueFrobenius (s : ↥((Set.range j.base)ᶜ)) :
    IsConj (WC.frobenius ⟨s.1, boundary_subset_finitePoints s.2⟩)
      (restrict (residueFrobenius s))
  /-- The residue Frobenius lift normalises inertia, so that it acts on the invariants. -/
  normalizes_inertia (s : ↥((Set.range j.base)ᶜ)) :
    (inertia s).map (MulAut.conj (residueFrobenius s)) = inertia s

namespace BoundaryDatum

variable {j : U ⟶ C} [IsOpenImmersion j] [Nonempty U] {WU : WeilGroup pU} {WC : WeilGroup p}
  (D : BoundaryDatum j WU WC)
variable (l : ℕ) [Fact l.Prime] {V : Type u} [AddCommGroup V] [Module (PadicAlgCl l) V]
  [FiniteDimensional (PadicAlgCl l) V]

/-- Blueprint `sk-d-real-boundary`: Boundary extension and inertia.

The boundary stalk of `J = j_* ℱ` at a geometric point over a boundary point `s`: the inertia
invariants `V^{I_s}` of the local generic stalk `V`. The residue Frobenius lift
`AlgebraicGeometry.BoundaryDatum.residueFrobenius` normalises `I_s`, hence acts on it
unambiguously. -/
noncomputable def boundaryStalk (ρ : Representation (PadicAlgCl l) WU.carrier V)
    (s : ↥((Set.range j.base)ᶜ)) : Submodule (PadicAlgCl l) V :=
  Representation.invariants (ρ.comp (D.inertia s).subtype)

omit [FiniteDimensional (PadicAlgCl l) V] in
/-- The residue Frobenius lift at `s` maps the boundary stalk `V ^ (I_s)` to itself, since it
normalises the inertia subgroup `I_s`. -/
theorem residueFrobenius_mem_boundaryStalk (ρ : Representation (PadicAlgCl l) WU.carrier V)
    (s : ↥((Set.range j.base)ᶜ)) {v : V} (hv : v ∈ D.boundaryStalk l ρ s) :
    ρ (D.residueFrobenius s) v ∈ D.boundaryStalk l ρ s := by
  rw [boundaryStalk, Representation.mem_invariants] at hv ⊢
  rintro ⟨g, hg⟩
  rw [← D.normalizes_inertia s] at hg
  obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.1 hg
  change ρ (D.residueFrobenius s * h * (D.residueFrobenius s)⁻¹) (ρ (D.residueFrobenius s) v) = _
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right, map_mul, Module.End.mul_apply]
  exact congrArg _ (hv ⟨h, hh⟩)

/-- Blueprint `sk-d-real-boundary`: Boundary extension and inertia.

The residue Frobenius `F_s` acting on the boundary stalk `V ^ (I_s)`, the Frobenius of the stalk
of `j_* ℱ` at a geometric point over the boundary point `s`. -/
noncomputable def boundaryFrobenius (ρ : Representation (PadicAlgCl l) WU.carrier V)
    (s : ↥((Set.range j.base)ᶜ)) : Module.End (PadicAlgCl l) (D.boundaryStalk l ρ s) :=
  (ρ (D.residueFrobenius s)).restrict fun _ ↦ D.residueFrobenius_mem_boundaryStalk l ρ s

/-- A lisse Weil sheaf on `C₀` restricts to a lisse Weil sheaf on `U₀`: the geometric part of
`W(U₀)` maps continuously into that of `W(C₀)`. -/
theorem isLisse_comp_restrict {ρ : Representation (PadicAlgCl l) WC.carrier V}
    (hρ : WC.IsLisse l ρ) : WU.IsLisse l (ρ.comp D.restrict) := by
  refine WeilGroup.IsLisse.of_continuous_apply fun φ v ↦ ?_
  have hmaps (g : WU.geometric) : D.restrict g.1 ∈ WC.geometric := by
    rw [MonoidHom.mem_ker, ← MonoidHom.comp_apply, D.deg_restrict]
    exact g.2
  have hc : Continuous fun g : WU.geometric ↦ (⟨D.restrict g.1, hmaps g⟩ : WC.geometric) :=
    (D.continuous_restrict.comp continuous_subtype_val).subtype_mk _
  exact (hρ.continuous_apply φ v).comp hc

end BoundaryDatum

namespace Etale

/-- Blueprint `def-wf-middle-extension`: Middle extension on a curve.

The *sheaf-theoretic middle extension* of a sheaf `ℱ` on `U₀` along an open immersion
`j : U₀ ↪ C₀` is the ordinary (underived) direct image `j_* ℱ`; the derived direct image
`R j_* ℱ` is a different object, whose higher cohomology sheaves have to be retained in
derived formulas. -/
noncomputable abbrev middleExtension (A : Type u') [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    Sheaf U.smallEtaleTopology A ⥤ Sheaf X.smallEtaleTopology A :=
  (j)_*[A]

end Etale

namespace Scheme

variable {j : U ⟶ C} [IsOpenImmersion j] {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

/-- Let `j : U₀ ↪ C₀` be an open immersion into a curve, `ℱ` a finite locally constant sheaf of
`Λ`-modules on `U₀` and `s` a closed point of `C₀` outside `U₀`. Then the restriction of the
middle extension `j_* ℱ` to the point `Spec k(s)` is finite locally constant.

This is an auxiliary finiteness input, weaker than the blueprint lemma
`lem-wf-boundary-stalk-invariants`, which identifies the stalk of `j_* ℱ` at a geometric point
`s̄` over `s`, Frobenius-equivariantly, with the inertia invariants `ℱ_η̄ ^ I_s`. That
identification implies this statement, since a sheaf on `Spec k(s)` is the continuous Galois
module of its geometric stalk, and `ℱ_η̄ ^ I_s` is finite. -/
theorem isFiniteLocallyConstantSheaf_upperStar_middleExtension
    (p : C ⟶ Spec (.of K)) [IsCurve p] (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsFiniteLocallyConstantSheaf F] (s : C) (hs : IsClosed {s})
    (hsj : s ∉ Set.range j.base) :
    Scheme.IsFiniteLocallyConstantSheaf
      ((C.fromSpecResidueField s)^*[ModuleCat.{u + 1} Λ].obj
        ((Etale.middleExtension (ModuleCat.{u + 1} Λ) j).obj F)) := by
  sorry

/-- Blueprint `sk-i-real-boundary`: Boundary stalks and restriction to an open.
Also `lem-wf-dense-open-pi1-surjective`, part (5).

The direct image `j_* ℱ` of a finite locally constant sheaf along an open immersion into a
curve `C₀` with finite complement is constructible. The complement consists of closed points,
since `C₀` is a Jacobson space, so the range of `j` and the boundary points stratify `C₀`
(`AlgebraicGeometry.Scheme.Stratification.ofOpenImmersion`). On `U₀` the restriction of
`j_* ℱ` is `ℱ`, and at a boundary point it is finite locally constant by
`AlgebraicGeometry.Scheme.isFiniteLocallyConstantSheaf_upperStar_middleExtension`. -/
theorem isConstructibleSheaf_lowerStar (p : C ⟶ Spec (.of K)) [IsCurve p]
    (hfin : (Set.range j.base)ᶜ.Finite)
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsFiniteLocallyConstantSheaf F] :
    Scheme.IsConstructibleSheaf ((Etale.middleExtension (ModuleCat.{u + 1} Λ) j).obj F) := by
  have : JacobsonSpace C := LocallyOfFiniteType.jacobsonSpace p
  have hcl : ∀ x ∈ (Set.range j.base)ᶜ, IsClosed {x} := fun x hx ↦
    _root_.isClosed_singleton_of_mem_of_finite j.isOpenEmbedding.isOpen_range.isClosed_compl hfin hx
  refine ⟨Stratification.ofOpenImmersion j hfin hcl, fun i ↦ ?_⟩
  induction i using Fin.cases with
  | zero =>
    exact IsFiniteLocallyConstantSheaf.of_iso (F := F)
      (asIso ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).counit.app F)).symm
  | succ i =>
    have := hfin.to_subtype
    have hx := ((Finite.equivFin ↥(Set.range j.base)ᶜ).symm i).2
    exact isFiniteLocallyConstantSheaf_upperStar_middleExtension p F _ (hcl _ hx) hx

/-- Blueprint `lem-a1-lisse-middle-extension`: Recovery from a dense lisse open, at a removed
point.

Let `𝒢` be a finite locally constant sheaf on a smooth curve `C₀` and `j : U₀ ↪ C₀` a dense
open. At a geometric point over a point `s` of `C₀` outside `U₀`, the adjunction map
`𝒢 ⟶ j_* j^* 𝒢` is an isomorphism on stalks: by `lem-wf-boundary-stalk-invariants` the target
stalk is `(𝒢_η̄) ^ I_s = (𝒢_s̄) ^ I_s`, and the inertia `I_s` acts trivially on the stalk of a
sheaf which is lisse at `s`. -/
theorem isIso_sheafFiber_map_unit_upperStarLowerStarAdjunction [SmoothOfRelativeDimension 1 p]
    (hdense : Dense (Set.range j.base)) (G : Sheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsFiniteLocallyConstantSheaf G] (s : C) (hs : s ∉ Set.range j.base) :
    IsIso ((C.uliftPointSmallEtale s).sheafFiber.map
      ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).unit.app G)) := by
  sorry

/-- Blueprint `sk-i-real-boundary`: Boundary stalks and restriction to an open.
Also `lem-a1-lisse-middle-extension`.

A finite locally constant sheaf `𝒢` on a smooth curve `C₀` is the direct image of its
restriction to a dense open `U₀`: the unit of the adjunction `j^* ⊣ j_*` is an isomorphism
at `𝒢`,

```
    𝒢 ──────▶ j_* j^* 𝒢
```

It suffices to check this on the stalks at all geometric points. At a point of `U₀` the stalk
of the unit is that of `j^*` of the unit, which is inverse to the counit `j^* j_* j^* 𝒢 ≅ j^* 𝒢`;
at a removed point this is `isIso_sheafFiber_map_unit_upperStarLowerStarAdjunction`. -/
theorem isIso_unit_upperStarLowerStarAdjunction [SmoothOfRelativeDimension 1 p]
    (hdense : Dense (Set.range j.base)) (G : Sheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsFiniteLocallyConstantSheaf G] :
    IsIso ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).unit.app G) := by
  refine Scheme.isIso_of_isIso_sheafFiber_map _ fun s ↦ ?_
  by_cases hs : s ∈ Set.range j.base
  · have h : Set.range (C.algClosurePoint s).base ⊆ Set.range j.base :=
      Scheme.range_base_subset_of_closedPoint_mem _
        (by exact (algClosurePoint_base C s _).symm ▸ hs)
    have := Etale.isIso_uliftSheafFiber_comp_map_of_isIso_upperStar_map (ModuleCat.{u + 1} Λ) j
      ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).unit.app G) inferInstance
      (IsOpenImmersion.lift j _ h)
    rwa [IsOpenImmersion.lift_fac] at this
  · exact isIso_sheafFiber_map_unit_upperStarLowerStarAdjunction (p := p) hdense G s hs

end Scheme

end AlgebraicGeometry
