/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.Extensions
public import WeilConjectures.WeilSheaf.Defs
public import WeilConjectures.WeilSheaf.HomologySequence
public import WeilConjectures.WeilSheaf.LowerShriekPackage
public import WeilConjectures.WeilSheaf.StalkFunctor
public import WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy
public import WeilConjectures.WeilSheaf.Tensor

/-!
# Mixed weight bounds for constructible Weil sheaves and complexes

This file sets up the language in which the Deligne–Laumon reduction to the affine line
(blueprint section `sec-deligne-laumon-general`) is stated. A constructible Weil sheaf is
`ι`-*mixed of weights at most* `w` if it admits a finite filtration whose successive quotients
are punctually `ι`-pure of some weight at most `w`, and a bounded constructible Weil complex `K`
is mixed of weights at most `w` if `𝓗ᵇK` is mixed of weights at most `w + b` for every `b`.

## Conventions

The `ℓ`-adic formalism these statements are phrased against is the provisional interface of
`WeilConjectures.WeilSheaf.Defs`: the abelian categories `AlgebraicGeometry.WeilSheaf k₀ l X` of
constructible Weil `ℚ̄_ℓ`-sheaves on a `k₀`-scheme `X`, their bounded derived categories
`AlgebraicGeometry.WeilComplex k₀ l X`, lissity, the geometric stalks with their local
Frobenius, the punctual weight conditions
`AlgebraicGeometry.WeilSheaf.IsPunctuallyPureOfWeight` and
`AlgebraicGeometry.WeilSheaf.HasWeightsAtMost`, the reality condition
`AlgebraicGeometry.WeilSheaf.IsReal`, and the direct images with compact support
`AlgebraicGeometry.WeilSheaf.higherLowerShriek` (`Rʳf₀!`) and
`AlgebraicGeometry.WeilComplex.derivedLowerShriek` (`Rf₀!`). The notions that other blueprint
blocks own are opaque placeholders there, each tagged `TODO(unify)` with the node that owns it;
what this block owns is the mixed upper bounds defined below.

Cohomological indexing is used throughout: `AlgebraicGeometry.WeilComplex.homologySheaf b` is
the `b`-th *cohomology* sheaf `𝓗ᵇK`, as in `DerivedCategory.homologyFunctor`, so the bound for
a complex of weights at most `w` is `w + b` in degree `b`, Deligne's convention.

## Main definitions

- `AlgebraicGeometry.WeilSheaf.IsMixedOfWeightsAtMost` and
  `AlgebraicGeometry.WeilComplex.IsMixedOfWeightsAtMost`: mixed of weights at most `w`, for a
  sheaf and for a complex.
- `AlgebraicGeometry.WeilSheaf.IsMixed`: mixed, that is, mixed of weights at most `w` for some
  `w`.
- `AlgebraicGeometry.HasDirectImageWeightBound`: the direct-image weight assertion for a single
  morphism, the statement the reductions of `sec-deligne-laumon-general` propagate, and its
  complex form `AlgebraicGeometry.HasDirectImageComplexWeightBound`.

Monotonicity in the bound and the bound for a zero sheaf are proved
(`AlgebraicGeometry.WeilSheaf.IsMixedOfWeightsAtMost.mono_weight` and
`AlgebraicGeometry.WeilSheaf.isMixedOfWeightsAtMost_of_isZero`), and the closure properties the
blueprint records alongside the definition — under subobjects, quotients and extensions — are
proved: `AlgebraicGeometry.WeilSheaf.IsMixedOfWeightsAtMost.of_mono`, `.of_epi` and
`.of_mono_cokernel`. They come from the general closure properties of objects with a finite
filtration (`CategoryTheory.ObjectProperty.filtrationClosure`), applied to the property
`AlgebraicGeometry.WeilSheaf.isPunctuallyPureOfWeightLE` of being punctually pure of some weight
at most `w`, which is closed under subobjects and quotients since the stalk functors are exact
(`AlgebraicGeometry.WeilSheaf.IsPunctuallyPureOfWeight.of_mono`). From them, the middle term
of an exact sequence whose outer terms are mixed of weights at most `w` is mixed of weights at
most `w`
(`AlgebraicGeometry.WeilSheaf.IsMixedOfWeightsAtMost.of_exact`), and so is a sheaf with a finite
filtration whose successive quotients are
(`AlgebraicGeometry.WeilSheaf.IsMixedOfWeightsAtMost.of_filtration`).

A mixed sheaf whose local Frobenius eigenvalues are bounded by `q_y ^ (v / 2)` is mixed of
weights at most `v` (`AlgebraicGeometry.WeilSheaf.IsMixedOfWeightsAtMost.of_hasWeightsAtMost`,
blueprint `lem-zl-mixed-punctual-cutoff`), and a constant twist shifts mixed weight bounds
(`AlgebraicGeometry.WeilSheaf.IsMixedOfWeightsAtMost.constantTwist`).

## References

- [Deligne, *La conjecture de Weil : II*][deligne1980], Publ. Math. IHÉS **52** (1980), §1, for
  mixed sheaves and their weight bounds.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

/-! ### Mixed sheaves -/

/-- `F` is `ι`-mixed of weights at most `w` if it admits a finite filtration

```
0 = G 0 ↪--- G 1 ↪--- ⋯ ↪--- G n ≅ F
         |        |            |
         v        v            v
      coker φ 0   ⋯      coker φ (n-1)
```

whose successive quotients `coker φᵢ` are punctually `ι`-pure of some weight at most `w`
(blueprint: `sk-d-dl-general-weights`, `def-weil-punctual-weights`). -/
def WeilSheaf.IsMixedOfWeightsAtMost (ι : PadicAlgCl l →+* ℂ) (F : WeilSheaf k₀ l X) (w : ℝ) :
    Prop :=
  ∃ (n : ℕ) (G : Fin (n + 1) → WeilSheaf k₀ l X)
    (φ : ∀ i : Fin n, G i.castSucc ⟶ G i.succ),
      IsZero (G 0) ∧ IsIsomorphic (G (Fin.last n)) F ∧ (∀ i : Fin n, Mono (φ i)) ∧
        ∀ i : Fin n, ∃ v ≤ w, (cokernel (φ i)).IsPunctuallyPureOfWeight ι v

/-- `F` is `ι`-*mixed* if it is mixed of weights at most `w` for some `w`, that is, if it admits
a finite filtration with punctually `ι`-pure quotients
(blueprint: `sk-d-dl-general-weights`). -/
def WeilSheaf.IsMixed (ι : PadicAlgCl l →+* ℂ) (F : WeilSheaf k₀ l X) : Prop :=
  ∃ w : ℝ, F.IsMixedOfWeightsAtMost ι w

namespace WeilSheaf

variable {ι : PadicAlgCl l →+* ℂ} {F G : WeilSheaf k₀ l X} {w w' : ℝ}

theorem IsMixedOfWeightsAtMost.isMixed (h : F.IsMixedOfWeightsAtMost ι w) : F.IsMixed ι :=
  ⟨w, h⟩

/-- Mixed upper bounds are monotone in the bound (blueprint: `sk-d-dl-general-weights`). -/
theorem IsMixedOfWeightsAtMost.mono_weight (h : F.IsMixedOfWeightsAtMost ι w) (hw : w ≤ w') :
    F.IsMixedOfWeightsAtMost ι w' := by
  obtain ⟨n, G, φ, h0, hlast, hmono, hpure⟩ := h
  refine ⟨n, G, φ, h0, hlast, hmono, fun i ↦ ?_⟩
  obtain ⟨v, hv, hvpure⟩ := hpure i
  exact ⟨v, hv.trans hw, hvpure⟩

/-- A zero sheaf is mixed of weights at most `w`, for every `w`: the filtration of length zero
exhibits it (blueprint: `sk-d-dl-general-weights`). -/
theorem isMixedOfWeightsAtMost_of_isZero (hF : IsZero F) (w : ℝ) :
    F.IsMixedOfWeightsAtMost ι w :=
  ⟨0, fun _ ↦ F, fun i ↦ i.elim0, hF, ⟨Iso.refl F⟩, fun i ↦ i.elim0, fun i ↦ i.elim0⟩

variable (ι w) in
/-- The property of a Weil sheaf of being punctually `ι`-pure of some weight at most `w`; the
sheaves mixed of weights at most `w` are those with a finite filtration whose successive
quotients have this property. -/
def isPunctuallyPureOfWeightLE : ObjectProperty (WeilSheaf k₀ l X) :=
  fun F ↦ ∃ v ≤ w, F.IsPunctuallyPureOfWeight ι v

instance : (isPunctuallyPureOfWeightLE (k₀ := k₀) (l := l) (X := X) ι w).IsClosedUnderSubobjects
    where
  prop_of_mono f _ := fun ⟨v, hv, h⟩ ↦ ⟨v, hv, h.of_mono f⟩

instance : (isPunctuallyPureOfWeightLE (k₀ := k₀) (l := l) (X := X) ι w).IsClosedUnderQuotients
    where
  prop_of_epi f _ := fun ⟨v, hv, h⟩ ↦ ⟨v, hv, h.of_epi f⟩

instance :
    (isPunctuallyPureOfWeightLE (k₀ := k₀) (l := l) (X := X) ι w).IsClosedUnderIsomorphisms where
  of_iso e := fun ⟨v, hv, h⟩ ↦ ⟨v, hv, h.of_epi e.hom⟩

/-- Being mixed of weights at most `w` is admitting a finite filtration whose successive
quotients are punctually `ι`-pure of some weight at most `w`. -/
theorem isMixedOfWeightsAtMost_iff_filtrationClosure :
    F.IsMixedOfWeightsAtMost ι w ↔ (isPunctuallyPureOfWeightLE ι w).filtrationClosure F := by
  rw [ObjectProperty.filtrationClosure_iff]
  rfl

/-- A subobject of a sheaf mixed of weights at most `w` is mixed of weights at most `w`: intersect
the filtration (blueprint: `sk-d-dl-general-weights`). -/
theorem IsMixedOfWeightsAtMost.of_mono (i : G ⟶ F) [Mono i] (h : F.IsMixedOfWeightsAtMost ι w) :
    G.IsMixedOfWeightsAtMost ι w := by
  rw [isMixedOfWeightsAtMost_iff_filtrationClosure] at h ⊢
  exact ObjectProperty.prop_of_mono _ i h

/-- A quotient of a sheaf mixed of weights at most `w` is mixed of weights at most `w`: take the
images of the filtration (blueprint: `sk-d-dl-general-weights`). -/
theorem IsMixedOfWeightsAtMost.of_epi (p : F ⟶ G) [Epi p] (h : F.IsMixedOfWeightsAtMost ι w) :
    G.IsMixedOfWeightsAtMost ι w := by
  rw [isMixedOfWeightsAtMost_iff_filtrationClosure] at h ⊢
  exact ObjectProperty.prop_of_epi _ p h

/-- An extension of a sheaf mixed of weights at most `w` by another one is mixed of weights at
most `w`: splice the two filtrations (blueprint: `sk-d-dl-general-weights`). -/
theorem IsMixedOfWeightsAtMost.of_mono_cokernel (i : G ⟶ F) [Mono i]
    (hG : G.IsMixedOfWeightsAtMost ι w) (hQ : (cokernel i).IsMixedOfWeightsAtMost ι w) :
    F.IsMixedOfWeightsAtMost ι w := by
  rw [isMixedOfWeightsAtMost_iff_filtrationClosure] at hG hQ ⊢
  exact ObjectProperty.prop_X₂_of_shortExact _
    (ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel i) inferInstance inferInstance)
    hG hQ

/-- Mixed upper bounds are invariant under isomorphism (blueprint: `sk-d-dl-general-weights`). -/
theorem IsMixedOfWeightsAtMost.of_iso (e : F ≅ G) (h : F.IsMixedOfWeightsAtMost ι w) :
    G.IsMixedOfWeightsAtMost ι w := by
  obtain ⟨n, H, φ, h0, ⟨e'⟩, hmono, hpure⟩ := h
  exact ⟨n, H, φ, h0, ⟨e' ≪≫ e⟩, hmono, hpure⟩

/-- In an exact sequence `A ⟶ B ⟶ C` of Weil sheaves whose outer terms are mixed of weights at
most `w`, the middle term is mixed of weights at most `w`: the kernel of `B ⟶ C` is a quotient
of `A`, and the cokernel of its inclusion is a subobject of `C`
(blueprint: `lem-zl-morphism-open-closed-reduction`, step 0). -/
theorem IsMixedOfWeightsAtMost.of_exact {S : ShortComplex (WeilSheaf k₀ l X)} (hS : S.Exact)
    (h₁ : S.X₁.IsMixedOfWeightsAtMost ι w) (h₃ : S.X₃.IsMixedOfWeightsAtMost ι w) :
    S.X₂.IsMixedOfWeightsAtMost ι w :=
  have := hS.epi_kernelLift
  (h₁.of_epi (kernel.lift S.g S.f S.zero)).of_mono_cokernel (kernel.ι S.g)
    (h₃.of_mono (Abelian.factorThruCoimage S.g))

open scoped AlgebraicGeometry.ProEtale in
omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] in
/-- A zero Weil sheaf is punctually pure of every weight: its stalks vanish. -/
theorem isPunctuallyPureOfWeight_of_isZero (hF : IsZero F) (w : ℝ) :
    F.IsPunctuallyPureOfWeight ι w := fun x α hα ↦ by
  have hz (s) : IsZero ((WeilCoefficients.toModuleCat l).obj (F.stalkObj s)) :=
    (WeilCoefficients.toModuleCat l).map_isZero ((Sheaf.Γ _ _).map_isZero
      ((s)^*[WeilCoefficients.{u} l].map_isZero
        ((ProEtale.AdicSheaf.forget _).map_isZero (isZero_iff_isZero_carrier.mp hF))))
  have : Subsingleton (F.stalk x).carrier := ModuleCat.subsingleton_of_isZero (hz _)
  obtain ⟨y, hy⟩ := hα.exists_hasEigenvector
  exact absurd (Subsingleton.elim y 0) hy.2

/-- **Punctual cutoff for an already mixed sheaf.** Let `G` be a constructible Weil sheaf on a
separated `k₀`-scheme of finite type, mixed of weights at most some `u`. If every eigenvalue
`α` of the local Frobenius of `G` at every closed point `y` satisfies `|ι α| ≤ q_y ^ (v / 2)`,
then `G` is mixed of weights at most `v`: a nonzero pure quotient of a mixed filtration has a
nonzero stalk at some closed point, and its eigenvalues there are eigenvalues of `G`
(blueprint: `lem-zl-mixed-punctual-cutoff`). -/
theorem IsMixedOfWeightsAtMost.of_hasWeightsAtMost
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] {u v : ℝ}
    (h : F.IsMixedOfWeightsAtMost ι u) (hv : F.HasWeightsAtMost ι v) :
    F.IsMixedOfWeightsAtMost ι v := by
  rw [isMixedOfWeightsAtMost_iff_filtrationClosure] at h ⊢
  induction h with
  | of_isZero hX => exact .of_isZero hX
  | of_mono i _ hi ih =>
    refine .of_mono i (ih (hv.of_mono i)) ?_
    obtain ⟨v', -, hpure⟩ := hi
    have hQ := hv.of_epi (cokernel.π i)
    by_cases hz : IsZero (cokernel i)
    · exact ⟨v, le_rfl, isPunctuallyPureOfWeight_of_isZero hz v⟩
    obtain ⟨x, hx⟩ := exists_nontrivial_stalk_of_not_isZero _ hz
    refine ⟨v', ?_, hpure⟩
    obtain ⟨α, hα⟩ := Module.End.exists_eigenvalue ((cokernel i).stalk x).frobeniusEnd
    have h₁ := hpure x α hα
    have h₂ := hQ x α hα
    rw [h₁] at h₂
    have hq : 1 < ((X ↘ Spec (CommRingCat.of k₀)).residueCard x.1 : ℝ) := by
      have hk : 1 < Nat.card k₀ := Finite.one_lt_card
      have hd := (X ↘ Spec (CommRingCat.of k₀)).degreeOver_ne_zero x.2
      exact_mod_cast Nat.one_lt_pow hd hk
    have := (Real.rpow_le_rpow_left_iff hq).1 h₂
    linarith

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] in
/-- The constant twist of Weil sheaves by a unit `b ∈ ℚ̄_ℓˣ`, as a functor: the transport of
pro-étale Weil sheaves along the identity, with the Weil structure multiplied by `b`. -/
noncomputable def constantTwistFunctor (b : (PadicAlgCl l)ˣ) :
    WeilSheaf k₀ l X ⥤ WeilSheaf k₀ l X :=
  (WeilSheaf.objectProperty k₀ l X).liftFullSubcategory (WeilSheaf.objectProperty k₀ l X)
    (Endofunctor.IsoAlgebra.mapOfNatIso (Functor.leftUnitor _ ≪≫ (Functor.rightUnitor _).symm ≪≫
      Functor.isoWhiskerLeft (frobeniusPullback k₀ l X)
        (NatIso.ofComponents (fun M ↦ WeilCoefficients.smulIso b M)
          (fun f ↦ (ProEtale.AdicSheaf.smul_comp _ f).symm))))
    fun _ h ↦ h

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] in
/-- The constant twist functor computes the constant twist. -/
noncomputable def constantTwistIso (F : WeilSheaf k₀ l X) (b : (PadicAlgCl l)ˣ) :
    F.constantTwist b ≅ (constantTwistFunctor b).obj F :=
  ObjectProperty.isoMk _ (ObjectProperty.isoMk _ (Endofunctor.Algebra.isoMk (Iso.refl _) (by
    change (frobeniusPullback k₀ l X).map (𝟙 _) ≫ (𝟙 _ ≫ 𝟙 _ ≫
        (WeilCoefficients.smulIso b _).hom) ≫ F.obj.str.hom =
      (F.obj.str.hom ≫ (WeilCoefficients.smulIso b F.obj.carrier).hom) ≫ 𝟙 _
    rw [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp, Category.id_comp,
      Category.id_comp]
    exact ProEtale.AdicSheaf.smul_comp _ _)))

instance (b : (PadicAlgCl l)ˣ) : PreservesFiniteLimits (constantTwistFunctor (k₀ := k₀) (l := l)
    (X := X) b) := by
  have : PreservesFiniteLimits (constantTwistFunctor (k₀ := k₀) (l := l) (X := X) b ⋙
      (WeilSheaf.objectProperty k₀ l X).ι) :=
    preservesFiniteLimits_of_natIso
      ((WeilSheaf.objectProperty k₀ l X).liftFullSubcategoryCompιIso _ _ _).symm
  have : ReflectsFiniteLimits (WeilSheaf.objectProperty k₀ l X).ι := ⟨fun _ _ _ ↦ inferInstance⟩
  exact preservesFiniteLimits_of_reflects_of_preserves _ (WeilSheaf.objectProperty k₀ l X).ι

instance (b : (PadicAlgCl l)ˣ) : PreservesFiniteColimits (constantTwistFunctor (k₀ := k₀)
    (l := l) (X := X) b) := by
  have : PreservesFiniteColimits (constantTwistFunctor (k₀ := k₀) (l := l) (X := X) b ⋙
      (WeilSheaf.objectProperty k₀ l X).ι) :=
    preservesFiniteColimits_of_natIso
      ((WeilSheaf.objectProperty k₀ l X).liftFullSubcategoryCompιIso _ _ _).symm
  have : ReflectsFiniteColimits (WeilSheaf.objectProperty k₀ l X).ι := {}
  exact preservesFiniteColimits_of_reflects_of_preserves _ (WeilSheaf.objectProperty k₀ l X).ι

instance (b : (PadicAlgCl l)ˣ) :
    (constantTwistFunctor (k₀ := k₀) (l := l) (X := X) b).Additive :=
  ObjectProperty.liftFullSubcategory_additive _ _ _ _

/-- The constant twist `G ⊗ 𝓑_b` of a sheaf mixed of weights at most `v` is mixed of weights at
most `v + c`, where `2 log_q |ι b| = c`: tensoring a mixed filtration with the rank-one sheaf
`𝓑_b` is exact, and it multiplies the eigenvalues at a closed point of degree `m` by `bᵐ`, so it
raises every punctual weight by `c` (blueprint: `lem-zl-relative-curve-mixedness`). -/
theorem IsMixedOfWeightsAtMost.constantTwist (h : F.IsMixedOfWeightsAtMost ι w)
    {b : (PadicAlgCl l)ˣ} {c : ℝ} (hb : 2 * Real.logb (Nat.card k₀) ‖ι b‖ = c) :
    (F.constantTwist b).IsMixedOfWeightsAtMost ι (w + c) :=
  by
  rw [isMixedOfWeightsAtMost_iff_filtrationClosure] at h ⊢
  refine ObjectProperty.prop_of_iso _ (constantTwistIso F b).symm
    (ObjectProperty.filtrationClosure_map (constantTwistFunctor b) (fun G ⟨v, hv, hG⟩ ↦
      ⟨v + c, by linarith, (hG.constantTwist hb).of_epi (constantTwistIso G b).hom⟩) h)

/-- A sheaf with a finite filtration `0 = G 0 ↪ G 1 ↪ ⋯ ↪ G n ≅ F` whose successive quotients
`coker φᵢ` are mixed of weights at most `w` is mixed of weights at most `w`: splice the filtrations
of the quotients along the filtration of `F` (blueprint: `lem-zl-composition-weight-bound`, the
extension step along the abutment filtration). -/
theorem IsMixedOfWeightsAtMost.of_filtration {n : ℕ} (G : Fin (n + 1) → WeilSheaf k₀ l X)
    (φ : ∀ i : Fin n, G i.castSucc ⟶ G i.succ) (h0 : IsZero (G 0))
    (hlast : IsIsomorphic (G (Fin.last n)) F) [∀ i, Mono (φ i)]
    (h : ∀ i : Fin n, (cokernel (φ i)).IsMixedOfWeightsAtMost ι w) :
    F.IsMixedOfWeightsAtMost ι w := by
  have key : ∀ (i : ℕ) (hi : i < n + 1), (G ⟨i, hi⟩).IsMixedOfWeightsAtMost ι w := by
    intro i
    induction i with
    | zero => exact fun _ ↦ isMixedOfWeightsAtMost_of_isZero h0 w
    | succ i ih =>
      intro hi
      exact (ih (by omega)).of_mono_cokernel (φ ⟨i, by omega⟩) (h ⟨i, by omega⟩)
  exact (key n (by omega)).of_iso hlast.some

end WeilSheaf

/-! ### Mixed complexes -/

/-- A bounded constructible Weil complex `K` is `ι`-*mixed of weights at most* `w` if its `b`-th
cohomology sheaf `𝓗ᵇK` is mixed of weights at most `w + b`, for every `b`; equivalently, the
bound in total degree `n` is `w + n` (blueprint: `sk-d-dl-general-weights`). -/
def WeilComplex.IsMixedOfWeightsAtMost (ι : PadicAlgCl l →+* ℂ) (K : WeilComplex k₀ l X)
    (w : ℝ) : Prop :=
  ∀ b : ℤ, ((WeilComplex.homologySheaf b).obj K).IsMixedOfWeightsAtMost ι (w + (b : ℝ))

/-- Mixed upper bounds of Weil complexes are invariant under isomorphism
(blueprint: `sk-d-dl-general-weights`). -/
theorem WeilComplex.IsMixedOfWeightsAtMost.of_iso {ι : PadicAlgCl l →+* ℂ}
    {K L : WeilComplex k₀ l X} {w : ℝ} (e : K ≅ L) (h : K.IsMixedOfWeightsAtMost ι w) :
    L.IsMixedOfWeightsAtMost ι w :=
  fun b ↦ (h b).of_iso ((WeilComplex.homologySheaf b).mapIso e)

open Pretriangulated in
/-- **Extension stability of complex weights.** If the outer terms of a distinguished triangle
`K₁ ⟶ K₂ ⟶ K₃ ⟶ K₁[1]` of Weil complexes are mixed of weights at most `w`, then so is the
middle term: the exact sequences `𝓗ᵇK₁ ⟶ 𝓗ᵇK₂ ⟶ 𝓗ᵇK₃` exhibit `𝓗ᵇK₂` as an extension of a
subobject of `𝓗ᵇK₃` by a quotient of `𝓗ᵇK₁` (blueprint: `lem-zl-complex-extension`). -/
theorem WeilComplex.IsMixedOfWeightsAtMost.of_distTriang {ι : PadicAlgCl l →+* ℂ}
    {T : Triangle (WeilComplex k₀ l X)} (hT : T ∈ distTriang _) {w : ℝ}
    (h₁ : T.obj₁.IsMixedOfWeightsAtMost ι w) (h₃ : T.obj₃.IsMixedOfWeightsAtMost ι w) :
    T.obj₂.IsMixedOfWeightsAtMost ι w :=
  fun b ↦ WeilSheaf.IsMixedOfWeightsAtMost.of_exact (WeilComplex.homologySheaf_exact₂ T hT b)
    (h₁ b) (h₃ b)

/-- **Finite pushforward preserves upper weights.** The direct image `Rp₀* = p₀!` along a finite
morphism `p` carries Weil complexes mixed of weights at most `w` to Weil complexes mixed of
weights at most `w`: `p₀*` is exact, and at a closed point `y` the geometric Frobenius permutes the
points over `y`, an orbit of length `e` contributing eigenvalues whose `e`-th powers are those of
the local Frobenius upstairs, with `q_x = q_yᵉ` (blueprint: `lem-zl-finite-pushforward`). -/
theorem WeilComplex.IsMixedOfWeightsAtMost.derivedLowerStar_of_isFinite {ι : PadicAlgCl l →+* ℂ}
    {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] (p : X ⟶ Y) [IsFinite p]
    [p.IsOver (Spec (CommRingCat.of k₀))] {w : ℝ} {K : WeilComplex k₀ l X}
    (hK : K.IsMixedOfWeightsAtMost ι w) :
    ((WeilComplex.derivedLowerStar p).obj K).IsMixedOfWeightsAtMost ι w :=
  sorry

/-- The direct-image weight assertion of the blueprint theorem `sk-thm-dl-general-sheaf`, for a
single morphism `f : X ⟶ Y` of `k₀`-schemes: every constructible Weil sheaf `F` on `X` that is
mixed of weights at most `w` has `Rʳf₀!F` mixed of weights at most `w + r`, for every `r`. The
reductions of the blueprint section `sec-deligne-laumon-general` propagate this assertion along
compositions and open–closed decompositions. -/
def HasDirectImageWeightBound (k₀ : Type u) [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] (ι : PadicAlgCl l →+* ℂ) {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))] (f : X ⟶ Y)
    [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))] : Prop :=
  haveI : LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀)) := by
    rw [← CategoryTheory.comp_over f (Spec (CommRingCat.of k₀))]; infer_instance
  ∀ (w : ℝ) (F : WeilSheaf k₀ l X), F.IsMixedOfWeightsAtMost ι w →
    ∀ r : ℕ, ((WeilSheaf.higherLowerShriek k₀ l f r).obj F).IsMixedOfWeightsAtMost ι (w + r)

/-- The complex form of the direct-image weight assertion, for a single morphism `f : X ⟶ Y` of
`k₀`-schemes: `Rf₀!` carries every Weil complex on `X` that is mixed of weights at most `w` to a
Weil complex mixed of weights at most `w`, for every `w`
(blueprint: `lem-zl-morphism-open-closed-reduction`). -/
def HasDirectImageComplexWeightBound (k₀ : Type u) [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] (ι : PadicAlgCl l →+* ℂ) {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))] (f : X ⟶ Y)
    [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))] : Prop :=
  haveI : LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀)) := by
    rw [← CategoryTheory.comp_over f (Spec (CommRingCat.of k₀))]; infer_instance
  ∀ (w : ℝ) (K : WeilComplex k₀ l X), K.IsMixedOfWeightsAtMost ι w →
    ((WeilComplex.derivedLowerShriek k₀ l f).obj K).IsMixedOfWeightsAtMost ι w

/-! ### Extension by zero and finite direct images -/

namespace WeilSheaf

variable {ι : PadicAlgCl l →+* ℂ} {w : ℝ}

/-- Extension by zero along a quasi-compact open immersion preserves mixed upper bounds: it is
exact, so it carries a mixed filtration to a filtration whose quotients are the extensions by
zero of punctually pure sheaves, which are punctually pure of the same weights
(blueprint: `lem-zl-morphism-open-closed-reduction`, part 2). -/
theorem IsMixedOfWeightsAtMost.extensionByZero {U : Scheme.{u}}
    [U.Over (Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]
    {F : WeilSheaf k₀ l U} (h : F.IsMixedOfWeightsAtMost ι w) :
    ((WeilSheaf.extensionByZero j).obj F).IsMixedOfWeightsAtMost ι w := by
  rw [isMixedOfWeightsAtMost_iff_filtrationClosure] at h ⊢
  exact ObjectProperty.filtrationClosure_map (WeilSheaf.extensionByZero j)
    (fun _ ⟨v, hv, hG⟩ ↦ ⟨v, hv, hG.extensionByZero j⟩) h

/-- A Weil sheaf mixed of weights at most `w`, placed in degree zero, is a Weil complex mixed of
weights at most `w`: its only nonzero cohomology sheaf is itself, in degree zero. -/
theorem IsMixedOfWeightsAtMost.toComplex {F : WeilSheaf k₀ l X}
    (h : F.IsMixedOfWeightsAtMost ι w) :
    (WeilSheaf.toComplex.obj F).IsMixedOfWeightsAtMost ι w := by
  intro b
  rcases lt_trichotomy b 0 with hb | rfl | hb
  · have : (((WeilSheaf.objectProperty k₀ l X).ι ⋙
        DerivedCategory.singleFunctor (ProEtaleWeilSheaf k₀ l X) 0).obj F).IsGE 0 :=
      inferInstanceAs (((DerivedCategory.singleFunctor _ 0).obj F.obj).IsGE 0)
    have : (WeilSheaf.toComplex.obj F).obj.IsGE 0 :=
      DerivedCategory.TStructure.t.isGE_of_iso (WeilSheaf.toComplexCompιIso.app F).symm 0
    exact isMixedOfWeightsAtMost_of_isZero (WeilComplex.isZero_homologySheaf_obj
      (DerivedCategory.isZero_of_isGE _ 0 b hb)) _
  · exact (h.of_iso (WeilSheaf.toComplexCompHomologySheafIso.app F).symm).mono_weight (by simp)
  · have : (((WeilSheaf.objectProperty k₀ l X).ι ⋙
        DerivedCategory.singleFunctor (ProEtaleWeilSheaf k₀ l X) 0).obj F).IsLE 0 :=
      inferInstanceAs (((DerivedCategory.singleFunctor _ 0).obj F.obj).IsLE 0)
    have : (WeilSheaf.toComplex.obj F).obj.IsLE 0 :=
      DerivedCategory.TStructure.t.isLE_of_iso (WeilSheaf.toComplexCompιIso.app F).symm 0
    exact isMixedOfWeightsAtMost_of_isZero (WeilComplex.isZero_homologySheaf_obj
      (DerivedCategory.isZero_of_isLE _ 0 b hb)) _

variable {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] (p : X ⟶ Y) [IsFinite p]
  [p.IsOver (Spec (CommRingCat.of k₀))]

/-- The direct image `p₀*` along a finite morphism preserves mixed upper bounds, the case of a
sheaf of `lem-zl-finite-pushforward`. -/
theorem IsMixedOfWeightsAtMost.higherLowerStar_zero_of_isFinite {F : WeilSheaf k₀ l X}
    (h : F.IsMixedOfWeightsAtMost ι w) :
    ((WeilSheaf.higherLowerStar p 0).obj F).IsMixedOfWeightsAtMost ι w :=
  ((h.toComplex.derivedLowerStar_of_isFinite p 0).of_iso
    ((WeilSheaf.higherLowerStarIso p 0).app F).symm).mono_weight (by simp)

/-- The direct image `p₀*` along a finite morphism preserves upper weight bounds: at a closed
point `y` the geometric Frobenius permutes the points `x` over `y`, and an orbit of length `e`
contributes eigenvalues `β` whose `e`-th powers are eigenvalues of the local Frobenius at `x`,
with `q_x = q_yᵉ`, so that `|ι β| ≤ q_y ^ (w / 2)` (blueprint: `lem-zl-finite-pushforward`, the
stalk computation, and `sk-l-dl-general-quasifinite`). -/
theorem HasWeightsAtMost.higherLowerStar_zero_of_isFinite {F : WeilSheaf k₀ l X}
    (h : F.HasWeightsAtMost ι w) :
    ((WeilSheaf.higherLowerStar p 0).obj F).HasWeightsAtMost ι w :=
  sorry

end WeilSheaf

end AlgebraicGeometry
