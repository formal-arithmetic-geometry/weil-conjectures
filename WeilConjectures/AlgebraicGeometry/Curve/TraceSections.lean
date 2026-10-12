/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.SmoothSections
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineChartBasis
public import WeilConjectures.RingTheory.Kaehler.TraceMap

/-!
# The trace of differentials on sections

Let `f : X ⟶ Y` be a morphism of schemes over a field `k` and `V` an open of `Y` such that
`f⁻¹V` is affine and `Γ(X, f⁻¹V)` is finite free over `Γ(Y, V)`. Identifying `Γ(Ω¹_{X/k}, f⁻¹V)`
with `Ω[Γ(X, f⁻¹V)⁄k]`, the trace of differentials `KaehlerDifferential.traceLin` for the
derivation `d : Γ(Y, V) → Γ(Ω¹_{Y/k}, V)` gives a map
`Γ(Ω¹_{X/k}, f⁻¹V) → Γ(Ω¹_{Y/k}, V)`, `c da ↦ Tr(C · dA)`. It is `Γ(Y, V)`-linear and compatible
with restriction to basic opens of `V`.

For a finite flat, generically unramified morphism `f : X ⟶ ℙ¹_k` from a smooth curve and `V` a
basic open of a standard chart, `ω ↦ (b ↦ Tr(b ω))` identifies `Γ(Ω¹_{X/k}, f⁻¹V)` with
`Hom_{Γ(V)}(Γ(X, f⁻¹V), Γ(Ω¹_{ℙ¹/k}, V))`: this is the local form of duality for `f`.

## Main definitions and results

- `AlgebraicGeometry.Scheme.Hom.traceSections`: the trace `Γ(Ω¹_{X/k}, f⁻¹V) → Γ(Ω¹_{Y/k}, V)`.
- `AlgebraicGeometry.Scheme.Hom.traceSections_restrict`: compatibility with restriction to basic
  opens.
- `AlgebraicGeometry.Scheme.Hom.traceSections_smul_eq_zero` and
  `AlgebraicGeometry.Scheme.Hom.exists_traceSections_smul_eq`: duality over the basic opens of the
  standard charts of `ℙ¹_k`.
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace

noncomputable section

namespace AlgebraicGeometry.Scheme.Hom

variable {k : Type u} [Field k] {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of k))]

lemma specStructureMap_comp_app (V : Y.Opens) :
    (Y ↘ Spec (.of k)).specStructureMap V ≫ f.app V =
      (X ↘ Spec (.of k)).specStructureMap (f ⁻¹ᵁ V) := by
  rw [specStructureMap, specStructureMap, Category.assoc, app_eq_appLE, appLE_comp_appLE]
  simp only [comp_over]

/-- The **trace of differentials on sections**: for `f⁻¹V` affine and `Γ(X, f⁻¹V)` finite free
over `Γ(Y, V)`, the map `Γ(Ω¹_{X/k}, f⁻¹V) → Γ(Ω¹_{Y/k}, V)`, `c da ↦ Tr(C · dA)`, where `A` and
`C` are the matrices of multiplication by `a` and `c` in a basis of `Γ(X, f⁻¹V)`. -/
def traceSections (V : Y.Opens) (hV : IsAffineOpen (f ⁻¹ᵁ V))
    (hfree : letI := (f.app V).hom.toAlgebra; Module.Free Γ(Y, V) Γ(X, f ⁻¹ᵁ V))
    (hfin : letI := (f.app V).hom.toAlgebra; Module.Finite Γ(Y, V) Γ(X, f ⁻¹ᵁ V)) :
    Γ((X ↘ Spec (.of k)).relativeDifferentials, f ⁻¹ᵁ V) →+
      Γ((Y ↘ Spec (.of k)).relativeDifferentials, V) :=
  letI := (f.app V).hom.toAlgebra
  letI : Algebra k Γ(Y, V) := ((Y ↘ Spec (.of k)).specStructureMap V).hom.toAlgebra
  letI : Algebra k Γ(X, f ⁻¹ᵁ V) :=
    ((X ↘ Spec (.of k)).specStructureMap (f ⁻¹ᵁ V)).hom.toAlgebra
  haveI : IsScalarTower k Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := .of_algebraMap_eq' <|
    (congrArg CommRingCat.Hom.hom (specStructureMap_comp_app f V)).symm
  letI : Module k Γ((Y ↘ Spec (.of k)).relativeDifferentials, V) :=
    Module.compHom _ (algebraMap k Γ(Y, V))
  haveI : IsScalarTower k Γ(Y, V) Γ((Y ↘ Spec (.of k)).relativeDifferentials, V) :=
    ⟨fun c r m ↦ by
      change (algebraMap k Γ(Y, V) c * r) • m = algebraMap k Γ(Y, V) c • r • m
      rw [mul_smul]⟩
  (KaehlerDifferential.traceLin
      ((Y ↘ Spec (.of k)).sectionsDerivation V rfl)).toAddMonoidHom.comp
    ((X ↘ Spec (.of k)).kaehlerSectionsEquiv (f ⁻¹ᵁ V) rfl hV).symm.toAddMonoidHom

variable {f}

/-- The trace of differentials on sections is `Γ(Y, V)`-linear. -/
lemma traceSections_smul (V : Y.Opens) (hV : IsAffineOpen (f ⁻¹ᵁ V)) (hfree) (hfin)
    (r : Γ(Y, V)) (ω : Γ((X ↘ Spec (.of k)).relativeDifferentials, f ⁻¹ᵁ V)) :
    f.traceSections V hV hfree hfin (f.app V r • ω) = r • f.traceSections V hV hfree hfin ω := by
  letI := (f.app V).hom.toAlgebra
  letI : Algebra k Γ(Y, V) := ((Y ↘ Spec (.of k)).specStructureMap V).hom.toAlgebra
  letI : Algebra k Γ(X, f ⁻¹ᵁ V) :=
    ((X ↘ Spec (.of k)).specStructureMap (f ⁻¹ᵁ V)).hom.toAlgebra
  haveI : IsScalarTower k Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := .of_algebraMap_eq' <|
    (congrArg CommRingCat.Hom.hom (specStructureMap_comp_app f V)).symm
  letI : Module k Γ((Y ↘ Spec (.of k)).relativeDifferentials, V) :=
    Module.compHom _ (algebraMap k Γ(Y, V))
  haveI : IsScalarTower k Γ(Y, V) Γ((Y ↘ Spec (.of k)).relativeDifferentials, V) :=
    ⟨fun c r m ↦ mul_smul (algebraMap k Γ(Y, V) c) r m⟩
  have h (ω') : f.traceSections V hV hfree hfin ω' =
      KaehlerDifferential.traceLin ((Y ↘ Spec (.of k)).sectionsDerivation V rfl)
        (((X ↘ Spec (.of k)).kaehlerSectionsEquiv (f ⁻¹ᵁ V) rfl hV).symm ω') := rfl
  rw [h, h, LinearEquiv.map_smul]
  exact (congrArg _ (algebraMap_smul (M := Ω[Γ(X, f ⁻¹ᵁ V)⁄k]) Γ(X, f ⁻¹ᵁ V) r _)).trans
    (map_smul _ r _)

/-- For `V` and `f⁻¹V` affine, the restriction of a basis of `Γ(X, f⁻¹V)` over `Γ(Y, V)` is a basis
of `Γ(X, f⁻¹ D(r))` over `Γ(Y, D(r))`: both rings are localizations at `r`. -/
lemma exists_basis_basicOpen {V : Y.Opens} (hV : IsAffineOpen V) (hV' : IsAffineOpen (f ⁻¹ᵁ V))
    (r : Γ(Y, V)) {ι : Type*}
    (b : letI := (f.app V).hom.toAlgebra; Module.Basis ι Γ(Y, V) Γ(X, f ⁻¹ᵁ V)) :
    letI := (f.app (Y.basicOpen r)).hom.toAlgebra
    ∃ b' : Module.Basis ι Γ(Y, Y.basicOpen r) Γ(X, f ⁻¹ᵁ Y.basicOpen r),
      ∀ i, b' i = X.presheaf.map (homOfLE (f.preimage_mono (Y.basicOpen_le r))).op (b i) := by
  letI := (f.app V).hom.toAlgebra
  letI := (f.app (Y.basicOpen r)).hom.toAlgebra
  letI : Algebra Γ(Y, V) Γ(Y, Y.basicOpen r) :=
    (Y.presheaf.map (homOfLE (Y.basicOpen_le r)).op).hom.toAlgebra
  letI : Algebra Γ(X, f ⁻¹ᵁ V) Γ(X, f ⁻¹ᵁ Y.basicOpen r) :=
    (X.presheaf.map (homOfLE (f.preimage_mono (Y.basicOpen_le r))).op).hom.toAlgebra
  letI : Algebra Γ(Y, V) Γ(X, f ⁻¹ᵁ Y.basicOpen r) :=
    (f.app V ≫ X.presheaf.map (homOfLE (f.preimage_mono (Y.basicOpen_le r))).op).hom.toAlgebra
  haveI : IsScalarTower Γ(Y, V) Γ(X, f ⁻¹ᵁ V) Γ(X, f ⁻¹ᵁ Y.basicOpen r) :=
    .of_algebraMap_eq' rfl
  haveI : IsScalarTower Γ(Y, V) Γ(Y, Y.basicOpen r) Γ(X, f ⁻¹ᵁ Y.basicOpen r) :=
    .of_algebraMap_eq' (congrArg CommRingCat.Hom.hom (f.naturality _)).symm
  haveI : IsLocalization.Away r Γ(Y, Y.basicOpen r) := hV.isLocalization_basicOpen r
  haveI : IsLocalization (Algebra.algebraMapSubmonoid Γ(X, f ⁻¹ᵁ V) (Submonoid.powers r))
      Γ(X, f ⁻¹ᵁ Y.basicOpen r) := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
    exact hV'.isLocalization_of_eq_basicOpen _ _ (f.preimage_basicOpen r)
  exact ⟨b.localizationLocalization Γ(Y, Y.basicOpen r) (Submonoid.powers r) _,
    b.localizationLocalization_apply _ _ _⟩

/-- Finiteness and freeness of `Γ(X, f⁻¹V)` over `Γ(Y, V)` pass to basic opens of `V`. -/
lemma free_finite_basicOpen {V : Y.Opens} (hV : IsAffineOpen V) (hV' : IsAffineOpen (f ⁻¹ᵁ V))
    (hfree : letI := (f.app V).hom.toAlgebra; Module.Free Γ(Y, V) Γ(X, f ⁻¹ᵁ V))
    (hfin : letI := (f.app V).hom.toAlgebra; Module.Finite Γ(Y, V) Γ(X, f ⁻¹ᵁ V))
    (r : Γ(Y, V)) :
    (letI := (f.app (Y.basicOpen r)).hom.toAlgebra;
      Module.Free Γ(Y, Y.basicOpen r) Γ(X, f ⁻¹ᵁ Y.basicOpen r)) ∧
    (letI := (f.app (Y.basicOpen r)).hom.toAlgebra;
      Module.Finite Γ(Y, Y.basicOpen r) Γ(X, f ⁻¹ᵁ Y.basicOpen r)) := by
  letI := (f.app V).hom.toAlgebra
  obtain ⟨b', -⟩ := exists_basis_basicOpen hV hV' r (Module.Free.chooseBasis Γ(Y, V) Γ(X, f ⁻¹ᵁ V))
  letI := (f.app (Y.basicOpen r)).hom.toAlgebra
  exact ⟨.of_basis b', .of_basis b'⟩

/-- **The trace of differentials on sections is compatible with restriction to basic opens.** -/
lemma traceSections_restrict {V : Y.Opens} (hV : IsAffineOpen V) (hV' : IsAffineOpen (f ⁻¹ᵁ V))
    (hfree) (hfin) (r : Γ(Y, V)) (hW : IsAffineOpen (f ⁻¹ᵁ Y.basicOpen r)) (hfree') (hfin')
    (ω : Γ((X ↘ Spec (.of k)).relativeDifferentials, f ⁻¹ᵁ V)) :
    f.traceSections (Y.basicOpen r) hW hfree' hfin'
        ((X ↘ Spec (.of k)).relativeDifferentials.presheaf.map
          (homOfLE (f.preimage_mono (Y.basicOpen_le r))).op ω) =
      (Y ↘ Spec (.of k)).relativeDifferentials.presheaf.map (homOfLE (Y.basicOpen_le r)).op
        (f.traceSections V hV' hfree hfin ω) :=
  sorry

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.Hom

open ProjectiveLine Polynomial

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]
  {f : X ⟶ ProjectiveLine (Spec (.of k))} [f.IsOver (Spec (.of k))] [IsFinite f] [Flat f]
  (hf : ∀ x : X, IsField (X.presheaf.stalk x) → (f.stalkMap x).hom.FormallyUnramified)
  (i : ULift.{u} (Fin 2)) {g : k[X]} (hg : g ≠ 0)

/-- `Γ(X, f⁻¹ Dᵢ(g))` is finite free over `Γ(ℙ¹_k, Dᵢ(g)) = k[t]_g`. -/
lemma free_finite_chartBasicOpen :
    (letI := (f.app (chartBasicOpen k i g)).hom.toAlgebra;
      Module.Free Γ(ProjectiveLine (Spec (.of k)), chartBasicOpen k i g)
        Γ(X, f ⁻¹ᵁ chartBasicOpen k i g)) ∧
    (letI := (f.app (chartBasicOpen k i g)).hom.toAlgebra;
      Module.Finite Γ(ProjectiveLine (Spec (.of k)), chartBasicOpen k i g)
        Γ(X, f ⁻¹ᵁ chartBasicOpen k i g)) :=
  sorry

include hf hg in
/-- **Duality over a basic open of a chart, injectivity.** If `Tr(b ω) = 0` for all
`b ∈ Γ(X, f⁻¹V)`, then `ω = 0`. -/
lemma traceSections_smul_eq_zero
    (ω : Γ((X ↘ Spec (.of k)).relativeDifferentials, f ⁻¹ᵁ chartBasicOpen k i g))
    (hω : ∀ b : Γ(X, f ⁻¹ᵁ chartBasicOpen k i g),
      f.traceSections _ ((isAffineOpen_chartBasicOpen k i g).preimage f)
        (free_finite_chartBasicOpen i).1 (free_finite_chartBasicOpen i).2 (b • ω) = 0) :
    ω = 0 :=
  sorry

include hf hg in
/-- **Duality over a basic open of a chart, surjectivity.** Every `Γ(V)`-linear map
`φ : Γ(X, f⁻¹V) → Γ(Ω¹_{ℙ¹/k}, V)` is `b ↦ Tr(b ω)` for some `ω`. -/
lemma exists_traceSections_smul_eq
    (φ : Γ(X, f ⁻¹ᵁ chartBasicOpen k i g) →+
      Γ((ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)).relativeDifferentials,
        chartBasicOpen k i g))
    (hφ : ∀ (r : Γ(ProjectiveLine (Spec (.of k)), chartBasicOpen k i g))
      (b : Γ(X, f ⁻¹ᵁ chartBasicOpen k i g)), φ (f.app _ r * b) = r • φ b) :
    ∃ ω : Γ((X ↘ Spec (.of k)).relativeDifferentials, f ⁻¹ᵁ chartBasicOpen k i g),
      ∀ b, f.traceSections _ ((isAffineOpen_chartBasicOpen k i g).preimage f)
        (free_finite_chartBasicOpen i).1 (free_finite_chartBasicOpen i).2 (b • ω) = φ b :=
  sorry

end AlgebraicGeometry.Scheme.Hom
