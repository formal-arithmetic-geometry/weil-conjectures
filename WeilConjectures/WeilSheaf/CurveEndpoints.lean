/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Curve.OpenAffine
public import WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk
public import WeilConjectures.DeligneLaumon.Reduction.Weights
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseExtensionByZeroLowerStar
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import WeilConjectures.Mathlib.Topology.KrullDimension
public import WeilConjectures.WeilSheaf.CohomologyExact
public import WeilConjectures.WeilSheaf.Curve
public import WeilConjectures.WeilSheaf.MiddleExtension
public import WeilConjectures.WeilSheaf.OpenImmersionRestriction

/-!
# The two endpoints of the compactly supported cohomology of a direct image on a curve

For a dense open immersion `j : U₀ ↪ C₀` into a smooth geometrically connected affine curve
and a lisse Weil sheaf `F` on `U₀`, all the compactly supported cohomology of the ordinary
direct image `j_*F` outside degrees `0, 1, 2` vanishes, degree zero vanishes as well because a
nonzero global section of a lisse sheaf on a connected open has full support on a nonproper
curve, and degree two is the geometric coinvariants `V_{π₁(U)}` Tate-twisted by `(-1)`.

The open `U₀` is again a smooth geometrically connected affine curve
(`AlgebraicGeometry.isAffine_of_isOpenImmersion_of_smoothOfRelativeDimension_one`), and the
boundary `Z₀ = C₀ ∖ U₀` is finite over `k₀`. The open–closed triangle
`RΓ_c(U, F) → RΓ_c(C, j_*F) → RΓ_c(Z, i^*j_*F) →` has its third term concentrated in degree
zero (`AlgebraicGeometry.WeilSheaf.subsingleton_compactlySupportedCohomology_of_isFinite`), so
`H_c^r(U, F) ≅ H_c^r(C, j_*F)` for `r ∉ {0, 1}`
(`AlgebraicGeometry.nonempty_equiv_compactlySupportedCohomology_directImage`). In degree two this
reduces the description of `H_c^2(C, j_*F)` to that of `H_c^2(U, F)`
(`AlgebraicGeometry.WeilSheaf.nonempty_equiv_compactlySupportedCohomology_two`). Purity of `F` of
weight `w` therefore makes degree two pure of weight `w + 2`.

This leaves degree one, which is the only place where the Fourier argument of
`WeilConjectures.DeligneLaumon.AffineLine.DegreeOne` is needed.

## Main statements

- `AlgebraicGeometry.WeilComplex.nonempty_equiv_cohomologyFrobeniusModule_of_distTriang`: a
  distinguished triangle of Weil complexes on `Spec k₀` whose third vertex has no cohomology in
  degrees `r - 1` and `r` induces an isomorphism in degree `r` between the first two vertices.
- `AlgebraicGeometry.nonempty_equiv_compactlySupportedCohomology_directImage`:
  `H_c^r(U, F) ≅ H_c^r(C, j_*F)` for `r ∉ {0, 1}`.
- `AlgebraicGeometry.subsingleton_compactlySupportedCohomology_directImage`: vanishing outside
  degrees `0, 1, 2`.
- `AlgebraicGeometry.subsingleton_compactlySupportedCohomology_directImage_zero`: vanishing in
  degree zero.
- `AlgebraicGeometry.nonempty_equiv_compactlySupportedCohomology_directImage_two`: the
  coinvariant description of degree two.
- `AlgebraicGeometry.isPureOfWeightOver_compactlySupportedCohomology_directImage_two`: its
  purity.
- `AlgebraicGeometry.WeilSheaf.hasWeightsAtMostOver_compactlySupportedCohomology_two`: the top
  compactly supported cohomology of a pure lisse sheaf on a smooth affine curve has weights at
  most `w + 2`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

namespace WeilComplex

/-- Let `K₁ ⟶ K₂ ⟶ K₃ ⟶ K₁[1]` be a distinguished triangle of Weil complexes on `Spec k₀`. If
`H^{r-1}(K₃) = H^r(K₃) = 0`, then `K₁ ⟶ K₂` induces a Frobenius-equivariant isomorphism
`H^r(K₁) ≅ H^r(K₂)`: this is the long exact cohomology sequence of the triangle. -/
theorem nonempty_equiv_cohomologyFrobeniusModule_of_distTriang
    {T : Triangle (WeilComplex k₀ l (Spec (CommRingCat.of k₀)))} (hT : T ∈ distTriang _) (r : ℤ)
    (h₁ : Subsingleton (T.obj₃.cohomologyFrobeniusModule (r - 1)).carrier)
    (h₂ : Subsingleton (T.obj₃.cohomologyFrobeniusModule r).carrier) :
    Nonempty ((T.obj₁.cohomologyFrobeniusModule r).Equiv
      (T.obj₂.cohomologyFrobeniusModule r)) := by
  -- the maps induced on cohomology, and the exactness of the cohomology sequence
  let φ : ∀ {K L : WeilComplex k₀ l (Spec (CommRingCat.of k₀))} (_ : K ⟶ L) (n : ℤ),
      (K.cohomologyFrobeniusModule n).carrier →ₗ[PadicAlgCl l]
        (L.cohomologyFrobeniusModule n).carrier := fun f n ↦
    ((WeilCoefficients.toModuleCat l).map
      (WeilSheaf.globalSectionsMap ((homologySheaf n).map f))).hom
  have hex : ∀ {T' : Triangle (WeilComplex k₀ l (Spec (CommRingCat.of k₀)))}
      (_ : T' ∈ distTriang _) (n : ℤ), Function.Exact (φ T'.mor₁ n) (φ T'.mor₂ n) :=
    fun hT' n ↦ (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (WeilSheaf.exact_map_globalSectionsFunctor k₀ l (homologySheaf_exact₂ _ hT' n))
  -- `H^r(K₃[-1]) ≅ H^{r-1}(K₃)` vanishes
  have h₁' : Subsingleton ((T.obj₃⟦(-1 : ℤ)⟧).cohomologyFrobeniusModule r).carrier :=
    (WeilSheaf.globalSectionsEquivOfIso (homologySheafShiftIso T.obj₃ (-1) r (r - 1)
      (by ring))).toLinearEquiv.toEquiv.subsingleton_congr.2 h₁
  have hinj : Function.Injective (φ T.mor₁ r) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have : Subsingleton (T.invRotate.obj₁.cohomologyFrobeniusModule r).carrier := h₁'
    obtain ⟨y, rfl⟩ := (hex (inv_rot_of_distTriang T hT) r x).1 hx
    rw [Subsingleton.elim y 0, map_zero]
  have hsurj : Function.Surjective (φ T.mor₁ r) := fun y ↦
    (hex hT r y).1 (Subsingleton.elim _ _)
  refine ⟨{ toLinearEquiv := LinearEquiv.ofBijective (φ T.mor₁ r) ⟨hinj, hsurj⟩
            map_frobenius := fun x ↦ ?_ }⟩
  have h := congrArg (fun g ↦ ((WeilCoefficients.toModuleCat l).map g).hom x)
    (WeilSheaf.globalSectionsMap_comp_frobeniusHom ((homologySheaf r).map T.mor₁))
  simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h.symm

end WeilComplex

variable {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k₀))] [IsAffine C]
  [SmoothOfRelativeDimension 1 (C ↘ Spec (CommRingCat.of k₀))]

/-- A smooth affine curve `C₀` is locally of finite type over `k₀`, being smooth over `k₀`. -/
local instance : LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k₀)) :=
  haveI := SmoothOfRelativeDimension.smooth 1 (C ↘ Spec (CommRingCat.of k₀))
  inferInstance

/-- *Top compact-support bound on a curve.* If `C₀` is a smooth affine curve and `G` is a lisse
Weil sheaf on `C₀`, punctually `ι`-pure of weight `w`, then `H_c^2(C, G)` has weights at most
`w + 2`: it is a Frobenius-equivariant quotient of the generic fibre, pure of weight `w`, twisted
by `(-1)`.
(blueprint: `lem-a1-curve-hc2-bound`) -/
theorem WeilSheaf.hasWeightsAtMostOver_compactlySupportedCohomology_two
    (ι : PadicAlgCl l →+* ℂ) (G : WeilSheaf k₀ l C) (hG : G.IsLisse) {w : ℝ}
    (hw : G.IsPunctuallyPureOfWeight ι w) :
    (G.compactlySupportedCohomology 2).HasWeightsAtMostOver k₀ ι (w + 2) := by
  -- TODO(adic): prove once Weil sheaves carry genuine `ℓ`-adic coefficients
  sorry

variable {U : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))] (j : U ⟶ C) [IsOpenImmersion j]
  [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))] [IsDominant j]
  [GeometricallyConnected (C ↘ Spec (CommRingCat.of k₀))]
  (F : WeilSheaf k₀ l U)

section Boundary

omit [Finite k₀] [U.Over (Spec (CommRingCat.of k₀))] [QuasiCompact j]
  [j.IsOver (Spec (CommRingCat.of k₀))] in
include k₀ j in
/-- The boundary `Z₀ = C₀ ∖ U₀` of the dense open `U₀`, with its reduced closed subscheme
structure, is a closed subscheme `i : Z₀ ⟶ C₀` complementary to `U₀` and finite over `k₀`: the
curve `C₀` is irreducible of dimension one, so the boundary is a finite set. -/
theorem exists_isFinite_closedComplement :
    ∃ (Z : Scheme.{u}) (_ : Z.Over (Spec (CommRingCat.of k₀))) (i : Z ⟶ C)
      (_ : IsClosedImmersion i) (_ : i.IsOver (Spec (CommRingCat.of k₀)))
      (_ : IsFinite (Z ↘ Spec (CommRingCat.of k₀))),
      IsCompl (Set.range j.base) (Set.range i.base) := by
  -- the boundary is finite
  have hfin : (Set.range j.base)ᶜ.Finite := by
    have := SmoothOfRelativeDimension.smooth 1 (C ↘ Spec (CommRingCat.of k₀))
    have := LocallyOfFiniteType.isLocallyNoetherian (C ↘ Spec (CommRingCat.of k₀))
    have := IsRegular.of_smooth (C ↘ Spec (CommRingCat.of k₀))
    have : ConnectedSpace C :=
      GeometricallyConnected.connectedSpace_of_subsingleton (f := C ↘ Spec (CommRingCat.of k₀))
    have := IsRegular.irreducibleSpace C
    have : IsNoetherian C := {}
    obtain ⟨u⟩ : Nonempty U := j.denseRange.nonempty_iff.2 inferInstance
    have hdim : topologicalKrullDim C ≤ 1 := by
      exact_mod_cast topologicalKrullDim_le_of_smoothOfRelativeDimension
        (C ↘ Spec (CommRingCat.of k₀)) 1
    exact j.isOpenEmbedding.isOpen_range.finite_compl_of_topologicalKrullDim_le_one hdim
      ⟨_, u, rfl⟩
  obtain ⟨Z, i, _, hi⟩ : ∃ (Z : Scheme.{u}) (i : Z ⟶ C), IsClosedImmersion i ∧
      Set.range i.base = (Set.range j.base)ᶜ :=
    ⟨_, j.opensRange.closedComplement, inferInstance, by simp⟩
  let : Z.Over (Spec (CommRingCat.of k₀)) := ⟨i ≫ C ↘ Spec (CommRingCat.of k₀)⟩
  have : i.IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
  refine ⟨Z, inferInstance, i, inferInstance, inferInstance, ?_, by rw [hi]; exact isCompl_compl⟩
  have hZ : Finite Z := by
    have h := hfin.preimage (f := i.base) i.isClosedEmbedding.injective.injOn
    rw [← hi, Set.preimage_range] at h
    exact Set.finite_univ_iff.1 h
  have : LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀)) :=
    inferInstanceAs (LocallyOfFiniteType (i ≫ C ↘ Spec (CommRingCat.of k₀)))
  have : QuasiCompact (Z ↘ Spec (CommRingCat.of k₀)) :=
    inferInstanceAs (QuasiCompact (i ≫ C ↘ Spec (CommRingCat.of k₀)))
  have : LocallyQuasiFinite (Z ↘ Spec (CommRingCat.of k₀)) :=
    locallyQuasiFinite_iff_finite_preimage_singleton.2 fun _ ↦ Set.toFinite _
  exact IsFinite.of_locallyQuasiFinite _

/-- *Boundary comparison in degrees other than `0, 1`.* For the dense open immersion
`j : U₀ ↪ C₀` and any Weil sheaf `F` on `U₀`, the open–closed triangle
`RΓ_c(U, F) → RΓ_c(C, j_*F) → RΓ_c(Z, i^*j_*F) →` along the finite boundary `i : Z₀ ↪ C₀`, whose
third term is concentrated in degree zero, gives Frobenius-equivariant isomorphisms
`H_c^r(U, F) ≅ H_c^r(C, j_*F)` for all `r ∉ {0, 1}`.
(blueprint: `lem-a1-middle-extension-endpoints`, step "Degree two and the range", from the
boundary localization triangle `prop-a1-curve-boundary-sequence`) -/
theorem nonempty_equiv_compactlySupportedCohomology_directImage
    [IsSeparated (U ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (U ↘ Spec (CommRingCat.of k₀))] {r : ℤ} (hr₀ : r ≠ 0) (hr₁ : r ≠ 1) :
    Nonempty ((F.compactlySupportedCohomology r).Equiv
      (((WeilSheaf.directImage j).obj F).compactlySupportedCohomology r)) := by
  obtain ⟨Z, _, i, _, _, _, hij⟩ := exists_isFinite_closedComplement (k₀ := k₀) j
  obtain ⟨T, hT, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ :=
    WeilComplex.exists_distTriang_derivedLowerShriek_openClosed j i hij
      (C ↘ Spec (CommRingCat.of k₀))
      (WeilSheaf.toComplex.obj ((WeilSheaf.directImage j).obj F))
  obtain ⟨eA⟩ := WeilSheaf.nonempty_upperStar_directImage_iso j F
  -- the three vertices
  let e₁' : T.obj₁ ≅ (WeilComplex.derivedLowerShriek k₀ l (U ↘ Spec (CommRingCat.of k₀))).obj
      (WeilSheaf.toComplex.obj F) :=
    e₁ ≪≫ (WeilComplex.derivedLowerShriek k₀ l (j ≫ C ↘ Spec (CommRingCat.of k₀))).mapIso
      (WeilComplex.upperStarToComplexIso j ((WeilSheaf.directImage j).obj F)
        ≪≫ WeilSheaf.toComplex.mapIso eA) ≪≫
      (WeilComplex.derivedLowerShriekCongr (comp_over j _)).app _
  let e₃' : T.obj₃ ≅ (WeilComplex.derivedLowerShriek k₀ l (Z ↘ Spec (CommRingCat.of k₀))).obj
      (WeilSheaf.toComplex.obj
        ((WeilSheaf.upperStar i).obj ((WeilSheaf.directImage j).obj F))) :=
    e₃ ≪≫ (WeilComplex.derivedLowerShriek k₀ l (i ≫ C ↘ Spec (CommRingCat.of k₀))).mapIso
      (WeilComplex.upperStarToComplexIso i ((WeilSheaf.directImage j).obj F)) ≪≫
      (WeilComplex.derivedLowerShriekCongr (comp_over i _)).app _
  -- the boundary has no cohomology outside degree zero
  have hZ (n : ℤ) (hn : n ≠ 0) : Subsingleton (T.obj₃.cohomologyFrobeniusModule n).carrier :=
    (WeilSheaf.globalSectionsEquivOfIso ((WeilComplex.homologySheaf n).mapIso
      e₃')).toLinearEquiv.toEquiv.subsingleton_congr.2
        (WeilSheaf.subsingleton_compactlySupportedCohomology_of_isFinite _ hn)
  obtain ⟨E⟩ := WeilComplex.nonempty_equiv_cohomologyFrobeniusModule_of_distTriang hT r
    (hZ _ (by omega)) (hZ _ hr₀)
  exact ⟨(WeilSheaf.globalSectionsEquivOfIso
    ((WeilComplex.homologySheaf r).mapIso e₁')).symm.trans
    (E.trans (WeilSheaf.globalSectionsEquivOfIso ((WeilComplex.homologySheaf r).mapIso e₂)))⟩

end Boundary

omit [IsDominant j] [GeometricallyConnected (C ↘ Spec (CommRingCat.of k₀))] in
/-- For a dense open immersion `j : U₀ ↪ C₀` with `C₀` a smooth geometrically connected affine
curve and `F` lisse on `U₀`, the compactly supported cohomology `H_c^r(C, j_*F)` vanishes for
every `r` outside `{0, 1, 2}`: `j_*F` is a Weil sheaf on the smooth affine curve `C₀`
(`AlgebraicGeometry.WeilSheaf.subsingleton_compactlySupportedCohomology_of_isAffine`).
(blueprint: `lem-a1-middle-extension-endpoints`) -/
theorem subsingleton_compactlySupportedCohomology_directImage (_hF : F.IsLisse) {r : ℤ}
    (hr : r < 0 ∨ 2 < r) :
    Subsingleton
      (((WeilSheaf.directImage j).obj F).compactlySupportedCohomology r).carrier :=
  WeilSheaf.subsingleton_compactlySupportedCohomology_of_isAffine _ hr

open ProEtale in
attribute [local instance] Compactification.over in
/-- In the situation of `AlgebraicGeometry.subsingleton_compactlySupportedCohomology_directImage`
the degree-zero compactly supported cohomology `H_c^0(C, j_*F)` vanishes, because a nonzero
global section of a lisse sheaf on a connected open has full support on a nonproper curve.

`H_c^0(C, j_*F)` is the space of global sections of `ī_! j̄_* F` on the compactification
`ī : C ⟶ Z`
(`AlgebraicGeometry.WeilSheaf.subsingleton_compactlySupportedCohomology_zero_of_isZero`).
The affine curve `C` is not proper, so a boundary point `z ∈ Z ∖ C` is a specialization of a
point of `C`, hence of the generic point of the irreducible curve `C`, which lies in the dense
open `U`; a global section of `ī_! j̄_* F` vanishes near `z`, so by lissity of `F` its
restriction to the connected curve `U`, hence the section itself, vanishes
(`ProEtale.IsAdicLisseSheaf.isZero_globalSections_adicOpenImmersionLowerShriek_adicLowerStar`).
(blueprint: `lem-a1-middle-extension-endpoints`) -/
theorem subsingleton_compactlySupportedCohomology_directImage_zero (hF : F.IsLisse) :
    Subsingleton
      (((WeilSheaf.directImage j).obj F).compactlySupportedCohomology 0).carrier := by
  have := SmoothOfRelativeDimension.smooth 1 (C ↘ Spec (CommRingCat.of k₀))
  have : GeometricallyIrreducible (C ↘ Spec (CommRingCat.of k₀)) :=
    .of_smooth_of_geometricallyConnected _
  have : ConnectedSpace C :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f := C ↘ Spec (CommRingCat.of k₀))
  have : Nonempty U := j.denseRange.nonempty_iff.2 inferInstance
  have : LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over j (Spec (CommRingCat.of k₀))]; infer_instance
  have : QuasiCompact (U ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over j (Spec (CommRingCat.of k₀))]; infer_instance
  have : GeometricallyIrreducible (U ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over j (Spec (CommRingCat.of k₀))]
    exact GeometricallyIrreducible.comp_of_isOpenImmersion j _
  refine WeilSheaf.subsingleton_compactlySupportedCohomology_zero_of_isZero _ ?_
  set c := HasCompactification.compactification (C ↘ Spec (CommRingCat.of k₀))
    (hf := hasCompactification_of_over (k₀ := k₀) (C ↘ Spec (CommRingCat.of k₀)))
  set p := (C ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure
  set q := (c.Z ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure
  set i := Scheme.Hom.geometricFiberMap c.i (comp_over c.i (Spec (CommRingCat.of k₀)))
  set pU := (U ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure
  set jb := Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀)))
  -- the geometric fibre `C̄` is a nonempty irreducible affine curve, open in the proper `Z̄`
  have : IsProper c.g := c.isProper
  have : IsProper (c.Z ↘ Spec (CommRingCat.of k₀)) := by
    change IsProper (c.g ≫ _)
    infer_instance
  have : IsProper q := inferInstanceAs (IsProper (Limits.pullback.snd _ _))
  have : GeometricallyConnected p :=
    inferInstanceAs (GeometricallyConnected (Limits.pullback.snd _ _))
  have : ConnectedSpace (C ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f := p)
  have : IsAffineHom p := inferInstanceAs (IsAffineHom (Limits.pullback.snd _ _))
  have : IsAffine (C ↘ Spec (CommRingCat.of k₀)).geometricFiber := isAffine_of_isAffineHom p
  have : SmoothOfRelativeDimension (0 + 1) (i ≫ q) := by
    rw [Scheme.Hom.geometricFiberMap_comp_geometricFiberToAlgebraicClosure]
    exact inferInstanceAs (SmoothOfRelativeDimension 1 (Limits.pullback.snd _ _))
  have : UniversallyOpen (C ↘ Spec (CommRingCat.of k₀)) := inferInstance
  have : IrreducibleSpace (Scheme.specAlgebraicClosure k₀).left :=
    inferInstanceAs (IrreducibleSpace (Spec (.of (AlgebraicClosure k₀))))
  have : IrreducibleSpace (C ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
    inferInstanceAs (IrreducibleSpace ↥(Limits.pullback (C := Scheme.{u})
      (C ↘ Spec (CommRingCat.of k₀)) (Scheme.specAlgebraicClosure k₀).hom))
  -- the geometric fibre `Ū` is a connected noetherian scheme
  have : GeometricallyConnected pU :=
    inferInstanceAs (GeometricallyConnected (Limits.pullback.snd _ _))
  have : ConnectedSpace (U ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f := pU)
  have : LocallyOfFiniteType pU :=
    inferInstanceAs (LocallyOfFiniteType (Limits.pullback.snd _ _))
  have : QuasiCompact pU := inferInstanceAs (QuasiCompact (Limits.pullback.snd _ _))
  have := LocallyOfFiniteType.isLocallyNoetherian pU
  have : CompactSpace (U ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
    (quasiCompact_iff_compactSpace pU).mp inferInstance
  have : IsNoetherian (U ↘ Spec (CommRingCat.of k₀)).geometricFiber := ⟨⟩
  -- a boundary point, specializing from the generic point of `C̄`, which lies in `Ū`
  obtain ⟨x, z, hz, hxz⟩ := exists_specializes_notMem_range_of_isProper i q 0
  have hη : genericPoint (C ↘ Spec (CommRingCat.of k₀)).geometricFiber ∈ Set.range jb.base := by
    have hd := Scheme.Hom.dense_range_geometricFiberMap (k₀ := k₀) j j.denseRange
    refine ((genericPoint_spec _).mem_open_set_iff jb.isOpenEmbedding.isOpen_range).2 ?_
    simpa using hd.nonempty
  obtain ⟨w, hw⟩ := hη
  exact IsAdicLisseSheaf.isZero_globalSections_adicOpenImmersionLowerShriek_adicLowerStar i jb hF
    hz (by rw [hw]; exact ((genericPoint_specializes x).map i.base.hom.continuous).trans hxz)

omit [Finite k₀] [QuasiCompact j] in
include j in
/-- The dense open `U₀` of the smooth geometrically connected affine curve `C₀` is again a
smooth geometrically connected affine curve: it is affine as an open of the Dedekind scheme
`C₀` (`AlgebraicGeometry.isAffine_of_isOpenImmersion_of_smoothOfRelativeDimension_one`), and
geometrically irreducible as a nonempty open of the geometrically irreducible `C₀`. -/
theorem isAffine_and_smoothOfRelativeDimension_and_geometricallyConnected :
    IsAffine U ∧ SmoothOfRelativeDimension 1 (U ↘ Spec (CommRingCat.of k₀)) ∧
      GeometricallyConnected (U ↘ Spec (CommRingCat.of k₀)) := by
  have := SmoothOfRelativeDimension.smooth 1 (C ↘ Spec (CommRingCat.of k₀))
  have : ConnectedSpace C :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f := C ↘ Spec (CommRingCat.of k₀))
  have : Nonempty U := j.denseRange.nonempty_iff.2 inferInstance
  have : GeometricallyIrreducible (C ↘ Spec (CommRingCat.of k₀)) :=
    .of_smooth_of_geometricallyConnected _
  refine ⟨isAffine_of_isOpenImmersion_of_smoothOfRelativeDimension_one j
    (C ↘ Spec (CommRingCat.of k₀)), ?_, ?_⟩
  · rw [← comp_over j (Spec (CommRingCat.of k₀)), ← zero_add 1]
    infer_instance
  · have : GeometricallyIrreducible (U ↘ Spec (CommRingCat.of k₀)) := by
      rw [← comp_over j (Spec (CommRingCat.of k₀))]
      exact GeometricallyIrreducible.comp_of_isOpenImmersion j _
    infer_instance

/--
In degree two, `H_c^2(C, j_*F)` is the geometric coinvariants `V_{π₁(U)}` of `F`, Tate-twisted
by `(-1)`: the Frobenius of the cohomology is `q` times the Frobenius of the coinvariants.

```
  H_c²(C, j_*F) ──e──▶ V_{π₁(U)}
        │                 │
   Frob │                 │ q · Frob
        ▼                 ▼
  H_c²(C, j_*F) ──e──▶ V_{π₁(U)}
```

The boundary comparison `H_c^2(U, F) ≅ H_c^2(C, j_*F)`
(`AlgebraicGeometry.nonempty_equiv_compactlySupportedCohomology_directImage`) reduces this to the
description of `H_c^2(U, F)` on the smooth geometrically connected affine curve `U₀`
(`AlgebraicGeometry.WeilSheaf.nonempty_equiv_compactlySupportedCohomology_two`,
blueprint `lem-a1-affine-hc2`).
(blueprint: `lem-a1-middle-extension-endpoints`)
-/
theorem nonempty_equiv_compactlySupportedCohomology_directImage_two
    [QuasiCompact (U ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))] (hF : F.IsLisse) :
    Nonempty ((((WeilSheaf.directImage j).obj F).compactlySupportedCohomology 2).Equiv
      ((F.geometricCoinvariants hF).tateTwist (Nat.card k₀) (-1))) := by
  have : IsSeparated (U ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over j (Spec (CommRingCat.of k₀))]; infer_instance
  obtain ⟨_, _, _⟩ := isAffine_and_smoothOfRelativeDimension_and_geometricallyConnected (k₀ := k₀) j
  obtain ⟨e⟩ := nonempty_equiv_compactlySupportedCohomology_directImage j F (r := 2)
    (by norm_num) (by norm_num)
  obtain ⟨e'⟩ := WeilSheaf.nonempty_equiv_compactlySupportedCohomology_two F hF
  exact ⟨e.symm.trans e'⟩

/-- If `F` is moreover punctually `ι`-pure of weight `w`, then `H_c^2(C, j_*F)` is pure of
weight `w + 2`: the Tate twist of
`AlgebraicGeometry.nonempty_equiv_compactlySupportedCohomology_directImage_two` raises weights
by two. (blueprint: `lem-a1-middle-extension-endpoints`) -/
theorem isPureOfWeightOver_compactlySupportedCohomology_directImage_two
    (ι : PadicAlgCl l →+* ℂ) (hF : F.IsLisse) {w : ℝ}
    (hw : F.IsPunctuallyPureOfWeight ι w) :
    (((WeilSheaf.directImage j).obj F).compactlySupportedCohomology 2).IsPureOfWeightOver
      k₀ ι (w + 2) := by
  have : QuasiCompact (C ↘ Spec (CommRingCat.of k₀)) := inferInstance
  have : QuasiCompact (U ↘ Spec (CommRingCat.of k₀)) := by
    rw [← CategoryTheory.comp_over j (Spec (CommRingCat.of k₀))]; infer_instance
  have : LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀)) := by
    rw [← CategoryTheory.comp_over j (Spec (CommRingCat.of k₀))]; infer_instance
  obtain ⟨e⟩ := nonempty_equiv_compactlySupportedCohomology_directImage_two j F hF
  have h := (WeilSheaf.isPureOfWeightOver_geometricCoinvariants ι F hF hw).tateTwist
    Nat.card_pos (-1)
  have h' : w - 2 * ((-1 : ℤ) : ℝ) = w + 2 := by push_cast; ring
  rw [h'] at h
  exact FrobeniusModule.IsPureOfWeight.of_equiv e h

end AlgebraicGeometry
