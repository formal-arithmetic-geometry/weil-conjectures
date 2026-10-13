/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.DeligneLaumon.AffineLine.Defs
public import WeilConjectures.WeilSheaf.OpenClosedTriangle
public import WeilConjectures.WeilSheaf.UpperStarLowerStar
public import WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary
public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.Trace
public import WeilConjectures.WeilSheaf.VerdierDualFinite
public import WeilConjectures.WeilSheaf.LowerStarTriangulated
public import WeilConjectures.WeilSheaf.DirectImageStalkMap
public import WeilConjectures.WeilSheaf.StalkConstantTwist
public import WeilConjectures.WeilSheaf.StalkUpperStar
public import WeilConjectures.WeilSheaf.TraceFunction
public import WeilConjectures.WeilSheaf.TraceFunctionOps
public import WeilConjectures.WeilSheaf.StalkIso
public import WeilConjectures.WeilSheaf.ConstantTwistCohomology
public import WeilConjectures.PointCount
public import WeilConjectures.ConstructibleSheaf.UniversalHomeomorphism
public import WeilConjectures.Mathlib.Topology.KrullDimension
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Local boundary duality on a curve

Let `j : U₀ ↪ C₀` be a dense open immersion of smooth curves and `F` a lisse Weil sheaf on
`U₀`. At a missing closed point `s` the two boundary modules `(j_*F^∨)_s̄` and `(R¹j_*F)_s̄`
are dual to one another, up to a Tate twist: the duality `𝔻_Z A(F) ≃ A(F^∨)(1)[1]` for the
boundary complex `A(F) = i^*Rj_*F` on the finite complement, obtained from Verdier exchange
and smooth curve duality, reads in degree `-1` as a perfect pairing into `ℚ̄_ℓ(-1)`.

The open–closed triangle `j_!F → j_*F → i_*i^*j_*F` also gives the boundary sequence
`H_c^0(Z, i^*j_*F) → H_c^1(U, F) → H_c^1(C, j_*F) → 0`, since the cohomology of the finite
boundary `Z` is concentrated in degree zero.

The second half of the same blueprint subsection, that a nonzero linear Artin–Schreier sheaf
`ℒ_{ψ(a x)}` is ramified at infinity, is stated for the Artin–Schreier extension of the local
field `k((t))` at infinity, where the inertia group acts:
`LaurentSeries.exists_algEquiv_apply_eq_add_C_of_pow_sub_eq_single`. It is not stated for
`AlgebraicGeometry.WeilSheaf.IsUnramifiedAtInfinity` (extension to a lisse sheaf across `∞`):
relating that condition to the inertia action at `∞` needs the fundamental representation of a
lisse Weil sheaf (`def-wf-fundamental-representation`), which does not exist yet, and a direct
proof would need the triviality of lisse `ℓ`-adic sheaves on `ℙ¹_k̄`.

## Main statements

- `AlgebraicGeometry.exists_linearEquiv_dual_stalk_higherDirectImage`: the local boundary
  pairing.
- `AlgebraicGeometry.exists_exact_compactlySupportedCohomology_boundary`: the boundary sequence
  in degrees zero and one.

## TODO

- Prove the local boundary pairing. The proof of the blueprint uses Verdier duality, dualizing
  complexes and the exceptional inverse image `Ri^!` for `ℚ̄_ℓ`-Weil complexes
  (`thm-coef-qbar-verdier`, `fix-cor-verdier-exchange`, `def-weil-exceptional-inverse-image`),
  none of which exists yet for `AlgebraicGeometry.WeilComplex`: the pro-étale Verdier dual
  `AlgebraicGeometry.ProEtale.verdierDual` is for sheaves with values in a fixed coefficient
  category, not for `ℚ̄_ℓ,X`-modules with a Weil structure.
  The alternative local route, `(j_*F)_s̄ = V^{I_s}` and `(R¹j_*F)_s̄ = H¹(I_s, V)` for the
  inertia representation `V` of `F` at `s`, followed by linear algebra over the tame quotient,
  is not available either: it needs the stalk of `Rj̄_*` at `s̄` as the pro-étale cohomology of
  the punctured strict henselization, and the comparison of pro-étale cohomology of a field
  with `ℚ̄_ℓ,X`-coefficients with continuous Galois cohomology.
- The maps `g` and `h` of `AlgebraicGeometry.exists_exact_compactlySupportedCohomology_boundary`
  should be the maps induced by the canonical arrow `WeilSheaf.extensionByZeroToDirectImage j`
  from `j_!F` to `j_*F`. This needs the identification `H_c(U, F) ≅ H_c(C, j_!F)` and the
  functoriality of `compactlySupportedCohomology`; once they exist, the existential statement
  should be replaced by one about these maps.
-/

/-
Plan of the proof of `exists_linearEquiv_dual_stalk_higherDirectImage` (work in progress).

Route: the Verdier duality argument of the blueprint, with the nodes of other sections stated
for Weil complexes in `WeilConjectures.WeilSheaf.VerdierDual` (each with `sorry`, each with its
blueprint id), and with honest data:
* `Rf^!` is the right adjoint of `Rf₀!` on Weil complexes (`WeilComplex.upperShriek`); that it
  exists is the constructible adjunction of `thm-coef-qbar-verdier`;
* `ω_X = Ra_X^! ℚ̄_ℓ` and `𝔻_X = RHom(-, ω_X)` (`ProEtaleWeilSheaf.derivedHom`).
Nodes used: `thm-coef-qbar-verdier` (adjunction, typing of `𝔻`, exactness, biduality,
`Rf^! = 𝔻 f^* 𝔻`), `fix-cor-verdier-exchange` (for `j`),
`cor-pur-adic-and-rational-smooth-dualizing-complexes` (`ω_U = ℚ̄_ℓ(1)[2]`, `ω_Z = ℚ̄_ℓ`),
`lem-sf-hom-finite-projective` (`RHom(P, N) = P^∨ ⊗ N` for lisse `P`),
`prop-sf-localization-all-stages` (4) (`Ri^! Rj_* = 0`, unit of `Ri_! ⊣ Ri^!`).
Proved here:
1. `𝔻_C Rj_* G ≅ j_! 𝔻_U G` (exchange + biduality);
2. `Ri^! 𝔻_C K ≅ 𝔻_Z i^* K` (`Rf^! = 𝔻 f^* 𝔻` + biduality);
3. `Ri^! j_! G ≅ i^* Rj_* G [-1]` (open–closed triangle, `j^* Rj_* = 𝟭`, step (4) of the
   localization node);
4. `𝔻_Z A(F) ≅ A(F^∨(1))[1]` for `A(F) = i^* Rj_* F`, using `𝔻_U F ≅ F^∨(1)[2]`;
5. `𝔻_Z` is t-exact on the finite reduced `Z` (dévissage from `𝔻_Z (G[0]) ≅ G^∨[0]`), hence
   `𝓗⁻¹(𝔻_Z A) ≅ (𝓗¹ A)^∨` as Weil sheaves on `Z`; taking stalks at `s`, with
   `(G^∨)_s = (G_s)^∨` and the twist `(1)` acting by `q_s⁻¹` on the local Frobenius, gives `e`.
-/

@[expose] public section

universe u

open CategoryTheory Polynomial Pretriangulated Opposite TopologicalSpace

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

open scoped ProEtale

/-- In a noetherian quasi-sober `T₀` space of dimension at most one, the complement of a dense
open subset is finite: a point outside the open is closed, being a proper specialization of the
generic point of an irreducible component, which lies in the open. -/
theorem _root_.Dense.finite_compl_of_topologicalKrullDim_le_one {X : Type*} [TopologicalSpace X]
    [QuasiSober X] [T0Space X] [NoetherianSpace X] (h : topologicalKrullDim X ≤ 1) {U : Set X}
    (hU : IsOpen U) (hd : Dense U) : Uᶜ.Finite := by
  have hcl : ∀ x ∉ U, IsClosed ({x} : Set X) := by
    intro x hx
    set Z := irreducibleComponent x
    have hZ : Z ∈ irreducibleComponents X := irreducibleComponent_mem_irreducibleComponents x
    have hZc : IsClosed Z := isClosed_of_mem_irreducibleComponents Z hZ
    obtain ⟨V, hVo, hVne, hVZ⟩ :=
      NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent Z hZ
    obtain ⟨u, huV, huU⟩ := hd.inter_open_nonempty V hVo hVne
    have : IrreducibleSpace Z := isIrreducible_iff_irreducibleSpace.mp hZ.1
    have hdim : topologicalKrullDim Z ≤ 1 := (topologicalKrullDim_subspace_le X Z).trans h
    have hU' : IsOpen (Subtype.val ⁻¹' U : Set Z) := hU.preimage continuous_subtype_val
    have hc := hU'.isClosed_singleton_of_mem_compl hdim ⟨⟨u, hVZ huV⟩, huU⟩
      (x := ⟨x, mem_irreducibleComponent⟩) hx
    simpa using hZc.isClosedMap_subtype_val _ hc
  obtain ⟨S, hSf, hSc, hSi, hS⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible
    hU.isClosed_compl
  have key : ∀ t ∈ S, ∃ z, t = {z} := by
    intro t ht
    obtain ⟨z, hz⟩ := QuasiSober.sober (hSi t ht) (hSc t ht)
    have hzU : z ∉ U := by
      have : z ∈ Uᶜ := hS ▸ Set.mem_sUnion_of_mem hz.mem ht
      exact this
    exact ⟨z, by rw [← hz.def, (hcl z hzU).closure_eq]⟩
  rw [hS]
  refine hSf.sUnion fun t ht ↦ ?_
  obtain ⟨z, rfl⟩ := key t ht
  exact Set.finite_singleton z

omit [Finite k₀] in
/-- The reduced closed complement `Z₀` of a dense open `U₀` of a smooth curve `C₀` over `k₀`: a
finite reduced `k₀`-scheme, `C₀` being noetherian of dimension one. -/
theorem exists_isReduced_isClosedImmersion_range_eq_compl_of_curve {U C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k₀))] (j : U ⟶ C) [IsOpenImmersion j] [IsDominant j]
    [SmoothOfRelativeDimension 1 (C ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (C ↘ Spec (CommRingCat.of k₀))] :
    ∃ (Z : Scheme.{u}) (_ : Z.Over (Spec (CommRingCat.of k₀))) (i : Z ⟶ C)
      (_ : IsClosedImmersion i) (_ : i.IsOver (Spec (CommRingCat.of k₀)))
      (_ : IsFinite (Z ↘ Spec (CommRingCat.of k₀))) (_ : IsReduced Z),
      Set.range i.base = (Set.range j.base)ᶜ := by
  have := LocallyOfFiniteType.isLocallyNoetherian (C ↘ Spec (CommRingCat.of k₀))
  have : CompactSpace C :=
    QuasiCompact.compactSpace_of_compactSpace (C ↘ Spec (CommRingCat.of k₀))
  have : IsNoetherian C := @IsNoetherian.mk _ inferInstance inferInstance
  have hfin : (Set.range j.base)ᶜ.Finite :=
    Dense.finite_compl_of_topologicalKrullDim_le_one (by exact_mod_cast
      topologicalKrullDim_le_of_smoothOfRelativeDimension (C ↘ Spec (CommRingCat.of k₀)) 1)
      j.isOpenEmbedding.isOpen_range j.denseRange
  let I := Scheme.IdealSheafData.vanishingIdeal
    (⟨(Set.range j.base)ᶜ, j.isOpenEmbedding.isOpen_range.isClosed_compl⟩ : Closeds C)
  have hI : Set.range I.subschemeι.base = (Set.range j.base)ᶜ := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    simp [I]
  let : I.subscheme.Over (Spec (CommRingCat.of k₀)) := ⟨I.subschemeι ≫ C ↘ _⟩
  have : I.subschemeι.IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
  have : Finite I.subscheme := by
    have := hfin.to_subtype
    rw [← hI] at this
    exact Finite.of_equiv _ (Equiv.ofInjective _ I.subschemeι.isClosedEmbedding.injective).symm
  have : LocallyOfFiniteType (I.subscheme ↘ Spec (CommRingCat.of k₀)) :=
    show LocallyOfFiniteType (I.subschemeι ≫ C ↘ _) from inferInstance
  have : LocallyQuasiFinite (I.subscheme ↘ Spec (CommRingCat.of k₀)) :=
    .of_finite_preimage_singleton _ fun _ ↦ Set.toFinite _
  exact ⟨I.subscheme, inferInstance, I.subschemeι, inferInstance, inferInstance,
    IsFinite.of_locallyQuasiFinite _, inferInstance, hI⟩

/-- The stalk of a pullback `φ^* F` at a closed point `x` is the stalk of `F` at `φ x`, with its
local Frobenius, when `x` and `φ x` have the same degree over `k₀` (for instance for a closed
immersion `φ`). -/
theorem WeilSheaf.nonempty_equiv_stalk_upperStar {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))] (φ : X ⟶ Y)
    [φ.IsOver (Spec (CommRingCat.of k₀))] (F : WeilSheaf k₀ l Y) (x : X.finitePoints)
    (y : Y.finitePoints) (hxy : φ.base x.1 = y.1)
    (hdeg : (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1 =
      (Y ↘ Spec (CommRingCat.of k₀)).degreeOver y.1) :
    Nonempty ((((WeilSheaf.upperStar φ).obj F).stalk x).Equiv (F.stalk y)) := by
  have hφ := comp_over φ (Spec (CommRingCat.of k₀))
  set s := (X ↘ Spec (CommRingCat.of k₀)).geometricFiberPointOfFinitePoint x
  have ht := Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow
    (X ↘ Spec (CommRingCat.of k₀)) x
  have ht' : (s ≫ Scheme.Hom.geometricFiberMap φ hφ) ≫
      ((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^
        (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1).hom =
      (specGeometricFrobenius k₀ ^ (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1).hom ≫
        (s ≫ Scheme.Hom.geometricFiberMap φ hφ) := by
    rw [Category.assoc, Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_pow,
      ← Category.assoc, ht, Category.assoc]
  have : IsIso (𝟙 _ : (Scheme.Hom.geometricFiberMap φ hφ)^*[WeilCoefficients.{u} l].obj
      F.obj.carrier.X ⟶ ((WeilSheaf.upperStar φ).obj F).obj.carrier.X) :=
    inferInstanceAs (IsIso (𝟙 ((Scheme.Hom.geometricFiberMap φ hφ)^*[WeilCoefficients.{u} l].obj
      F.obj.carrier.X)))
  obtain ⟨e₁⟩ := WeilSheaf.nonempty_equiv_stalkAt_of_upperStar
    (G := (WeilSheaf.upperStar φ).obj F) (θ := 𝟙 _)
    (WeilSheaf.upperStar_frobeniusStr_compatible (φ := φ) F) s _ ht ht'
  set s' := (Y ↘ Spec (CommRingCat.of k₀)).geometricFiberPointOfFinitePoint y
  have hbase : (s' ≫ (Y ↘ Spec (CommRingCat.of k₀)).geometricFiberProj).base
      (IsLocalRing.closedPoint (AlgebraicClosure k₀)) = y.1 :=
    Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricFiberProj_base _ y
  have hss' : ((s ≫ Scheme.Hom.geometricFiberMap φ hφ) ≫
      (Y ↘ Spec (CommRingCat.of k₀)).geometricFiberProj).base
        (IsLocalRing.closedPoint (AlgebraicClosure k₀)) =
      (s' ≫ (Y ↘ Spec (CommRingCat.of k₀)).geometricFiberProj).base
        (IsLocalRing.closedPoint (AlgebraicClosure k₀)) := by
    rw [hbase, Category.assoc, Scheme.Hom.geometricFiberMap_comp_geometricFiberProj,
      ← Category.assoc, ← hxy]
    exact congrArg φ.base
      (Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricFiberProj_base _ x)
  have hs' := Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow
    (Y ↘ Spec (CommRingCat.of k₀)) y
  have key : ∀ (m : ℕ) (hm : m = (Y ↘ Spec (CommRingCat.of k₀)).degreeOver y.1)
      (h₁ : s' ≫ ((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).hom =
        (specGeometricFrobenius k₀ ^ m).hom ≫ s')
      (h₂ : (s ≫ Scheme.Hom.geometricFiberMap φ hφ) ≫
        ((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).hom =
        (specGeometricFrobenius k₀ ^ m).hom ≫ (s ≫ Scheme.Hom.geometricFiberMap φ hφ)),
      Nonempty ((F.stalkAt (s ≫ Scheme.Hom.geometricFiberMap φ hφ) m h₂).Equiv (F.stalk y)) := by
    rintro m rfl h₁ h₂
    exact F.nonempty_equiv_stalkAt _ _ hss' (by rw [hss', hbase]; exact y.2) _ h₂ h₁
  obtain ⟨e₂⟩ := key _ hdeg (hdeg ▸ hs') ht'
  exact ⟨e₁.symm.trans e₂⟩

/-- The direct image of Weil sheaves commutes with constant twists. -/
noncomputable def WeilSheaf.lowerStarConstantTwistIso {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))] (φ : X ⟶ Y)
    [φ.IsOver (Spec (CommRingCat.of k₀))] [QuasiCompact φ] [QuasiSeparated φ]
    [LocallyOfFiniteType φ] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    (P : WeilSheaf k₀ l X) (b : (PadicAlgCl l)ˣ) :
    (WeilSheaf.lowerStar φ).obj (P.constantTwist b) ≅
      ((WeilSheaf.lowerStar φ).obj P).constantTwist b :=
  ObjectProperty.isoMk _
    ((ProEtaleWeilSheaf.lowerStar k₀ l φ).mapIso (P.constantTwistObjIso b) ≪≫
      (ProEtaleWeilSheaf.constantTwistCompLowerStarIso k₀ l φ b).app P.obj ≪≫
      (((WeilSheaf.lowerStar φ).obj P).constantTwistObjIso b).symm)

/--
For a dense open immersion `j : U₀ ↪ C₀` of smooth curves, a lisse Weil sheaf `F` on `U₀` and a
closed point `s` of `C₀` outside `U₀`, there is a Frobenius-equivariant perfect pairing
`(j_*F^∨)_s̄ ⊗ (R¹j_*F)_s̄ → ℚ̄_ℓ(-1)`:

```
  (j_*F^∨)_s̄ ⊗ (R¹j_*F)_s̄ ──────▶ ℚ̄_ℓ(-1)
       │           │                  │
  Frob │      Frob │                  │ q_s
       ▼           ▼                  ▼
  (j_*F^∨)_s̄ ⊗ (R¹j_*F)_s̄ ──────▶ ℚ̄_ℓ(-1)
```

It is exhibited as a linear isomorphism of `(j_*F^∨)_s̄` onto the `ℚ̄_ℓ`-dual of `(R¹j_*F)_s̄`
which intertwines the two local Frobenius actions up to the factor `q_s` coming from the Tate
twist. (blueprint: `lem-a1-local-boundary-duality`, `sk-i-dl-a1-local`)
-/
theorem exists_linearEquiv_dual_stalk_higherDirectImage
    {U C : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))] [C.Over (Spec (CommRingCat.of k₀))]
    (j : U ⟶ C) [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]
    [IsDominant j]
    [SmoothOfRelativeDimension 1 (C ↘ Spec (CommRingCat.of k₀))]
    [IsSeparated (C ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (C ↘ Spec (CommRingCat.of k₀))]
    (F : WeilSheaf k₀ l U) (hF : F.IsLisse) (s : C.finitePoints)
    (hsU : s.1 ∉ Set.range j.base) :
    ∃ e : (((WeilSheaf.directImage j).obj (F.dual hF)).stalk s).carrier ≃ₗ[PadicAlgCl l]
        Module.Dual (PadicAlgCl l) (((WeilSheaf.higherDirectImage j 1).obj F).stalk s).carrier,
      ∀ a b, e ((((WeilSheaf.directImage j).obj (F.dual hF)).stalk s).frobenius a)
          ((((WeilSheaf.higherDirectImage j 1).obj F).stalk s).frobenius b) =
        (((C ↘ Spec (CommRingCat.of k₀)).residueCard s.1 : PadicAlgCl l)) * e a b := by
  classical
  rw [WeilSheaf.higherDirectImage_obj_eq]
  -- the open `U` is a smooth separated curve
  have hjC : j ≫ C ↘ Spec (CommRingCat.of k₀) = U ↘ Spec (CommRingCat.of k₀) := comp_over j _
  have : LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀)) := by rw [← hjC]; infer_instance
  have : IsSeparated (U ↘ Spec (CommRingCat.of k₀)) := by rw [← hjC]; infer_instance
  have : QuasiCompact (U ↘ Spec (CommRingCat.of k₀)) := by rw [← hjC]; infer_instance
  have : SmoothOfRelativeDimension 1 (U ↘ Spec (CommRingCat.of k₀)) := by
    have h : SmoothOfRelativeDimension (0 + 1) (j ≫ C ↘ Spec (CommRingCat.of k₀)) :=
      inferInstance
    rw [hjC] at h
    exact h
  -- the reduced closed complement `Z`, finite over `k₀`, and the point `z` of `Z` over `s`
  obtain ⟨Z, _, i, _, _, _, _, hij⟩ :=
    exists_isReduced_isClosedImmersion_range_eq_compl_of_curve (k₀ := k₀) j
  have : IsSeparated (Z ↘ Spec (CommRingCat.of k₀)) := inferInstance
  have : LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀)) := inferInstance
  have : QuasiCompact (Z ↘ Spec (CommRingCat.of k₀)) := inferInstance
  have hc : IsCompl (Set.range j.base) (Set.range i.base) := by
    rw [hij]
    exact isCompl_compl
  obtain ⟨z, hz⟩ : s.1 ∈ Set.range i.base := by
    rw [hij]
    exact hsU
  have := Scheme.Hom.isIso_residueFieldMap i z
  have hzf : z ∈ Z.finitePoints := (Scheme.Hom.mem_finitePoints_iff_of_isIso i z).1 (hz ▸ s.2)
  let zf : Z.finitePoints := ⟨z, hzf⟩
  have hdeg : (Z ↘ Spec (CommRingCat.of k₀)).degreeOver zf.1 =
      (C ↘ Spec (CommRingCat.of k₀)).degreeOver s.1 := by
    rw [← comp_over i (Spec (CommRingCat.of k₀)), Scheme.Hom.degreeOver_comp_of_isIso, hz]
  -- the boundary complex `A(F) = i^* Rj_* F` and its Verdier dual
  let A := (WeilComplex.upperStar i).obj
    ((WeilComplex.derivedLowerStar j).obj (WeilSheaf.toComplex.obj F))
  let c := WeilSheaf.cyclotomicUnit k₀ l ^ (1 : ℤ)
  let G := (F.dual hF).constantTwist c
  obtain ⟨eU⟩ := WeilComplex.nonempty_verdierDual_toComplex_iso_of_isLisse 1 F hF
  obtain ⟨eT⟩ := WeilSheaf.nonempty_dual_tensorObj_tateTwistSheaf_iso F hF 1
  obtain ⟨e₄⟩ := WeilComplex.nonempty_verdierDual_upperStar_derivedLowerStar_iso j i hc
    (WeilSheaf.toComplex.obj F)
  -- `𝔻_Z A(F) ≅ A(F^∨(1))[1]`, hence `𝓗⁻¹(𝔻_Z A(F)) ≅ i^*((j_* F^∨)(1))`
  let E₁ : (WeilComplex.verdierDual k₀ l Z).obj (op A) ≅
      (((WeilComplex.upperStar i).obj ((WeilComplex.derivedLowerStar j).obj
        (WeilSheaf.toComplex.obj G)))⟦(2 * ((1 : ℕ) : ℤ))⟧)⟦(-1 : ℤ)⟧ :=
    e₄ ≪≫ (shiftFunctor _ (-1 : ℤ)).mapIso ((WeilComplex.upperStar i).mapIso
      ((WeilComplex.derivedLowerStar j).mapIso (eU ≪≫
        (shiftFunctor _ (2 * ((1 : ℕ) : ℤ))).mapIso (WeilSheaf.toComplex.mapIso eT)) ≪≫
        ((WeilComplex.derivedLowerStar j).commShiftIso (2 * ((1 : ℕ) : ℤ))).app _) ≪≫
      ((WeilComplex.upperStar i).commShiftIso (2 * ((1 : ℕ) : ℤ))).app _)
  let L : (WeilComplex.homologySheaf (-1)).obj ((WeilComplex.verdierDual k₀ l Z).obj (op A)) ≅
      (WeilSheaf.upperStar i).obj (((WeilSheaf.lowerStar j).obj (F.dual hF)).constantTwist c) :=
    (WeilComplex.homologySheaf (-1)).mapIso E₁ ≪≫
      WeilComplex.homologySheafShiftIso _ (-1) (-1) (-2) (by norm_num) ≪≫
      WeilComplex.homologySheafShiftIso _ _ (-2) 0 (by norm_num) ≪≫
      WeilComplex.homologySheafUpperStarIso i 0 _ ≪≫
      (WeilSheaf.upperStar i).mapIso (WeilSheaf.homologySheafZeroDerivedLowerStarIso j G ≪≫
        WeilSheaf.lowerStarConstantTwistIso j (F.dual hF) c)
  -- `𝔻_Z` is t-exact on the finite `Z`: `𝓗⁻¹(𝔻_Z A(F)) ≅ (𝓗¹ A(F))^∨`
  set H := (WeilComplex.homologySheaf 1).obj A
  have hH : H.IsLisse := WeilSheaf.isLisse_of_isFinite_of_isReduced H
  obtain ⟨R₁⟩ := WeilComplex.nonempty_homologySheaf_neg_one_verdierDual_iso A
  obtain ⟨R₂⟩ := WeilComplex.nonempty_verdierDual_toComplex_iso_of_isFinite H
  obtain ⟨R₃⟩ := WeilSheaf.nonempty_dual_tensorObj_tateTwistSheaf_iso H hH 0
  let R : (WeilComplex.homologySheaf (-1)).obj ((WeilComplex.verdierDual k₀ l Z).obj (op A)) ≅
      (H.dual hH).constantTwist (WeilSheaf.cyclotomicUnit k₀ l ^ (0 : ℤ)) :=
    R₁ ≪≫ (WeilComplex.homologySheaf 0).mapIso R₂ ≪≫
      WeilSheaf.toComplexCompHomologySheafIso.app _ ≪≫ R₃
  -- the stalks at `z`
  have S₁ := (WeilSheaf.nonempty_equiv_stalk_upperStar i
    (((WeilSheaf.lowerStar j).obj (F.dual hF)).constantTwist c) zf s hz hdeg).some
  have S₂ := (WeilSheaf.nonempty_equiv_stalk_constantTwist
    ((WeilSheaf.lowerStar j).obj (F.dual hF)) c s).some
  have S₃ : (((WeilSheaf.upperStar i).obj
      (((WeilSheaf.lowerStar j).obj (F.dual hF)).constantTwist c)).stalk zf).Equiv
      (((H.dual hH).constantTwist (WeilSheaf.cyclotomicUnit k₀ l ^ (0 : ℤ))).stalk zf) :=
    (WeilSheaf.nonempty_equiv_stalk_of_iso (L.symm ≪≫ R) zf).some
  have S₄ := (WeilSheaf.nonempty_equiv_stalk_constantTwist (H.dual hH)
    (WeilSheaf.cyclotomicUnit k₀ l ^ (0 : ℤ)) zf).some
  have S₅ := (WeilSheaf.nonempty_equiv_stalk_dual hH zf).some
  have S₆ : (H.stalk zf).Equiv (((WeilSheaf.upperStar i).obj ((WeilComplex.homologySheaf 1).obj
      ((WeilComplex.derivedLowerStar j).obj (WeilSheaf.toComplex.obj F)))).stalk zf) :=
    (WeilSheaf.nonempty_equiv_stalk_of_iso (WeilComplex.homologySheafUpperStarIso i 1 _)
      zf).some
  have S₇ := (WeilSheaf.nonempty_equiv_stalk_upperStar i ((WeilComplex.homologySheaf 1).obj
      ((WeilComplex.derivedLowerStar j).obj (WeilSheaf.toComplex.obj F))) zf s hz hdeg).some
  -- the linear algebra
  set q : PadicAlgCl l := (Nat.card k₀ : PadicAlgCl l)
  set d := (C ↘ Spec (CommRingCat.of k₀)).degreeOver s.1
  have hcd : (c : PadicAlgCl l) ^ d = (q ^ d)⁻¹ := by
    rw [WeilSheaf.cyclotomicUnit_zpow_eq, zpow_neg, zpow_one, inv_pow]
  have hq : q ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hk : (c : PadicAlgCl l) ^ d ≠ 0 := by
    rw [hcd]
    exact inv_ne_zero (pow_ne_zero _ hq)
  have hone : ((WeilSheaf.cyclotomicUnit k₀ l ^ (0 : ℤ) : (PadicAlgCl l)ˣ) : PadicAlgCl l) ^
      (Z ↘ Spec (CommRingCat.of k₀)).degreeOver zf.1 = 1 := by
    simp
  let Ψ := S₂.symm.trans (S₁.symm.trans (S₃.trans S₄))
  let ψ := S₆.trans S₇
  refine ⟨Ψ.toLinearEquiv ≪≫ₗ S₅.toLinearEquiv ≪≫ₗ ψ.toLinearEquiv.symm.dualMap, fun a b ↦ ?_⟩
  have hΨ := Ψ.map_frobenius a
  rw [show ((((WeilSheaf.lowerStar j).obj (F.dual hF)).stalk s).rescale
      ((c : PadicAlgCl l) ^ d)).frobenius a = (c : PadicAlgCl l) ^ d •
        (((WeilSheaf.lowerStar j).obj (F.dual hF)).stalk s).frobenius a from
      FrobeniusModule.frobeniusEnd_rescale_apply hk a,
    show (((H.dual hH).stalk zf).rescale
      (((WeilSheaf.cyclotomicUnit k₀ l ^ (0 : ℤ) : (PadicAlgCl l)ˣ) : PadicAlgCl l) ^
        (Z ↘ Spec (CommRingCat.of k₀)).degreeOver zf.1)).frobenius (Ψ.toLinearEquiv a) =
      _ • ((H.dual hH).stalk zf).frobenius (Ψ.toLinearEquiv a) from
      FrobeniusModule.frobeniusEnd_rescale_apply (by rw [hone]; exact one_ne_zero) _,
    hone, one_smul, map_smul] at hΨ
  have hΨ' : Ψ.toLinearEquiv ((((WeilSheaf.lowerStar j).obj (F.dual hF)).stalk s).frobenius a) =
      (q ^ d) • ((H.dual hH).stalk zf).frobenius (Ψ.toLinearEquiv a) := by
    rw [← hΨ, smul_smul, hcd, mul_inv_cancel₀ (pow_ne_zero _ hq), one_smul]
  simp only [LinearEquiv.trans_apply, LinearEquiv.dualMap_apply]
  rw [hΨ', map_smul, S₅.map_frobenius, FrobeniusModule.Equiv.symm_map_frobenius ψ b,
    LinearMap.smul_apply, FrobeniusModule.dual_frobenius_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, smul_eq_mul]
  simp [Scheme.Hom.residueCard, q, d]

set_option maxHeartbeats 1600000 in
-- the cohomology of the three terms of the triangle unfolds through the Weil structures
/-- *Boundary localization sequence for a curve.* Let `j : U₀ ↪ C₀` be a dense open immersion
of smooth curves, `i : Z₀ ↪ C₀` the closed complement and `F` a lisse Weil sheaf on `U₀`. The
open–closed triangle `j_!F → j_*F → i_*i^*j_*F →` gives a long exact sequence of compactly
supported cohomology, and since the boundary `Z₀` is finite its cohomology is concentrated in
degree zero (`AlgebraicGeometry.WeilSheaf.subsingleton_compactlySupportedCohomology_of_isFinite`).
Hence there are Frobenius-equivariant maps forming an exact sequence

`H_c^0(Z, i^*j_*F) → H_c^1(U, F) → H_c^1(C, j_*F) → 0`,

and a Frobenius-equivariant injection `H_c^0(U, F) ↪ H_c^0(C, j_*F)`.
(blueprint: `prop-a1-curve-boundary-sequence`) -/
theorem exists_exact_compactlySupportedCohomology_boundary
    {U C Z : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))] [C.Over (Spec (CommRingCat.of k₀))]
    [Z.Over (Spec (CommRingCat.of k₀))]
    (j : U ⟶ C) [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]
    [IsDominant j] (i : Z ⟶ C) [IsClosedImmersion i] [i.IsOver (Spec (CommRingCat.of k₀))]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    [SmoothOfRelativeDimension 1 (C ↘ Spec (CommRingCat.of k₀))]
    [IsSeparated (C ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (C ↘ Spec (CommRingCat.of k₀))] [IsSeparated (U ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (U ↘ Spec (CommRingCat.of k₀))] [IsFinite (Z ↘ Spec (CommRingCat.of k₀))]
    (F : WeilSheaf k₀ l U) (_hF : F.IsLisse) :
    -- `j_*F` on `C` and the boundary sheaf `i^*j_*F` on `Z`
    let A := (WeilSheaf.directImage j).obj F
    let B := (WeilSheaf.upperStar i).obj A
    (∃ (δ : (B.compactlySupportedCohomology 0).carrier →ₗ[PadicAlgCl l]
          (F.compactlySupportedCohomology 1).carrier)
        (g : (F.compactlySupportedCohomology 1).carrier →ₗ[PadicAlgCl l]
          (A.compactlySupportedCohomology 1).carrier),
        Function.Exact δ g ∧ Function.Surjective g ∧
          (∀ x, δ ((B.compactlySupportedCohomology 0).frobenius x) =
            (F.compactlySupportedCohomology 1).frobenius (δ x)) ∧
          ∀ x, g ((F.compactlySupportedCohomology 1).frobenius x) =
            (A.compactlySupportedCohomology 1).frobenius (g x)) ∧
      ∃ h : (F.compactlySupportedCohomology 0).carrier →ₗ[PadicAlgCl l]
          (A.compactlySupportedCohomology 0).carrier,
        Function.Injective h ∧ ∀ x, h ((F.compactlySupportedCohomology 0).frobenius x) =
          (A.compactlySupportedCohomology 0).frobenius (h x) := by
  intro A B
  have : IsSeparated (Z ↘ Spec (CommRingCat.of k₀)) := inferInstance
  have : LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀)) := inferInstance
  have : QuasiCompact (Z ↘ Spec (CommRingCat.of k₀)) := inferInstance
  -- the open–closed triangle `RΓ_c(U, j^*K) → RΓ_c(C, K) → RΓ_c(Z, i^*K) →` for `K = j_*F`
  obtain ⟨α, β, γ, hT⟩ := WeilComplex.exists_distTriang_derivedLowerShriek_structure_openClosed j i
    hij
    (WeilSheaf.toComplex.obj A)
  set T := Triangle.mk α β γ
  -- identification of the outer terms
  have hA : A = (WeilSheaf.lowerStar j).obj F := rfl
  let eU : (WeilComplex.upperStar j).obj (WeilSheaf.toComplex.obj A) ≅
      WeilSheaf.toComplex.obj F :=
    (WeilSheaf.toComplexCompUpperStarIso j).app A ≪≫
      WeilSheaf.toComplex.mapIso (hA ▸ WeilSheaf.upperStarDirectImageIso j F)
  let eZ : (WeilComplex.upperStar i).obj (WeilSheaf.toComplex.obj A) ≅
      WeilSheaf.toComplex.obj B :=
    (WeilSheaf.toComplexCompUpperStarIso i).app A
  let EU (r : ℤ) := WeilComplex.cohomologyEquivOfIso
    ((WeilComplex.derivedLowerShriek k₀ l (U ↘ Spec (CommRingCat.of k₀))).mapIso eU) r
  let EZ (r : ℤ) := WeilComplex.cohomologyEquivOfIso
    ((WeilComplex.derivedLowerShriek k₀ l (Z ↘ Spec (CommRingCat.of k₀))).mapIso eZ) r
  -- the boundary has no cohomology outside degree `0`
  have hZ (r : ℤ) (hr : r ≠ 0) : Subsingleton (T.obj₃.cohomologyFrobeniusModule r).carrier := by
    have h := WeilSheaf.subsingleton_compactlySupportedCohomology_of_isFinite B hr
    exact ⟨fun a b ↦ (EZ r).toLinearEquiv.injective (h.elim _ _)⟩
  refine ⟨⟨(EU 1).toLinearEquiv.toLinearMap ∘ₗ WeilComplex.cohomologyδ T 0 1 rfl ∘ₗ
      (EZ 0).toLinearEquiv.symm.toLinearMap,
    WeilComplex.cohomologyMap T.mor₁ 1 ∘ₗ (EU 1).toLinearEquiv.symm.toLinearMap, ?_, ?_, ?_, ?_⟩,
    WeilComplex.cohomologyMap T.mor₁ 0 ∘ₗ (EU 0).toLinearEquiv.symm.toLinearMap, ?_, ?_⟩
  · intro y
    have hex := WeilComplex.exact_cohomologyδ_right T 0 1 rfl hT ((EU 1).toLinearEquiv.symm y)
    change WeilComplex.cohomologyMap T.mor₁ 1 ((EU 1).toLinearEquiv.symm y) = 0 ↔
      ∃ x, (EU 1).toLinearEquiv (WeilComplex.cohomologyδ T 0 1 rfl
        ((EZ 0).toLinearEquiv.symm x)) = y
    rw [hex]
    constructor
    · rintro ⟨x, hx⟩
      refine ⟨(EZ 0).toLinearEquiv x, ?_⟩
      rw [LinearEquiv.symm_apply_apply, hx, LinearEquiv.apply_symm_apply]
    · rintro ⟨x, hx⟩
      refine ⟨(EZ 0).toLinearEquiv.symm x, ?_⟩
      rw [← hx, LinearEquiv.symm_apply_apply]
  · intro z
    have := hZ 1 one_ne_zero
    obtain ⟨x, hx⟩ := (WeilComplex.exact_cohomologyMap T 1 hT z).1 (Subsingleton.elim _ _)
    refine ⟨(EU 1).toLinearEquiv x, ?_⟩
    change WeilComplex.cohomologyMap T.mor₁ 1 ((EU 1).toLinearEquiv.symm
      ((EU 1).toLinearEquiv x)) = z
    rw [LinearEquiv.symm_apply_apply, hx]
  · intro x
    change (EU 1).toLinearEquiv (WeilComplex.cohomologyδ T 0 1 rfl
        ((EZ 0).toLinearEquiv.symm ((B.compactlySupportedCohomology 0).frobenius x))) =
      (F.compactlySupportedCohomology 1).frobenius ((EU 1).toLinearEquiv
        (WeilComplex.cohomologyδ T 0 1 rfl ((EZ 0).toLinearEquiv.symm x)))
    erw [(EZ 0).symm_map_frobenius x, WeilComplex.cohomologyδ_frobenius, (EU 1).map_frobenius]
    rfl
  · intro x
    change WeilComplex.cohomologyMap T.mor₁ 1
        ((EU 1).toLinearEquiv.symm ((F.compactlySupportedCohomology 1).frobenius x)) =
      (A.compactlySupportedCohomology 1).frobenius
        (WeilComplex.cohomologyMap T.mor₁ 1 ((EU 1).toLinearEquiv.symm x))
    erw [(EU 1).symm_map_frobenius x, WeilComplex.cohomologyMap_frobenius]
    rfl
  · refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
    change WeilComplex.cohomologyMap T.mor₁ 0 ((EU 0).toLinearEquiv.symm x) = 0 at hx
    obtain ⟨z, hz⟩ := (WeilComplex.exact_cohomologyδ_right T (-1) 0 (by norm_num) hT _).1 hx
    have := hZ (-1) (by norm_num)
    rw [Subsingleton.elim z 0, map_zero] at hz
    have := congrArg (EU 0).toLinearEquiv hz
    rwa [LinearEquiv.apply_symm_apply, map_zero, eq_comm] at this
  · intro x
    change WeilComplex.cohomologyMap T.mor₁ 0
        ((EU 0).toLinearEquiv.symm ((F.compactlySupportedCohomology 0).frobenius x)) =
      (A.compactlySupportedCohomology 0).frobenius
        (WeilComplex.cohomologyMap T.mor₁ 0 ((EU 0).toLinearEquiv.symm x))
    erw [(EU 0).symm_map_frobenius x, WeilComplex.cohomologyMap_frobenius]
    rfl

end AlgebraicGeometry
