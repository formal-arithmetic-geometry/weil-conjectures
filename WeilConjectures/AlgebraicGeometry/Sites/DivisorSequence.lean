/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyColimit
public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import WeilConjectures.AlgebraicGeometry.Sites.PointCohomology
public import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.EdgeMap

/-!
# The divisor sequence and the generic-point injection for the Brauer group

For an integral regular noetherian scheme `X` with generic point `i : Spec k(X) ⟶ X` there is
a short exact sequence of étale sheaves

```
  0 ──▶ 𝔾ₘ ──unit──▶ i_* i^* 𝔾ₘ ──div──▶ ∐_{x ∈ X⁽¹⁾} i_{x*} ℤ ──▶ 0
```

the third map sending a rational function to its divisor. The points of `X⁽¹⁾` are the points
of coheight one, and `i_{x*} ℤ` is the pushforward of the constant sheaf `ℤ` along
`Spec κ(x) ⟶ X`. Taking the long exact cohomology sequence and using
`H¹(X, i_{x*} ℤ) = 0`, together with the vanishing of `R¹i_* 𝔾ₘ` for the Leray spectral
sequence of `i`, gives Grothendieck's residue injection

```
   Spec k(X) ──── i ────▶ X            H²(X_ét, 𝔾ₘ)
                                            │ cohomologyMap i 𝔾ₘ 2  (injective)
                                            ▼
                                       H²(Spec k(X)_ét, i^* 𝔾ₘ)
```

whose target is `H²(Spec k(X)_ét, 𝔾ₘ) = Br(k(X))` by
`AlgebraicGeometry.Scheme.isIso_upperStarGmSheafToGmSheaf_fromSpecFunctionField`.

## Main definitions

- `AlgebraicGeometry.Scheme.genericGm`: the sheaf `i_* i^* 𝔾ₘ`.
- `AlgebraicGeometry.Scheme.toGenericGm`: the unit `𝔾ₘ ⟶ i_* i^* 𝔾ₘ`, the first map of the
  divisor sequence.
- `AlgebraicGeometry.Scheme.pointConstantInt`: the sheaf `i_{x*} ℤ` of a point `x` of `X`.

## Main statements

- `AlgebraicGeometry.Scheme.isIso_upperStarGmSheafToGmSheaf_fromSpecFunctionField`: the
  pullback of `𝔾ₘ` along the generic point is `𝔾ₘ`. The proof is `sorry`.
- `AlgebraicGeometry.Scheme.mono_toGenericGm`: the unit `𝔾ₘ ⟶ i_* i^* 𝔾ₘ` is a monomorphism.
- `AlgebraicGeometry.Scheme.nonempty_cokernel_toGenericGm_iso`: its cokernel is
  `⨁_{x ∈ X⁽¹⁾} i_{x*} ℤ`. The proof is `sorry`.
- `AlgebraicGeometry.Scheme.exists_shortExact_divisorSequence`: the divisor sequence is short
  exact, from the two previous statements.
- `AlgebraicGeometry.Scheme.subsingleton_H_one_pointConstantInt`: `H¹(X, i_{x*} ℤ) = 0`.
- `AlgebraicGeometry.Scheme.epi_lowerStar_map_cokernelπ_upperStar_gmSheaf`: `R¹i_* 𝔾ₘ = 0`
  along the generic point. The proof is `sorry`.
- `AlgebraicGeometry.Scheme.injective_cohomologyMap_gmSheaf_two`: the map
  `Br(X) = H²(X, 𝔾ₘ) → H²(Spec k(X), 𝔾ₘ) = Br(k(X))` along the generic point is injective.

## TODO

The divisor map itself is not named: `exists_shortExact_divisorSequence` asserts that *some*
map `div` out of `i_* i^* 𝔾ₘ` makes the sequence short exact, rather than that the map
`f ↦ ∑_{x ∈ X⁽¹⁾} ord_x(f) [x]` built from `AlgebraicGeometry.Scheme.ord` does. The first map
is pinned down, since it is the one that Grothendieck's residue argument uses.

The third term is a colimit cocone taken as an argument rather than the coproduct
`∐ fun x ↦ X.pointConstantInt x`. The sheaf category is Grothendieck abelian, so the
coproduct does exist, but synthesising `Limits.HasCoproduct` for a family indexed by a type
in the universe of the points of `X` does not terminate in a usable time here; it should be
replaced by `∐ …` once that is fixed.

## Blueprint references

The labels quoted below are labels of the *sketch* blueprint, which lives in the separate
repository `formal-arithmetic-geometry/weil-conjectures-blueprint`, not of `blueprint/src` in
this repository.
-/

@[expose] public section

universe u

open CategoryTheory Limits Order

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) [IsIntegral X]

/-- The étale sheaf `i_* i^* 𝔾ₘ` on `X`, the pushforward along the generic point
`i : Spec k(X) ⟶ X` of the pullback of `𝔾ₘ`. It is written this way, rather than as the
pushforward of the sheaf `𝔾ₘ` of `Spec k(X)`, so that the unit
`AlgebraicGeometry.Scheme.toGenericGm` of the adjunction lands in it by construction; the
comparison of the two is `AlgebraicGeometry.Scheme.genericGmIso`. -/
noncomputable def genericGm : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (Etale.lowerStar AddCommGrpCat.{u + 1} X.fromSpecFunctionField).obj
    ((Etale.upperStar AddCommGrpCat.{u + 1} X.fromSpecFunctionField).obj X.gmSheaf)

/-- The unit `𝔾ₘ ⟶ i_* i^* 𝔾ₘ` of the adjunction
`AlgebraicGeometry.Etale.upperStarLowerStarAdjunction` at the generic point: the first map of
the divisor sequence. -/
noncomputable def toGenericGm : X.gmSheaf ⟶ X.genericGm :=
  (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} X.fromSpecFunctionField).unit.app
    X.gmSheaf

/-- The comparison map `i^* 𝔾ₘ ⟶ 𝔾ₘ` along the generic point `i : Spec k(X) ⟶ X` is an
isomorphism. The morphism `i` is not étale, but both sheaves have stalk `(k(X)ˢᵉᵖ)ˣ` at a
separable closure of `k(X)`: the strict henselisation of the local ring `𝒪_{X,η} = k(X)` is
`k(X)ˢᵉᵖ`. The proof is `sorry`. -/
theorem isIso_upperStarGmSheafToGmSheaf_fromSpecFunctionField :
    IsIso (upperStarGmSheafToGmSheaf X.fromSpecFunctionField) :=
  sorry

/-- The sheaf `i_* i^* 𝔾ₘ` is the pushforward of the sheaf `𝔾ₘ` of `Spec k(X)`, because the
pullback of `𝔾ₘ` along the generic point is `𝔾ₘ`
(`AlgebraicGeometry.Scheme.isIso_upperStarGmSheafToGmSheaf_fromSpecFunctionField`). -/
noncomputable def genericGmIso : X.genericGm ≅
    (Etale.lowerStar AddCommGrpCat.{u + 1} X.fromSpecFunctionField).obj
      (Spec X.functionField).gmSheaf :=
  haveI := X.isIso_upperStarGmSheafToGmSheaf_fromSpecFunctionField
  (Etale.lowerStar AddCommGrpCat.{u + 1} X.fromSpecFunctionField).mapIso
    (asIso (upperStarGmSheafToGmSheaf X.fromSpecFunctionField))

/-- The étale sheaf `i_{x*} ℤ` on `X`: the pushforward of the constant sheaf `ℤ` along the
canonical morphism `Spec κ(x) ⟶ X` of a point `x` of `X`. -/
noncomputable def pointConstantInt (x : X) : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (Etale.lowerStar AddCommGrpCat.{u + 1} (X.fromSpecResidueField x)).obj
    ((constantSheaf _ AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))

/-- The first map of the divisor sequence is injective: `𝔾ₘ ⟶ i_* 𝔾ₘ` along the generic point
`i : Spec k(X) ⟶ X` is a monomorphism. On an étale `X`-scheme `U` it is the map on units
`Γ(U, 𝒪)ˣ ⟶ Γ(U ×_X Spec k(X), 𝒪)ˣ` induced by restriction to the generic fibre, which is
injective because `U` is flat over the integral scheme `X`
(`AlgebraicGeometry.Scheme.injective_Γ_map_pullback_fst_fromSpecFunctionField`).
This is the injectivity `A^× ⟶ (S⁻¹A)^×` in the proof of `lem-sc-divisor-sequence-general`,
proved on sections rather than on stalks. -/
theorem mono_gmSheafToLowerStarGmSheaf_fromSpecFunctionField :
    Mono (gmSheafToLowerStarGmSheaf X.fromSpecFunctionField) := by
  refine Sheaf.Hom.mono_of_presheaf_mono _ _ _ (h := ?_)
  suffices ∀ V, Mono ((gmSheafToLowerStarGmSheaf X.fromSpecFunctionField).hom.app V) from
    NatTrans.mono_of_mono_app _
  intro V
  rw [AddCommGrpCat.mono_iff_injective]
  intro a b h
  have hinj := X.injective_Γ_map_pullback_fst_fromSpecFunctionField V.unop.hom
  exact ULift.ext _ _ (Units.ext (hinj (congrArg (fun x ↦ (Additive.toMul x.down).val) h)))

/-- **The unit `𝔾ₘ ⟶ i_* i^* 𝔾ₘ` is a monomorphism**, the left exactness of the divisor
sequence. Composed with `i_*` of the comparison map `i^* 𝔾ₘ ⟶ 𝔾ₘ` it is the restriction map
`𝔾ₘ ⟶ i_* 𝔾ₘ` to the generic fibre, which is a monomorphism by
`AlgebraicGeometry.Scheme.mono_gmSheafToLowerStarGmSheaf_fromSpecFunctionField`.
(blueprint: `lem-sc-divisor-sequence-general`, injectivity) -/
theorem mono_toGenericGm : Mono X.toGenericGm := by
  have h := X.mono_gmSheafToLowerStarGmSheaf_fromSpecFunctionField
  have e : X.toGenericGm ≫ (Etale.lowerStar _ _).map
      (upperStarGmSheafToGmSheaf X.fromSpecFunctionField) =
      gmSheafToLowerStarGmSheaf X.fromSpecFunctionField := by
    simp [toGenericGm, upperStarGmSheafToGmSheaf, Adjunction.homEquiv_counit]
  rw [← e] at h
  exact mono_of_mono _ ((Etale.lowerStar _ _).map (upperStarGmSheafToGmSheaf _))

/-- **The cokernel of `𝔾ₘ ⟶ i_* i^* 𝔾ₘ` is the sheaf of Weil divisors.** Let `X` be an
integral regular locally noetherian scheme with generic point `i : Spec k(X) ⟶ X`. Then the
cokernel of the unit `𝔾ₘ ⟶ i_* i^* 𝔾ₘ` is isomorphic to `⨁_{x ∈ X⁽¹⁾} i_{x*} ℤ`, the vertex
of any colimit cocone `c` on the family `x ↦ i_{x*} ℤ`; the isomorphism is induced by the
divisor map `f ↦ ∑_x ord_x(f) [x]`. This is exactness in the middle and on the right of the
divisor sequence.

On the stalk at a geometric point over `x`, with `A = 𝒪^{sh}_{X,x̄}` and `S = 𝒪_{X,x} ∖ {0}`,
the claim is that `(S⁻¹A)^× / A^× ⟶ ⨁_𝔮 ℤ`, over the height-one primes `𝔮` of `A` meeting
`S`, is bijective. Injectivity is algebraic Hartogs for the noetherian normal domain `A`,
surjectivity uses that the regular local ring `A` is a UFD (Auslander–Buchsbaum). The proof is
`sorry`: it needs the stalks of étale sheaves at geometric points as strict henselisations,
regularity of strict henselisations and the factoriality of regular local rings, none of
which is available.
(blueprint: `lem-sc-divisor-sequence-general`, exactness in the middle and surjectivity) -/
theorem nonempty_cokernel_toGenericGm_iso [IsLocallyNoetherian X] [IsRegular X]
    (c : Cofan fun x : {x : X // coheight x = 1} ↦ X.pointConstantInt x.1) (hc : IsColimit c) :
    Nonempty (cokernel X.toGenericGm ≅ c.pt) :=
  sorry

/-- **The divisor sequence.** Let `X` be an integral regular locally noetherian scheme with
generic point `i : Spec k(X) ⟶ X`, and let `X⁽¹⁾` be its set of coheight-one points. Then
there is a divisor map `div` making

```
  0 ──▶ 𝔾ₘ ──unit──▶ i_* i^* 𝔾ₘ ──div──▶ ∐_{x ∈ X⁽¹⁾} i_{x*} ℤ ──▶ 0
```

a short exact sequence of étale sheaves on `X`, where the third term is the vertex of any
colimit cocone `c` on the family `x ↦ i_{x*} ℤ`. The first map is pinned down as the unit
`AlgebraicGeometry.Scheme.toGenericGm`, which is the form the residue argument of
`AlgebraicGeometry.Scheme.injective_cohomologyMap_gmSheaf_two` uses; `div` itself is only
asserted to exist, see the TODO in the module docstring. The unit is a monomorphism by
`AlgebraicGeometry.Scheme.mono_toGenericGm`, and its cokernel is `c.pt` by
`AlgebraicGeometry.Scheme.nonempty_cokernel_toGenericGm_iso`.
(blueprint: `lem-sc-divisor-sequence-general`) -/
theorem exists_shortExact_divisorSequence [IsLocallyNoetherian X] [IsRegular X]
    (c : Cofan fun x : {x : X // coheight x = 1} ↦ X.pointConstantInt x.1) (hc : IsColimit c) :
    ∃ (d : X.genericGm ⟶ c.pt) (w : X.toGenericGm ≫ d = 0),
      (ShortComplex.mk X.toGenericGm d w).ShortExact := by
  have := X.mono_toGenericGm
  obtain ⟨e⟩ := X.nonempty_cokernel_toGenericGm_iso c hc
  refine ⟨cokernel.π _ ≫ e.hom, by simp, { mono_f := this, epi_g := epi_comp _ _, exact := ?_ }⟩
  exact ShortComplex.exact_of_g_is_cokernel _
    (IsColimit.ofIsoColimit (cokernelIsCokernel _) (Cofork.ext e (by simp)))

omit [IsIntegral X] in
/-- **`H¹` of a point sheaf vanishes.** For a point `x` of `X`, `H¹(X, i_{x*} ℤ) = 0`: the edge
map of the Leray spectral sequence of `i_x : Spec κ(x) ⟶ X` embeds `H¹(X, i_{x*} ℤ)` into
`H¹(Spec κ(x), ℤ) = Hom_cont(Gal(κ(x)ˢᵉᵖ/κ(x)), ℤ) = 0`. This is Step 2 of the proof of
`lem-sc-brauer-injectivity`. -/
theorem subsingleton_H_one_pointConstantInt (x : X) :
    Subsingleton (Sheaf.H (X.pointConstantInt x) 1) := by
  have h := Etale.injective_edgeMap_one (X.fromSpecResidueField x)
    ((constantSheaf _ AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift ℤ)))
  have := subsingleton_H_one_constantSheaf_of_isField (X.residueField x) (Field.toIsField _)
  exact ⟨fun a b ↦ h (this.elim _ _)⟩

/-- **`R¹i_* 𝔾ₘ = 0` along the generic point.** Let `X` be an integral regular noetherian
scheme with generic point `i : Spec k(X) ⟶ X`. Then the first higher direct image
`R¹i_*(i^* 𝔾ₘ)` vanishes; here this is phrased as: for every monomorphism `ι : i^* 𝔾ₘ ⟶ I` into
an injective sheaf, `i_*` maps the cokernel map of `ι` to an epimorphism (so that
`0 ⟶ i_* i^* 𝔾ₘ ⟶ i_* I ⟶ i_* (I / i^* 𝔾ₘ) ⟶ 0` is exact and `R¹i_*(i^* 𝔾ₘ)`, its obstruction,
is zero).

The stalk of `R¹i_* 𝔾_{m,η}` at a geometric point `x̄` over `x` is `H¹(Spec S⁻¹A, 𝔾ₘ)` for the
strict henselisation `A = 𝒪^{sh}_{X,x̄}` and `S = 𝒪_{X,x} ∖ {0}`, which by Hilbert 90 is
`Pic(S⁻¹A)`; this vanishes since `A` is a noetherian regular local ring, hence a UFD, and so is
its localization `S⁻¹A`. The proof is `sorry`: it needs stalks of higher direct images, Hilbert
90 for `H¹(-, 𝔾ₘ) = Pic`, and regularity of strict henselisations, none of which is available.
This is Step 3 of the proof of `lem-sc-brauer-injectivity`. -/
theorem epi_lowerStar_map_cokernelπ_upperStar_gmSheaf [IsNoetherian X] [IsRegular X]
    {I : Sheaf (Spec X.functionField).smallEtaleTopology AddCommGrpCat.{u + 1}}
    (ι : (Etale.upperStar AddCommGrpCat.{u + 1} X.fromSpecFunctionField).obj X.gmSheaf ⟶ I)
    [Mono ι] [Injective I] :
    Epi ((Etale.lowerStar AddCommGrpCat.{u + 1} X.fromSpecFunctionField).map (cokernel.π ι)) :=
  sorry

/-- **Grothendieck's residue injection for the Brauer group.** Let `X` be an integral regular
noetherian scheme with function field `k(X)`. Then the pullback along the generic point
`i : Spec k(X) ⟶ X`

```
   Spec k(X) ──── i ────▶ X            H²(X_ét, 𝔾ₘ)
                                            │ cohomologyMap i 𝔾ₘ 2
                                            ▼
                                       H²(Spec k(X)_ét, i^* 𝔾ₘ)
```

is injective, that is, `Br(X) = H²(X, 𝔾ₘ) ↪ H²(Spec k(X), 𝔾ₘ) = Br(k(X))`; the target is
identified with the cohomological Brauer group of `k(X)` by
`AlgebraicGeometry.Scheme.isIso_upperStarGmSheafToGmSheaf_fromSpecFunctionField`. In particular
this holds for a smooth curve.

The map factors as `H²(X, 𝔾ₘ) ⟶ H²(X, i_* i^* 𝔾ₘ) ⟶ H²(Spec k(X), i^* 𝔾ₘ)`, the unit of
`i^* ⊣ i_*` followed by the edge map of the Leray spectral sequence of `i`. The first map is
injective by the long exact cohomology sequence of the divisor sequence, since
`H¹(X, ⨁_x i_{x*} ℤ) = 0`; the second is injective since `R¹i_*(i^* 𝔾ₘ) = 0`.
(blueprint: `lem-sc-brauer-injectivity`) -/
theorem injective_cohomologyMap_gmSheaf_two [IsNoetherian X] [IsRegular X] :
    Function.Injective (Etale.cohomologyMap X.fromSpecFunctionField X.gmSheaf 2) := by
  have : HasColimitsOfSize.{u + 1, u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    IsGrothendieckAbelian.hasColimits _
  have : HasColimitsOfSize.{u, u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    hasColimitsOfSizeShrink.{u, u, u + 1, u + 1} _
  let P := fun x : {x : X // coheight x = 1} ↦ X.pointConstantInt x.1
  obtain ⟨d, w, hS⟩ := X.exists_shortExact_divisorSequence (colimit.cocone (Discrete.functor P))
    (colimit.isColimit _)
  -- Step 2: the unit `𝔾ₘ ⟶ i_* i^* 𝔾ₘ` is injective on `H²`, as `H¹(X, ⨁_x i_{x*} ℤ) = 0`
  have h₃ : Subsingleton (Sheaf.H (colimit.cocone (Discrete.functor P)).pt 1) :=
    subsingleton_H_of_isColimit_cofan X (colimit.isColimit _) 1
      fun x ↦ X.subsingleton_H_one_pointConstantInt x.1
  have hα : Function.Injective (Sheaf.H.map X.toGenericGm 2) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    rw [Sheaf.H.map_apply] at ha
    obtain ⟨b, rfl⟩ := Abelian.Ext.covariant_sequence_exact₁ _ hS a ha (n₀ := 1) rfl
    rw [Subsingleton.elim b 0, Abelian.Ext.zero_comp]
  -- Step 3: the edge map `H²(X, i_* i^* 𝔾ₘ) ⟶ H²(Spec k(X), i^* 𝔾ₘ)` is injective
  let ι := Injective.ι ((Etale.upperStar AddCommGrpCat.{u + 1} X.fromSpecFunctionField).obj
    X.gmSheaf)
  have hβ := Etale.injective_edgeMap_two X.fromSpecFunctionField ι
    (X.epi_lowerStar_map_cokernelπ_upperStar_gmSheaf ι)
  intro a b h
  rw [Etale.cohomologyMap_eq_map_counit_comp, Etale.cohomologyMap_eq_map_counit_comp _ _ _ b] at h
  exact hα (hβ h)

end AlgebraicGeometry.Scheme
