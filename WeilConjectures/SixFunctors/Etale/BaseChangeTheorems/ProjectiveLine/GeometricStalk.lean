/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.FieldExtension
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Coefficients
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.StrictHenselizationStalk
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Curve
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilConjectures.Mathlib.Topology.KrullDimension
public import Mathlib.RingTheory.KrullDimension.Polynomial

/-!
# The exchange morphism of the projective line at a geometric point

Let `p : ℙ¹_S ⟶ S` be the projective line and

```
X' --g'--> ℙ¹_S
|            |
f'           p
v            v
T ----g----> S
```

a cartesian square. This file proves that the degree-`q` exchange morphism
`g⁻¹ Rᵠp_* F ⟶ Rᵠf'_* g'⁻¹ F` is an isomorphism for every torsion sheaf `F`, and identifies its
stalk at a geometric point `t̄` of `T` with the pullback map
`Hᵠ(ℙ¹_{κ(s̄)}, F|) ⟶ Hᵠ(ℙ¹_{κ(t̄)}, F|)` between the cohomologies of two projective lines over
separably closed fields.

The geometric input is the computation of the stalks of the higher direct images
(`AlgebraicGeometry.Etale.nonempty_addEquiv_sheafFiber_higherDirectImage_projectiveLine`): for a
geometric point `t̄ : Spec Ω ⟶ T`,
`(Rᵠf'_* g'⁻¹ F)_{t̄} ≅ Hᵠ(ℙ¹_Ω, F|)`. Indeed, by the strict henselisation stalk formula the
stalk is the cohomology of `ℙ¹` over the strict henselisation `𝒪ˢʰ_{T,t̄}`; by the strictly
henselian comparison this is the cohomology of the closed fibre `ℙ¹_κ`, `κ` the separably
closed residue field of `𝒪ˢʰ_{T,t̄}`; and the cohomology of a proper curve does not change
under the extension `κ ⊆ Ω` of separably closed fields.

Applied to an injective torsion sheaf `I` on `ℙ¹_S`, the case `T = S` shows that
`Hᵠ(ℙ¹_Ω, I|) = 0` for `q > 0` and every geometric point `Spec Ω ⟶ S`, since `Rᵠp_* I = 0`. So
all geometric stalks of `Rᵠf'_* g'⁻¹ I` vanish, which is the injective acyclicity of `p`
(`AlgebraicGeometry.Etale.hasInjectiveAcyclicity_projectiveLine`). By the change of
coefficients of `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Coefficients`, injective
acyclicity with all coefficient rings `Λ ⧸ rΛ` gives the base change property, and hence that
the exchange morphism is an isomorphism
(`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_projectiveLine`).

## Main statements

- `AlgebraicGeometry.Etale.nonempty_addEquiv_sheafFiber_higherDirectImage_projectiveLine`: the
  geometric stalks of the higher direct images of a base change of `ℙ¹`.
- `AlgebraicGeometry.Etale.hasInjectiveAcyclicity_projectiveLine`: the projection
  `ℙ¹_S ⟶ S` has injective acyclicity.
- `AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_projectiveLine`: the degree-`q`
  exchange morphism of `ℙ¹` is an isomorphism on torsion sheaves.
- `AlgebraicGeometry.Etale.exists_addEquiv_sheafFiber_baseChangeHomologyMap_projectiveLine`:
  the stalk of the exchange morphism of `ℙ¹` at a geometric point is the pullback map between
  the cohomologies of two projective lines over separably closed fields.

## References

- Stacks Project, proof of Theorem 59.91.11, <https://stacks.math.columbia.edu/tag/095T>
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

section Auxiliary

/-! ### Auxiliary constructions -/

/-- For `c = a ≫ b`, the isomorphism `a^*(b^* F) ≅ c^* F` of the underlying abelian sheaves of
the pullbacks of a sheaf `F` of `Λ`-modules, where the outer pullback `a^*` is taken on abelian
sheaves. -/
noncomputable def Etale.upperStarForget₂CompIso {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z)
    (c : X ⟶ Z) (h : c = a ≫ b) (F : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (a)^*[AddCommGrpCat.{u + 1}].obj ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ)
      AddCommGrpCat.{u + 1})).obj ((b)^*[ModuleCat.{u + 1} Λ].obj F)) ≅
      (sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        ((c)^*[ModuleCat.{u + 1} Λ].obj F) :=
  asIso (upperStarForget₂Comparison Λ a _) ≪≫
    (sheafCompose _ _).mapIso ((Etale.upperStarComp _ a b c h).app F).symm

/-- The additive isomorphism `Hⁿ(Z, G) ≃+ Hⁿ(Z, G')` induced by an isomorphism `G ≅ G'` of
abelian étale sheaves. -/
noncomputable def Etale.sheafHAddEquiv {Z : Scheme.{u}}
    {G G' : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}} (e : G ≅ G') (n : ℕ) :
    Sheaf.H G n ≃+ Sheaf.H G' n :=
  AddEquiv.ofBijective (Sheaf.H.map e.hom n) (bijective_sheafHMap_hom e n)

end Auxiliary

/-- **Geometric stalks of the higher direct images of `ℙ¹`.** Let

```
X' --g'--> ℙ¹_S
|            |
f'           p
v            v
T ----g----> S
```

be cartesian, `τ : Spec Ω ⟶ T` a geometric point (`Ω` separably closed), `F` a torsion sheaf of
`Λ`-modules on `ℙ¹_S` and `q ≥ 0`. Then the stalk `(Rᵠf'_* g'⁻¹ F)_τ` is isomorphic to
`Hᵠ(ℙ¹_Ω, F|)`, the cohomology of the pullback of `F` along `ℙ¹_Ω ⟶ ℙ¹_S`.

By the strict henselisation stalk formula
(`AlgebraicGeometry.Etale.nonempty_addEquiv_sheafFiber_higherDirectImage`) the stalk is
`Hᵠ(ℙ¹_A, F|)`, `A = 𝒪ˢʰ_{T,τ}`; by the strictly henselian comparison
(`AlgebraicGeometry.Etale.bijective_cohomologyMap_projectiveLine_residueField`) this is the
cohomology of the closed fibre `ℙ¹_κ`, `κ` the residue field of `A`; and since `τ` factors
through `Spec Ω ⟶ Spec κ` with `κ` separably closed, the invariance of the cohomology of
proper curves (`AlgebraicGeometry.IsCurve.bijective_cohomologyMap_of_isSepClosed`) identifies
it with `Hᵠ(ℙ¹_Ω, F|)`. -/
theorem Etale.nonempty_addEquiv_sheafFiber_higherDirectImage_projectiveLine
    {S T X' : Scheme.{u}} {g : T ⟶ S} {f' : X' ⟶ T} {g' : X' ⟶ ProjectiveLine S}
    (sq : IsPullback g' f' (ProjectiveLine S ↘ S) g)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (τ : Spec (.of Ω) ⟶ T)
    (F : Sheaf (ProjectiveLine S).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsTorsionModuleSheaf F] (q : ℕ) :
    Nonempty (((pointSmallEtale τ).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj
        (Etale.higherDirectImage Λ f' q ((g')^*[ModuleCat.{u + 1} Λ].obj F)) ≃+
      Sheaf.H ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        ((ProjectiveSpace.map _ (τ ≫ g))^*[ModuleCat.{u + 1} Λ].obj F)) q) := by
  have : QuasiCompact f' := MorphismProperty.of_isPullback sq inferInstance
  have : QuasiSeparated f' := MorphismProperty.of_isPullback sq inferInstance
  let A := strictHenselization τ
  let b := strictLocalizationToBase τ
  let a : ProjectiveLine (strictLocalization τ) ⟶ X' :=
    sq.lift (ProjectiveSpace.map _ (b ≫ g))
      (ProjectiveLine (strictLocalization τ) ↘ strictLocalization τ ≫ b) (by simp)
  have hsq : IsPullback a (ProjectiveLine (strictLocalization τ) ↘ strictLocalization τ) f' b :=
    IsPullback.of_right (by rw [sq.lift_fst]; exact ProjectiveSpace.isPullback_map _ _)
      (sq.lift_snd _ _ _) sq
  obtain ⟨e₀⟩ := Etale.nonempty_addEquiv_sheafFiber_higherDirectImage Λ f' τ hsq
    ((g')^*[ModuleCat.{u + 1} Λ].obj F) q
  obtain ⟨φ, hφ⟩ := exists_residueField_hom_strictLocalization τ
  let res : Spec (.of (IsLocalRing.ResidueField A)) ⟶ Spec A :=
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))
  let ι₁ : Spec (.of Ω) ⟶ Spec (.of (IsLocalRing.ResidueField A)) :=
    Spec.map (CommRingCat.ofHom φ)
  have hι₁ : ι₁ ≫ res ≫ b = τ := by
    refine Eq.trans ?_ hφ
    rw [← Category.assoc, ← Spec.map_comp]
    rfl
  have hτg : τ ≫ g = ι₁ ≫ res ≫ b ≫ g :=
    (congrArg (· ≫ g) hι₁).symm.trans (by simp only [Category.assoc])
  let F₁ := (ProjectiveSpace.map (ULift.{u} (Fin 2)) (b ≫ g))^*[ModuleCat.{u + 1} Λ].obj F
  let F₂ := (ProjectiveSpace.map (ULift.{u} (Fin 2)) (res ≫ b ≫ g))^*[ModuleCat.{u + 1} Λ].obj F
  have hc := Etale.bijective_cohomologyMap_projectiveLine_residueField A Λ F₁ q
  have hd := IsCurve.bijective_cohomologyMap_of_isSepClosed Λ _
    (ProjectiveSpace.isPullback_map _ ι₁) F₂ q
  let i₁ := Etale.upperStarForget₂CompIso Λ a g' (ProjectiveSpace.map _ (b ≫ g))
    (sq.lift_fst _ _ _).symm F
  let i₂ := Etale.upperStarForget₂CompIso Λ (ProjectiveSpace.map _ res)
    (ProjectiveSpace.map _ (b ≫ g)) (ProjectiveSpace.map _ (res ≫ b ≫ g))
    (by rw [← ProjectiveSpace.map_comp]) F
  let i₃ := Etale.upperStarForget₂CompIso Λ (ProjectiveSpace.map _ ι₁)
    (ProjectiveSpace.map _ (res ≫ b ≫ g)) (ProjectiveSpace.map _ (τ ≫ g))
    (by rw [← ProjectiveSpace.map_comp, hτg]) F
  exact ⟨e₀.trans ((Etale.sheafHAddEquiv i₁ q).trans ((AddEquiv.ofBijective _ hc).trans
    ((Etale.sheafHAddEquiv i₂ q).trans ((AddEquiv.ofBijective _ hd).trans
      (Etale.sheafHAddEquiv i₃ q)))))⟩

/-- **Vanishing on geometric fibres for injective sheaves.** Let `I` be an injective torsion
sheaf of `Λ`-modules on `ℙ¹_S` and `σ : Spec Ω ⟶ S` a geometric point. Then
`Hᵠ(ℙ¹_Ω, I|) = 0` for `q > 0`: by
`AlgebraicGeometry.Etale.nonempty_addEquiv_sheafFiber_higherDirectImage_projectiveLine` for the
trivial base change, this group is the stalk at `σ` of `Rᵠp_* I`, which vanishes because `I`
is injective. -/
lemma Etale.subsingleton_H_projectiveLine_of_injective {S : Scheme.{u}} {Ω : Type u} [Field Ω]
    [IsSepClosed Ω] (σ : Spec (.of Ω) ⟶ S)
    (I : Sheaf (ProjectiveLine S).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsTorsionModuleSheaf I] [Injective I] (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ)
      AddCommGrpCat.{u + 1})).obj ((ProjectiveSpace.map _ σ)^*[ModuleCat.{u + 1} Λ].obj I)) q) := by
  obtain ⟨e⟩ := Etale.nonempty_addEquiv_sheafFiber_higherDirectImage_projectiveLine Λ
    (IsPullback.of_id_fst (f := ProjectiveLine S ↘ S)) σ I q
  rw [Category.comp_id] at e
  have : Injective ((𝟙 (ProjectiveLine S))^*[ModuleCat.{u + 1} Λ].obj I) :=
    Injective.of_iso ((Etale.upperStarId _ _).app I).symm inferInstance
  have hZ : IsZero (Etale.higherDirectImage Λ (ProjectiveLine S ↘ S) q
      ((𝟙 (ProjectiveLine S))^*[ModuleCat.{u + 1} Λ].obj I)) :=
    Functor.isZero_homologyFunctor_rightDerivedFunctorPlus_singleFunctor
      ((ProjectiveLine S ↘ S)_*[ModuleCat.{u + 1} Λ])
    ((𝟙 (ProjectiveLine S))^*[ModuleCat.{u + 1} Λ].obj I) (q := q) (by lia)
  have := (pointSmallEtale σ).sheafFiber_additive (A := ModuleCat.{u + 1} Λ)
  have := ModuleCat.subsingleton_of_isZero
    (((pointSmallEtale σ).sheafFiber (A := ModuleCat.{u + 1} Λ)).map_isZero hZ)
  exact e.symm.toEquiv.subsingleton

/-- **Injective acyclicity of the projective line**: for every scheme `S`, the projection
`ℙ¹_S ⟶ S` satisfies `AlgebraicGeometry.Etale.HasInjectiveAcyclicity`. For an injective
torsion sheaf `I` on `ℙ¹_S`, a cartesian square as above and `q > 0`, the stalk of
`Rᵠf'_* g'⁻¹ I` at a geometric point `τ : Spec Ω ⟶ T` is `Hᵠ(ℙ¹_Ω, I|)`
(`AlgebraicGeometry.Etale.nonempty_addEquiv_sheafFiber_higherDirectImage_projectiveLine`),
which vanishes (`AlgebraicGeometry.Etale.subsingleton_H_projectiveLine_of_injective`). As the
geometric points are conservative, `Rᵠf'_* g'⁻¹ I = 0`.
(blueprint: `prop-weil-pbc-projective-line`) -/
theorem Etale.hasInjectiveAcyclicity_projectiveLine (S : Scheme.{u}) :
    Etale.HasInjectiveAcyclicity Λ (ProjectiveLine S ↘ S) := by
  intro T X' g f' g' sq I _ _ q hq
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hq.le
  change IsZero (Etale.higherDirectImage Λ f' n ((g')^*[ModuleCat.{u + 1} Λ].obj I))
  refine (IsZero.iff_id_eq_zero _).2
    (Scheme.sheafHom_ext_of_sheafFiber_map_algClosurePoint fun t ↦ ?_)
  obtain ⟨e⟩ := Etale.nonempty_addEquiv_sheafFiber_higherDirectImage_projectiveLine Λ sq
    (T.algClosurePoint t) I n
  have := Etale.subsingleton_H_projectiveLine_of_injective Λ (T.algClosurePoint t ≫ g) I n
    (by lia)
  have := e.toEquiv.subsingleton
  ext x
  exact Subsingleton.elim _ _

/-- **The exchange morphism of `ℙ¹` is an isomorphism on torsion sheaves.** For every
cartesian square

```
X' --g'--> ℙ¹_S
|            |
f'           p
v            v
T ----g----> S
```

every torsion sheaf `F` of `Λ`-modules on `ℙ¹_S` and every `q ≥ 0`, the degree-`q` exchange
morphism `g⁻¹ Rᵠp_* F ⟶ Rᵠf'_* g'⁻¹ F` is an isomorphism. The projection `p` has injective
acyclicity for every coefficient ring
(`AlgebraicGeometry.Etale.hasInjectiveAcyclicity_projectiveLine`), so it satisfies the base
change property (`AlgebraicGeometry.Etale.hasTorsionBaseChange_of_hasInjectiveAcyclicity`),
which is applied to `F` placed in degree `0`. -/
theorem Etale.isIso_baseChangeHomologyMap_projectiveLine
    {S T X' : Scheme.{u}} {g : T ⟶ S} {f' : X' ⟶ T} {g' : X' ⟶ ProjectiveLine S}
    (sq : IsPullback g' f' (ProjectiveLine S ↘ S) g)
    (F : Sheaf (ProjectiveLine S).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsTorsionModuleSheaf F] (q : ℕ) :
    IsIso (Etale.baseChangeHomologyMap Λ sq q F) := by
  have hT : Etale.HasTorsionBaseChange Λ (ProjectiveLine S ↘ S) :=
    Etale.hasTorsionBaseChange_of_hasInjectiveAcyclicity Λ _ fun _ _ ↦
      Etale.hasInjectiveAcyclicity_projectiveLine _ S
  have := hT sq _ (Etale.DerivedCategory.Plus.moduleTorsionHomology_singleFunctor_obj Λ _ F)
  rw [← Etale.baseChange_eq_derivedBaseChangeMapPlus] at this
  exact (Etale.isIso_baseChange_app_singleFunctor_obj_iff Λ sq F).1 this q

/-- **The exchange morphism of `ℙ¹` on a geometric stalk.** Let

```
X' --g'--> ℙ¹_S
|            |
f'           p
v            v
T ----g----> S
```

be cartesian, let `F` be a torsion sheaf of `Λ`-modules on `ℙ¹_S` and `q ≥ 0`. Let
`τ : Spec k' ⟶ T` and `σ : Spec k ⟶ S` be geometric points whose fields are algebraic over
the residue fields of their images — so that `k` and `k'` are the residue fields of the strict
henselisations of `S` at `σ` and of `T` at `τ` — and let `ι : Spec k' ⟶ Spec k` be compatible
with `g`. Then the stalk at `τ` of the degree-`q` exchange morphism
`g⁻¹ Rᵠp_* F ⟶ Rᵠf'_* g'⁻¹ F` (`AlgebraicGeometry.Etale.baseChangeHomologyMap`) is, up to
isomorphisms of its source and target, the pullback map
`Hᵠ(ℙ¹_k, F|) ⟶ Hᵠ(ℙ¹_{k'}, F|)` along `ℙ¹_{k'} ⟶ ℙ¹_k`.

**Form of the statement.** The blueprint identifies the two stalks with the cohomologies of
the closed fibres through the canonical maps `ρ ∘ Φ`. This statement only asserts that
*some* isomorphisms `e₁`, `e₂` make the square commute, which is weaker: the project has no
edge map yet comparing the higher direct images `Rᵠp_*`, defined as homology in
`DerivedCategory.Plus`, with the `Ext`-groups `CategoryTheory.Sheaf.H`, so the canonical maps
cannot be stated. In this weak form the hypotheses `hσ` and `hτ` are not needed.

**Proof.** The target stalk is `Hᵠ(ℙ¹_{k'}, F|)`
(`AlgebraicGeometry.Etale.nonempty_addEquiv_sheafFiber_higherDirectImage_projectiveLine`),
which is `e₂`. The stalk map is bijective
(`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_projectiveLine`, proved independently of
this statement from the injective acyclicity of `ℙ¹`), and so is the pullback map
(`AlgebraicGeometry.IsCurve.bijective_cohomologyMap_of_isSepClosed`); `e₁` is the isomorphism
making the square commute.
(blueprint: `lemma-weil-pbc-p1-exchange-geometric-stalk`) -/
theorem Etale.exists_addEquiv_sheafFiber_baseChangeHomologyMap_projectiveLine
    {S T X' : Scheme.{u}} {g : T ⟶ S} {f' : X' ⟶ T} {g' : X' ⟶ ProjectiveLine S}
    (sq : IsPullback g' f' (ProjectiveLine S ↘ S) g)
    {k k' : Type u} [Field k] [IsSepClosed k] [Field k'] [IsSepClosed k']
    (σ : Spec (.of k) ⟶ S) (τ : Spec (.of k') ⟶ T) (ι : Spec (.of k') ⟶ Spec (.of k))
    (hι : ι ≫ σ = τ ≫ g)
    (_hσ : ∃ (s : S) (φ : S.residueField s ⟶ .of k),
      φ.hom.IsIntegral ∧ Spec.map φ ≫ S.fromSpecResidueField s = σ)
    (_hτ : ∃ (t : T) (φ : T.residueField t ⟶ .of k'),
      φ.hom.IsIntegral ∧ Spec.map φ ≫ T.fromSpecResidueField t = τ)
    (F : Sheaf (ProjectiveLine S).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsTorsionModuleSheaf F] (q : ℕ) :
    ∃ (e₁ : ((pointSmallEtale τ).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj
          ((Etale.baseChangeSourceFunctor Λ g (ProjectiveLine S ↘ S) q).obj F) ≃+
        Sheaf.H ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
          ((ProjectiveSpace.map _ σ)^*[ModuleCat.{u + 1} Λ].obj F)) q)
      (e₂ : ((pointSmallEtale τ).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj
          ((Etale.baseChangeTargetFunctor Λ g' f' q).obj F) ≃+
        Sheaf.H ((ProjectiveSpace.map _ ι)^*[AddCommGrpCat.{u + 1}].obj
          ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
            ((ProjectiveSpace.map _ σ)^*[ModuleCat.{u + 1} Λ].obj F))) q),
      ∀ x, e₂ ((((pointSmallEtale τ).sheafFiber (A := ModuleCat.{u + 1} Λ)).map
          (Etale.baseChangeHomologyMap Λ sq q F)).hom x) =
        Etale.cohomologyMap (ProjectiveSpace.map _ ι)
          ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
            ((ProjectiveSpace.map _ σ)^*[ModuleCat.{u + 1} Λ].obj F)) q (e₁ x) := by
  have := Etale.isIso_baseChangeHomologyMap_projectiveLine Λ sq F q
  have hm := (ConcreteCategory.isIso_iff_bijective
    (((pointSmallEtale τ).sheafFiber (A := ModuleCat.{u + 1} Λ)).map
      (Etale.baseChangeHomologyMap Λ sq q F))).1 inferInstance
  obtain ⟨e₀⟩ := Etale.nonempty_addEquiv_sheafFiber_higherDirectImage_projectiveLine Λ sq τ F q
  let eT : (Etale.baseChangeTargetFunctor Λ g' f' q).obj F ≅
      Etale.higherDirectImage Λ f' q ((g')^*[ModuleCat.{u + 1} Λ].obj F) :=
    (DerivedCategory.Plus.homologyFunctor _ q).mapIso
      (((f')_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus.mapIso
        ((((g')^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).app F))
  have hστ : ProjectiveSpace.map (ULift.{u} (Fin 2)) (τ ≫ g) =
      ProjectiveSpace.map _ ι ≫ ProjectiveSpace.map _ σ := by
    rw [← ProjectiveSpace.map_comp, hι]
  let e₂ := (((pointSmallEtale τ).sheafFiber (A := ModuleCat.{u + 1} Λ)).mapIso
    eT).toLinearEquiv.toAddEquiv.trans
      (e₀.trans (Etale.sheafHAddEquiv (Etale.upperStarForget₂CompIso Λ _ _ _ hστ F) q).symm)
  have hc := IsCurve.bijective_cohomologyMap_of_isSepClosed Λ _
    (ProjectiveSpace.isPullback_map _ ι) ((ProjectiveSpace.map _ σ)^*[ModuleCat.{u + 1} Λ].obj F) q
  refine ⟨(AddEquiv.ofBijective _ hm).trans (e₂.trans (AddEquiv.ofBijective _ hc).symm), e₂,
    fun x ↦ ?_⟩
  rw [AddEquiv.trans_apply, AddEquiv.trans_apply]
  exact (AddEquiv.ofBijective_apply_symm_apply _ hc).symm

end AlgebraicGeometry
