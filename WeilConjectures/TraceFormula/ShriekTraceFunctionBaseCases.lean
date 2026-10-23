/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.AlgebraicGeometry.PolynomialAffineSpace
public import WeilConjectures.TraceFormula.GenericQuotient
public import WeilConjectures.TraceFormula.ShriekTraceFunctionInduction

/-!

# The base cases of the sheaf–function compatibility of the Weil lower shriek

By Noetherian induction (`ProEtale.CondensedRing.weilShriekTraceFunction_of_genericallyHolds`),
the sheaf–function compatibility `ProEtale.CondensedRing.ShriekTraceFunctionAt` of the Weil lower
shriek holds along every morphism as soon as it holds generically
(`ProEtale.CondensedRing.ShriekTraceFunctionGenericallyHolds`). This file reduces the generic
statement to three base cases, stated as separate inputs:

- **dimension zero** (`ProEtale.CondensedRing.shriekTraceFunctionAt_of_isFinite_of_etale`): `f`
  finite étale. Then `Rf_! = f_*` and the stalk of `f_* K` at `ȳ` is `⊕_{x̄ ↦ ȳ} K_x̄`, on which
  the Frobenius permutes the summands; only the summands at points of degree `n + 1` contribute
  to the trace;
- **curves** (`ProEtale.CondensedRing.shriekTraceFunctionAt_of_smoothOfRelativeDimension_one`):
  `f` smooth of relative dimension one. By compactly supported base change to `ȳ` this is the
  trace formula for a smooth curve over a finite field, deduced from the Lefschetz–Verdier
  formula of the model-Frobenius setting (`WeilConjectures.TraceFormula.LefschetzVerdier`) and
  the vanishing of the local terms of the Frobenius graph away from its fixed points
  (`WeilConjectures.TraceFormula.LocalTermLocality`);
- **closed immersions**
  (`ProEtale.CondensedRing.shriekTraceFunctionAt_of_isClosedImmersion`): `Ri_! = i_*`, whose
  stalk at `ȳ` is `K_ȳ` if `ȳ` lies on the closed subscheme and `0` otherwise.

The closed-immersion case cannot be avoided: every morphism built from finite étale morphisms
and smooth morphisms of relative dimension one by composition (`shriekTraceFunctionAt_comp`)
and open–closed dévissage of the source (`shriekTraceFunctionAt_of_isCompl`) satisfies
`dim 𝒪_{X,x} ≥ dim 𝒪_{Y,f(x)}`, which fails for a closed point of the affine line.

## The reduction

The reduction (`ProEtale.CondensedRing.shriekTraceFunctionGenericallyHolds_of_baseCases`) goes
through the generic quotient of `X` by its automorphism `e_X` of finite order
(`AlgebraicGeometry.exists_isFinite_etale_of_powSucc_eq_refl`): there are a nonempty
`e_X`-stable open `U ⊆ X`, its reduction `Z`, and a finite étale morphism `π : Z ⟶ V` to an
affine scheme `V`, invariant under `e_Z`. The compatibility along `U ⟶ Y` follows from the one
along `Z ⟶ Y` by dévissage (`U = ∅ ⊔ Z`), and `Z ⟶ Y` factors as the chain
```
Z ⟶ Z ×_k E ⟶ V ×_k E ⟶ 𝔸ᴺ_k ×_k E ⟶ 𝔸ᴺ⁻¹_k ×_k E ⟶ ⋯ ⟶ 𝔸⁰_k ×_k E ⟶ E ⟶ Y
```
of the graph of `Z ⟶ E` (a closed immersion), `π ×_k E` (finite étale), a closed embedding of
`V` into `𝔸ᴺ_k`, the coordinate projections (smooth of relative dimension one), an isomorphism,
and the closed immersion of the fixed locus `E` of `e_Y^{m+1}`, through which `Z ⟶ Y` factors.
The automorphisms of the intermediate schemes are the products of `e_Z`, the identity and `e_E`;
they have finite order, so that `shriekTraceFunctionAt_comp` composes the base cases.

## Sorried inputs

- `ProEtale.CondensedRing.shriekTraceFunctionAt_of_isFinite_of_etale`;
- `ProEtale.CondensedRing.shriekTraceFunctionAt_of_smoothOfRelativeDimension_one`;
- `ProEtale.CondensedRing.shriekTraceFunctionAt_of_isClosedImmersion`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### The empty scheme -/

section Empty

variable {k : Type u} [Field k]

/-- The empty scheme over `Spec k`. -/
noncomputable def emptyOver : Over (Spec (.of k)) := Over.mk (Scheme.emptyTo _)

instance : IsEmpty (emptyOver (k := k)).left := inferInstanceAs (IsEmpty (∅ : Scheme))

instance : LocallyOfFiniteType (emptyOver (k := k)).hom :=
  inferInstanceAs (LocallyOfFiniteType (Scheme.emptyTo _))

instance : QuasiCompact (emptyOver (k := k)).hom :=
  inferInstanceAs (QuasiCompact (Scheme.emptyTo _))

instance : IsSeparated (emptyOver (k := k)).hom :=
  inferInstanceAs (IsSeparated (Scheme.emptyTo _))

/-- The morphism from the empty scheme. -/
noncomputable def emptyOverTo (X : Over (Spec (.of k))) : emptyOver ⟶ X :=
  Over.homMk (Scheme.emptyTo _) (Scheme.empty_ext _ _)

instance (X : Over (Spec (.of k))) : IsOpenImmersion (emptyOverTo X).left :=
  inferInstanceAs (IsOpenImmersion (Scheme.emptyTo _))

lemma emptyOverTo_ext {X : Over (Spec (.of k))} (f g : emptyOver ⟶ X) : f = g :=
  Over.OverMorphism.ext (Scheme.empty_ext _ _)

end Empty

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [Finite k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-! ### The base cases -/

/-- The sheaf–function compatibility holds along every finite étale morphism `f` (for `e_X` of
finite order). -/
def ShriekTraceFunctionFiniteEtale : Prop :=
  ∀ (X Y : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (eX : X ≅ X) (eY : Y ≅ Y) (f : X ⟶ Y) (hf : eX.hom ≫ f = f ≫ eY.hom),
    [IsFinite f.left] → [Etale f.left] → (∃ m : ℕ, eX.powSucc m = Iso.refl X) →
    ShriekTraceFunctionAt ℓ eX eY hf

/-- The sheaf–function compatibility holds along every morphism `f` smooth of relative dimension
one (for `e_X` of finite order). -/
def ShriekTraceFunctionCurve : Prop :=
  ∀ (X Y : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (eX : X ≅ X) (eY : Y ≅ Y) (f : X ⟶ Y) (hf : eX.hom ≫ f = f ≫ eY.hom),
    [SmoothOfRelativeDimension 1 f.left] → (∃ m : ℕ, eX.powSucc m = Iso.refl X) →
    ShriekTraceFunctionAt ℓ eX eY hf

/-- The sheaf–function compatibility holds along every closed immersion `f` (for `e_X` of finite
order). -/
def ShriekTraceFunctionClosedImmersion : Prop :=
  ∀ (X Y : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (eX : X ≅ X) (eY : Y ≅ Y) (f : X ⟶ Y) (hf : eX.hom ≫ f = f ≫ eY.hom),
    [IsClosedImmersion f.left] → (∃ m : ℕ, eX.powSucc m = Iso.refl X) →
    ShriekTraceFunctionAt ℓ eX eY hf

/-- **Dimension zero** (still `sorry`): the sheaf–function compatibility holds along a finite
étale morphism `f`. The stalk of `Rf_! K = f_* K` at `ȳ` is the sum of the stalks `K_x̄` over
the geometric points `x̄ ↦ ȳ`, permuted by the Frobenius; the trace only sees the summands at
the points fixed by the Frobenius, which are the points of degree `n + 1`. -/
theorem shriekTraceFunctionAt_of_isFinite_of_etale {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (eX : X ≅ X) (eY : Y ≅ Y) {f : X ⟶ Y} (hf : eX.hom ≫ f = f ≫ eY.hom)
    [IsFinite f.left] [Etale f.left] (he : ∃ m : ℕ, eX.powSucc m = Iso.refl X) :
    ShriekTraceFunctionAt ℓ eX eY hf :=
  sorry

/-- **Curves** (still `sorry`): the sheaf–function compatibility holds along a smooth morphism
`f` of relative dimension one. By compactly supported base change to `ȳ`, it is the trace
formula for the smooth curve `X_ȳ` over a finite field, which follows from the Lefschetz–Verdier
formula for the Frobenius graph on a compactification and the vanishing of the local terms
away from the fixed points (blueprint `thm-trf-grothendieck-lefschetz-finite-ring`, the case of
curves). -/
theorem shriekTraceFunctionAt_of_smoothOfRelativeDimension_one {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (eX : X ≅ X) (eY : Y ≅ Y) {f : X ⟶ Y} (hf : eX.hom ≫ f = f ≫ eY.hom)
    [SmoothOfRelativeDimension 1 f.left] (he : ∃ m : ℕ, eX.powSucc m = Iso.refl X) :
    ShriekTraceFunctionAt ℓ eX eY hf :=
  sorry

/-- **Closed immersions** (still `sorry`): the sheaf–function compatibility holds along a closed
immersion `i : X ⟶ Y`. For a point `ȳ` of `Y` of degree `n + 1`: if `ȳ = x̄ ≫ i`, then
`t(Ri_! K; ȳ) = t(Li^* Ri_! K; x̄) = t(K; x̄)` by the stalks of pullbacks
(`ProEtale.CondensedRing.weilStalkSupertrace_weilUpperStar`) and the isomorphism
`Li^* Ri_! K ≅ K` of Weil objects, the compactly supported base change along the cartesian square
`(𝟙, 𝟙, i, i)` (`i` is a monomorphism); otherwise `ȳ` lies on the open complement `V`, and
`Lj^* Ri_! K = 0` by base change along the empty square `V ×_Y X = ∅`. -/
theorem shriekTraceFunctionAt_of_isClosedImmersion {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (eX : X ≅ X) (eY : Y ≅ Y) {f : X ⟶ Y} (hf : eX.hom ≫ f = f ≫ eY.hom)
    [IsClosedImmersion f.left] (he : ∃ m : ℕ, eX.powSucc m = Iso.refl X) :
    ShriekTraceFunctionAt ℓ eX eY hf :=
  sorry

variable {ℓ k}

/-! ### The chain -/

section Chain

variable (H₀ : ShriekTraceFunctionFiniteEtale ℓ k) (H₁ : ShriekTraceFunctionCurve ℓ k)
  (H₂ : ShriekTraceFunctionClosedImmersion ℓ k)

section Projections

variable {E Y : Over (Spec (.of k))} [LocallyOfFiniteType E.hom] [QuasiCompact E.hom]
  [IsSeparated E.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {eE : E ≅ E} {eY : Y ≅ Y} {m : ℕ} (heE : eE.powSucc m = Iso.refl E) {ι : E ⟶ Y}
  (hι : eE.hom ≫ ι = ι ≫ eY.hom)

include H₀ H₁ heE in
/-- The compatibility along the projection `𝔸ʲ_k ×_k E ⟶ E` followed by `ι : E ⟶ Y`, from the
one along `ι`: the projection is the composite of the coordinate projections, smooth of relative
dimension one, and of the isomorphism `𝔸⁰_k ×_k E ≅ E`. -/
lemma shriekTraceFunctionAt_overProdSnd_polyAffine
    (Hι : ShriekTraceFunctionAt ℓ eE eY hι) (j : ℕ) :
    ShriekTraceFunctionAt ℓ (overProdIso (Iso.refl (polyAffine k j)) eE) eY
      (comp_comm_of_comp_comm _ eY eE (by simp) hι :
        (overProdIso (Iso.refl (polyAffine k j)) eE).hom ≫ overProdSnd _ E ≫ ι =
          (overProdSnd _ E ≫ ι) ≫ eY.hom) := by
  have hfin : ∀ j, ((overProdIso (Iso.refl (polyAffine k j)) eE).powSucc m) = Iso.refl _ :=
    fun j ↦ by rw [overProdIso_powSucc, heE, Iso.powSucc_refl, overProdIso_refl]
  induction j with
  | zero =>
    exact shriekTraceFunctionAt_comp ℓ _ eY eE (by simp) hι ⟨m, hfin 0⟩ ⟨m, heE⟩
      (H₀ _ _ _ _ _ _ ⟨m, hfin 0⟩) Hι
  | succ j ih =>
    have hp : (overProdIso (Iso.refl (polyAffine k (j + 1))) eE).hom ≫
        overProdMap (polyAffineProj k j) (𝟙 E) =
          overProdMap (polyAffineProj k j) (𝟙 E) ≫
            (overProdIso (Iso.refl (polyAffine k j)) eE).hom := by
      simp only [overProdIso_hom, Iso.refl_hom, ← overProdMap_comp, Category.id_comp,
        Category.comp_id]
    refine ShriekTraceFunctionAt.of_eq ℓ (by simp)
      (shriekTraceFunctionAt_comp ℓ _ eY _ hp _ ⟨m, hfin (j + 1)⟩ ⟨m, hfin j⟩
        (H₁ _ _ _ _ _ hp ⟨m, hfin (j + 1)⟩) ih)

end Projections

include H₀ H₁ H₂ in
/-- The chain `Z ⟶ Z ×_k E ⟶ V ×_k E ⟶ 𝔸ᴺ_k ×_k E ⟶ E ⟶ Y`, for a factorization of `g` through
a closed immersion `ι : E ⟶ Y` with an automorphism `e_E` of finite order and a finite étale
morphism `π : Z ⟶ V` to an affine scheme with `e_Z ≫ π = π`. -/
lemma shriekTraceFunctionAt_of_isFinite_of_etale_of_comp_eq_aux
    {Z Y V E : Over (Spec (.of k))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    [IsSeparated Z.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [IsAffine V.left] [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    [LocallyOfFiniteType E.hom] [QuasiCompact E.hom] [IsSeparated E.hom]
    (eZ : Z ≅ Z) (eY : Y ≅ Y) (eE : E ≅ E) {g : Z ⟶ Y} (hg : eZ.hom ≫ g = g ≫ eY.hom) {m : ℕ}
    (heZ : eZ.powSucc m = Iso.refl Z) (heE : eE.powSucc m = Iso.refl E) (π : Z ⟶ V)
    [IsFinite π.left] [Etale π.left] (hπ : eZ.hom ≫ π = π) (ι : E ⟶ Y)
    [IsClosedImmersion ι.left] (hι : eE.hom ≫ ι = ι ≫ eY.hom) (gE : Z ⟶ E)
    (hgE : eZ.hom ≫ gE = gE ≫ eE.hom) (hgE' : gE ≫ ι = g) :
    ShriekTraceFunctionAt ℓ eZ eY hg := by
  -- a closed embedding of `V` into an affine space
  obtain ⟨N, ιV, _⟩ := exists_isClosedImmersion_polyAffine V
  have hfin : ∀ {W : Over (Spec (.of k))} (eW : W ≅ W), eW.powSucc m = Iso.refl W →
      (overProdIso eW eE).powSucc m = Iso.refl _ :=
    fun eW h ↦ by rw [overProdIso_powSucc, h, heE, overProdIso_refl]
  have hfinV := hfin (Iso.refl V) (Iso.powSucc_refl _)
  have hfinN := hfin (Iso.refl (polyAffine k N)) (Iso.powSucc_refl _)
  have hfinZ := hfin eZ heZ
  -- the compatibility along `E ⟶ Y` and along `𝔸ᴺ_k ×_k E ⟶ E ⟶ Y`
  have HN := shriekTraceFunctionAt_overProdSnd_polyAffine H₀ H₁ heE hι
    (H₂ _ _ _ _ _ hι ⟨m, heE⟩) N
  -- `V ×_k E ⟶ 𝔸ᴺ_k ×_k E`
  have h₃ : (overProdIso (Iso.refl V) eE).hom ≫ overProdMap ιV (𝟙 E) =
      overProdMap ιV (𝟙 E) ≫ (overProdIso (Iso.refl (polyAffine k N)) eE).hom := by
    simp only [overProdIso_hom, Iso.refl_hom, ← overProdMap_comp, Category.id_comp,
      Category.comp_id]
  have H₃ := shriekTraceFunctionAt_comp ℓ _ eY _ h₃ _ ⟨m, hfinV⟩ ⟨m, hfinN⟩
    (H₂ _ _ _ _ _ h₃ ⟨m, hfinV⟩) HN
  -- `Z ×_k E ⟶ V ×_k E`
  have h₂ : (overProdIso eZ eE).hom ≫ overProdMap π (𝟙 E) =
      overProdMap π (𝟙 E) ≫ (overProdIso (Iso.refl V) eE).hom := by
    simp only [overProdIso_hom, Iso.refl_hom, ← overProdMap_comp, Category.id_comp,
      Category.comp_id, hπ]
  have H₂' := shriekTraceFunctionAt_comp ℓ _ eY _ h₂ _ ⟨m, hfinZ⟩ ⟨m, hfinV⟩
    (H₀ _ _ _ _ _ h₂ ⟨m, hfinZ⟩) H₃
  -- the graph `Z ⟶ Z ×_k E`
  have h₁ : eZ.hom ≫ overGraph gE = overGraph gE ≫ (overProdIso eZ eE).hom :=
    (overGraph_overProdMap _ _ hgE.symm).symm
  have H₁' := shriekTraceFunctionAt_comp ℓ _ eY _ h₁ _ ⟨m, heZ⟩ ⟨m, hfinZ⟩
    (H₂ _ _ _ _ _ h₁ ⟨m, heZ⟩) H₂'
  refine ShriekTraceFunctionAt.of_eq ℓ ?_ H₁'
  simp [hgE']

include H₀ H₁ H₂ in
/-- **The chain**: the compatibility along `g : Z ⟶ Y`, if `Z` has a finite étale morphism
`π : Z ⟶ V` to an affine scheme, invariant under `e_Z` of finite order. The morphism `g` factors
through the fixed locus of `e_Y^{m+1}`. -/
theorem shriekTraceFunctionAt_of_isFinite_of_etale_of_comp_eq
    {Z Y V : Over (Spec (.of k))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    [IsSeparated Z.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [IsAffine V.left] [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    (eZ : Z ≅ Z) (eY : Y ≅ Y) {g : Z ⟶ Y} (hg : eZ.hom ≫ g = g ≫ eY.hom) {m : ℕ}
    (heZ : eZ.powSucc m = Iso.refl Z) (π : Z ⟶ V) [IsFinite π.left] [Etale π.left]
    (hπ : eZ.hom ≫ π = π) :
    ShriekTraceFunctionAt ℓ eZ eY hg := by
  have hgm : g ≫ 𝟙 Y = g ≫ (eY.powSucc m).hom := by
    rw [Category.comp_id, ← Iso.powSucc_hom_comp_eq_comp_powSucc_hom eZ eY hg m, heZ,
      Iso.refl_hom, Category.id_comp]
  have hc := (Iso.powSucc_hom_comp_eq_comp_powSucc_hom eY eY rfl m).symm
  refine shriekTraceFunctionAt_of_isFinite_of_etale_of_comp_eq_aux H₀ H₁ H₂ eZ eY
    (fixedLocusIso (eY.powSucc m).hom eY hc) hg heZ (fixedLocusIso_powSucc eY m) π hπ _
    (fixedLocusIso_hom_ι _ eY hc) (equalizer.lift g hgm) (equalizer.hom_ext ?_)
    (equalizer.lift_ι _ _)
  simp [hg]

end Chain

/-! ### The reduction -/

variable (ℓ k) in
/-- **Generic structure**: the three base cases give the sheaf–function compatibility
generically. A nonempty `X` with an automorphism `e_X` of finite order has a nonempty
`e_X`-stable open `U` whose reduction `Z` is finite étale over an affine scheme `V`, invariantly
under `e_Z` (the generic quotient by `e_X`); the compatibility along `U ⟶ Y` follows from the one
along `Z ⟶ Y` by dévissage, and `Z ⟶ Y` is a composite of base cases
(`shriekTraceFunctionAt_of_isFinite_of_etale_of_comp_eq`). -/
theorem shriekTraceFunctionGenericallyHolds_of_baseCases
    (H₀ : ShriekTraceFunctionFiniteEtale ℓ k) (H₁ : ShriekTraceFunctionCurve ℓ k)
    (H₂ : ShriekTraceFunctionClosedImmersion ℓ k) :
    ShriekTraceFunctionGenericallyHolds ℓ k := by
  intro X Y _ _ _ _ _ _ eX eY f hf ⟨m, hm⟩ hX
  obtain ⟨U, _, _, _, eU, j, _, hj, Z, _, _, _, eZ, i, _, hi, V, _, _, π, _, _, hU, hsurj, hπ⟩ :=
    exists_isFinite_etale_of_powSucc_eq_refl X eX hm
  refine ⟨U, inferInstance, inferInstance, inferInstance, eU, j, inferInstance, hj, hU, ?_⟩
  have heU : eU.powSucc m = Iso.refl U := by
    ext1
    refine Over.OverMorphism.ext ?_
    rw [← cancel_mono j.left, ← Over.comp_left,
      Iso.powSucc_hom_comp_eq_comp_powSucc_hom eU eX hj m, hm]
    simp
  have heZ : eZ.powSucc m = Iso.refl Z := by
    ext1
    refine Over.OverMorphism.ext ?_
    rw [← cancel_mono i.left, ← Over.comp_left,
      Iso.powSucc_hom_comp_eq_comp_powSucc_hom eZ eU hi m, heU]
    simp
  have h₀ : (Iso.refl emptyOver).hom ≫ emptyOverTo U = emptyOverTo U ≫ eU.hom :=
    emptyOverTo_ext _ _
  refine shriekTraceFunctionAt_of_isCompl ℓ eU eY (Iso.refl _) eZ _ h₀ hi ?_ ⟨m, heU⟩
    (shriekTraceFunctionAt_of_isEmpty ℓ _ eY _)
    (shriekTraceFunctionAt_of_isFinite_of_etale_of_comp_eq H₀ H₁ H₂ eZ eY _ heZ π hπ)
  rw [hsurj.range_eq, Set.range_eq_empty]
  exact isCompl_bot_top

variable (ℓ k) in
/-- The sheaf–function compatibility holds generically, from the three base cases. -/
theorem shriekTraceFunctionGenericallyHolds : ShriekTraceFunctionGenericallyHolds ℓ k :=
  shriekTraceFunctionGenericallyHolds_of_baseCases ℓ k
    (fun _ _ _ _ _ _ _ _ eX eY _ hf _ _ he ↦
      shriekTraceFunctionAt_of_isFinite_of_etale ℓ k eX eY hf he)
    (fun _ _ _ _ _ _ _ _ eX eY _ hf _ he ↦
      shriekTraceFunctionAt_of_smoothOfRelativeDimension_one ℓ k eX eY hf he)
    (fun _ _ _ _ _ _ _ _ eX eY _ hf _ he ↦
      shriekTraceFunctionAt_of_isClosedImmersion ℓ k eX eY hf he)

end AlgebraicGeometry.ProEtale.CondensedRing
