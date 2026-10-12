/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections
public import WeilConjectures.AlgebraicGeometry.Cohomology.ProperFinite
public import WeilConjectures.AlgebraicGeometry.Modules.FiniteFreeComplex

/-!
# Higher direct images are computed by finite free complexes

For a proper morphism of finite presentation and a coherent sheaf flat over the base, the higher
direct images are locally computed by bounded complexes of finite free modules
(`AlgebraicGeometry.Scheme.Modules.exists_isFiniteFreeComplex_higherDirectImage`); in
particular they are coherent.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {X T : Scheme.{u}}
variable (f : X ⟶ T) (ℱ : X.Modules)

section Coherence

variable [IsProper f] [LocallyOfFinitePresentation f] [QuasiCompact f]
  [HasInjectiveResolutions X.Modules] [ℱ.IsFinitePresentation]

/-- **Perfectness of the higher direct images, with base change.** With `f : X ⟶ T` proper of
finite presentation and `ℱ` an `𝒪_X`-module of finite presentation which is flat over `T`, every
point `t` of `T` has an open neighbourhood `U` over which `R f_* ℱ` is represented by a bounded
complex `P` of finite free `𝒪_U`-modules whose formation commutes with every base change: for
every `g : T' ⟶ U`, with `f' : X' ⟶ T'` the base change of `f` along `g ≫ U.ι` in the cartesian
square `sq`
```
X' ------g'-------> X
|                   |
f'                  f
v                   v
T' --g--> U --U.ι--> T
```
and `ℱ'` the pullback of `ℱ` to `X'`, the cohomology of the pullback `g^* P` is `R^q f'_* ℱ'`.

Taking `g = 𝟙 U` and for `sq` the square `(isPullback_morphismRestrict f U).flip`, and
combining with `AlgebraicGeometry.Scheme.Modules.nonempty_higherDirectImage_iso_restrict`, the
cohomology of `P` itself is `R^q f_* ℱ|_U`.

The isomorphisms are only required to exist for each `g` and `q` separately: they are not
asserted to be the canonical base-change maps, nor to be compatible with composition of the
`g`. This suffices for semicontinuity of the fibre dimension and for the perfect locus, but not
for the clause of Grauert's theorem saying that the canonical maps
`R^q f_* ℱ ⊗ κ(t) → H^q(X_t, ℱ_t)` are isomorphisms; stating that needs the base-change map of
higher direct images, which is not available.

The proof needs, over a Noetherian affine base, Mumford's complex, obtained from the Čech complex
of a finite affine cover, which is a bounded complex of flat modules by the flatness of `ℱ`,
together with `AlgebraicGeometry.Scheme.Modules.isFinitePresentation_higherDirectImage`; the
general case reduces to this by Noetherian approximation of `(f, ℱ)` [EGA IV₃, §8 and §11.2].
Alternatively, it follows from Kiehl's theorem that `R f_* ℱ` is pseudo-coherent, and finite
Tor-amplitude coming from flatness [Stacks, Tags 0B91 and 0A1H].

(blueprint: `sk-thm-picard-coherence`) -/
theorem exists_isFiniteFreeComplex_higherDirectImage (hℱ : ℱ.IsFlatOver f) (t : T) :
    ∃ (U : T.Opens) (P : CochainComplex U.toScheme.Modules ℤ) (d : ℕ), t ∈ U ∧
      IsFiniteFreeComplex P d ∧
      ∀ {T' X' : Scheme.{u}} (g : T' ⟶ U.toScheme) (g' : X' ⟶ X) (f' : X' ⟶ T')
        [HasInjectiveResolutions X'.Modules], IsPullback g' f' f (g ≫ U.ι) → ∀ q : ℕ,
        Nonempty ((((Modules.pullback g).mapHomologicalComplex _).obj P).homology q ≅
          (higherDirectImage f' q).obj ((Modules.pullback g').obj ℱ)) :=
  sorry

/-- **Coherence of the higher direct images over a locally Noetherian base.** With
`f : X ⟶ T` proper, `T` locally Noetherian and `ℱ` a coherent `𝒪_X`-module, the higher direct
image `R^q f_* ℱ` is a coherent `𝒪_T`-module for every `q` [EGA III₁, 3.2.1],
[Stacks, Tag 02O5]. Coherence is spelled as quasi-coherence together with finite presentation;
quasi-coherence of `R^q f_* ℱ` is
`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_higherDirectImage`, so only finite
presentation is stated here.

The Noetherian hypothesis cannot be dropped, even for `ℱ` flat over `T`. Let `k` be a field,
`V` an infinite-dimensional `k`-vector space, `T = Spec (k ⊕ V)` with `V` a square-zero ideal,
`E` an elliptic curve over `k` and `f : E × T ⟶ T` the projection. Line bundles on `E × T`
which are trivial on `E` are classified by `H¹(E, 𝒪_E) ⊗_k V ≅ V`; let `ℒ` be the one with class
a nonzero `v ∈ V`. The sequence `0 ⟶ 𝒪_E ⊗_k V ⟶ ℒ ⟶ 𝒪_E ⟶ 0` has connecting map
`k ⟶ H¹(E, 𝒪_E) ⊗_k V` sending `1` to `v`, so `f_* ℒ` corresponds to the module `V`, which is
killed by `V` and infinite-dimensional over `k`, hence not of finite type over `k ⊕ V`.

(blueprint: `sk-thm-picard-coherence`) -/
theorem isFinitePresentation_higherDirectImage [IsLocallyNoetherian T]
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] (q : ℕ) :
    ((higherDirectImage f q).obj ℱ).IsFinitePresentation := by
  have hP (V : T.Opens) (hV : IsAffineOpen V) :
      ∃ P : (((higherDirectImage f q).obj ℱ).restrict hV.fromSpec).Presentation, P.IsFinite := by
    have := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
    have : IsNoetherianRing Γ(Spec Γ(T, V), ⊤) :=
      isNoetherianRing_of_ringEquiv _ (Scheme.ΓSpecIso Γ(T, V)).commRingCatIsoToRingEquiv.symm
    have := isGrothendieckAbelian (Limits.pullback f hV.fromSpec)
    obtain ⟨e⟩ := nonempty_higherDirectImage_iso_restrict f ℱ hV.fromSpec _ _
      (IsPullback.of_hasPullback f hV.fromSpec) q
    have : ((Modules.pullback (pullback.fst f hV.fromSpec)).obj ℱ).IsFinitePresentation :=
      (SheafOfModules.isFinitePresentation (Limits.pullback f hV.fromSpec).ringCatSheaf).prop_of_iso
        ((restrictFunctorIsoPullback _).app ℱ) (isFinitePresentation_restrictFunctor _ ℱ)
    have : ((Modules.pullback (pullback.fst f hV.fromSpec)).obj ℱ).IsQuasicoherent :=
      (SheafOfModules.isQuasicoherent (Limits.pullback f hV.fromSpec).ringCatSheaf).prop_of_iso
        ((restrictFunctorIsoPullback _).app ℱ) (isQuasicoherent_restrictFunctor _ ℱ)
    have := finite_sections_higherDirectImage (pullback.snd f hV.fromSpec)
      ((Modules.pullback (pullback.fst f hV.fromSpec)).obj ℱ) q
    let φ : Γ((higherDirectImage (pullback.snd f hV.fromSpec) q).obj
        ((Modules.pullback (pullback.fst f hV.fromSpec)).obj ℱ), ⊤) →ₗ[Γ(Spec Γ(T, V), ⊤)]
        Γ(((higherDirectImage f q).obj ℱ).restrict hV.fromSpec, ⊤) :=
      { toFun := e.hom.app ⊤, map_add' := map_add _, map_smul' := Hom.app_smul e.hom }
    have : Module.Finite Γ(Spec Γ(T, V), ⊤)
        Γ(((higherDirectImage f q).obj ℱ).restrict hV.fromSpec, ⊤) :=
      Module.Finite.of_surjective φ (ConcreteCategory.bijective_of_isIso (e.hom.app ⊤)).2
    have := finite_sections_top_of_finite
      (((higherDirectImage f q).obj ℱ).restrict hV.fromSpec)
    have := isQuasicoherent_higherDirectImage f ℱ q
    exact exists_presentation_isFinite _
  have (V : T.affineOpens) : IsOpenImmersion (IsAffineOpen.fromSpec (U := V.1) V.2) :=
    IsAffineOpen.isOpenImmersion_fromSpec V.2
  choose P _ using fun V : T.affineOpens ↦ hP V.1 V.2
  refine isFinitePresentation_of_iSup_opensRange_eq_top _ _ ?_ P
  exact (iSup_congr fun V ↦ IsAffineOpen.opensRange_fromSpec V.2).trans
    (iSup_affineOpens_eq_top T)

end Coherence

end AlgebraicGeometry.Scheme.Modules
