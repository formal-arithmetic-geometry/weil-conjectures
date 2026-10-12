/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.MumfordComplex
public import WeilConjectures.AlgebraicGeometry.NoetherianApproximation.Model

/-!
# Perfectness of the higher direct images, with base change

For a proper morphism `f : X ⟶ T` of finite presentation and an `𝒪_X`-module `ℱ` of finite
presentation which is flat over `T`, the higher direct images are locally on `T` computed by a
bounded complex of finite free modules, compatibly with every base change
(`AlgebraicGeometry.Scheme.Modules.exists_isFiniteFreeComplex_higherDirectImage`).

Over an affine open `V` of `T`, the pair `(f, ℱ)` is the base change of a pair `(p, 𝒢)` over an
affine scheme `S` with Noetherian ring of global sections
(`AlgebraicGeometry.Scheme.Modules.exists_isNoetherianRing_model`), for which the statement is
`AlgebraicGeometry.Scheme.Modules.exists_isFiniteFreeComplex_higherDirectImage_of_isNoetherianRing`;
base changes of `f` over `V` are base changes of `p`.
-/

@[expose] public section

universe u

open CategoryTheory Limits DerivedCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- The pullback of a bounded complex of finite free modules is a bounded complex of finite free
modules. -/
lemma IsFiniteFreeComplex.pullback {X Z : Scheme.{u}} {P : CochainComplex X.Modules ℤ} {d : ℕ}
    (hP : IsFiniteFreeComplex P d) (j : Z ⟶ X) :
    IsFiniteFreeComplex (((Modules.pullback j).mapHomologicalComplex _).obj P) d where
  isStrictlyGE := by
    have := hP.isStrictlyGE
    rw [CochainComplex.isStrictlyGE_iff]
    exact fun i hi ↦ (Modules.pullback j).map_isZero (P.isZero_of_isStrictlyGE 0 i hi)
  isStrictlyLE := by
    have := hP.isStrictlyLE
    rw [CochainComplex.isStrictlyLE_iff]
    exact fun i hi ↦ (Modules.pullback j).map_isZero (P.isZero_of_isStrictlyLE d i hi)
  exists_iso_free n := by
    obtain ⟨r, ⟨e⟩⟩ := hP.exists_iso_free n
    exact ⟨r, ⟨(Modules.pullback j).mapIso e ≪≫ pullbackFreeIso j _⟩⟩

section General

variable {X T : Scheme.{u}}
variable (f : X ⟶ T) (ℱ : X.Modules)

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
theorem exists_isFiniteFreeComplex_higherDirectImage [IsProper f] [LocallyOfFinitePresentation f]
    [QuasiCompact f] [HasInjectiveResolutions X.Modules] [ℱ.IsFinitePresentation]
    (hℱ : ℱ.IsFlatOver f) (t : T) :
    ∃ (U : T.Opens) (P : CochainComplex U.toScheme.Modules ℤ) (d : ℕ), t ∈ U ∧
      IsFiniteFreeComplex P d ∧
      ∀ {T' X' : Scheme.{u}} (g : T' ⟶ U.toScheme) (g' : X' ⟶ X) (f' : X' ⟶ T')
        [HasInjectiveResolutions X'.Modules], IsPullback g' f' f (g ≫ U.ι) → ∀ q : ℕ,
        Nonempty ((((Modules.pullback g).mapHomologicalComplex _).obj P).homology q ≅
          (higherDirectImage f' q).obj ((Modules.pullback g').obj ℱ)) := by
  -- an affine open neighbourhood `V` of `t`
  obtain ⟨V, hV, htV, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 T.isBasis_affineOpens)
    (show t ∈ (⊤ : T.Opens) from trivial)
  have : IsAffine V.toScheme := hV
  -- the restriction of `(f, ℱ)` over `V`
  set fV := f ∣_ V
  set ℱV := (Modules.pullback (f ⁻¹ᵁ V).ι).obj ℱ
  have : IsProper fV := IsZariskiLocalAtTarget.restrict ‹_› V
  have : LocallyOfFinitePresentation fV := IsZariskiLocalAtTarget.restrict ‹_› V
  have : ℱV.IsFinitePresentation :=
    (SheafOfModules.isFinitePresentation (f ⁻¹ᵁ V).toScheme.ringCatSheaf).prop_of_iso
      ((restrictFunctorIsoPullback _).app ℱ) (isFinitePresentation_restrictFunctor _ ℱ)
  have hℱV : ℱV.IsFlatOver fV := by
    refine IsFlatOver.of_comp_isOpenImmersion V.ι ?_
    rw [morphismRestrict_ι]
    exact hℱ.pullback_of_isOpenImmersion _
  -- a Noetherian model of `(fV, ℱV)`
  obtain ⟨S, Y, _, _, π, p, _, _, 𝒢, _, h, h𝒢, hsq, ⟨e⟩⟩ :=
    exists_isNoetherianRing_model fV ℱV hℱV
  obtain ⟨a, P₀, d, hs₀, hP₀, hbc₀⟩ :=
    exists_isFiniteFreeComplex_higherDirectImage_of_isNoetherianRing p 𝒢 h𝒢 (π ⟨t, htV⟩)
  -- the open `U = π⁻¹ D(a)` of `T`
  set U : T.Opens := V.ι ''ᵁ (π ⁻¹ᵁ S.basicOpen a)
  have hUV : U ≤ V := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hrange : Set.range (T.homOfLE hUV ≫ π) ⊆ Set.range (S.basicOpen a).ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    obtain ⟨z, hz, hzy⟩ := y.2
    have : T.homOfLE hUV y = z := Subtype.ext (by rw [Scheme.homOfLE_apply, ← hzy]; rfl)
    rw [Scheme.Hom.comp_apply, this]
    exact hz
  let j : U.toScheme ⟶ (S.basicOpen a).toScheme :=
    IsOpenImmersion.lift (S.basicOpen a).ι (T.homOfLE hUV ≫ π) hrange
  have hj : j ≫ (S.basicOpen a).ι = T.homOfLE hUV ≫ π := IsOpenImmersion.lift_fac _ _ _
  refine ⟨U, ((Modules.pullback j).mapHomologicalComplex _).obj P₀, d,
    ⟨⟨t, htV⟩, hs₀, rfl⟩, hP₀.pullback j, ?_⟩
  intro T' X' g g' f' _ sq q
  -- the square over `V`
  have hg'V : Set.range g' ⊆ Set.range (f ⁻¹ᵁ V).ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    change f (g' x) ∈ V
    rw [← Scheme.Hom.comp_apply, sq.w, Scheme.Hom.comp_apply]
    exact hUV (g (f' x)).2
  let g'V : X' ⟶ (f ⁻¹ᵁ V).toScheme := IsOpenImmersion.lift (f ⁻¹ᵁ V).ι g' hg'V
  have hg'Vfac : g'V ≫ (f ⁻¹ᵁ V).ι = g' := IsOpenImmersion.lift_fac _ _ _
  have sq₁ : IsPullback g'V f' fV (g ≫ T.homOfLE hUV) := by
    refine IsPullback.of_right ?_ ?_ (isPullback_morphismRestrict f V).flip
    · rw [hg'Vfac, Category.assoc, Scheme.homOfLE_ι]
      exact sq
    · rw [← cancel_mono V.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hg'Vfac,
        sq.w, Category.assoc, Category.assoc, Scheme.homOfLE_ι]
  have sq₂ : IsPullback (g'V ≫ h) f' p ((g ≫ j) ≫ (S.basicOpen a).ι) := by
    rw [Category.assoc, hj, ← Category.assoc]
    exact sq₁.paste_horiz hsq
  obtain ⟨e₁⟩ := hbc₀ (g ≫ j) (g'V ≫ h) f' sq₂ q
  -- the comparison of the modules
  let e₂ : (Modules.pullback (g'V ≫ h)).obj 𝒢 ≅ (Modules.pullback g').obj ℱ :=
    (pullbackComp g'V h).symm.app 𝒢 ≪≫ (Modules.pullback g'V).mapIso e ≪≫
      (pullbackComp g'V (f ⁻¹ᵁ V).ι).app ℱ ≪≫
      eqToIso (congrArg (fun φ ↦ (Modules.pullback φ).obj ℱ) hg'Vfac)
  exact ⟨HomologicalComplex.homologyMapIso
    ((NatIso.mapHomologicalComplex (pullbackComp g j) _).app P₀) q ≪≫ e₁ ≪≫
      (higherDirectImage f' q).mapIso e₂⟩

end General

section Perfect

variable {X S : Scheme.{u}} (f : X ⟶ S) (ℱ : X.Modules) {ι : Type u} (U : ι → X.Opens)
  [IsAffine S] [Finite ι] [Nonempty ι] (hU : ∀ i, IsAffineOpen (U i)) (hU' : iSup U = ⊤)
  [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ]

include hU hU' in
/-- **Perfectness of `Rf_* ℱ` and base change.** Let `f : X ⟶ S` be proper of finite
presentation with `S = Spec A` affine, and `ℱ` an `𝒪_X`-module of finite presentation, flat over
`S`. Then `Rf_* ℱ` is perfect and its formation commutes with arbitrary base change:

* locally on `S`, `Rf_* ℱ` is represented by a bounded complex of finite free modules whose
  pullback along every `g : T' ⟶ S` computes the higher direct images of `ℱ_{T'}`; this is the
  classical input `exists_isFiniteFreeComplex_higherDirectImage` of `sk-thm-picard-coherence`
  [Stacks, Tag 0B91];
* over the affine base, `Rf_* ℱ` is represented by the bounded complex `K` of flat `A`-modules
  of `AlgebraicGeometry.Scheme.Modules.isIso_cechModuleComplexBaseChangeComparison`, and for every
  cartesian square with `T = Spec B` affine, `Lg^* Rf_* ℱ = B ⊗[A] K ≅ Rf_{T*} ℱ_T` in `D(B)`
  (`lem-pc-rf-base-change-flat-module`; proper morphisms are quasi-compact and separated);
* if `A` is noetherian, `Rf_* ℱ` is a perfect object of `D(A)`, and so are all its base changes
  `Rf_{T*} ℱ_T` in `D(B)`
  (`AlgebraicGeometry.Scheme.Modules.isPerfect_Q_cechModuleComplex_of_isNoetherianRing`,
  `AlgebraicGeometry.Scheme.Modules.isPerfect_Q_cechModuleComplex_baseChange`).

Perfectness in `D(A)` over a non-noetherian base is the classical input of the first item; it is
not deduced here from it, as the comparison of the two representatives of `Rf_* ℱ` would need
the finite free complexes to be quasi-isomorphic to the Čech complex.

(blueprint: `lem-pc-rf-perfect-base-change`) -/
theorem perfect_and_baseChange_cechModuleComplex_of_isProper [IsProper f]
    [LocallyOfFinitePresentation f] [HasInjectiveResolutions X.Modules] [Fintype ι]
    [ℱ.IsFinitePresentation] (hℱ : ℱ.IsFlatOver f) :
    (∀ t : S, ∃ (V : S.Opens) (P : CochainComplex V.toScheme.Modules ℤ) (d : ℕ), t ∈ V ∧
      IsFiniteFreeComplex P d ∧
      ∀ {T' X' : Scheme.{u}} (g : T' ⟶ V.toScheme) (g' : X' ⟶ X) (f' : X' ⟶ T')
        [HasInjectiveResolutions X'.Modules], IsPullback g' f' f (g ≫ V.ι) → ∀ q : ℕ,
        Nonempty ((((Modules.pullback g).mapHomologicalComplex _).obj P).homology q ≅
          (higherDirectImage f' q).obj ((Modules.pullback g').obj ℱ))) ∧
    (∀ {T Y : Scheme.{u}} {g : T ⟶ S} {g' : Y ⟶ X} {f' : Y ⟶ T} (H : IsPullback g' f' f g)
      [IsAffine T] [Algebra Γ(S, ⊤) Γ(T, ⊤)] (hg : algebraMap Γ(S, ⊤) Γ(T, ⊤) = g.appTop.hom),
      IsIso (cechModuleComplexBaseChangeComparison f ℱ U hU H hg)) ∧
    (IsNoetherianRing Γ(S, ⊤) → (Q.obj (cechModuleComplex f ℱ U)).IsPerfect ∧
      ∀ {T Y : Scheme.{u}} {g : T ⟶ S} {g' : Y ⟶ X} {f' : Y ⟶ T} (_ : IsPullback g' f' f g)
        [IsAffine T] [Algebra Γ(S, ⊤) Γ(T, ⊤)] (_ : algebraMap Γ(S, ⊤) Γ(T, ⊤) = g.appTop.hom),
        (Q.obj (cechModuleComplex f' ((pullback g').obj ℱ) (fun i ↦ g' ⁻¹ᵁ U i))).IsPerfect) := by
  refine ⟨fun t ↦ exists_isFiniteFreeComplex_higherDirectImage f ℱ hℱ t,
    fun H _ _ hg ↦ isIso_cechModuleComplexBaseChangeComparison f ℱ U hU hU' hℱ H hg,
    fun _ ↦ ?_⟩
  have hP := isPerfect_Q_cechModuleComplex_of_isNoetherianRing f ℱ U hU hU' hℱ
  exact ⟨hP, fun H _ _ hg ↦ (isPerfect_Q_cechModuleComplex_baseChange f ℱ U hU hU' hℱ hP H hg).2⟩

end Perfect

end AlgebraicGeometry.Scheme.Modules
