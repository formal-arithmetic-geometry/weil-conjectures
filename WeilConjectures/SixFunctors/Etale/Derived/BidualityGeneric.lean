/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.CoordinateGenericFibre
public import WeilConjectures.SixFunctors.Etale.Derived.GeometricGenericDuality
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk

/-!
# Verdier biduality at the nonclosed points

The inductive step of the proof of Verdier biduality
(`thm-weil-etale-geometric-biduality`) at a nonclosed point: through a coordinate sending the
point to the generic point of `𝔸¹_k`, biduality in lower dimension on the geometric generic
fibre gives biduality at the point.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- The statement proved by induction on the dimension: Verdier biduality on `Dctf(X, Λ)` for
every separated scheme `X` of finite type and of dimension at most `d` over an algebraically
closed field in which the exponent of `Λ` is invertible. -/
def BidualityUpTo (d : ℕ) : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] [HasInvertibleExponent Λ (Spec (.of k))]
    (X : Scheme.{u}) (a : X ⟶ Spec (.of k)) [IsSeparated a] [LocallyOfFiniteType a]
    [QuasiCompact a], topologicalKrullDim X ≤ (d : WithBot ℕ∞) →
    ∀ (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K →
        IsIso ((verdierDualDoubleDual (ModuleCat.{u + 1} Λ) a).app K)

/-- Blueprint `lem-weil-delta-restriction`, after an arbitrary functor `G`: for a quasi-compact
open immersion `j : U ⟶ Y` and `Y` over `S`, `G` sends the restriction `Lj^* δ_K` of the
double-dual morphism of `Y` to an isomorphism if and only if it sends the double-dual morphism
`δ_{Lj^* K}` of `U` to an isomorphism: the two are identified up to isomorphisms by the
comparison `Lj^* 𝔻_Y ≅ 𝔻_U Lj^*`. -/
theorem isIso_map_leftDerivedUpperStar_map_verdierDualDoubleDual_app_iff_of_finite
    {U Y S : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j] [HasCompactification j]
    [QuasiCompact j] (aY : Y ⟶ S) [HasCompactification aY] [HasCompactification (j ≫ aY)]
    [QuasiCompact (j ≫ aY)] {D : Type*} [Category D]
    (G : _root_.DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤ D)
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (G.map (L((j)^*[ModuleCat.{u + 1} Λ]).map
        ((verdierDualDoubleDual (ModuleCat.{u + 1} Λ) aY).app K))) ↔
      IsIso (G.map ((verdierDualDoubleDual (ModuleCat.{u + 1} Λ) (j ≫ aY)).app
        (L((j)^*[ModuleCat.{u + 1} Λ]).obj K))) := by
  obtain ⟨e⟩ := nonempty_iso_rightDerivedUpperShriek_comp Λ j aY
  let e' : L((j)^*[ModuleCat.{u + 1} Λ]).obj (dualizingComplex _ aY) ≅
      dualizingComplex _ (j ≫ aY) :=
    (leftDerivedUpperStarIsoMapDerivedCategory _ j).app _ ≪≫
      (rightDerivedUpperShriekIsoOfIsOpenImmersion Λ j).symm.app _ ≪≫ (e.app (𝟙_ _)).symm
  have h := G.congr_map (leftDerivedUpperStar_map_verdierDualDoubleDual_app_comp
    (ModuleCat.{u + 1} Λ) j aY (j ≫ aY) e'.hom K)
  simp only [Functor.map_comp] at h
  have := isIso_leftDerivedUpperStarVerdierDualHom (ModuleCat.{u + 1} Λ) aY j (j ≫ aY) e'.hom K
  have := isIso_leftDerivedUpperStarVerdierDualHom (ModuleCat.{u + 1} Λ) aY j (j ≫ aY) e'.hom
    ((verdierDual (ModuleCat.{u + 1} Λ) aY).obj (op K))
  constructor
  · intro
    have : IsIso (G.map ((verdierDualDoubleDual (ModuleCat.{u + 1} Λ) (j ≫ aY)).app
        (L((j)^*[ModuleCat.{u + 1} Λ]).obj K)) ≫ G.map ((verdierDual (ModuleCat.{u + 1} Λ)
          (j ≫ aY)).map (leftDerivedUpperStarVerdierDualHom (ModuleCat.{u + 1} Λ) j aY (j ≫ aY)
            e'.hom K).op)) := by
      rw [← h]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (G.map ((verdierDual (ModuleCat.{u + 1} Λ) (j ≫ aY)).map
      (leftDerivedUpperStarVerdierDualHom (ModuleCat.{u + 1} Λ) j aY (j ≫ aY) e'.hom K).op))
  · intro
    have : IsIso (G.map (L((j)^*[ModuleCat.{u + 1} Λ]).map
        ((verdierDualDoubleDual (ModuleCat.{u + 1} Λ) aY).app K)) ≫
          G.map (leftDerivedUpperStarVerdierDualHom (ModuleCat.{u + 1} Λ) j aY (j ≫ aY) e'.hom
            ((verdierDual (ModuleCat.{u + 1} Λ) aY).obj (op K)))) := by
      rw [h]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (G.map (leftDerivedUpperStarVerdierDualHom
      (ModuleCat.{u + 1} Λ) j aY (j ≫ aY) e'.hom ((verdierDual (ModuleCat.{u + 1} Λ) aY).obj
        (op K))))

omit [Finite Λ] in
/-- A morphism `f` of complexes on `X` whose derived pullback along `h : Y ⟶ X` is an
isomorphism induces isomorphisms on the stalks of the cohomology sheaves at every geometric
point of `X` factoring through `h`: the stalk of `Hᵠ f` at `s ≫ h` is the stalk of
`h^* Hᵠ f = Hᵠ(Lh^* f)` at `s`. -/
lemma isIso_sheafFiber_map_homologyFunctor_map_of_isIso_leftDerivedUpperStar_map
    {X Y : Scheme.{u}} (h : Y ⟶ X) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ Y)
    {K L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (f : K ⟶ L) (hf : IsIso (L((h)^*[ModuleCat.{u + 1} Λ]).map f)) (q : ℤ) :
    IsIso ((pointSmallEtale (s ≫ h)).ulift.{u + 1}.sheafFiber.map
      ((_root_.DerivedCategory.homologyFunctor _ q).map f)) := by
  rw [← NatIso.isIso_map_iff (upperStarCompUliftSheafFiberIso (ModuleCat.{u + 1} Λ) h s),
    Functor.comp_map]
  have : IsIso ((h)^*[ModuleCat.{u + 1} Λ].map
      ((_root_.DerivedCategory.homologyFunctor _ q).map f)) := by
    rw [← Functor.comp_map, NatIso.isIso_map_iff
      (leftDerivedUpperStarHomologyFunctorIso (ModuleCat.{u + 1} Λ) h q), Functor.comp_map]
    infer_instance
  infer_instance

/-- **Geometric points over the generic point factor through the geometric generic fibre.** Let
`p : V ⟶ Y` with `Y` integral, and let `s : Spec Ω ⟶ V` be a geometric point with `Ω`
algebraically closed lying over the generic point of `Y`. Then `s` factors through the
projection `V ×_Y Spec \overline{K(Y)} ⟶ V`: the map `K(Y) ⟶ Ω` extends to the algebraic
closure. -/
theorem exists_comp_pullbackFst_eq_of_apply_eq_genericPoint {V Y : Scheme.{u}} [IsIntegral Y]
    (p : V ⟶ Y) {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ V)
    (hs : p (s (IsLocalRing.closedPoint Ω)) = genericPoint Y) :
    ∃ s' : Spec (.of Ω) ⟶ pullback p Y.geometricGenericPoint,
      s' ≫ pullback.fst p Y.geometricGenericPoint = s := by
  have key (y : Y) (hy : (s ≫ p) (IsLocalRing.closedPoint Ω) = y) :
      ∃ ψ : Y.presheaf.stalk y ⟶ .of Ω, Spec.map ψ ≫ Y.fromSpecStalk y = s ≫ p := by
    subst hy
    exact ⟨_, Scheme.Spec_stalkClosedPointTo_fromSpecStalk (s ≫ p)⟩
  obtain ⟨ψ, hψ⟩ := key (genericPoint Y) (by rw [Scheme.Hom.comp_apply, hs])
  let _ : Algebra Y.functionField Ω := ψ.hom.toAlgebra
  let ψ' : AlgebraicClosure Y.functionField →ₐ[Y.functionField] Ω := IsAlgClosed.lift
  have hψ' : CommRingCat.ofHom (algebraMap Y.functionField (AlgebraicClosure Y.functionField)) ≫
      CommRingCat.ofHom ψ'.toRingHom = ψ := by
    ext z
    exact ψ'.commutes z
  refine ⟨pullback.lift s (Spec.map (CommRingCat.ofHom ψ'.toRingHom)) ?_,
    pullback.lift_fst _ _ _⟩
  rw [Scheme.geometricGenericPoint, ← Spec.map_comp_assoc, hψ', hψ]

/-- **Biduality at nonclosed points.** Assume Verdier biduality in dimensions `< d`. Let `X` be
separated of finite type over an algebraically closed field `k` with `dim X ≤ d`, and let
`K ∈ Dctf(X, Λ)`. Then at every nonclosed point `x` of `X` the geometric stalks of the
cohomology of `δ_K` are isomorphisms. A coordinate `t` on an affine neighbourhood `V` of `x`
sends `x` to the generic point of `𝔸¹_k`; the geometric generic fibre `V_η̄` has dimension
`< d` (`lem-fin-coordinate-generic-dimension`), so `δ` is an isomorphism on it, and it is the
restriction of `δ_K` (`lem-weil-geometric-generic-duality`, `lem-weil-delta-restriction`); and a
geometric point over `x` factors through `V_η̄`. -/
theorem isIso_sheafFiber_map_verdierDualDoubleDual_app_of_not_isClosed (d : ℕ)
    (IH : ∀ d' < d, BidualityUpTo Λ d') {k : Type u} [Field k] [IsAlgClosed k]
    [HasInvertibleExponent Λ (Spec (.of k))] {X : Scheme.{u}} (a : X ⟶ Spec (.of k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    (hX : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K) (x : X)
    (hx : ¬ IsClosed ({x} : Set X)) (q : ℤ) :
    IsIso ((X.uliftPointSmallEtale x).sheafFiber.map
      ((_root_.DerivedCategory.homologyFunctor _ q).map
        ((verdierDualDoubleDual (ModuleCat.{u + 1} Λ) a).app K))) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace a
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated a
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace a
  -- an affine open neighbourhood `U` of `x`, in which `x` is not closed
  obtain ⟨U : X.Opens, hU, hxU, -⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
    (show x ∈ (⊤ : X.Opens) from trivial)
  have : IsAffine U := hU
  let x' : U := ⟨x, hxU⟩
  have hx' : ¬ IsClosed ({x'} : Set U) := fun h ↦ hx (by
    have h' : x' ∈ U.ι ⁻¹' closedPoints X := (U.ι.isOpenEmbedding.preimage_closedPoints).ge h
    simpa [x', Scheme.Opens.ι_apply] using h')
  -- a coordinate `p : U ⟶ 𝔸¹_k` sending `x` to the generic point
  obtain ⟨t, ht⟩ := Scheme.exists_coordinate_apply_eq_genericPoint (U.ι ≫ a) hx'
  let p := Scheme.coordinate (U.ι ≫ a) t
  have hp : p ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))) = U.ι ≫ a :=
    Scheme.coordinate_comp _ t
  have : IsSeparated p := by
    have : IsSeparated (p ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k)))) := by
      rw [hp]
      infer_instance
    exact IsSeparated.of_comp p (Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))))
  have : LocallyOfFiniteType p := by
    have : LocallyOfFiniteType
        (p ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k)))) := by
      rw [hp]
      infer_instance
    exact locallyOfFiniteType_of_comp p (Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))))
  -- the geometric generic fibre `g : U_η̄ ⟶ U` of `p`, with structure morphism `b`
  let g := pullback.fst p (affineLineGeometricGenericPoint k)
  let b := pullback.snd p (affineLineGeometricGenericPoint k)
  have : HasInvertibleExponent Λ
      (Spec (.of (AlgebraicClosure (Spec (.of (Polynomial k))).functionField))) :=
    .of_hom (affineLineGeometricGenericPoint k ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))))
  -- the geometric point at `x` factors through `g`
  have hsU : Set.range (X.algClosurePoint x) ⊆ Set.range U.ι := by
    rintro _ ⟨z, rfl⟩
    simpa [Scheme.Opens.range_ι] using hxU
  let sU := IsOpenImmersion.lift U.ι (X.algClosurePoint x) hsU
  have hsU' : sU ≫ U.ι = X.algClosurePoint x := IsOpenImmersion.lift_fac _ _ _
  have hpt : sU (IsLocalRing.closedPoint _) = x' := U.ι.isOpenEmbedding.injective (by
    rw [← Scheme.Hom.comp_apply, hsU']
    simp [x', Scheme.Opens.ι_apply])
  obtain ⟨s', hs'⟩ := exists_comp_pullbackFst_eq_of_apply_eq_genericPoint p sU
    (by rw [hpt]; exact ht)
  -- `dim U_η̄ < d`
  have hdim : topologicalKrullDim (pullback p (affineLineGeometricGenericPoint k) : Scheme) + 1 ≤
      d := by
    have hη : ¬ IsClosed ({genericPoint (Spec (.of (Polynomial k)))} : Set (Spec (.of _))) := by
      rw [genericPoint_eq_bot_of_affine, PrimeSpectrum.isClosed_singleton_iff_isMaximal]
      exact fun h ↦ Polynomial.not_isField k (Ring.isField_iff_maximal_bot.2 h)
    refine (topologicalKrullDim_pullback_add_one_le p _ ⟨IsLocalRing.closedPoint _, rfl⟩
      fun hc ↦ hη ?_).trans ((topologicalKrullDim_subspace_le X U).trans hX)
    have hmem : affineLineGeometricGenericPoint k (IsLocalRing.closedPoint _) ∈
        Set.range (Scheme.fromSpecStalk _ (genericPoint (Spec (.of (Polynomial k))))) := by
      rw [affineLineGeometricGenericPoint, Scheme.geometricGenericPoint, Scheme.Hom.comp_apply]
      exact Set.mem_range_self _
    rw [Scheme.range_fromSpecStalk, Set.mem_ofPred_eq, specializes_iff_mem_closure,
      hc.closure_eq, Set.mem_singleton_iff] at hmem
    rw [hmem]
    exact hc
  obtain ⟨d', hd', hdim'⟩ : ∃ d' < d,
      topologicalKrullDim (pullback p (affineLineGeometricGenericPoint k) : Scheme) ≤ d' := by
    have : Nonempty (TopologicalSpace.IrreducibleCloseds
        (pullback p (affineLineGeometricGenericPoint k) : Scheme)) :=
      ⟨⟨closure {s' (IsLocalRing.closedPoint _)}, isIrreducible_singleton.closure,
        isClosed_closure⟩⟩
    have h0 : (0 : WithBot ℕ∞) ≤
        topologicalKrullDim (pullback p (affineLineGeometricGenericPoint k) : Scheme) :=
      Order.krullDim_nonneg
    generalize topologicalKrullDim (pullback p (affineLineGeometricGenericPoint k) : Scheme) = D
      at h0 hdim ⊢
    induction D using WithBot.recBotCoe with
    | bot => exact absurd h0 (by simp)
    | coe m =>
      induction m using ENat.recTopCoe with
      | top => exact absurd hdim (by norm_cast)
      | coe m =>
        norm_cast at hdim
        exact ⟨m, by omega, le_rfl⟩
  -- biduality on `U_η̄` by induction, hence `Lg^* Lι^* δ_K` is an isomorphism
  have hKU := constructibleFiniteTor_leftDerivedUpperStar (ModuleCat.{u + 1} Λ) U.ι hK
  have hKg := constructibleFiniteTor_leftDerivedUpperStar (ModuleCat.{u + 1} Λ) g hKU
  have h₁ := IH d' hd' _ (pullback p (affineLineGeometricGenericPoint k)) b hdim' _ hKg
  have h₂ := (isIso_leftDerivedUpperStar_map_verdierDualDoubleDual_app_iff_geometricGenericPoint
    Λ (U.ι ≫ a) p hp hKU).2 h₁
  have h₃ := (isIso_map_leftDerivedUpperStar_map_verdierDualDoubleDual_app_iff_of_finite Λ U.ι a
    L((g)^*[ModuleCat.{u + 1} Λ]) K).2 h₂
  have h₄ : IsIso (L((g ≫ U.ι)^*[ModuleCat.{u + 1} Λ]).map
      ((verdierDualDoubleDual (ModuleCat.{u + 1} Λ) a).app K)) := by
    rw [NatIso.isIso_map_iff (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) g U.ι)]
    exact h₃
  -- the stalk at `x` is the stalk at a point of `U_η̄`
  have hfac : s' ≫ g ≫ U.ι = X.algClosurePoint x := by
    rw [← Category.assoc, hs', hsU']
  rw [Scheme.uliftPointSmallEtale, ← hfac]
  exact isIso_sheafFiber_map_homologyFunctor_map_of_isIso_leftDerivedUpperStar_map Λ (g ≫ U.ι) s'
    _ h₄ q

end Etale

end AlgebraicGeometry
