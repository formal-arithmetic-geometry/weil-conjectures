/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelPointTrace
public import WeilConjectures.WeilSheaf.ArtinSchreierDual
public import WeilConjectures.WeilSheaf.ArtinSchreierPullback
public import WeilConjectures.WeilSheaf.FourierFirstFormula
public import WeilConjectures.WeilSheaf.FourierInversion.TensorLisse

/-!
# The trivialization at zero of the Artin–Schreier sheaves

The Artin–Schreier sheaf `ℒ_ψ` comes with a specified trivialization at the origin
`0 : Spec k₀ ⟶ 𝔸¹`: the origin lifts to the Artin–Schreier cover `u^q - u = x` through the root
`u = 0`, i.e. `0 ≫ AS = 0`, and `AS^* ℒ_ψ ≅ ℚ̄_ℓ` is the evaluation at the tautological root
(`AlgebraicGeometry.WeilSheaf.upperStarArtinSchreierMapImageIso`). Pulling back gives
`0^* ℒ_ψ ≅ 0^* AS^* ℒ_ψ ≅ 0^* ℚ̄_ℓ ≅ ℚ̄_ℓ`.

We construct this trivialization (`AlgebraicGeometry.artinSchreierZeroIso`) and the induced
trivialization `x^* ℒ_{ψ,f} ≅ ℚ̄_ℓ` at a rational point `x` where the function `f` vanishes
(`AlgebraicGeometry.artinSchreierOfTrivialization`), together with the canonical comparison
isomorphisms needed to read an isomorphism of tensor products and duals at a point:

* `AlgebraicGeometry.WeilSheaf.upperStarTensorObjIso`: `φ^* (F ⊗ G) ≅ φ^* F ⊗ φ^* G`;
* `AlgebraicGeometry.WeilSheaf.tensorObjIsoOfIso`: functoriality of `⊗` in isomorphisms;
* `AlgebraicGeometry.WeilSheaf.adicConstantTensorObjIso`: `ℚ̄_ℓ ⊗ G ≅ G`.

The blueprint clauses of `lemma-artin-schreier-character-sheaf` stating that the multiplication
and duality isomorphisms respect these trivializations are
`AlgebraicGeometry.exists_iso_tensorObj_artinSchreierOf_compatible` and
`AlgebraicGeometry.exists_iso_dual_artinSchreier_compatible`. They are proved by rescaling any
such isomorphism by a scalar: every automorphism of `ℚ̄_ℓ` on `Spec k₀` is a scalar, scalars
commute with all morphisms and pullbacks, so every automorphism of the restriction to a rational
point of a sheaf trivial there lifts (`AlgebraicGeometry.WeilSheaf.exists_upperStar_mapIso_eq`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

section Origin

omit [Finite k₀] in
/-- The origin is fixed by scalings: `a · 0 = 0`. -/
@[reassoc (attr := simp)]
lemma affineLine.zero_comp_smul (a : k₀) :
    affineLine.zero k₀ ≫ affineLine.smul k₀ a = affineLine.zero k₀ := by
  refine AffineSpace.hom_ext (by simp [affineLine.smul, affineLine.zero]) fun _ ↦ ?_
  simp [affineLine.smul, affineLine.zero, AffineSpace.smul_appTop_coord,
    AffineSpace.zeroSection_appTop_coord]

/-- The origin lifts to the Artin–Schreier cover through the root `u = 0` of `u^q - u = 0`:
`AS(0) = 0`. -/
@[reassoc (attr := simp)]
lemma affineLine.zero_comp_artinSchreierMap :
    affineLine.zero k₀ ≫ affineLine.artinSchreierMap k₀ = affineLine.zero k₀ := by
  let := Fintype.ofFinite k₀
  refine AffineSpace.hom_ext
    (by simp [affineLine.artinSchreierMap, affineLine.zero]) fun _ ↦ ?_
  simp only [affineLine.zero, affineLine.artinSchreierMap, Scheme.Hom.comp_appTop,
    CommRingCat.comp_apply, AffineSpace.artinSchreierMap_appTop_coord, map_sub, map_pow,
    AffineSpace.zeroSection_appTop_coord]
  simp [Fintype.card_ne_zero]

omit [Finite k₀] in
/-- A rational point `x` of `X` at which the function `f` vanishes is mapped by `f : X ⟶ 𝔸¹` to
the origin. -/
lemma affineLine.comp_homOfSection_eq_zero {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    (x : Spec (CommRingCat.of k₀) ⟶ X) [x.IsOver (Spec (CommRingCat.of k₀))] {f : Γ(X, ⊤)}
    (hf : x.appTop f = 0) :
    x ≫ affineLine.homOfSection k₀ f = affineLine.zero k₀ := by
  refine AffineSpace.hom_ext ?_ fun _ ↦ ?_
  · rw [Category.assoc, affineLine.homOfSection, AffineSpace.homOfVector_over,
      comp_over, affineLine.zero, AffineSpace.zeroSection_over]
    rfl
  · rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, affineLine.homOfSection,
      AffineSpace.homOfVector_appTop_coord, hf, affineLine.zero,
      AffineSpace.zeroSection_appTop_coord]

end Origin

section Comparison

/-- `φ^* g^* F ≅ g'^* F` for `φ ≫ g = g'`, from the composition and congruence isomorphisms. -/
noncomputable def WeilSheaf.upperStarUpperStarIsoOfComp {X Y Z : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
    [Z.Over (Spec (CommRingCat.of k₀))] (φ : X ⟶ Y) (g : Y ⟶ Z) (g' : X ⟶ Z)
    [φ.IsOver (Spec (CommRingCat.of k₀))] [g.IsOver (Spec (CommRingCat.of k₀))]
    [g'.IsOver (Spec (CommRingCat.of k₀))] (h : φ ≫ g = g') (F : WeilSheaf k₀ l Z) :
    (WeilSheaf.upperStar φ).obj ((WeilSheaf.upperStar g).obj F) ≅
      (WeilSheaf.upperStar g').obj F :=
  ((WeilSheaf.upperStarCompIso φ g).app F).symm ≪≫ (WeilSheaf.upperStarCongr h).app F

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- The tensor product `F ⊗ G` of Weil sheaves only depends on `F` and `G` up to
isomorphism. -/
noncomputable def WeilSheaf.tensorObjIsoOfIso {F F' G G' : WeilSheaf k₀ l X} (e : F ≅ F')
    (e' : G ≅ G') (hF : F.IsLisse) (hF' : F'.IsLisse) :
    F.tensorObj G hF ≅ F'.tensorObj G' hF' :=
  ObjectProperty.isoMk _ (ProEtaleWeilSheaf.ihomMapIsoLeft
      ((ObjectProperty.ι _).mapIso (WeilSheaf.dualIsoOfIso e hF hF')).symm _ ≪≫
    ProEtaleWeilSheaf.ihomMapIsoRight _ ((ObjectProperty.ι _).mapIso e'))

/-- The left unitor of the tensor product of Weil sheaves: `ℚ̄_ℓ ⊗ G ≅ G`, from
`ℚ̄_ℓ^∨ ≅ ℚ̄_ℓ` and `𝓗om(ℚ̄_ℓ, G) ≅ G`. -/
noncomputable def WeilSheaf.adicConstantTensorObjIso (G : WeilSheaf k₀ l X) :
    (WeilSheaf.adicConstant k₀ l X).tensorObj G (WeilSheaf.isLisse_adicConstant k₀ l X) ≅ G :=
  ObjectProperty.isoMk _ (ProEtaleWeilSheaf.ihomMapIsoLeft
      ((ObjectProperty.ι _).mapIso WeilSheaf.dualAdicConstantIso).symm _ ≪≫
    ProEtaleWeilSheaf.ihomAdicConstantIso G.obj)

/-- Pullback commutes with the tensor product with a lisse Weil sheaf:
`φ^* (F ⊗ G) ≅ φ^* F ⊗ φ^* G`. -/
noncomputable def WeilSheaf.upperStarTensorObjIso {Y : Scheme.{u}}
    [Y.Over (Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))] (φ : X ⟶ Y)
    [φ.IsOver (Spec (CommRingCat.of k₀))] (F G : WeilSheaf k₀ l Y) (hF : F.IsLisse) :
    (WeilSheaf.upperStar φ).obj (F.tensorObj G hF) ≅
      ((WeilSheaf.upperStar φ).obj F).tensorObj ((WeilSheaf.upperStar φ).obj G)
        (ProEtale.IsAdicLisseSheaf.upperStar _ hF) :=
  ObjectProperty.isoMk _
    (eqToIso (by rw [WeilSheaf.upperStar_obj_obj, WeilSheaf.tensorObj_obj, Functor.comp_obj,
        ProEtaleWeilSheaf.ihomFunctor_obj]) ≪≫
      (ProEtaleWeilSheaf.ihomFunctorDualCompUpperStarIso φ F hF).app G.obj ≪≫
      eqToIso (by rw [Functor.comp_obj, WeilSheaf.tensorObj_obj, WeilSheaf.upperStar_obj_obj,
        ProEtaleWeilSheaf.ihomFunctor_obj]))

end Comparison

section Trivialization

attribute [local instance high] WeilSheaf.hasImage_artinSchreierIdempotent

variable (ψ : AddChar k₀ (PadicAlgCl l))

/-- The trivialization `φ^* ℒ_ψ ≅ ℚ̄_ℓ` of the pullback of `ℒ_ψ` along a morphism `φ` with
`AS ∘ φ = φ`, i.e. lifting to the Artin–Schreier cover through `u = φ`:
`φ^* ℒ_ψ ≅ φ^* AS^* ℒ_ψ ≅ φ^* ℚ̄_ℓ ≅ ℚ̄_ℓ`. -/
noncomputable def WeilSheaf.upperStarArtinSchreierImageIso {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] (φ : X ⟶ affineLine k₀)
    [φ.IsOver (Spec (CommRingCat.of k₀))] (h : φ ≫ affineLine.artinSchreierMap k₀ = φ) :
    (WeilSheaf.upperStar φ).obj (image (WeilSheaf.artinSchreierIdempotent ψ)) ≅
      WeilSheaf.adicConstant k₀ l X :=
  (WeilSheaf.upperStarUpperStarIsoOfComp φ (affineLine.artinSchreierMap k₀) φ h _).symm ≪≫
    (WeilSheaf.upperStar φ).mapIso (WeilSheaf.upperStarArtinSchreierMapImageIso ψ) ≪≫
    WeilSheaf.upperStarAdicConstantIso φ

/-- Unfolding `0^* ℒ_{ψ(a x)} = 0^* [a]^* ℒ_ψ`, with the named instance
`AlgebraicGeometry.WeilSheaf.hasImage_artinSchreierIdempotent` for the image (this keeps the
kernel from unfolding the pullback functors). -/
noncomputable def upperStarZeroArtinSchreierIso (a : k₀) :
    (WeilSheaf.upperStar (affineLine.zero k₀)).obj (artinSchreier ψ a) ≅
      (WeilSheaf.upperStar (affineLine.zero k₀)).obj
        ((WeilSheaf.upperStar (affineLine.smul k₀ a)).obj
          (image (WeilSheaf.artinSchreierIdempotent ψ))) :=
  eqToIso (congrArg (WeilSheaf.upperStar (affineLine.zero k₀)).obj
    (artinSchreier_eq_upperStar_image ψ a))

/-- The trivialization `0^* [a]^* ℒ_ψ ≅ 0^* ℒ_ψ ≅ ℚ̄_ℓ`, as `a · 0 = 0` and `AS(0) = 0`. -/
noncomputable def upperStarZeroUpperStarSMulArtinSchreierImageIso (a : k₀) :
    (WeilSheaf.upperStar (affineLine.zero k₀)).obj
        ((WeilSheaf.upperStar (affineLine.smul k₀ a)).obj
          (image (WeilSheaf.artinSchreierIdempotent ψ))) ≅
      WeilSheaf.adicConstant k₀ l (Spec (CommRingCat.of k₀)) :=
  WeilSheaf.upperStarUpperStarIsoOfComp (affineLine.zero k₀) (affineLine.smul k₀ a)
      (affineLine.zero k₀) (affineLine.zero_comp_smul a)
      (image (WeilSheaf.artinSchreierIdempotent ψ)) ≪≫
    WeilSheaf.upperStarArtinSchreierImageIso ψ (affineLine.zero k₀)
      affineLine.zero_comp_artinSchreierMap

/-- **The specified trivialization at zero** of the Artin–Schreier sheaf `ℒ_{ψ(a x)}`:
`0^* ℒ_{ψ(a x)} ≅ 0^* ℒ_ψ ≅ ℚ̄_ℓ`, through the root `u = 0` of `u^q - u = 0` over `x = 0`
(blueprint `lemma-artin-schreier-character-sheaf`). -/
noncomputable def artinSchreierZeroIso (a : k₀) :
    (WeilSheaf.upperStar (affineLine.zero k₀)).obj (artinSchreier ψ a) ≅
      WeilSheaf.adicConstant k₀ l (Spec (CommRingCat.of k₀)) :=
  upperStarZeroArtinSchreierIso ψ a ≪≫ upperStarZeroUpperStarSMulArtinSchreierImageIso ψ a

/-- The trivialization of the Artin–Schreier sheaf `ℒ_{ψ,f}` at a rational point `x` at which
`f` vanishes: `x^* ℒ_{ψ,f} ≅ 0^* ℒ_ψ ≅ ℚ̄_ℓ`, induced by the specified trivialization at zero
`AlgebraicGeometry.artinSchreierZeroIso` (blueprint `lemma-artin-schreier-character-sheaf`). -/
noncomputable def artinSchreierOfTrivialization {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] (f : Γ(X, ⊤)) (x : Spec (CommRingCat.of k₀) ⟶ X)
    [x.IsOver (Spec (CommRingCat.of k₀))] (hf : x.appTop f = 0) :
    (WeilSheaf.upperStar x).obj (artinSchreierOf ψ f) ≅
      WeilSheaf.adicConstant k₀ l (Spec (CommRingCat.of k₀)) :=
  eqToIso (congrArg (WeilSheaf.upperStar x).obj (artinSchreierOf_eq ψ f)) ≪≫
    WeilSheaf.upperStarUpperStarIsoOfComp x (affineLine.homOfSection k₀ f) (affineLine.zero k₀)
      (affineLine.comp_homOfSection_eq_zero x hf) (artinSchreier ψ 1) ≪≫
    artinSchreierZeroIso ψ 1

end Trivialization

section Scalar

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- Multiplication by a scalar commutes with morphisms of Weil sheaves. -/
@[reassoc]
lemma WeilSheaf.smulEnd_comp (b : PadicAlgCl l) {F G : WeilSheaf k₀ l X} (f : F ⟶ G) :
    WeilSheaf.smulEnd b F ≫ f = f ≫ WeilSheaf.smulEnd b G :=
  ObjectProperty.hom_ext _ (ProEtaleWeilSheaf.smulEnd_comp b f.hom)

/-- Multiplication by scalars on a Weil sheaf is multiplicative in the scalar. -/
lemma WeilSheaf.smulEnd_smulEnd (b c : PadicAlgCl l) (F : WeilSheaf k₀ l X) :
    WeilSheaf.smulEnd b F ≫ WeilSheaf.smulEnd c F = WeilSheaf.smulEnd (c * b) F :=
  ObjectProperty.hom_ext _ (ProEtaleWeilSheaf.smulEnd_smulEnd b c F.obj)

/-- Multiplication by `1` on a Weil sheaf is the identity. -/
lemma WeilSheaf.smulEnd_one (F : WeilSheaf k₀ l X) : WeilSheaf.smulEnd 1 F = 𝟙 F :=
  ObjectProperty.hom_ext _ (ProEtaleWeilSheaf.smulEnd_one F.obj)

/-- The pullback of Weil sheaves commutes with multiplication by a scalar. -/
lemma WeilSheaf.upperStar_map_smulEnd {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k₀))]
    (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))] (b : PadicAlgCl l)
    (F : WeilSheaf k₀ l Y) :
    (WeilSheaf.upperStar φ).map (WeilSheaf.smulEnd b F) =
      WeilSheaf.smulEnd b ((WeilSheaf.upperStar φ).obj F) :=
  ObjectProperty.hom_ext _ (ProEtaleWeilSheaf.upperStar_map_smulEnd φ b F.obj)

omit [Finite k₀] in
/-- The geometric fiber `Spec k₀ ×_{Spec k₀} Spec k̄` of the point `Spec k₀` has at most one
point. -/
lemma Scheme.Hom.subsingleton_geometricFiber_spec :
    Subsingleton (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀)).geometricFiber := by
  have : IsIso (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀)) :=
    inferInstanceAs (IsIso (𝟙 _))
  have : Subsingleton (Scheme.specAlgebraicClosure k₀).left :=
    inferInstanceAs (Subsingleton (PrimeSpectrum (AlgebraicClosure k₀)))
  exact (pullback.snd (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀))
    (Scheme.specAlgebraicClosure k₀).hom).isOpenEmbedding.injective.subsingleton

/-- Every endomorphism of the constant Weil sheaf `ℚ̄_ℓ` on `Spec k₀` is the multiplication by a
scalar. -/
lemma WeilSheaf.exists_eq_smulEnd_adicConstant_spec
    (φ : WeilSheaf.adicConstant k₀ l (Spec (CommRingCat.of k₀)) ⟶
      WeilSheaf.adicConstant k₀ l (Spec (CommRingCat.of k₀))) :
    ∃ c : PadicAlgCl l, φ = WeilSheaf.smulEnd c _ := by
  have := Scheme.Hom.subsingleton_geometricFiber_spec (k₀ := k₀)
  obtain ⟨c, hc⟩ := ProEtale.AdicSheaf.exists_eq_smul_unit
    (V := (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀)).geometricFiber) φ.hom.hom.f
  exact ⟨c, ObjectProperty.hom_ext _ (ObjectProperty.hom_ext _ (Endofunctor.Algebra.Hom.ext hc))⟩

/-- Distinct scalars act differently on the constant Weil sheaf `ℚ̄_ℓ` on `Spec k₀`. -/
lemma WeilSheaf.eq_of_smulEnd_adicConstant_spec_eq {c d : PadicAlgCl l}
    (h : WeilSheaf.smulEnd c (WeilSheaf.adicConstant k₀ l (Spec (CommRingCat.of k₀))) =
      WeilSheaf.smulEnd d _) : c = d := by
  obtain ⟨x⟩ := Scheme.Hom.nonempty_geometricFiber k₀ (Spec (CommRingCat.of k₀))
  have hs (b : PadicAlgCl l) :
      (ProEtale.AdicSheaf.unitEndFun (WeilSheaf.smulEnd b
        (WeilSheaf.adicConstant k₀ l (Spec (CommRingCat.of k₀)))).hom.hom.f).1 x = b := by
    change b * 1 = b
    exact mul_one b
  rw [← hs c, ← hs d, h]

/-- An automorphism of the restriction `x^* B` of a Weil sheaf `B` to a rational point `x`, at
which `B` is trivial, is the restriction of an automorphism of `B`: it is the multiplication by a
scalar. -/
lemma WeilSheaf.exists_upperStar_mapIso_eq (x : Spec (CommRingCat.of k₀) ⟶ X)
    [x.IsOver (Spec (CommRingCat.of k₀))] {B : WeilSheaf k₀ l X}
    (τ : (WeilSheaf.upperStar x).obj B ≅ WeilSheaf.adicConstant k₀ l (Spec (CommRingCat.of k₀)))
    (e : (WeilSheaf.upperStar x).obj B ≅ (WeilSheaf.upperStar x).obj B) :
    ∃ α : B ≅ B, (WeilSheaf.upperStar x).mapIso α = e := by
  obtain ⟨c, hc⟩ := WeilSheaf.exists_eq_smulEnd_adicConstant_spec (τ.inv ≫ e.hom ≫ τ.hom)
  obtain ⟨c', hc'⟩ := WeilSheaf.exists_eq_smulEnd_adicConstant_spec (τ.inv ≫ e.inv ≫ τ.hom)
  have he : e.hom = WeilSheaf.smulEnd c _ := by
    calc e.hom = τ.hom ≫ (τ.inv ≫ e.hom ≫ τ.hom) ≫ τ.inv := by simp
      _ = WeilSheaf.smulEnd c _ := by
        rw [hc, ← WeilSheaf.smulEnd_comp_assoc, Iso.hom_inv_id, Category.comp_id]
  have hcc : c' * c = 1 := by
    refine WeilSheaf.eq_of_smulEnd_adicConstant_spec_eq (k₀ := k₀) (l := l) ?_
    rw [← WeilSheaf.smulEnd_smulEnd, ← hc, ← hc', WeilSheaf.smulEnd_one]
    simp
  refine ⟨⟨WeilSheaf.smulEnd c B, WeilSheaf.smulEnd c' B, ?_, ?_⟩, ?_⟩
  · rw [WeilSheaf.smulEnd_smulEnd, hcc, WeilSheaf.smulEnd_one]
  · rw [WeilSheaf.smulEnd_smulEnd, mul_comm, hcc, WeilSheaf.smulEnd_one]
  · ext1
    rw [Functor.mapIso_hom, WeilSheaf.upperStar_map_smulEnd, he]

/-- Any isomorphism `μ₀ : A ≅ B` can be corrected by an automorphism of `B` so that its
restriction to a rational point `x`, at which `B` is trivial, is a given isomorphism. -/
lemma WeilSheaf.exists_iso_upperStar_mapIso_eq (x : Spec (CommRingCat.of k₀) ⟶ X)
    [x.IsOver (Spec (CommRingCat.of k₀))] {A B : WeilSheaf k₀ l X}
    (τ : (WeilSheaf.upperStar x).obj B ≅ WeilSheaf.adicConstant k₀ l (Spec (CommRingCat.of k₀)))
    (μ₀ : A ≅ B) (R : (WeilSheaf.upperStar x).obj A ≅ (WeilSheaf.upperStar x).obj B) :
    ∃ μ : A ≅ B, (WeilSheaf.upperStar x).mapIso μ = R := by
  obtain ⟨α, hα⟩ := WeilSheaf.exists_upperStar_mapIso_eq x τ
    (((WeilSheaf.upperStar x).mapIso μ₀).symm ≪≫ R)
  exact ⟨μ₀ ≪≫ α, by rw [Functor.mapIso_trans, hα, Iso.self_symm_id_assoc]⟩

end Scalar

section Compatibility

variable (ψ : AddChar k₀ (PadicAlgCl l))

/-- **The multiplication isomorphism respects the trivializations at zero**
(blueprint `lemma-artin-schreier-character-sheaf--4`). For global functions `f, g` on `X` and a
rational point `x` at which both vanish, there is an isomorphism
`μ : ℒ_{ψ,f} ⊗ ℒ_{ψ,g} ≅ ℒ_{ψ,f+g}` whose pullback to `x`, read through the canonical
isomorphism `x^* (ℒ_{ψ,f} ⊗ ℒ_{ψ,g}) ≅ x^* ℒ_{ψ,f} ⊗ x^* ℒ_{ψ,g}` and the specified
trivializations `x^* ℒ_{ψ,h} ≅ ℚ̄_ℓ` (`AlgebraicGeometry.artinSchreierOfTrivialization`), is
the unit isomorphism `ℚ̄_ℓ ⊗ ℚ̄_ℓ ≅ ℚ̄_ℓ`. For `X = 𝔸²`, `f = x₁`, `g = x₂` and `x = (0, 0)`,
this is the statement that `m^* ℒ_ψ ≅ pr₁^* ℒ_ψ ⊗ pr₂^* ℒ_ψ` respects the trivializations at
zero: the root `0` over `0` of the Artin–Schreier cover is sent to `0 + 0 = 0`. -/
theorem exists_iso_tensorObj_artinSchreierOf_compatible {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    (f g : Γ(X, ⊤)) (x : Spec (CommRingCat.of k₀) ⟶ X) [x.IsOver (Spec (CommRingCat.of k₀))]
    (hf : x.appTop f = 0) (hg : x.appTop g = 0) :
    ∃ μ : (artinSchreierOf ψ f).tensorObj (artinSchreierOf ψ g) (isLisse_artinSchreierOf ψ f) ≅
        artinSchreierOf ψ (f + g),
      (WeilSheaf.upperStar x).mapIso μ =
        WeilSheaf.upperStarTensorObjIso x _ _ (isLisse_artinSchreierOf ψ f) ≪≫
          WeilSheaf.tensorObjIsoOfIso (artinSchreierOfTrivialization ψ f x hf)
            (artinSchreierOfTrivialization ψ g x hg) _
            (WeilSheaf.isLisse_adicConstant k₀ l _) ≪≫
          WeilSheaf.adicConstantTensorObjIso _ ≪≫
          (artinSchreierOfTrivialization ψ (f + g) x (by rw [map_add, hf, hg, add_zero])).symm := by
  obtain ⟨μ₀⟩ := nonempty_iso_tensorObj_artinSchreierOf ψ f g
  exact WeilSheaf.exists_iso_upperStar_mapIso_eq x
    (artinSchreierOfTrivialization ψ (f + g) x (by rw [map_add, hf, hg, add_zero])) μ₀ _

/-- **The duality isomorphism respects the trivializations at zero**
(blueprint `lemma-artin-schreier-character-sheaf--5`). There is an isomorphism
`δ : ℒ_{ψ(a x)}^∨ ≅ ℒ_{ψ⁻¹(a x)}` whose pullback to the origin, read through the canonical
isomorphism `0^* (ℒ^∨) ≅ (0^* ℒ)^∨` and the specified trivializations at zero
(`AlgebraicGeometry.artinSchreierZeroIso`) of `ℒ_{ψ(a x)}` and `ℒ_{ψ⁻¹(a x)}`, is the canonical
isomorphism `ℚ̄_ℓ^∨ ≅ ℚ̄_ℓ`. -/
theorem exists_iso_dual_artinSchreier_compatible (a : k₀) :
    ∃ δ : (artinSchreier ψ a).dual (isLisse_artinSchreier ψ a) ≅ artinSchreier ψ⁻¹ a,
      (WeilSheaf.upperStar (affineLine.zero k₀)).mapIso δ =
        (WeilSheaf.upperStarDualIso (affineLine.zero k₀) _ (isLisse_artinSchreier ψ a)).symm ≪≫
          WeilSheaf.dualIsoOfIso (artinSchreierZeroIso ψ a) _
            (WeilSheaf.isLisse_adicConstant k₀ l _) ≪≫
          WeilSheaf.dualAdicConstantIso ≪≫ (artinSchreierZeroIso ψ⁻¹ a).symm := by
  obtain ⟨δ₀⟩ := nonempty_iso_dual_artinSchreier ψ a
  exact WeilSheaf.exists_iso_upperStar_mapIso_eq (affineLine.zero k₀)
    (artinSchreierZeroIso ψ⁻¹ a) δ₀ _

end Compatibility

end AlgebraicGeometry
