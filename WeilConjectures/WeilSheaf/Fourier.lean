/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Group.AddChar
public import WeilConjectures.AlgebraicGeometry.AffineSpace.ArtinSchreier
public import WeilConjectures.WeilSheaf.Tensor

/-!
# Artin–Schreier sheaves and the Fourier–Deligne transform

Let `k₀` be a finite field with `q` elements and `ψ` an additive character of `k₀` with values
in `ℚ̄_ℓ`. The Artin–Schreier map `AS : 𝔸¹ ⟶ 𝔸¹`, `x ↦ x^q - x`, is a finite étale torsor
under `k₀`, acting by the translations `σ_c : x ↦ x + c`; it is defined over `k₀`, so the
pushforward `AS_* ℚ̄_ℓ` of the constant Weil sheaf is a Weil sheaf, and each `σ_c`, satisfying
`σ_c ≫ AS = AS`, acts on it by a morphism of Weil sheaves
(`AlgebraicGeometry.WeilSheaf.artinSchreierTranslationAction`). The *Artin–Schreier sheaf*
`ℒ_ψ` is the image of the idempotent `e_ψ = q⁻¹ ∑_{c ∈ k₀} ψ(-c) σ_c` of `AS_* ℚ̄_ℓ`, its
`ψ`-isotypic component, and `ℒ_{ψ(a x)}` is its pullback along `x ↦ a x`
(`AlgebraicGeometry.artinSchreier`). It is lisse of rank one and pure of weight zero.

The *Fourier–Deligne transform* of a Weil complex `K` on the affine line is

`FT_ψ(K) = Rpr₂!(pr₁^* K ⊗ μ^* ℒ_ψ)[1]`,

where `pr₁, pr₂ : 𝔸¹ ×_{k₀} 𝔸¹ ⟶ 𝔸¹` are the projections and `μ` is the multiplication
(`AlgebraicGeometry.fourierTransform`), with Laumon's shift by the relative dimension one. The
tensor product with the lisse kernel `μ^* ℒ_ψ` is the internal hom out of its dual,
derived on the category of pro-étale Weil sheaves (`AlgebraicGeometry.WeilComplex.ihomLisse`).

## Main declarations

- `AlgebraicGeometry.WeilSheaf.artinSchreierPushforward`: `AS_* ℚ̄_ℓ`, with the translation
  action `AlgebraicGeometry.WeilSheaf.artinSchreierTranslationAction`.
- `AlgebraicGeometry.artinSchreier` and `AlgebraicGeometry.fourierTransform`: the
  Artin–Schreier sheaves and the Fourier–Deligne transform of the affine line.
- `AlgebraicGeometry.WeilSheaf.HasLinearArtinSchreierConstituent`: a geometric linear
  Artin–Schreier sheaf is a constituent of the geometric restriction of a Weil sheaf.

## Implementation notes

The compatibility of the translation action with the Weil structure of `AS_* ℚ̄_ℓ`, the
compatibility of the internal hom of pro-étale Weil sheaves with morphisms in the second
variable, and the constructibility statements which make the transforms land in Weil complexes
are stated as separate lemmas with `sorry`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor MonoidalCategory

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry

open scoped ProEtale

section AffineLine

variable (k₀ : Type u) [Field k₀] [Finite k₀]

/-- The Artin–Schreier map `AS : x ↦ x^q - x` of the affine line over `k₀`, `q = #k₀`, the Lang
isogeny of the additive group. -/
noncomputable def affineLine.artinSchreierMap : affineLine k₀ ⟶ affineLine k₀ :=
  letI := Fintype.ofFinite k₀
  AffineSpace.artinSchreierMap PUnit (Spec (CommRingCat.of k₀)) (Fintype.card k₀)

instance : (affineLine.artinSchreierMap k₀).IsOver (Spec (CommRingCat.of k₀)) :=
  ⟨AffineSpace.artinSchreierMap_over _ _ _⟩

instance : IsFinite (affineLine.artinSchreierMap k₀) := by
  let := Fintype.ofFinite k₀
  exact AffineSpace.isFinite_artinSchreierMap _ _ Fintype.one_lt_card.ne'

/-- The translation `σ_c : x ↦ x + c` of the affine line over `k₀` by `c ∈ k₀`. -/
noncomputable def affineLine.translation (c : k₀) : affineLine k₀ ⟶ affineLine k₀ :=
  AffineSpace.translation fun _ ↦ (Scheme.ΓSpecIso (.of k₀)).inv.hom c

instance (c : k₀) : (affineLine.translation k₀ c).IsOver (Spec (CommRingCat.of k₀)) :=
  ⟨AffineSpace.translation_over _⟩

lemma affineLine.translation_add (c d : k₀) :
    affineLine.translation k₀ (c + d) =
      affineLine.translation k₀ c ≫ affineLine.translation k₀ d := by
  simp only [affineLine.translation, map_add]
  exact AffineSpace.translation_add _ _

lemma affineLine.translation_zero : affineLine.translation k₀ 0 = 𝟙 _ := by
  simp only [affineLine.translation, map_zero]
  exact AffineSpace.translation_zero

@[reassoc]
lemma affineLine.translation_comp_translation_neg (c : k₀) :
    affineLine.translation k₀ c ≫ affineLine.translation k₀ (-c) = 𝟙 _ := by
  rw [← affineLine.translation_add, add_neg_cancel, affineLine.translation_zero]

@[reassoc]
lemma affineLine.translation_neg_comp_translation (c : k₀) :
    affineLine.translation k₀ (-c) ≫ affineLine.translation k₀ c = 𝟙 _ := by
  rw [← affineLine.translation_add, neg_add_cancel, affineLine.translation_zero]

@[reassoc]
lemma affineLine.translation_comp_artinSchreierMap (c : k₀) :
    affineLine.translation k₀ c ≫ affineLine.artinSchreierMap k₀ =
      affineLine.artinSchreierMap k₀ := by
  let := Fintype.ofFinite k₀
  exact AffineSpace.translation_comp_artinSchreierMap_of_finiteField k₀ _ fun _ ↦ c

/-- The multiplication `x ↦ a x` of the affine line over `k₀` by `a ∈ k₀`. -/
noncomputable def affineLine.smul (a : k₀) : affineLine k₀ ⟶ affineLine k₀ :=
  AffineSpace.smul PUnit (Spec (CommRingCat.of k₀)) ((Scheme.ΓSpecIso (.of k₀)).inv.hom a)

instance (a : k₀) : (affineLine.smul k₀ a).IsOver (Spec (CommRingCat.of k₀)) :=
  ⟨AffineSpace.smul_over _ _ _⟩

/-- The translation `σ_c` of the geometric affine line `𝔸¹_{k̄}`, the base change of the
translation of `𝔸¹_{k₀}`, as an automorphism. -/
noncomputable def affineLine.geometricTranslationIso (c : k₀) :
    (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber ≅
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber where
  hom := Scheme.Hom.geometricFiberMap (affineLine.translation k₀ c)
    (comp_over (affineLine.translation k₀ c) (Spec (CommRingCat.of k₀)))
  inv := Scheme.Hom.geometricFiberMap (affineLine.translation k₀ (-c))
    (comp_over (affineLine.translation k₀ (-c)) (Spec (CommRingCat.of k₀)))
  hom_inv_id := Scheme.Hom.geometricFiber_hom_ext _
    (by rw [Category.assoc, Scheme.Hom.geometricFiberMap_comp_geometricFiberProj,
      Scheme.Hom.geometricFiberMap_comp_geometricFiberProj_assoc,
      affineLine.translation_comp_translation_neg, Category.comp_id, Category.id_comp])
    (by simp)
  inv_hom_id := Scheme.Hom.geometricFiber_hom_ext _
    (by rw [Category.assoc, Scheme.Hom.geometricFiberMap_comp_geometricFiberProj,
      Scheme.Hom.geometricFiberMap_comp_geometricFiberProj_assoc,
      affineLine.translation_neg_comp_translation, Category.comp_id, Category.id_comp])
    (by simp)

/-- The base change `ĀS : 𝔸¹_{k̄} ⟶ 𝔸¹_{k̄}` of the Artin–Schreier map to `k̄`. -/
noncomputable abbrev affineLine.geometricArtinSchreierMap :
    (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber ⟶
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
  Scheme.Hom.geometricFiberMap (affineLine.artinSchreierMap k₀)
    (comp_over (affineLine.artinSchreierMap k₀) (Spec (CommRingCat.of k₀)))

/-- The base change of `σ_c ≫ AS = AS` to `k̄`. -/
lemma affineLine.geometricTranslation_comp_artinSchreierMap (c : k₀) :
    (affineLine.geometricTranslationIso k₀ c).hom ≫ affineLine.geometricArtinSchreierMap k₀ =
      affineLine.geometricArtinSchreierMap k₀ :=
  Scheme.Hom.geometricFiber_hom_ext _
    (by rw [affineLine.geometricTranslationIso, affineLine.geometricArtinSchreierMap,
      Category.assoc,
      Scheme.Hom.geometricFiberMap_comp_geometricFiberProj,
      Scheme.Hom.geometricFiberMap_comp_geometricFiberProj_assoc,
      affineLine.translation_comp_artinSchreierMap])
    (by simp [affineLine.geometricTranslationIso, affineLine.geometricArtinSchreierMap])

end AffineLine

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]

section Scalar

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- Multiplication by a scalar `b ∈ ℚ̄_ℓ` commutes with the Weil structure of a Weil sheaf: the
Frobenius pullback, a pushforward, is `ℚ̄_ℓ`-linear. -/
lemma WeilSheaf.smul_comm_str (b : PadicAlgCl l) (F : WeilSheaf k₀ l X) :
    (WeilSheaf.frobeniusPullback k₀ l X).map
        (ObjectProperty.homMk (ULift.up b • 𝟙 F.obj.carrier.obj)) ≫ F.obj.obj.str =
      F.obj.obj.str ≫ ObjectProperty.homMk (ULift.up b • 𝟙 F.obj.carrier.obj) :=
  sorry

/-- Multiplication by a scalar `b ∈ ℚ̄_ℓ`, as an endomorphism of a Weil sheaf. -/
noncomputable def WeilSheaf.smulEnd (b : PadicAlgCl l) (F : WeilSheaf k₀ l X) : F ⟶ F :=
  ObjectProperty.homMk (ObjectProperty.homMk
    ⟨ObjectProperty.homMk (ULift.up b • 𝟙 F.obj.carrier.obj), WeilSheaf.smul_comm_str b F⟩)

end Scalar

section ArtinSchreier

variable (k₀ l) in
/-- The pushforward `AS_* ℚ̄_ℓ` of the constant Weil sheaf along the Artin–Schreier map, a
Weil sheaf of rank `q` on the affine line. -/
noncomputable def WeilSheaf.artinSchreierPushforward : WeilSheaf k₀ l (affineLine k₀) :=
  (WeilSheaf.lowerStar (affineLine.artinSchreierMap k₀)).obj
    (WeilSheaf.adicConstant k₀ l (affineLine k₀))

variable (l) in
/-- The action of the translation `σ_c` on the underlying sheaf `ĀS_* ℚ̄_ℓ` of
`AS_* ℚ̄_ℓ`, pulling back sections along `σ_c` and using `σ_c ≫ AS = AS`:
```
ĀS_* ℚ̄_ℓ ⟶ ĀS_* σ̄_c* ℚ̄_ℓ ≅ (σ̄_c ≫ ĀS)_* ℚ̄_ℓ = ĀS_* ℚ̄_ℓ
```
-/
noncomputable def artinSchreierTranslationSheafHom (c : k₀) :
    (affineLine.geometricArtinSchreierMap k₀)_*[
        WeilCoefficients.{u} l].obj
      (ProEtale.adicConstantSheaf l (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber) ⟶
    (affineLine.geometricArtinSchreierMap k₀)_*[
        WeilCoefficients.{u} l].obj
      (ProEtale.adicConstantSheaf l (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber) :=
  (affineLine.geometricArtinSchreierMap k₀)_*[
      WeilCoefficients.{u} l].map
      (ProEtale.adicConstantSheafLowerStarIso l (affineLine.geometricTranslationIso k₀ c)).inv ≫
    (ProEtale.lowerStarComp (WeilCoefficients.{u} l) (affineLine.geometricTranslationIso k₀ c).hom
      (affineLine.geometricArtinSchreierMap k₀)).hom.app
      (ProEtale.adicConstantSheaf l (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber) ≫
    (ProEtale.lowerStarCongr (WeilCoefficients.{u} l)
      (affineLine.geometricTranslation_comp_artinSchreierMap k₀ c)).hom.app
      (ProEtale.adicConstantSheaf l (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber)

/-- The action of `σ_c` on `AS_* ℚ̄_ℓ` commutes with its Weil structure: the translation and
the Artin–Schreier map are defined over `k₀`, hence commute with the geometric Frobenius. -/
lemma artinSchreierTranslationSheafHom_comm (c : k₀) :
    (WeilSheaf.frobeniusPullback k₀ l (affineLine k₀)).map
        (artinSchreierTranslationSheafHom l c) ≫
      (WeilSheaf.artinSchreierPushforward k₀ l).obj.obj.str =
    (WeilSheaf.artinSchreierPushforward k₀ l).obj.obj.str ≫
      artinSchreierTranslationSheafHom l c :=
  sorry

variable (l) in
/-- The action of the translation `σ_c : x ↦ x + c` on `AS_* ℚ̄_ℓ`, as an endomorphism of Weil
sheaves. -/
noncomputable def WeilSheaf.artinSchreierTranslationAction (c : k₀) :
    WeilSheaf.artinSchreierPushforward k₀ l ⟶ WeilSheaf.artinSchreierPushforward k₀ l :=
  ObjectProperty.homMk (ObjectProperty.homMk
    ⟨artinSchreierTranslationSheafHom l c, artinSchreierTranslationSheafHom_comm c⟩)

/-- The endomorphism `e_ψ = q⁻¹ ∑_{c ∈ k₀} ψ(-c) σ_c` of `AS_* ℚ̄_ℓ`, `q = #k₀`, the projector
onto the `ψ`-isotypic component. -/
noncomputable def WeilSheaf.artinSchreierIdempotent (ψ : AddChar k₀ (PadicAlgCl l)) :
    WeilSheaf.artinSchreierPushforward k₀ l ⟶ WeilSheaf.artinSchreierPushforward k₀ l :=
  letI := Fintype.ofFinite k₀
  ∑ c : k₀, WeilSheaf.smulEnd ((Nat.card k₀ : PadicAlgCl l)⁻¹ * ψ (-c)) _ ≫
    WeilSheaf.artinSchreierTranslationAction l c

-- TODO(unify): sk-def-as
/-- The Artin–Schreier sheaf `ℒ_{ψ(a x)}` on the affine line: the pullback along `x ↦ a x` of
the `ψ`-isotypic component `ℒ_ψ` of the pushforward of the constant sheaf along the
Artin–Schreier cover `u^q - u = x`, which is Galois over the line with group `k₀`, so that its
isotypic components are indexed by the additive characters of `k₀`. The component `ℒ_ψ` is the
image of the projector `e_ψ` (`AlgebraicGeometry.WeilSheaf.artinSchreierIdempotent`). It is
lisse of rank one and of weight zero. -/
noncomputable def artinSchreier (ψ : AddChar k₀ (PadicAlgCl l)) (a : k₀) :
    WeilSheaf k₀ l (affineLine k₀) :=
  (WeilSheaf.upperStar (affineLine.smul k₀ a)).obj (image (WeilSheaf.artinSchreierIdempotent ψ))

/-- The Artin–Schreier sheaves are lisse: `ℒ_ψ` is a direct summand of the finite étale
pushforward `AS_* ℚ̄_ℓ`, which is lisse, and pullback preserves lisse sheaves. -/
theorem isLisse_artinSchreier (ψ : AddChar k₀ (PadicAlgCl l)) (a : k₀) :
    (artinSchreier ψ a).IsLisse :=
  sorry

end ArtinSchreier

section Constituent

variable (k₀) in
/-- The multiplication `x ↦ a x` of the geometric affine line `𝔸¹_{k̄}` by `a ∈ k̄`. It is
defined over `k̄`, not over `k₀`, and has no Frobenius structure. -/
noncomputable def affineLine.geometricSMul (a : AlgebraicClosure k₀) :
    (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber ⟶
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
  pullback.lift
    (AffineSpace.homOfVector
      ((affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure ≫
        (Scheme.specAlgebraicClosure k₀).hom)
      fun _ ↦ (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure.appTop
          ((Scheme.ΓSpecIso (.of (AlgebraicClosure k₀))).inv.hom a) *
        (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberProj.appTop
          (AffineSpace.coord _ PUnit.unit))
    (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure
    (AffineSpace.homOfVector_over _ _)

variable {U : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]

-- TODO(unify): sk-d-real-operations
/-- `F.HasLinearArtinSchreierConstituent ψ a j` says that the restriction along `j : U ⟶ 𝔸¹` of
the geometric linear Artin–Schreier sheaf `ℒ_{ψ(a x)}`, for `a` in the algebraic closure of
`k₀`, is a constituent of the pullback of `F` to `U ⊗_{k₀} k̄`: a subquotient of the
underlying sheaf of `F` on `Ū`. The geometric sheaf `ℒ_{ψ(a x)}` is the pullback of the
underlying sheaf of `ℒ_ψ` along the multiplication `x ↦ a x` of `𝔸¹_{k̄}`
(`AlgebraicGeometry.affineLine.geometricSMul`); it is defined over the finite subextension
`k₀(a)`, where it is `AlgebraicGeometry.artinSchreier` for the character `ψ ∘ Tr`, but only its
pullback to the geometric affine line is used here. Being lisse of rank one, it is irreducible,
so a subquotient isomorphic to it is an irreducible constituent. -/
def WeilSheaf.HasLinearArtinSchreierConstituent (F : WeilSheaf k₀ l U)
    (ψ : AddChar k₀ (PadicAlgCl l)) (a : AlgebraicClosure k₀) (j : U ⟶ affineLine k₀)
    [j.IsOver (Spec (CommRingCat.of k₀))] : Prop :=
  ∃ (B : Sheaf (Scheme.ProEt.topology (U ↘ Spec (CommRingCat.of k₀)).geometricFiber)
      (WeilCoefficients.{u} l)) (i : B ⟶ F.obj.carrier)
    (p : B ⟶ (Scheme.Hom.geometricFiberMap j (comp_over j _))^*[WeilCoefficients.{u} l].obj
      ((affineLine.geometricSMul k₀ a)^*[WeilCoefficients.{u} l].obj
        (artinSchreier ψ 1).obj.carrier)), Mono i ∧ Epi p

end Constituent

section Fourier

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

variable (k₀ l X) in
/-- The internal hom `B ↦ [A, B]` out of a fixed pro-étale Weil sheaf, as a functor. -/
noncomputable def ProEtaleWeilSheaf.ihomFunctor (A : ProEtaleWeilSheaf k₀ l X) :
    ProEtaleWeilSheaf k₀ l X ⥤ ProEtaleWeilSheaf k₀ l X where
  obj B := ProEtaleWeilSheaf.ihom k₀ l X A B
  map f := ObjectProperty.homMk ⟨(CategoryTheory.ihom A.carrier).map f.hom.f,
    ProEtaleWeilSheaf.ihom_map_comm A f⟩
  map_id _ := ObjectProperty.hom_ext _ (Algebra.Hom.ext ((CategoryTheory.ihom A.carrier).map_id _))
  map_comp _ _ := ObjectProperty.hom_ext _
    (Algebra.Hom.ext ((CategoryTheory.ihom A.carrier).map_comp _ _))

instance (A : ProEtaleWeilSheaf k₀ l X) : (ProEtaleWeilSheaf.ihomFunctor k₀ l X A).Additive :=
  have := (ihom.adjunction A.carrier).right_adjoint_additive
  ⟨ObjectProperty.hom_ext _ (Algebra.Hom.ext (CategoryTheory.ihom A.carrier).map_add)⟩

/-- **Finiteness for the tensor product with a lisse Weil sheaf.** For a lisse Weil sheaf `F`,
the right derived functor of `[F, -]` on pro-étale Weil sheaves carries Weil complexes to Weil
complexes: on complexes with constructible cohomology it is the tensor product with the lisse
dual `F^∨`, which is exact and preserves constructibility. -/
theorem WeilComplex.objectProperty_rightDerivedFunctor_ihomFunctor (F : WeilSheaf k₀ l X)
    (hF : F.IsLisse) (K : _root_.DerivedCategory (ProEtaleWeilSheaf k₀ l X))
    (hK : WeilComplex.objectProperty k₀ l X K) :
    WeilComplex.objectProperty k₀ l X
      ((ProEtaleWeilSheaf.ihomFunctor k₀ l X F.obj).rightDerivedFunctor.obj K) :=
  sorry

/-- The derived internal hom `R[F, -]` out of a lisse Weil sheaf `F`, on Weil complexes. -/
noncomputable def WeilComplex.ihomLisse (F : WeilSheaf k₀ l X) (hF : F.IsLisse) :
    WeilComplex k₀ l X ⥤ WeilComplex k₀ l X :=
  (WeilComplex.objectProperty k₀ l X).liftFullSubcategory (WeilComplex.objectProperty k₀ l X)
    (ProEtaleWeilSheaf.ihomFunctor k₀ l X F.obj).rightDerivedFunctor
    (WeilComplex.objectProperty_rightDerivedFunctor_ihomFunctor F hF)

instance (F : WeilSheaf k₀ l X) (hF : F.IsLisse) : (WeilComplex.ihomLisse F hF).Additive :=
  ObjectProperty.liftFullSubcategory_additive _ _ _ _

/-- The tensor product `G ⊗ -` with a lisse Weil sheaf `G`, on Weil complexes: the derived
internal hom out of the dual `G^∨`, `G` being locally free of finite rank over `ℚ̄_ℓ,X̄`. -/
noncomputable def WeilComplex.tensorLisse (G : WeilSheaf k₀ l X) (hG : G.IsLisse) :
    WeilComplex k₀ l X ⥤ WeilComplex k₀ l X :=
  WeilComplex.ihomLisse (G.dual hG) hG.dual

instance (G : WeilSheaf k₀ l X) (hG : G.IsLisse) : (WeilComplex.tensorLisse G hG).Additive := by
  unfold WeilComplex.tensorLisse
  infer_instance

variable (k₀) in
/-- The affine plane `𝔸¹ ×_{k₀} 𝔸¹` over `k₀`, with its two projections and the multiplication
map to the affine line. -/
noncomputable def affinePlane : Scheme.{u} :=
  pullback (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) (affineLine k₀ ↘ Spec (CommRingCat.of k₀))

noncomputable instance : (affinePlane k₀).Over (Spec (CommRingCat.of k₀)) :=
  ⟨pullback.fst _ _ ≫ affineLine k₀ ↘ Spec (CommRingCat.of k₀)⟩

variable (k₀) in
/-- The first projection `pr₁ : 𝔸¹ ×_{k₀} 𝔸¹ ⟶ 𝔸¹`. -/
noncomputable def affinePlane.fst : affinePlane k₀ ⟶ affineLine k₀ :=
  pullback.fst _ _

variable (k₀) in
/-- The second projection `pr₂ : 𝔸¹ ×_{k₀} 𝔸¹ ⟶ 𝔸¹`. -/
noncomputable def affinePlane.snd : affinePlane k₀ ⟶ affineLine k₀ :=
  pullback.snd _ _

instance : (affinePlane.fst k₀).IsOver (Spec (CommRingCat.of k₀)) :=
  ⟨rfl⟩

instance : (affinePlane.snd k₀).IsOver (Spec (CommRingCat.of k₀)) :=
  ⟨pullback.condition.symm⟩

instance : IsSeparated (affinePlane.snd k₀) :=
  MorphismProperty.pullback_snd _ _ inferInstance

instance : QuasiCompact (affinePlane.snd k₀) :=
  MorphismProperty.pullback_snd _ _ inferInstance

instance : LocallyOfFiniteType (affinePlane.snd k₀) :=
  MorphismProperty.pullback_snd _ _ inferInstance

variable (k₀) in
/-- The multiplication `μ : 𝔸¹ ×_{k₀} 𝔸¹ ⟶ 𝔸¹`, `(x, y) ↦ x y`. -/
noncomputable def affinePlane.mul : affinePlane k₀ ⟶ affineLine k₀ :=
  AffineSpace.homOfVector (affinePlane k₀ ↘ Spec (CommRingCat.of k₀)) fun _ ↦
    (affinePlane.fst k₀).appTop (AffineSpace.coord _ PUnit.unit) *
      (affinePlane.snd k₀).appTop (AffineSpace.coord _ PUnit.unit)

instance : (affinePlane.mul k₀).IsOver (Spec (CommRingCat.of k₀)) :=
  ⟨AffineSpace.homOfVector_over _ _⟩

/-- The kernel `μ^* ℒ_ψ` of the Fourier–Deligne transform on `𝔸¹ ×_{k₀} 𝔸¹`. -/
noncomputable def fourierKernel (ψ : AddChar k₀ (PadicAlgCl l)) :
    WeilSheaf k₀ l (affinePlane k₀) :=
  (WeilSheaf.upperStar (affinePlane.mul k₀)).obj (artinSchreier ψ 1)

/-- The kernel of the Fourier–Deligne transform is lisse, as a pullback of the lisse
Artin–Schreier sheaf. -/
theorem isLisse_fourierKernel (ψ : AddChar k₀ (PadicAlgCl l)) : (fourierKernel ψ).IsLisse :=
  ProEtale.IsAdicLisseSheaf.upperStar _ (isLisse_artinSchreier ψ 1)

-- TODO(unify): sk-def-ft
/-- The Fourier–Deligne transform `FT_ψ(K) = Rpr₂!(pr₁^* K ⊗ μ^* ℒ_ψ)[1]` from Weil complexes
on the affine line to Weil complexes on the dual affine line, with Laumon's shift by the
relative dimension one. It is a triangulated functor between the triangulated categories of
Weil complexes. -/
noncomputable def fourierTransform (ψ : AddChar k₀ (PadicAlgCl l)) :
    WeilComplex k₀ l (affineLine k₀) ⥤ WeilComplex k₀ l (affineLine k₀) :=
  WeilComplex.upperStar (affinePlane.fst k₀) ⋙
    WeilComplex.tensorLisse (fourierKernel ψ) (isLisse_fourierKernel ψ) ⋙
    WeilComplex.derivedLowerShriek k₀ l (affinePlane.snd k₀) ⋙
    shiftFunctor _ (1 : ℤ)

-- TODO(unify): sk-def-ft
instance (ψ : AddChar k₀ (PadicAlgCl l)) : (fourierTransform (l := l) ψ).Additive := by
  unfold fourierTransform
  infer_instance

-- TODO(unify): sk-thm-inversion
/-- **Fourier inversion**: for a nontrivial additive character the Fourier–Deligne transform is
an equivalence between the triangulated categories of Weil complexes on the two dual lines, with
quasi-inverse `FT_{ψ⁻¹}` up to the Tate twist `(1)`. -/
theorem isEquivalence_fourierTransform (ψ : AddChar k₀ (PadicAlgCl l)) (hψ : ψ ≠ 1) :
    (fourierTransform (l := l) ψ).IsEquivalence :=
  sorry

end Fourier

end AlgebraicGeometry
