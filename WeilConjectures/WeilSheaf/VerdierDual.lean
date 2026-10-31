/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
public import WeilConjectures.WeilSheaf.DerivedHom
public import WeilConjectures.WeilSheaf.DerivedHomTriangulated
public import WeilConjectures.WeilSheaf.LowerShriekFunctoriality
public import WeilConjectures.WeilSheaf.TateTwist
import WeilConjectures.WeilSheaf.Bidual
import WeilConjectures.WeilSheaf.DerivedHomSingleResolution

/-!
# The exceptional inverse image and the Verdier dual of Weil complexes

For a separated morphism of finite type `f : X ⟶ Y` of separated `k₀`-schemes of finite type,
the direct image with compact support `Rf₀!` of Weil complexes
(`AlgebraicGeometry.WeilComplex.derivedLowerShriek`) has a right adjoint `Rf^!` on Weil
complexes; this is the constructible adjunction `Rf_! ⊣ Rf^!` of the six-functor chapter
(`det-pd-biduality-coefficients`), stated here as
`AlgebraicGeometry.WeilComplex.isLeftAdjoint_derivedLowerShriek`. The exceptional inverse image
`AlgebraicGeometry.WeilComplex.upperShriek f` is *defined* as that right adjoint, which is how
the blueprint characterizes it (`def-weil-exceptional-inverse-image`); so that no data is chosen
from the unproved existence statement, it takes the existence of the right adjoint
(`AlgebraicGeometry.WeilComplex.HasUpperShriek f`) as a hypothesis. It gives the dualizing
complex `ω_X = Ra_X^! ℚ̄_ℓ` (`AlgebraicGeometry.WeilComplex.dualizingComplex`) and the Verdier
dual `𝔻_X = RHom(-, ω_X)` (`AlgebraicGeometry.WeilComplex.verdierDual`), the derived internal
hom of pro-étale Weil sheaves into `ω_X` (`AlgebraicGeometry.ProEtaleWeilSheaf.derivedHom`).

The statements of the duality theory for Weil complexes that the boundary duality of
`sec-deligne-laumon-a1` uses belong to the chapters on the six functors and on smooth purity;
they are stated here with `sorry`, each with the blueprint node it renders:

- `det-pd-biduality-coefficients`: the adjunction `Rf₀! ⊣ Rf^!`, the fact that `𝔻_X` preserves Weil
  complexes, its exactness, biduality `K ≅ 𝔻_X 𝔻_X K` and `Rf^! ≅ 𝔻_X f^* 𝔻_Y`;
- `fix-cor-verdier-exchange`: `𝔻_Y Rf₀! ≅ Rf_* 𝔻_X`;
- `cor-pur-adic-and-rational-smooth-dualizing-complexes`: `ω_X ≅ ℚ̄_ℓ(d)[2d]` for `X` smooth of
  pure dimension `d`;
- `lem-sf-hom-finite-projective`: `RHom(P, N) ≅ P^∨ ⊗ N` for a lisse `P` (the biduality
  `P ≅ P^∨∨` is proved in `WeilConjectures.WeilSheaf.Bidual`);
- `prop-sf-localization-all-stages`, clause (4): `Ri^! Rj_* = 0` and the unit
  `Q ⟶ Ri^! Ri_* Q` is an isomorphism, for complementary immersions `i` and `j`.

All isomorphisms are stated as the existence of an isomorphism, as in
`WeilConjectures.WeilSheaf.LowerShriekFunctoriality`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Pretriangulated

namespace AlgebraicGeometry

open Pretriangulated.Opposite in
variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

open MonoidalCategory Functor.LaxMonoidal in
private theorem bidual_evaluation_equivariance
    {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]
    (G : C ⥤ C) [G.LaxBraided] {A B D U : C}
    (p : G.obj A ⟶ A) (q : G.obj B ⟶ B) [IsIso q]
    (r : G.obj D ⟶ D) (s : G.obj U ⟶ U) (d : A ⟶ D)
    (a : B ⊗ A ⟶ U) (b : D ⊗ B ⟶ U)
    (hd : d ▷ B ≫ b = (β_ A B).hom ≫ a)
    (h₁ : (q ⊗ₘ p) ≫ a = μ G B A ≫ G.map a ≫ s)
    (h₂ : (r ⊗ₘ q) ≫ b = μ G D B ≫ G.map b ≫ s) :
    (G.map d ≫ r) ▷ B ≫ b = (p ≫ d) ▷ B ≫ b := by
  apply (cancel_epi (G.obj A ◁ q)).mp
  rw [comp_whiskerRight, comp_whiskerRight]
  simp only [Category.assoc]
  rw [whisker_exchange_assoc, ← tensorHom_def'_assoc, h₂]
  rw [μ_natural_left_assoc, ← G.map_comp_assoc, hd, G.map_comp]
  simp only [Category.assoc]
  rw [Functor.LaxBraided.braided_assoc, ← h₁]
  rw [← BraidedCategory.braiding_naturality_assoc]
  simp only [tensorHom_def', Category.assoc]

private theorem closed_uncurry_left_natural
    {D : Type*} [Category D] {H : Dᵒᵖ × D ⥤ D}
    (S : WeilConjectures.CoefficientClosedStructure H)
    {L L' : D} (K W : D) (g : L' ⟶ L) (v : L ⟶ H.obj (op K, W)) :
    (S.transpose L' K W).symm (g ≫ v) =
      S.tensor.map (Prod.mkHom g (𝟙 K)) ≫ (S.transpose L K W).symm v := by
  let := S.monoidal
  have ht : S.tensor.map (Prod.mkHom g (𝟙 K)) =
      (MonoidalCategory.tensorRight K).map g := MonoidalCategory.tensorHom_id g K
  rw [ht]
  exact (S.adjunction K).homEquiv_naturality_left_symm g v

private theorem symmetric_closed_uncurry_left_natural
    {D : Type*} [Category D] {H : Dᵒᵖ × D ⥤ D}
    (S : WeilConjectures.CoefficientClosedStructure H)
    (B : @BraidedCategory D _ S.monoidal)
    {L L' : D} (K W : D) (g : L' ⟶ L) (v : L ⟶ H.obj (op K, W)) :
    (B.braiding K L').hom ≫ (S.transpose L' K W).symm (g ≫ v) =
      S.tensor.map (Prod.mkHom (𝟙 K) g) ≫
        (B.braiding K L).hom ≫ (S.transpose L K W).symm v := by
  rw [closed_uncurry_left_natural S K W g v]
  let := S.monoidal
  let := B
  have hb := BraidedCategory.braiding_naturality (𝟙 K) g
  simpa only [WeilConjectures.CoefficientClosedStructure.tensor,
    MonoidalCategory.tensor_map, Category.assoc] using
    congrArg (fun z ↦ z ≫ (S.transpose L K W).symm v) hb.symm

private noncomputable def isoOfNaturalHomEquiv
    {D : Type*} [Category D] {U V : D}
    (e : ∀ L : D, (L ⟶ U) ≃ (L ⟶ V))
    (hn : ∀ (L L' : D) (g : L' ⟶ L) (v : L ⟶ U), e L' (g ≫ v) = g ≫ e L v) :
    U ≅ V where
  hom := e U (𝟙 U)
  inv := (e V).symm (𝟙 V)
  hom_inv_id := by
    apply (e U).injective
    rw [hn, Equiv.apply_symm_apply, Category.comp_id]
  inv_hom_id := by
    rw [← hn U V ((e V).symm (𝟙 V)) (𝟙 U), Category.comp_id,
      Equiv.apply_symm_apply]

namespace WeilSheaf

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

open ProEtale MonoidalCategory Functor.LaxMonoidal in
private theorem bidual_frobenius (P : WeilSheaf k₀ l X) (hP : P.IsLisse) :
    (frobeniusPullback k₀ l X).map (ProEtale.adicNativeBidual P.obj.carrier) ≫
        ((P.dual hP).dual hP.dual).obj.str.hom =
      P.obj.str.hom ≫ ProEtale.adicNativeBidual P.obj.carrier := by
  let G := ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv)_*[
    WeilCoefficients.{u} l]
  let A := P.obj.carrier
  let B := (P.dual hP).obj.carrier
  let U := (adicConstant k₀ l X).obj.carrier
  let d := ProEtale.adicNativeBidual A
  have hd : d.hom ▷ B.X ≫ Mod.evaluation B U =
      (β_ A.X B.X).hom ≫ Mod.evaluation A U :=
    ProEtale.adicNativeBidual_transpose A
  apply Mod.uncurryHom_injective
  exact bidual_evaluation_equivariance G P.obj.str.hom.hom
    (P.dual hP).obj.str.hom.hom ((P.dual hP).dual hP.dual).obj.str.hom.hom
    (adicConstant k₀ l X).obj.str.hom.hom d.hom
    (Mod.evaluation A U) (Mod.evaluation B U) hd
    (dual_evaluation_str P hP) (dual_evaluation_str (P.dual hP) hP.dual)

/-- **Biduality of a lisse sheaf** (blueprint: `lem-sf-hom-finite-projective`, "the canonical
map `P ⟶ P^∨∨` is an isomorphism"). -/
theorem nonempty_iso_dual_dual (P : WeilSheaf k₀ l X) (hP : P.IsLisse) :
    Nonempty (P ≅ (P.dual hP).dual hP.dual) := by
  let d : P ⟶ (P.dual hP).dual hP.dual := ObjectProperty.homMk
    ⟨ProEtale.adicNativeBidual P.obj.carrier, bidual_frobenius P hP⟩
  have := ProEtale.isIso_adicNativeBidual_of_isLisse P.obj.carrier hP
  have : IsIso d.hom.hom.f :=
    inferInstanceAs (IsIso (ProEtale.adicNativeBidual P.obj.carrier))
  have : IsIso d.hom.hom := Endofunctor.Algebra.iso_of_iso _
  have : IsIso d.hom := (ObjectProperty.isIso_hom_iff _).mp inferInstance
  have : IsIso d := (ObjectProperty.isIso_hom_iff _).mp inferInstance
  exact ⟨asIso d⟩

end WeilSheaf

namespace WeilComplex

section Proper

variable {Z Y : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] (g : Z ⟶ Y) [g.IsOver (Spec (CommRingCat.of k₀))]
  [IsProper g] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]

/-- **The proper exceptional adjunction** (blueprint: `det-pd-biduality-coefficients`, "the
constructible adjunction `Rf_! ⊣ Rf^!`", for a proper `f`, where `Rf_! = Rf_*`): for a proper
morphism `g : Z ⟶ Y` of `k₀`-schemes, `Y` of finite type, the direct image `Rg_*` of Weil complexes
has a right adjoint `Rg^!`. The general case
`AlgebraicGeometry.WeilComplex.isLeftAdjoint_derivedLowerShriek` reduces to this one through a
compactification. -/
theorem isLeftAdjoint_derivedLowerStar_of_isProper :
    (derivedLowerStar (k₀ := k₀) (l := l) g).IsLeftAdjoint :=
  sorry

end Proper

section UpperShriek

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

variable (k₀ l) in
/-- The direct image with compact support `Rf₀!` of Weil complexes along `f` has a right adjoint,
the exceptional inverse image `Rf^!` (`AlgebraicGeometry.WeilComplex.upperShriek`). That it
always has one is `AlgebraicGeometry.WeilComplex.isLeftAdjoint_derivedLowerShriek`. -/
abbrev HasUpperShriek : Prop :=
  (derivedLowerShriek k₀ l f).IsLeftAdjoint

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] in
/-- **The constructible exceptional adjunction** (blueprint: `det-pd-biduality-coefficients`, "the
constructible adjunction `Rf_! ⊣ Rf^!`"; the exceptional inverse image itself is defined at the
finite stage as `AlgebraicGeometry.ProEtale.rightDerivedUpperShriek`): for a
separated morphism of finite type `f : X ⟶ Y` of `k₀`-schemes of finite type, the direct image
with compact support `Rf₀!` of Weil complexes has a right adjoint. -/
theorem isLeftAdjoint_derivedLowerShriek : HasUpperShriek k₀ l f := by
  have hXS : X ↘ Spec (CommRingCat.of k₀) = f ≫ Y ↘ Spec (CommRingCat.of k₀) :=
    (comp_over f (Spec (CommRingCat.of k₀))).symm
  have : LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀)) := hXS ▸ inferInstance
  have : QuasiCompact (X ↘ Spec (CommRingCat.of k₀)) := hXS ▸ inferInstance
  obtain ⟨h, hW, _, _, _, _, _, G, ⟨adj⟩, _⟩ :=
    nativeWeil_localizing_brown_adjoints k₀ l f
  let hX := (nativeWeil_localizing_hulls k₀ l X).2.2.2.2.1
  let hY := (nativeWeil_localizing_hulls k₀ l Y).2.2.2.2.1
  let iX := ObjectProperty.ιOfLE hX
  let iY := ObjectProperty.ιOfLE hY
  let R : WeilComplex k₀ l Y ⥤ WeilComplex k₀ l X :=
    (objectProperty k₀ l X).lift (iY ⋙ G ⋙ (nativeWeilLocalizingHull k₀ l X).ι)
      (nativeBrownRight_preserves_weilComplex k₀ l f hW G adj)
  let a : derivedLowerShriek k₀ l f ⊣ R :=
    adj.restrictFullyFaithful (ObjectProperty.fullyFaithfulιOfLE hX)
      (ObjectProperty.fullyFaithfulιOfLE hY) (Iso.refl _) (Iso.refl _)
  exact a.isLeftAdjoint

variable [HasUpperShriek k₀ l f]

/-- The exceptional inverse image `Rf^!` of Weil complexes along a separated morphism of finite
type `f : X ⟶ Y` of `k₀`-schemes of finite type: the right adjoint of the direct image with
compact support `Rf₀!` (blueprint: `def-weil-exceptional-inverse-image`, which characterizes
`Rf^!` by the adjunction `Hom(Rf_! K, L) ≅ Hom(K, Rf^! L)` on constructible complexes). -/
noncomputable def upperShriek : WeilComplex k₀ l Y ⥤ WeilComplex k₀ l X :=
  (derivedLowerShriek k₀ l f).rightAdjoint

/-- The adjunction `Rf₀! ⊣ Rf^!`. -/
noncomputable def derivedLowerShriekUpperShriekAdjunction :
    derivedLowerShriek k₀ l f ⊣ upperShriek (k₀ := k₀) (l := l) f :=
  Adjunction.ofIsLeftAdjoint _

end UpperShriek

section VerdierDual

variable (k₀ l) (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [HasUpperShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))]

/-- The dualizing complex `ω_X = Ra_X^! ℚ̄_ℓ` of a separated `k₀`-scheme of finite type `X`: the
exceptional inverse image of the constant Weil sheaf `ℚ̄_ℓ` on `Spec k₀` along the structure
morphism (blueprint: `det-pd-biduality-coefficients`, `fix-cor-verdier-exchange`). -/
noncomputable def dualizingComplex : WeilComplex k₀ l X :=
  (upperShriek (X ↘ Spec (CommRingCat.of k₀))).obj
    (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l (Spec (CommRingCat.of k₀))))

variable {X} in
/-- **The Verdier dual preserves Weil complexes** (blueprint: `det-pd-biduality-coefficients`, the
duality `D_{X,ℚ̄_ℓ} : D^b_c(X, ℚ̄_ℓ)ᵒᵖ ⥤ D^b_c(X, ℚ̄_ℓ)` is the internal hom into
`ω_{X,ℚ̄_ℓ} = Ra_X^! ℚ̄_ℓ`): the derived internal hom `RHom(K, ω_X)` of a Weil complex `K` into
the dualizing complex is a Weil complex. -/
theorem objectProperty_derivedHom_dualizingComplex (K : WeilComplex k₀ l X) :
    WeilComplex.objectProperty k₀ l X
      ((ProEtaleWeilSheaf.derivedHom k₀ l X (dualizingComplex k₀ l X).obj).obj (op K.obj)) := by
  have h := (ProEtaleWeilSheaf.weil_geometric_hom_constructibility k₀ l X).2.2
    K (dualizingComplex k₀ l X)
  obtain ⟨e⟩ := ProEtaleWeilSheaf.nativeGeometricForget_derivedHomComparison
    k₀ l X K.obj (dualizingComplex k₀ l X).obj
  apply ((ProEtaleWeilSheaf.weil_geometric_hom_constructibility k₀ l X).1 _).mpr
  have : (ProEtale.constantModelBoundedConstructible (Profinite.padicAlgClRingObj l)
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).IsClosedUnderIsomorphisms :=
    (ProEtale.constantModelConstructibleFiniteTor_wellDefined (Profinite.padicAlgClRingObj l)
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).2.1
  exact (ProEtale.constantModelBoundedConstructible (Profinite.padicAlgClRingObj l)
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).prop_of_iso e.symm h.2.2.1

/-- The Verdier dual `𝔻_X K = RHom(K, ω_X)` of Weil complexes on a separated `k₀`-scheme of
finite type `X`, the derived internal hom into the dualizing complex
(blueprint: `det-pd-biduality-coefficients`, `fix-cor-verdier-exchange`). -/
noncomputable def verdierDual : (WeilComplex k₀ l X)ᵒᵖ ⥤ WeilComplex k₀ l X :=
  ObjectProperty.lift _
    ((ObjectProperty.ι _).op ⋙ ProEtaleWeilSheaf.derivedHom k₀ l X (dualizingComplex k₀ l X).obj)
    fun K ↦ objectProperty_derivedHom_dualizingComplex k₀ l K.unop

@[simp]
lemma verdierDual_obj_obj (K : (WeilComplex k₀ l X)ᵒᵖ) :
    ((verdierDual k₀ l X).obj K).obj =
      (ProEtaleWeilSheaf.derivedHom k₀ l X (dualizingComplex k₀ l X).obj).obj (op K.unop.obj) :=
  rfl

/-- **Verdier biduality** (blueprint: `det-pd-biduality-coefficients`, "evaluation and biduality
descend, giving a natural isomorphism `K ≅ D_{X,ℚ̄_ℓ} D_{X,ℚ̄_ℓ} K`"). -/
theorem nonempty_iso_verdierDual_rightOp_comp_verdierDual :
    Nonempty (𝟭 (WeilComplex k₀ l X) ≅ (verdierDual k₀ l X).rightOp ⋙ verdierDual k₀ l X) := by
  classical
  let : Fintype k₀ := Fintype.ofFinite k₀
  obtain ⟨n, hp, hn⟩ := FiniteField.card k₀ (ringChar k₀)
  let D : WeilConjectures.FiniteFieldDatum.{u} :=
    { p := ringChar k₀, a := n, q := Nat.card k₀, prime := hp
      exponent_pos := n.pos, cardinality_eq := by simpa only [Nat.card_eq_fintype_card] using hn
      k₀ := k₀, card_base := rfl, k := AlgebraicClosure k₀ }
  let : Fact (l ≠ D.p) := ⟨Ne.symm (Fact.out : ringChar k₀ ≠ l)⟩
  let T : WeilConjectures.NativeExceptionalForgetful.Space D :=
    { base := Over.mk (X ↘ Spec (CommRingCat.of k₀))
      separated := inferInstanceAs (IsSeparated (X ↘ Spec (CommRingCat.of k₀)))
      finiteType := inferInstanceAs (LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀)))
      quasiCompact := inferInstanceAs (QuasiCompact (X ↘ Spec (CommRingCat.of k₀))) }
  have : IsSeparated (T.base.left ↘ Spec (CommRingCat.of D.k₀)) := by
    change IsSeparated (X ↘ Spec (CommRingCat.of k₀))
    infer_instance
  have : LocallyOfFiniteType (T.base.left ↘ Spec (CommRingCat.of D.k₀)) := by
    change LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))
    infer_instance
  have : QuasiCompact (T.base.left ↘ Spec (CommRingCat.of D.k₀)) := by
    change QuasiCompact (X ↘ Spec (CommRingCat.of k₀))
    infer_instance
  have : HasUpperShriek D.k₀ l (T.base.left ↘ Spec (CommRingCat.of D.k₀)) := by
    change HasUpperShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))
    infer_instance
  exact native_bidual_iso D l T

open Pretriangulated.Opposite in
/-- **The Verdier dual is exact** (blueprint: `det-pd-biduality-coefficients`, "an exact
`ℚ̄_ℓ`-linear anti-equivalence `D_{X,ℚ̄_ℓ}`"): it commutes with the shifts and carries distinguished
triangles of `(WeilComplex X)ᵒᵖ` to distinguished triangles. -/
theorem exists_commShift_isTriangulated_verdierDual :
    ∃ _ : (verdierDual k₀ l X).CommShift ℤ, (verdierDual k₀ l X).IsTriangulated := by
  obtain ⟨_, _⟩ := DerivedCategory.exists_commShift_isTriangulated_bifunctorRHom
    (ProEtaleWeilSheaf.ihomBifunctor k₀ l X) (dualizingComplex k₀ l X).obj
  unfold verdierDual ProEtaleWeilSheaf.derivedHom
  exact ⟨Functor.CommShift.ofComp ((WeilComplex.objectProperty k₀ l X).liftCompιIso _ _) ℤ,
    ObjectProperty.isTriangulated_lift _ _ _⟩

attribute [local irreducible] ProEtaleWeilSheaf.nativeDerivedClosedComparison

private theorem exists_dualizing_hom_equiv (K : WeilComplex k₀ l X) :
    ∃ e : ∀ L : WeilComplex k₀ l X,
      (L ⟶ (verdierDual k₀ l X).obj (op K)) ≃
        ((derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))).obj
          ((nativeConstructibleTensor k₀ l X).obj (K, L)) ⟶
            WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l
              (Spec (CommRingCat.of k₀)))),
      ∀ (L L' : WeilComplex k₀ l X) (g : L' ⟶ L)
        (v : L ⟶ (verdierDual k₀ l X).obj (op K)),
        e L' (g ≫ v) =
          (derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))).map
            ((nativeConstructibleTensor k₀ l X).map (Prod.mkHom (𝟙 K) g)) ≫ e L v := by
  let C := ProEtaleWeilSheaf.nativeDerivedClosedComparison k₀ l X
  let W := dualizingComplex k₀ l X
  let m := C.homModels.nativeModel W.obj
  let c := fun L : WeilComplex k₀ l X ↦
    ((objectProperty k₀ l X).fullyFaithfulι.homEquiv
      (X := L) (Y := (verdierDual k₀ l X).obj (op K))).trans
    (((m.app (op K.obj)).symm.homToEquiv).trans
    ((C.weilClosed.transpose L.obj K.obj W.obj).symm.trans
    (((C.weilSymmetry.braiding K.obj L.obj).symm.homFromEquiv).trans
    ((objectProperty k₀ l X).fullyFaithfulι.homEquiv
      (X := (nativeConstructibleTensor k₀ l X).obj (K, L)) (Y := W)).symm)))
  let a := derivedLowerShriekUpperShriekAdjunction (k₀ := k₀) (l := l)
    (X ↘ Spec (CommRingCat.of k₀))
  let t := fun L : WeilComplex k₀ l X ↦
    (a.homEquiv ((nativeConstructibleTensor k₀ l X).obj (K, L))
      (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l
        (Spec (CommRingCat.of k₀))))).symm
  refine ⟨fun L ↦ (c L).trans (t L), ?_⟩
  intro L L' g v
  have hc : c L' (g ≫ v) =
      (nativeConstructibleTensor k₀ l X).map (Prod.mkHom (𝟙 K) g) ≫ c L v := by
    apply ObjectProperty.hom_ext
    change (C.weilSymmetry.braiding K.obj L'.obj).hom ≫
        (C.weilClosed.transpose L'.obj K.obj W.obj).symm
          ((g.hom ≫ v.hom) ≫ m.inv.app (op K.obj)) =
      C.weilClosed.tensor.map (Prod.mkHom (𝟙 K.obj) g.hom) ≫
        (C.weilSymmetry.braiding K.obj L.obj).hom ≫
          (C.weilClosed.transpose L.obj K.obj W.obj).symm
            (v.hom ≫ m.inv.app (op K.obj))
    rw [Category.assoc]
    exact symmetric_closed_uncurry_left_natural C.weilClosed
      C.weilSymmetry.toBraidedCategory
      K.obj W.obj g.hom (v.hom ≫ m.inv.app (op K.obj))
  change t L' (c L' (g ≫ v)) = _
  rw [hc]
  exact a.homEquiv_naturality_left_symm _ _

private theorem exists_dualizing_hom_equiv_reversed (K : WeilComplex k₀ l X) :
    ∃ e : ∀ L : WeilComplex k₀ l X,
      (L ⟶ (verdierDual k₀ l X).obj (op K)) ≃
        ((derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))).obj
          ((nativeConstructibleTensor k₀ l X).obj (L, K)) ⟶
            WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l
              (Spec (CommRingCat.of k₀)))),
      ∀ (L L' : WeilComplex k₀ l X) (g : L' ⟶ L)
        (v : L ⟶ (verdierDual k₀ l X).obj (op K)),
        e L' (g ≫ v) =
          (derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))).map
            ((nativeConstructibleTensor k₀ l X).map (Prod.mkHom g (𝟙 K))) ≫ e L v := by
  let C := ProEtaleWeilSheaf.nativeDerivedClosedComparison k₀ l X
  let W := dualizingComplex k₀ l X
  let m := C.homModels.nativeModel W.obj
  let c := fun L : WeilComplex k₀ l X ↦
    ((objectProperty k₀ l X).fullyFaithfulι.homEquiv
      (X := L) (Y := (verdierDual k₀ l X).obj (op K))).trans
    (((m.app (op K.obj)).symm.homToEquiv).trans
    ((C.weilClosed.transpose L.obj K.obj W.obj).symm.trans
    ((objectProperty k₀ l X).fullyFaithfulι.homEquiv
      (X := (nativeConstructibleTensor k₀ l X).obj (L, K)) (Y := W)).symm))
  let a := derivedLowerShriekUpperShriekAdjunction (k₀ := k₀) (l := l)
    (X ↘ Spec (CommRingCat.of k₀))
  let t := fun L : WeilComplex k₀ l X ↦
    (a.homEquiv ((nativeConstructibleTensor k₀ l X).obj (L, K))
      (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l
        (Spec (CommRingCat.of k₀))))).symm
  refine ⟨fun L ↦ (c L).trans (t L), ?_⟩
  intro L L' g v
  have hc : c L' (g ≫ v) =
      (nativeConstructibleTensor k₀ l X).map (Prod.mkHom g (𝟙 K)) ≫ c L v := by
    apply ObjectProperty.hom_ext
    change (C.weilClosed.transpose L'.obj K.obj W.obj).symm
        ((g.hom ≫ v.hom) ≫ m.inv.app (op K.obj)) =
      C.weilClosed.tensor.map (Prod.mkHom g.hom (𝟙 K.obj)) ≫
        (C.weilClosed.transpose L.obj K.obj W.obj).symm
          (v.hom ≫ m.inv.app (op K.obj))
    rw [Category.assoc]
    exact closed_uncurry_left_natural C.weilClosed
      K.obj W.obj g.hom (v.hom ≫ m.inv.app (op K.obj))
  change t L' (c L' (g ≫ v)) = _
  rw [hc]
  exact a.homEquiv_naturality_left_symm _ _

end VerdierDual

section Exchange

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  [HasUpperShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))]
  [HasUpperShriek k₀ l (Y ↘ Spec (CommRingCat.of k₀))]

/-- **The exceptional inverse image as a conjugate of the pullback** (blueprint:
`det-pd-biduality-coefficients`, "`Rf^! = D_X f^* D_Y`"): `Rf^! L ≅ 𝔻_X f^* 𝔻_Y L`. -/
theorem nonempty_upperShriek_obj_iso [HasUpperShriek k₀ l f] (L : WeilComplex k₀ l Y) :
    Nonempty ((upperShriek f).obj L ≅
      (verdierDual k₀ l X).obj (op ((upperStar f).obj ((verdierDual k₀ l Y).obj (op L))))) := by
  let D := (verdierDual k₀ l Y).obj (op L)
  obtain ⟨b⟩ := nonempty_iso_verdierDual_rightOp_comp_verdierDual k₀ l Y
  obtain ⟨eY, hY⟩ := exists_dualizing_hom_equiv_reversed k₀ l Y D
  obtain ⟨eX, hX⟩ := exists_dualizing_hom_equiv_reversed k₀ l X ((upperStar f).obj D)
  obtain ⟨_, _, _, _, pi, gamma, _, _, _, _, _, _, hn⟩ :=
    native_compact_structure_tensor_comparison k₀ l f
  let p := fun M : WeilComplex k₀ l X ↦ nativeStructureTensorHomEquiv k₀ l f pi gamma M D
  let a := derivedLowerShriekUpperShriekAdjunction (k₀ := k₀) (l := l) f
  let e := fun M : WeilComplex k₀ l X ↦
    (eX M).trans ((p M).symm.trans
      ((eY ((derivedLowerShriek k₀ l f).obj M)).symm.trans
        (((b.app L).symm.homToEquiv).trans (a.homEquiv M L))))
  refine ⟨(isoOfNaturalHomEquiv e ?_).symm⟩
  intro M M' g v
  have hx := hX M M' g v
  have hp := hn g (𝟙 D) (eX M v)
  simp only [nativeStructureTensorLeft, nativeCompactProjectionLeft,
    nativeStructureTensorRight, nativeStructureTensorInput,
    Functor.comp_map, Functor.prod_map, Functor.id_map] at hp
  rw [(upperStar f).map_id D] at hp
  have hy := hY ((derivedLowerShriek k₀ l f).obj M)
    ((derivedLowerShriek k₀ l f).obj M') ((derivedLowerShriek k₀ l f).map g)
    ((eY ((derivedLowerShriek k₀ l f).obj M)).symm ((p M).symm (eX M v)))
  have hy' : (eY ((derivedLowerShriek k₀ l f).obj M')).symm
      ((derivedLowerShriek k₀ l (Y ↘ Spec (CommRingCat.of k₀))).map
        ((nativeConstructibleTensor k₀ l Y).map
          (Prod.mkHom ((derivedLowerShriek k₀ l f).map g) (𝟙 D))) ≫
          (p M).symm (eX M v)) =
      (derivedLowerShriek k₀ l f).map g ≫
        (eY ((derivedLowerShriek k₀ l f).obj M)).symm ((p M).symm (eX M v)) := by
    apply (eY ((derivedLowerShriek k₀ l f).obj M')).injective
    simpa only [Equiv.apply_symm_apply] using hy.symm
  change a.homEquiv _ _
    ((eY ((derivedLowerShriek k₀ l f).obj M')).symm
      ((p M').symm (eX M' (g ≫ v))) ≫ (b.app L).inv) = _
  rw [hx, hp, hy', Category.assoc]
  exact a.homEquiv_naturality_left g _

/-- **Verdier exchange** (blueprint: `fix-cor-verdier-exchange`): for a separated morphism of
finite type `f : X ⟶ Y`, `𝔻_Y (Rf₀! M) ≅ Rf_* (𝔻_X M)`. -/
theorem nonempty_verdierDual_derivedLowerShriek_iso (M : WeilComplex k₀ l X) :
    Nonempty ((verdierDual k₀ l Y).obj (op ((derivedLowerShriek k₀ l f).obj M)) ≅
      (derivedLowerStar f).obj ((verdierDual k₀ l X).obj (op M))) := by
  obtain ⟨eY, hY⟩ := exists_dualizing_hom_equiv k₀ l Y
    ((derivedLowerShriek k₀ l f).obj M)
  obtain ⟨eX, hX⟩ := exists_dualizing_hom_equiv k₀ l X M
  obtain ⟨_, _, _, _, pi, gamma, _, _, _, _, _, hn, _⟩ :=
    native_compact_structure_tensor_comparison k₀ l f
  let p := nativeStructureTensorHomEquiv k₀ l f pi gamma M
  let a := upperStarDerivedLowerStarAdjunction (k₀ := k₀) (l := l) f
  let e := fun L : WeilComplex k₀ l Y ↦
    (eY L).trans ((p L).trans
      ((eX ((upperStar f).obj L)).symm.trans
        (a.homEquiv L ((verdierDual k₀ l X).obj (op M)))))
  refine ⟨isoOfNaturalHomEquiv e ?_⟩
  intro L L' g v
  have hy := hY L L' g v
  have hp := hn (𝟙 M) g (eY L v)
  simp only [nativeStructureTensorLeft, nativeCompactProjectionLeft,
    nativeStructureTensorRight, nativeStructureTensorInput,
    Functor.comp_map, Functor.prod_map, Functor.id_map] at hp
  rw [(derivedLowerShriek k₀ l f).map_id M] at hp
  have hx := hX ((upperStar f).obj L) ((upperStar f).obj L')
    ((upperStar f).map g) ((eX ((upperStar f).obj L)).symm (p L (eY L v)))
  have hx' : (eX ((upperStar f).obj L')).symm
      ((derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))).map
        ((nativeConstructibleTensor k₀ l X).map
          (Prod.mkHom (𝟙 M) ((upperStar f).map g))) ≫ p L (eY L v)) =
      (upperStar f).map g ≫ (eX ((upperStar f).obj L)).symm (p L (eY L v)) := by
    apply (eX ((upperStar f).obj L')).injective
    simpa only [Equiv.apply_symm_apply] using hx.symm
  change a.homEquiv _ _ ((eX ((upperStar f).obj L')).symm (p L' (eY L' (g ≫ v)))) = _
  rw [hy]
  rw [hp, hx']
  exact a.homEquiv_naturality_left g _

end Exchange

section Smooth

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [HasUpperShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))]

/-- **The dualizing complex of a smooth scheme** (blueprint:
`cor-pur-adic-and-rational-smooth-dualizing-complexes`, at the coefficient stage `ℚ̄_ℓ`): if `X`
is smooth of pure dimension `d` over `k₀`, then `ω_X ≅ ℚ̄_ℓ(d)[2d]`. -/
theorem nonempty_dualizingComplex_iso (d : ℕ)
    [SmoothOfRelativeDimension d (X ↘ Spec (CommRingCat.of k₀))] :
    Nonempty (dualizingComplex k₀ l X ≅
      ((tateTwist k₀ l X d).obj
        (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)))⟦(2 * d : ℤ)⟧) := by
  let J := upperShriek (k₀ := k₀) (l := l) (X ↘ Spec (CommRingCat.of k₀))
  let adj := derivedLowerShriekUpperShriekAdjunction (k₀ := k₀) (l := l)
    (X ↘ Spec (CommRingCat.of k₀))
  obtain ⟨hge, hle⟩ := smooth_dualizing_concentration J adj d
  let K := dualizingComplex k₀ l X
  let b : ℤ := -2 * (d : ℤ)
  have : K.obj.IsGE b := hge
  have : K.obj.IsLE b := hle
  obtain ⟨A, ⟨e⟩⟩ :=
    _root_.DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE K.obj b
  obtain ⟨h⟩ := nonempty_smooth_dualizing_cohomology_iso J adj d
  let L := WeilSheaf.tateTwistSheaf k₀ l X d
  let hL : L.IsLisse := WeilSheaf.isLisse_tateTwistSheaf k₀ l X d
  let T := L.tensorObj (WeilSheaf.adicConstant k₀ l X) hL
  let eA : A ≅ T.obj :=
    ((_root_.DerivedCategory.singleFunctorCompHomologyFunctorIso _ b).app A).symm ≪≫
      (_root_.DerivedCategory.homologyFunctor _ b).mapIso e.symm ≪≫
      (WeilSheaf.objectProperty k₀ l X).ι.mapIso h
  let eK : K ≅ (WeilSheaf.toComplex.obj T)⟦(2 * d : ℤ)⟧ :=
    ObjectProperty.isoMk _ (e ≪≫ (_root_.DerivedCategory.singleFunctor _ b).mapIso eA ≪≫
      ((_root_.DerivedCategory.singleFunctors _).shiftIso (2 * (d : ℤ)) b 0
        (by dsimp [b]; lia)).symm.app _ ≪≫
      (((objectProperty k₀ l X).ι.commShiftIso (2 * (d : ℤ))).app
        (WeilSheaf.toComplex.obj T)).symm)
  have := ProEtaleWeilSheaf.preservesFiniteColimits_ihomFunctor (L.dual hL).obj hL.dual
  let F := ProEtaleWeilSheaf.ihomFunctor k₀ l X (L.dual hL).obj
  let eT : (tateTwist k₀ l X d).obj
      (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)) ≅
      WeilSheaf.toComplex.obj T :=
    ObjectProperty.isoMk _
      (F.singleFunctorCompRightDerivedFunctorIso.app (WeilSheaf.adicConstant k₀ l X).obj)
  exact ⟨eK ≪≫ (shiftFunctor _ (2 * (d : ℤ))).mapIso eT.symm⟩

end Smooth

section Lisse

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

/-- **The internal hom out of a lisse sheaf** (blueprint: `lem-sf-hom-finite-projective`): for
a lisse Weil sheaf `P`, a locally free `ℚ̄_ℓ,X̄`-module of finite rank, and a Weil complex `N`,
`P^∨ ⊗ N` and `RHom(P, N)` are isomorphic. The blueprint asserts that the canonical map
`P^∨ ⊗ N ⟶ RHom(P, N)` is an isomorphism; only the existence of an isomorphism is stated here. -/
theorem nonempty_tensorLisse_dual_iso_derivedHom (P : WeilSheaf k₀ l X) (hP : P.IsLisse)
    (N : WeilComplex k₀ l X) :
    Nonempty (((tensorLisse (P.dual hP) hP.dual).obj N).obj ≅
      (ProEtaleWeilSheaf.derivedHom k₀ l X N.obj).obj (op (WeilSheaf.toComplex.obj P).obj)) := by
  obtain ⟨e⟩ := WeilSheaf.nonempty_iso_dual_dual P hP
  obtain ⟨c, _, _, _, hc⟩ :=
    ProEtaleWeilSheaf.derivedHom_single_resolution (k₀ := k₀) (l := l) (X := X)
  obtain ⟨d, _⟩ := hc P.obj N.obj N.property.1.1
  let e' := (WeilSheaf.objectProperty k₀ l X).ι.mapIso e
  let h := (ProEtaleWeilSheaf.ihomBifunctor k₀ l X).mapIso e'.op
  exact ⟨(Functor.rightDerivedFunctorNatIso h).app N.obj ≪≫ d.symm⟩

end Lisse

end WeilComplex

end AlgebraicGeometry
