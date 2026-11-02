/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleConstantDerivedEncoding
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleAmbientRingedExchange
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingPullbackComparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalDerivedPullbackNormalization
public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictConstantTowerOperationsSupplement
public import WeilConjectures.CategoryTheory.Derived.DerivedExactCube
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.CategoryTheory.SixFunctors.MateIsoAlongEquivalences
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Coherence

/-!
# Constant scalar encoding preserves the ambient pro-etale exchange

Source: Stacks Tag 07A7, with constant-module encoding Tags 093I and 03CY.
(blueprint: lem-pe-constant-exchange-encoding).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Inverse mates of isomorphisms are isomorphisms when the vertical functors are
 equivalences. Source: the iterated-mate conjugation identity
(blueprint: lem-pe-constant-exchange-encoding). -/
private theorem inverseMate_isIso [G.IsEquivalence] [H.IsEquivalence]
    (β : TwoSquare R₁ H G R₂) [IsIso β.natTrans] :
    IsIso ((mateEquiv adj₁ adj₂).symm β).natTrans := by
  let aG : G ⊣ G.asEquivalence.inverse := G.asEquivalence.toAdjunction
  let aH : H ⊣ H.asEquivalence.inverse := H.asEquivalence.toAdjunction
  have : IsIso aG.unit := by
    simp only [aG, Equivalence.toAdjunction_unit]
    infer_instance
  have : IsIso aH.counit := by
    simp only [aH, Equivalence.toAdjunction_counit]
    infer_instance
  have : IsIso β := by
    change IsIso β.natTrans
    infer_instance
  have hβ : IsIso (mateEquiv aH aG β).natTrans := by
    dsimp only [mateEquiv, Equiv.coe_fn_mk, TwoSquare.natTrans, TwoSquare.mk]
    infer_instance
  let α := (mateEquiv adj₁ adj₂).symm β
  have hh := iterated_mateEquiv_conjugateEquiv adj₁ adj₂ aG aH α
  have hα : mateEquiv adj₁ adj₂ α = β := Equiv.apply_symm_apply _ _
  have : IsIso (conjugateEquiv (adj₁.comp aH) (aG.comp adj₂) α.natTrans) := by
    rw [← hh, hα]
    exact hβ
  exact conjugateEquiv_of_iso (adj₁.comp aH) (aG.comp adj₂) α.natTrans

private abbrev E (T : Scheme.{u}) := proEtaleModuleRestriction T A

private abbrev L {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  StrictTower.modulePullback (ULift.{u + 1, u} A) f

private abbrev R {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  StrictTower.moduleDirectImage (ULift.{u + 1, u} A) f

private abbrev P {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f

private abbrev S {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f

private def adj {X Y : Scheme.{u}} (f : X ⟶ Y) : L A f ⊣ R A f :=
  proEtaleRingModuleAdjunction f (proEtaleConstantRing Y A) (proEtaleConstantRing X A)
    (proEtaleConstantRingComparison f A)

private def adjFixed {X Y : Scheme.{u}} (f : X ⟶ Y) : P A f ⊣ S A f :=
  ProEtale.upperStarLowerStarAdjunction _ f

/-- The adjunct of the fixed constant-ring isomorphism preserves constant scalar sections. -/
private theorem scalarSquare {X Y : Scheme.{u}} (f : X ⟶ Y) :
    proEtaleModuleScalarUnit Y A ≫
        Functor.whiskerRight (proEtaleRingDirectImageMap f
          (proEtaleConstantRing Y A) (proEtaleConstantRing X A)
          (proEtaleConstantRingComparison f A)).hom
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) =
      Functor.whiskerLeft (proEtaleBaseChange f).op (proEtaleModuleScalarUnit X A) := by
  have hc : proEtaleRingDirectImageMap f
      (proEtaleConstantRing Y A) (proEtaleConstantRing X A)
      (proEtaleConstantRingComparison f A) = proEtaleCoefficientDirectImageMap f A := by
    exact (proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _ |>.apply_symm_apply _
  rw [hc]
  have h := ((sheafificationAdjunction (ProEt.topology Y) CommRingCat.{u + 1}).homEquiv
    ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A)))
    ((proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj
      (proEtaleConstantRing X A))).apply_symm_apply
    (Functor.whiskerLeft (proEtaleBaseChange f).op
      (toSheafify (ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A)))))
  change toSheafify _ _ ≫ (proEtaleCoefficientDirectImageMap f A).hom = _ at h
  exact congrArg (fun z ↦ Functor.whiskerRight z
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})) h

/-- Direct image in both coefficient presentations has the same underlying sections. -/
private def push {X Y : Scheme.{u}} (f : X ⟶ Y) :
    R A f ⋙ E A Y ≅ E A X ⋙ S A f := by
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · refine ObjectProperty.isoMk _ (NatIso.ofComponents (fun U ↦ ?_) ?_)
    · let e : ((R A f ⋙ E A Y).obj M).obj.obj U ≃ₗ[ULift.{u + 1, u} A]
          ((E A X ⋙ S A f).obj M).obj.obj U :=
        { toFun := fun x ↦ x
          invFun := fun x ↦ x
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl
          map_add' := fun _ _ ↦ rfl
          map_smul' := by
            intro r m
            have h := congrArg (fun t ↦ (t.app U).hom r) (scalarSquare A f)
            exact congrArg (fun a ↦ a •
              (show M.val.obj ((proEtaleBaseChange f).op.obj U) from m)) h }
      exact e.toModuleIso
    · intro U V g
      ext x
      rfl
  · intro M N g
    ext U x
    rfl

private def pull {X Y : Scheme.{u}} (f : X ⟶ Y) :
    L A f ⋙ E A X ≅ E A Y ⋙ P A f := by
  let β : TwoSquare (R A f) (E A X) (E A Y) (S A f) := (push A f).hom
  have : IsIso β.natTrans := inferInstanceAs (IsIso (push A f).hom)
  have := inverseMate_isIso
    (adj A f) (adjFixed A f) β
  exact (asIso ((mateEquiv (adj A f) (adjFixed A f)).symm β).natTrans).symm

private abbrev comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :=
  StrictTower.moduleGComp (ULift.{u + 1, u} A) f g

private abbrev LD {X Y : Scheme.{u}} (f : X ⟶ Y) := (L A f).mapDerivedCategory

private def square (A : Type u) [CommRing A]
    {X' X Y' Y : Scheme.{u}} {h : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare h f' f g) :
    LD A g ⋙ LD A f' ≅ LD A f ⋙ LD A h :=
  Scheme.proEtaleAmbientRingedPullbackComparison sq
    (Scheme.proEtaleConstantRing X A) (Scheme.proEtaleConstantRing Y A)
    (Scheme.proEtaleConstantRing X' A) (Scheme.proEtaleConstantRing Y' A)
    (Scheme.proEtaleConstantRingComparison f A)
    (Scheme.proEtaleConstantRingComparison g A)
    (Scheme.proEtaleConstantRingComparison h A)
    (Scheme.proEtaleConstantRingComparison f' A)
    ((heq_of_eq (Scheme.proEtaleConstantRingCompositeCoefficients_eq h f A)).trans
      ((congr_arg_heq (fun q : X' ⟶ Y ↦ Scheme.proEtaleConstantRingComparison q A)
        sq.w).trans
          (heq_of_eq (Scheme.proEtaleConstantRingCompositeCoefficients_eq f' g A)).symm))

/-- The coefficient pullback square, over fixed category and functor instances.
Keeping this equation as one predicate gives concrete derived applications the same
implicit instance arguments as the abstract mate theorem.
Source: adjunction mate calculus, Bhatt--Scholze Lemma 6.5.9(3).
(blueprint: lem-pe-constant-exchange-encoding). -/
private def coefficientPullbackSquare
    (θ : G ⋙ V ⟶ U ⋙ H) (θe : Ge ⋙ Ve ⟶ Ue ⋙ He)
    (αU : U ⋙ T₂ ≅ T₁ ⋙ Ue) (αV : V ⋙ T₄ ≅ T₃ ⋙ Ve)
    (αG : G ⋙ T₃ ⟶ T₁ ⋙ Ge) (αH : H ⋙ T₄ ⟶ T₂ ⋙ He)
    (M : C₁) : Prop :=
  T₄.map (θ.app M) ≫ αH.app (U.obj M) ≫ He.map (αU.hom.app M) =
    αV.hom.app (G.obj M) ≫ Ve.map (αG.app M) ≫ θe.app (T₁.obj M)

/-- Pointwise coefficient transport requires the pull-comparison cube only at `R.obj K`.
The exchange maps and push comparisons satisfy their two counit mate equations.

Source: Mathlib's adjunction mates and Bhatt--Scholze, Lemma 6.5.9(3).
(blueprint: lem-pe-constant-exchange-encoding)

Proof. Apply injectivity of the second target adjunction's inverse Hom equivalence.
Replace both exchange maps by their adjuncts. Naturality of the target square moves
its first push comparison past the square map; its mate equation replaces the result.
Naturality of the target counit and the second mate equation rewrite the other side.
Move the mapped source exchange past the inverse pull comparison by naturality and
replace its adjunct. Naturality of the remaining horizontal comparison leaves the
pull-comparison cube precomposed and postcomposed with inverse vertical comparisons.
Cancel these isomorphisms. The resulting equality is the desired Hom-equivalence
image equality, hence the original coefficient/exchange equality. No map B or Be is
assumed invertible. -/
private theorem coefficient_exchange_of_counit_at
    (θ : G ⋙ V ⟶ U ⋙ H) (θe : Ge ⋙ Ve ⟶ Ue ⋙ He)
    (K : C₂)
    (B : (R ⋙ G).obj K ⟶ (H ⋙ S).obj K)
    (Be : (Re ⋙ Ge).obj (T₂.obj K) ⟶ (He ⋙ Se).obj (T₂.obj K))
    (hB : V.map B ≫ b.counit.app (H.obj K) =
      θ.app (R.obj K) ≫ H.map (a.counit.app K))
    (hBe : Ve.map Be ≫ be.counit.app (He.obj (T₂.obj K)) =
      θe.app (Re.obj (T₂.obj K)) ≫ He.map (ae.counit.app (T₂.obj K)))
    (αU : U ⋙ T₂ ≅ T₁ ⋙ Ue) (αV : V ⋙ T₄ ≅ T₃ ⋙ Ve)
    (αG : G ⋙ T₃ ⟶ T₁ ⋙ Ge) (αH : H ⋙ T₄ ⟶ T₂ ⋙ He)
    (δ : T₁.obj (R.obj K) ⟶ Re.obj (T₂.obj K))
    (δ' : T₃.obj (S.obj (H.obj K)) ⟶ Se.obj (T₄.obj (H.obj K)))
    (hδ : Ue.map δ ≫ ae.counit.app (T₂.obj K) =
      αU.inv.app (R.obj K) ≫ T₂.map (a.counit.app K))
    (hδ' : Ve.map δ' ≫ be.counit.app (T₄.obj (H.obj K)) =
      αV.inv.app (S.obj (H.obj K)) ≫ T₄.map (b.counit.app (H.obj K)))
    (hcube : coefficientPullbackSquare θ θe αU αV αG αH (R.obj K)) :
    αG.app (R.obj K) ≫ Ge.map δ ≫ Be =
      T₃.map B ≫ δ' ≫ Se.map (αH.app K) := by
  unfold coefficientPullbackSquare at hcube
  apply (be.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_symm_apply, Functor.map_comp, Category.assoc]
  rw [hBe]
  have hn := θe.naturality (δ)
  rw [reassoc_of% hn, ← Functor.map_comp, hδ]
  have hn' := be.counit.naturality (αH.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_map] at hn'
  rw [hn', reassoc_of% (hδ')]
  rw [reassoc_of% (αV.inv.naturality (B)), ← Functor.map_comp_assoc, hB]
  simp only [Functor.map_comp, Category.assoc]
  have hnH := αH.naturality (a.counit.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_map, Functor.id_obj] at hnH
  rw [hnH]
  have hc := congrArg (fun z ↦ αV.inv.app (G.obj (R.obj K)) ≫ z ≫
    He.map (αU.inv.app (R.obj K))) hcube
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app] at hc
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp] at hc
  simp only [Functor.comp_obj] at hc
  simpa only [Category.assoc, He.map_id, Category.id_comp] using congrArg
    (fun z ↦ z ≫ He.map (T₂.map (a.counit.app K))) hc.symm

/-- Exact constant-section restriction identifies the ringed and fixed-scalar mates.
No properness, torsion, classicality or boundedness assumption enters this comparison.
Source: Stacks Tag 07A7, and blueprint sk-thm-properbasechange, module and pro-etale
comparison paragraphs (blueprint: lem-pe-constant-exchange-encoding).
Proof: on module sheaves, restricting the scalar action along constant sections gives
an exact equivalence. Direct image in both encodings evaluates on the same base-changed
object, and the constant-section equation identifies its scalar action. Conjugate this
comparison through the normalized pullback/direct-image adjunctions to obtain the
pullback comparison. The sectionwise composition comparisons on direct images agree;
conjugation therefore identifies the two pullback squares. Apply the equivalences to
complexes. Exactness computes pullback termwise; equivalences transport K-injectives,
so the direct-image comparisons derive to isomorphisms. Their unit and counit equations
are preserved by derived adjunction. The normalized termwise characterization of the
ambient pullback comparison identifies it with this derived square. Expanding both mates
as unit, square and counit gives three commuting comparison squares. Compose them to
obtain the asserted arrow isomorphism.
-/
theorem proEtaleConstantExchange_encoding (A : Type u) [CommRing A]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g)
    (hc : HEq
      (proEtaleRingCompositeCoefficients g' f
        (proEtaleConstantRing Y A) (proEtaleConstantRing X A) (proEtaleConstantRing X' A)
        (proEtaleConstantRingComparison f A) (proEtaleConstantRingComparison g' A))
      (proEtaleRingCompositeCoefficients f' g
        (proEtaleConstantRing Y A) (proEtaleConstantRing Y' A) (proEtaleConstantRing X' A)
        (proEtaleConstantRingComparison g A) (proEtaleConstantRingComparison f' A)))
    (K : proEtaleDerivedCategory X A) :
    Nonempty (Arrow.mk ((proEtaleDerivedModuleRestriction Y' A).map
      ((proEtaleAmbientRingedExchange sq
        (proEtaleConstantRing X A) (proEtaleConstantRing Y A)
        (proEtaleConstantRing X' A) (proEtaleConstantRing Y' A)
        (proEtaleConstantRingComparison f A) (proEtaleConstantRingComparison g A)
        (proEtaleConstantRingComparison g' A) (proEtaleConstantRingComparison f' A) hc).app K)) ≅
      Arrow.mk ((ProEtale.derivedBaseChangeMap
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) sq.toCommSq).app
          ((proEtaleDerivedModuleRestriction X A).obj K))) := by
  sorry

end AlgebraicGeometry.Scheme
