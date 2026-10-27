module

public import Sheaf.Paper.FiniteTripleProductDefinitions
import Sheaf.Paper.FiniteProductOpenRestrictionPasting
import Sheaf.Paper.FiniteProductOrdinaryNaturality

/-! # Finite triple-product normal forms

Source: blueprint lem-sf-kunneth-coherence, clause (ii).
(blueprint: lem-pur-finite-triple-product-normal-forms).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe v u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

/-- Two binary identities and one naturality square paste to the left iterated identity. -/
private theorem finiteTripleProduct_substitute_left {D : Type u} [Category.{v} D]
    (T : D ⥤ D ⥤ D) {X Y Z W U V P Q R S : D}
    (m : (T.obj X).obj Y ⟶ W) (d : W ⟶ U)
    (c : Z ⟶ V) (a : (T.obj X).obj Y ⟶ P)
    (p : P ⟶ Q) (q : Q ⟶ U)
    (n : (T.obj W).obj Z ⟶ R) (e : R ⟶ S)
    (o : (T.obj U).obj V ⟶ S)
    (o' : (T.obj Q).obj V ⟶ S)
    (hinner : m ≫ d = a ≫ p ≫ q)
    (houter : n ≫ e = (T.map d).app Z ≫ (T.obj U).map c ≫ o)
    (hnat : (T.map q).app V ≫ o = o') :
    (T.map m).app Z ≫ n ≫ e =
      (T.map a).app Z ≫ (T.obj P).map c ≫ (T.map p).app V ≫ o' := by
  rw [houter, ← Category.assoc ((T.map m).app Z),
    ← NatTrans.comp_app, ← Functor.map_comp, hinner]
  simp only [Functor.map_comp, NatTrans.comp_app, Category.assoc]
  rw [← NatTrans.naturality_assoc, ← NatTrans.naturality_assoc, hnat]

/-- The analogous substitution in the second variable. -/
private theorem finiteTripleProduct_substitute_right {D : Type u} [Category.{v} D]
    (T : D ⥤ D ⥤ D) {X Y Z W U V P Q R S : D}
    (m : (T.obj Y).obj Z ⟶ W) (d : W ⟶ U)
    (c : X ⟶ V) (a : (T.obj Y).obj Z ⟶ P)
    (p : P ⟶ Q) (q : Q ⟶ U)
    (n : (T.obj X).obj W ⟶ R) (e : R ⟶ S)
    (o : (T.obj V).obj U ⟶ S)
    (o' : (T.obj V).obj Q ⟶ S)
    (hinner : m ≫ d = a ≫ p ≫ q)
    (houter : n ≫ e = (T.map c).app W ≫ (T.obj V).map d ≫ o)
    (hnat : (T.obj V).map q ≫ o = o') :
    (T.obj X).map m ≫ n ≫ e =
      (T.map c).app ((T.obj Y).obj Z) ≫ (T.obj V).map a ≫
        (T.obj V).map p ≫ o' := by
  rw [houter, (T.map c).naturality_assoc m, ← Functor.map_comp_assoc, hinner]
  simp only [Functor.map_comp, Category.assoc]
  rw [hnat]


namespace FiniteTripleProduct

private theorem binary_restriction (A : Type (u + 1)) [CommRing A] [Finite A]
    {B X Y : Scheme.{u}} {f : X ⟶ B} {g : Y ⟶ B}
    (G : FiniteProductGeometry f g) (M : D A X) (N : D A Y) :
    restrictPair A G M N ((extend A G.cf.i).obj M) ((extend A G.cg.i).obj N)
        ((openAdj A G.cf.i).unit.app M) ((openAdj A G.cg.i).unit.app N) ≫
      L(upperStar (ModuleCat.{u + 1} A) (finiteProductCompactification G).i).map
        (finiteProductOpenTensor G (ModuleCat.{u + 1} A) M N) =
      (openAdj A (finiteProductCompactification G).i).unit.app (external A G M N) := by
  have h := restrictPair_pasting A G M N ((extend A G.cf.i).obj M) ((extend A G.cg.i).obj N)
      ((openAdj A G.cf.i).unit.app M) ((openAdj A G.cg.i).unit.app N)
      (𝟙 _) (𝟙 _) (by simp) (by simp)
  have he : externalMap A G.r G.t
      (𝟙 ((extend A G.cf.i).obj M)) (𝟙 ((extend A G.cg.i).obj N)) = 𝟙 _ := by
    unfold externalMap
    simp
  rw [he] at h
  have hm := congrArg
    (L(upperStar (ModuleCat.{u + 1} A) (finiteProductCompactification G).i).map)
    (Category.id_comp (finiteProductOpenTensor G (ModuleCat.{u + 1} A) M N))
  exact (congrArg (fun k ↦ restrictPair A G M N
    ((extend A G.cf.i).obj M) ((extend A G.cg.i).obj N)
    ((openAdj A G.cf.i).unit.app M) ((openAdj A G.cg.i).unit.app N) ≫ k) hm).symm.trans h

private theorem unit_identity (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] (M : D A X) :
    (openAdj A j).unit.app M ≫ L(upperStar (ModuleCat.{u + 1} A) j).map
      (𝟙 ((extend A j).obj M)) = (openAdj A j).unit.app M := by
  simpa only [CategoryTheory.Functor.map_id, CategoryTheory.Functor.comp_obj,
    CategoryTheory.Functor.id_obj] using
    (Category.comp_id ((openAdj A j).unit.app M))

end FiniteTripleProduct

private theorem comparison_eq (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (c d : Compactification f) :
    finiteForwardCompactificationComparison A c d = towerCandidateComparison A c d := rfl

private theorem geometry_cf {B X Y : Scheme.{u}} {f : X ⟶ B} {g : Y ⟶ B}
    (c : Compactification f) (d : Compactification g) :
    (finiteProductGeometry c d).cf = c := rfl

private theorem geometry_cg {B X Y : Scheme.{u}} {f : X ⟶ B} {g : Y ⟶ B}
    (c : Compactification f) (d : Compactification g) :
    (finiteProductGeometry c d).cg = d := rfl

private theorem compactification_g {B X Y : Scheme.{u}} {f : X ⟶ B} {g : Y ⟶ B}
    (G : FiniteProductGeometry f g) :
    (finiteProductCompactification G).g = G.t ≫ G.cg.g := rfl

private theorem binary_equation (A : Type (u + 1)) [CommRing A] [Finite A]
    {B X Y : Scheme.{u}} {f : X ⟶ B} {g : Y ⟶ B}
    [QuasiCompact f] [QuasiCompact g]
    [HasCompactification f] [HasCompactification g]
    (G : FiniteProductGeometry f g) [HasCompactification (G.q ≫ g)]
    (c : Compactification f) (d : Compactification g)
    (e : Compactification (G.q ≫ g))
    (M : FiniteTripleProduct.D A X) (N : FiniteTripleProduct.D A Y)
    (hM : FiniteTripleProduct.origin A X M) (hN : FiniteTripleProduct.origin A Y N)
    (b : FiniteProductCompactificationDomain G A c d M N)
    (h : FiniteProductCompactificationEquation G A c d e M N hM hN b) :
    FiniteTripleProduct.xi A G c d e M N b.2.2.2.2.2 ≫
      (FiniteTripleProduct.compare A e (finiteProductCompactification G)
        (FiniteTripleProduct.external A G M N) b.2.2.2.2.2).hom =
    finiteProductTensorMapLeft (ModuleCat.{u + 1} A) B
        (FiniteTripleProduct.compare A c G.cf M hM).hom
        ((FiniteTripleProduct.support A d).obj N) ≫
      finiteProductTensorMapRight (ModuleCat.{u + 1} A) B
        ((FiniteTripleProduct.support A G.cf).obj M)
        (FiniteTripleProduct.compare A d G.cg N hN).hom ≫
      finiteProductOrdinary A G.cf.g G.cg.g G.sqT
        ((FiniteTripleProduct.extend A G.cf.i).obj M)
        ((FiniteTripleProduct.extend A G.cg.i).obj N) ≫
      R(lowerStar (ModuleCat.{u + 1} A) (G.t ≫ G.cg.g)).map
        (finiteProductOpenTensor G (ModuleCat.{u + 1} A) M N) := by
  dsimp only [FiniteProductCompactificationEquation, finiteProductForwardInCoordinates,
    finiteProductOrdinaryInCoordinates, finiteProductTargetModel, Iso.refl_inv,
    rightDerivedLowerShriekOfCompactification, finiteProductCompactification,
    CategoryTheory.Functor.comp_obj] at h
  rw [Category.comp_id] at h
  simpa only [FiniteTripleProduct.xi, FiniteTripleProduct.compare, comparison_eq,
    finiteProductTensorMapLeft, finiteProductTensorMapRight, Iso.app_hom,
    FiniteTripleProduct.support, FiniteTripleProduct.extend,
    rightDerivedLowerShriekOfCompactification,
    finiteProductCompactification, CategoryTheory.Functor.comp_obj,
    ObjectProperty.ι_obj] using h

/-- The two separate finite triple-product normal forms and their normalized
compactification-change compatibility.
Source: blueprint latest, lem-sf-kunneth-coherence.proof.md, clause (ii) and
proper reduction; the five-step concrete finite-level DAG argument
(blueprint: lem-pur-finite-triple-product-normal-forms).

Proof:
1. Form the binary and both iterated product compactifications. Base change and
composition preserve openness and properness, and the universal property identifies
both bracketings with the triple fibre product. All schemes and maps retain the
standing finite-type class.
2. The binary open comparison is the same normalized e as in
lem-pur-finite-open-product-swap: both restrict to the identity, which characterizes
a map into open extension by its fully faithful adjunction. Each binary comparison
and the canonical extension compositor is invertible. Pulling back and tensoring
preserves their restriction equations; hence both pasted comparisons are invertible
and satisfy the two displayed triple-unit equations, separately.
3. Apply lem-pur-finite-product-compactification first to (1,2), then to (12,3).
The normalized comparison for the inner target is the same as the outer source.
Substitute both equations. Naturality of ordinary exchange, projection and symmetry,
and of the ordinary direct-image compositor, moves Ra12*(e12) through the outer
ordinary product. Functoriality gives Rc*(e_L) after the left ordinary triple word.
The domain conditions supply the origin and bounded-below hypotheses for every tensor.
4. Repeat with (2,3) and (1,23). Naturality in the second input moves Ra23*(e23)
through the outer ordinary product and yields the right equation with Rc*(e_R).
These calculations do not compare the two ordinary words or invert PF or exchange.
5. Repeat both binary identities for arbitrary original and displayed compactifications.
The normalized comparisons and composition isomorphisms are independent of all choices;
common refinements and their cocycle identify the endpoint transports. Thus each
right-hand normal form is the same forward iterate in every original coordinate
system, proving compatibility for every refinement and arbitrary change of choices.
-/
theorem finiteTripleProduct_normalForms (C : WeilConjectures.PurityFiniteSetting.{u})
    {B X₁ X₂ X₃ : Scheme.{u}}
    [B.Over (Spec (.of C.field.k))] [X₁.Over (Spec (.of C.field.k))]
    [X₂.Over (Spec (.of C.field.k))] [X₃.Over (Spec (.of C.field.k))]
    [IsSeparated (B ↘ Spec (.of C.field.k))]
    [IsSeparated (X₁ ↘ Spec (.of C.field.k))]
    [IsSeparated (X₂ ↘ Spec (.of C.field.k))]
    [IsSeparated (X₃ ↘ Spec (.of C.field.k))]
    [LocallyOfFiniteType (B ↘ Spec (.of C.field.k))]
    [LocallyOfFiniteType (X₁ ↘ Spec (.of C.field.k))]
    [LocallyOfFiniteType (X₂ ↘ Spec (.of C.field.k))]
    [LocallyOfFiniteType (X₃ ↘ Spec (.of C.field.k))]
    [QuasiCompact (B ↘ Spec (.of C.field.k))]
    [QuasiCompact (X₁ ↘ Spec (.of C.field.k))]
    [QuasiCompact (X₂ ↘ Spec (.of C.field.k))]
    [QuasiCompact (X₃ ↘ Spec (.of C.field.k))]
    (f₁ : X₁ ⟶ B) (f₂ : X₂ ⟶ B) (f₃ : X₃ ⟶ B)
    [f₁.IsOver (Spec (.of C.field.k))] [f₂.IsOver (Spec (.of C.field.k))]
    [f₃.IsOver (Spec (.of C.field.k))]
    [IsSeparated f₁] [LocallyOfFiniteType f₁] [QuasiCompact f₁]
    [IsSeparated f₂] [LocallyOfFiniteType f₂] [QuasiCompact f₂]
    [IsSeparated f₃] [LocallyOfFiniteType f₃] [QuasiCompact f₃]
    (M₁ : _root_.DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology X₁) (ModuleCat.{u + 1} C.Coefficient)))
    (M₂ : _root_.DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology X₂) (ModuleCat.{u + 1} C.Coefficient)))
    (M₃ : _root_.DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology X₃) (ModuleCat.{u + 1} C.Coefficient)))
    (w₁ : Scheme.FixedEtaleOriginWitness X₁ C.Coefficient M₁)
    (w₂ : Scheme.FixedEtaleOriginWitness X₂ C.Coefficient M₂)
    (w₃ : Scheme.FixedEtaleOriginWitness X₃ C.Coefficient M₃) :
    FiniteTripleProductNormalForms C f₁ f₂ f₃ M₁ M₂ M₃ w₁ w₂ w₃ := by
  let : CompactSpace B := QuasiCompact.compactSpace_of_compactSpace
    (B ↘ Spec (.of C.field.k))
  let : QuasiSeparatedSpace B := quasiSeparatedSpace_of_quasiSeparated
    (B ↘ Spec (.of C.field.k))
  let : CompactSpace X₁ := QuasiCompact.compactSpace_of_compactSpace
    (X₁ ↘ Spec (.of C.field.k))
  let : QuasiSeparatedSpace X₁ := quasiSeparatedSpace_of_quasiSeparated
    (X₁ ↘ Spec (.of C.field.k))
  let : CompactSpace X₂ := QuasiCompact.compactSpace_of_compactSpace
    (X₂ ↘ Spec (.of C.field.k))
  let : QuasiSeparatedSpace X₂ := quasiSeparatedSpace_of_quasiSeparated
    (X₂ ↘ Spec (.of C.field.k))
  let : CompactSpace X₃ := QuasiCompact.compactSpace_of_compactSpace
    (X₃ ↘ Spec (.of C.field.k))
  let : QuasiSeparatedSpace X₃ := quasiSeparatedSpace_of_quasiSeparated
    (X₃ ↘ Spec (.of C.field.k))
  intro c₁ c₂ c₃ o₁ o₂ o₃ o₁₂ o₂₃ oL oR sL sR b₁₂ b₂₃ bL bR
  have h₁₂ := (finiteProduct_compactification C f₁ f₂ M₁ M₂ w₁ w₂)
    c₁ c₂ o₁ o₂ o₁₂ b₁₂
  have h₂₃ := (finiteProduct_compactification C f₂ f₃ M₂ M₃ w₂ w₃)
    c₂ c₃ o₂ o₃ o₂₃ b₂₃
  let : (FiniteTripleProduct.g12 c₁ c₂).P.Over (Spec (.of C.field.k)) :=
    ⟨((FiniteTripleProduct.g12 c₁ c₂).q ≫ f₂) ≫ B ↘ Spec (.of C.field.k)⟩
  let : (FiniteTripleProduct.g23 c₂ c₃).P.Over (Spec (.of C.field.k)) :=
    ⟨((FiniteTripleProduct.g23 c₂ c₃).q ≫ f₃) ≫ B ↘ Spec (.of C.field.k)⟩
  let : ((FiniteTripleProduct.g12 c₁ c₂).q ≫ f₂).IsOver
      (Spec (.of C.field.k)) := ⟨rfl⟩
  let : ((FiniteTripleProduct.g23 c₂ c₃).q ≫ f₃).IsOver
      (Spec (.of C.field.k)) := ⟨rfl⟩
  have : IsSeparated ((FiniteTripleProduct.g12 c₁ c₂).q ≫ f₂) := by
    dsimp [FiniteTripleProduct.g12, finiteProductGeometry]
    infer_instance
  have : LocallyOfFiniteType ((FiniteTripleProduct.g12 c₁ c₂).q ≫ f₂) := by
    dsimp [FiniteTripleProduct.g12, finiteProductGeometry]
    infer_instance
  have : IsSeparated ((FiniteTripleProduct.g23 c₂ c₃).q ≫ f₃) := by
    dsimp [FiniteTripleProduct.g23, finiteProductGeometry]
    infer_instance
  have : LocallyOfFiniteType ((FiniteTripleProduct.g23 c₂ c₃).q ≫ f₃) := by
    dsimp [FiniteTripleProduct.g23, finiteProductGeometry]
    infer_instance
  have : IsSeparated ((FiniteTripleProduct.g12 c₁ c₂).P ↘ Spec (.of C.field.k)) :=
    inferInstanceAs (IsSeparated
      (((FiniteTripleProduct.g12 c₁ c₂).q ≫ f₂) ≫ B ↘ Spec (.of C.field.k)))
  have : LocallyOfFiniteType ((FiniteTripleProduct.g12 c₁ c₂).P ↘ Spec (.of C.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType
      (((FiniteTripleProduct.g12 c₁ c₂).q ≫ f₂) ≫ B ↘ Spec (.of C.field.k)))
  have : QuasiCompact ((FiniteTripleProduct.g12 c₁ c₂).P ↘ Spec (.of C.field.k)) :=
    inferInstanceAs (QuasiCompact
      (((FiniteTripleProduct.g12 c₁ c₂).q ≫ f₂) ≫ B ↘ Spec (.of C.field.k)))
  have : IsSeparated ((FiniteTripleProduct.g23 c₂ c₃).P ↘ Spec (.of C.field.k)) :=
    inferInstanceAs (IsSeparated
      (((FiniteTripleProduct.g23 c₂ c₃).q ≫ f₃) ≫ B ↘ Spec (.of C.field.k)))
  have : LocallyOfFiniteType ((FiniteTripleProduct.g23 c₂ c₃).P ↘ Spec (.of C.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType
      (((FiniteTripleProduct.g23 c₂ c₃).q ≫ f₃) ≫ B ↘ Spec (.of C.field.k)))
  have : QuasiCompact ((FiniteTripleProduct.g23 c₂ c₃).P ↘ Spec (.of C.field.k)) :=
    inferInstanceAs (QuasiCompact
      (((FiniteTripleProduct.g23 c₂ c₃).q ≫ f₃) ≫ B ↘ Spec (.of C.field.k)))
  let N₁₂ : _root_.DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology (FiniteTripleProduct.g12 c₁ c₂).P)
        (ModuleCat.{u + 1} C.Coefficient)) :=
    ⟨FiniteTripleProduct.d12 C.Coefficient c₁ c₂ M₁.obj M₂.obj, b₁₂.2.2.2.2.2.plus⟩
  let N₂₃ : _root_.DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology (FiniteTripleProduct.g23 c₂ c₃).P)
        (ModuleCat.{u + 1} C.Coefficient)) :=
    ⟨FiniteTripleProduct.d23 C.Coefficient c₂ c₃ M₂.obj M₃.obj, b₂₃.2.2.2.2.2.plus⟩
  obtain ⟨K₁₂, hK₁₂, ⟨i₁₂⟩⟩ := b₁₂.2.2.2.2.2
  obtain ⟨K₂₃, hK₂₃, ⟨i₂₃⟩⟩ := b₂₃.2.2.2.2.2
  let w₁₂ : Scheme.FixedEtaleOriginWitness _ C.Coefficient N₁₂ :=
    ⟨⟨K₁₂, hK₁₂⟩, i₁₂⟩
  let w₂₃ : Scheme.FixedEtaleOriginWitness _ C.Coefficient N₂₃ :=
    ⟨⟨K₂₃, hK₂₃⟩, i₂₃⟩
  have hL := (finiteProduct_compactification C
    ((FiniteTripleProduct.g12 c₁ c₂).q ≫ f₂) f₃ N₁₂ M₃ w₁₂ w₃)
    (finiteProductCompactification (FiniteTripleProduct.g12 c₁ c₂)) c₃ o₁₂ o₃ oL bL
  have hR := (finiteProduct_compactification C f₁
    ((FiniteTripleProduct.g23 c₂ c₃).q ≫ f₃) M₁ N₂₃ w₁ w₂₃)
    c₁ (finiteProductCompactification (FiniteTripleProduct.g23 c₂ c₃)) o₁ o₂₃ oR bR
  have h₁₂' := binary_equation C.Coefficient _ _ _ _ _ _ _ _ _ h₁₂
  have h₂₃' := binary_equation C.Coefficient _ _ _ _ _ _ _ _ _ h₂₃
  have hL' := binary_equation C.Coefficient _ _ _ _ _ _ _ _ _ hL
  have hR' := binary_equation C.Coefficient _ _ _ _ _ _ _ _ _ hR
  have := finiteProductOpenTensor_isIso (FiniteTripleProduct.g12 c₁ c₂)
    C.Coefficient M₁.obj M₂.obj
  have := finiteProductOpenTensor_isIso (FiniteTripleProduct.g23 c₂ c₃)
    C.Coefficient M₂.obj M₃.obj
  have := finiteProductOpenTensor_isIso (FiniteTripleProduct.gL c₁ c₂ c₃)
    C.Coefficient (FiniteTripleProduct.d12 C.Coefficient c₁ c₂ M₁.obj M₂.obj) M₃.obj
  have := finiteProductOpenTensor_isIso (FiniteTripleProduct.gR c₁ c₂ c₃)
    C.Coefficient M₁.obj (FiniteTripleProduct.d23 C.Coefficient c₂ c₃ M₂.obj M₃.obj)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold FiniteTripleProduct.eL FiniteTripleProduct.externalMap
    infer_instance
  · unfold FiniteTripleProduct.eR FiniteTripleProduct.externalMap
    infer_instance
  · exact FiniteTripleProduct.restrictPair_pasting C.Coefficient
      (FiniteTripleProduct.gL c₁ c₂ c₃)
      (FiniteTripleProduct.d12 C.Coefficient c₁ c₂ M₁.obj M₂.obj) M₃.obj
      (FiniteTripleProduct.e12Source C.Coefficient c₁ c₂ M₁.obj M₂.obj)
      ((FiniteTripleProduct.extend C.Coefficient c₃.i).obj M₃.obj)
      (FiniteTripleProduct.restriction12 C.Coefficient c₁ c₂ M₁.obj M₂.obj)
      ((FiniteTripleProduct.openAdj C.Coefficient c₃.i).unit.app M₃.obj)
      (finiteProductOpenTensor (FiniteTripleProduct.g12 c₁ c₂)
        (ModuleCat.{u + 1} C.Coefficient) M₁.obj M₂.obj) (𝟙 _)
      (FiniteTripleProduct.binary_restriction C.Coefficient
        (FiniteTripleProduct.g12 c₁ c₂) M₁.obj M₂.obj)
      (FiniteTripleProduct.unit_identity C.Coefficient c₃.i M₃.obj)
  · exact FiniteTripleProduct.restrictPair_pasting C.Coefficient
      (FiniteTripleProduct.gR c₁ c₂ c₃)
      M₁.obj (FiniteTripleProduct.d23 C.Coefficient c₂ c₃ M₂.obj M₃.obj)
      ((FiniteTripleProduct.extend C.Coefficient c₁.i).obj M₁.obj)
      (FiniteTripleProduct.e23Source C.Coefficient c₂ c₃ M₂.obj M₃.obj)
      ((FiniteTripleProduct.openAdj C.Coefficient c₁.i).unit.app M₁.obj)
      (FiniteTripleProduct.restriction23 C.Coefficient c₂ c₃ M₂.obj M₃.obj)
      (𝟙 _) (finiteProductOpenTensor (FiniteTripleProduct.g23 c₂ c₃)
        (ModuleCat.{u + 1} C.Coefficient) M₂.obj M₃.obj)
      (FiniteTripleProduct.unit_identity C.Coefficient c₁.i M₁.obj)
      (FiniteTripleProduct.binary_restriction C.Coefficient
        (FiniteTripleProduct.g23 c₂ c₃) M₂.obj M₃.obj)
  · let A := C.Coefficient
    let G := FiniteTripleProduct.gL c₁ c₂ c₃
    let E := FiniteTripleProduct.e12Source A c₁ c₂ M₁.obj M₂.obj
    let H := (FiniteTripleProduct.extend A
      (finiteProductCompactification (FiniteTripleProduct.g12 c₁ c₂)).i).obj N₁₂.obj
    let J := (FiniteTripleProduct.extend A c₃.i).obj M₃.obj
    let e₁₂ := finiteProductOpenTensor (FiniteTripleProduct.g12 c₁ c₂)
      (ModuleCat.{u + 1} A) M₁.obj M₂.obj
    let eout := finiteProductOpenTensor G (ModuleCat.{u + 1} A) N₁₂.obj M₃.obj
    let F := R(lowerStar (ModuleCat.{u + 1} A) (G.t ≫ c₃.g))
    have hn := finiteProductOrdinary_naturality A
      (finiteProductCompactification (FiniteTripleProduct.g12 c₁ c₂)).g c₃.g
      G.sqT e₁₂ (𝟙 J)
    dsimp only [finiteProductTensorMapRight] at hn
    simp only [CategoryTheory.Functor.map_id, Category.id_comp] at hn
    have hb := finiteTripleProduct_substitute_left (derivedTensor (ModuleCat.{u + 1} A) B)
      (FiniteTripleProduct.xi A (FiniteTripleProduct.g12 c₁ c₂)
        o₁ o₂ o₁₂ M₁.obj M₂.obj b₁₂.2.2.2.2.2)
      (FiniteTripleProduct.compare A o₁₂
        (finiteProductCompactification (FiniteTripleProduct.g12 c₁ c₂))
        N₁₂.obj b₁₂.2.2.2.2.2).hom
      (FiniteTripleProduct.compare A o₃ c₃ M₃.obj
        ⟨w₃.complex.obj, w₃.complex.property, ⟨w₃.iso⟩⟩).hom
      (finiteProductTensorMapLeft (ModuleCat.{u + 1} A) B
          (FiniteTripleProduct.compare A o₁ c₁ M₁.obj
            ⟨w₁.complex.obj, w₁.complex.property, ⟨w₁.iso⟩⟩).hom
          ((FiniteTripleProduct.support A o₂).obj M₂.obj) ≫
        finiteProductTensorMapRight (ModuleCat.{u + 1} A) B
          ((FiniteTripleProduct.support A c₁).obj M₁.obj)
          (FiniteTripleProduct.compare A o₂ c₂ M₂.obj
            ⟨w₂.complex.obj, w₂.complex.property, ⟨w₂.iso⟩⟩).hom)
      (finiteProductOrdinary A c₁.g c₂.g (FiniteTripleProduct.g12 c₁ c₂).sqT
        ((FiniteTripleProduct.extend A c₁.i).obj M₁.obj)
        ((FiniteTripleProduct.extend A c₂.i).obj M₂.obj))
      (R(lowerStar (ModuleCat.{u + 1} A)
        (finiteProductCompactification (FiniteTripleProduct.g12 c₁ c₂)).g).map e₁₂)
      (FiniteTripleProduct.xi A G o₁₂ o₃ oL N₁₂.obj M₃.obj bL.2.2.2.2.2)
      (FiniteTripleProduct.compare A oL (finiteProductCompactification G)
        (FiniteTripleProduct.dL A c₁ c₂ c₃ M₁.obj M₂.obj M₃.obj) bL.2.2.2.2.2).hom
      (finiteProductOrdinary A
        (finiteProductCompactification (FiniteTripleProduct.g12 c₁ c₂)).g c₃.g
        G.sqT H J ≫ F.map eout)
      (finiteProductOrdinary A
        (finiteProductCompactification (FiniteTripleProduct.g12 c₁ c₂)).g c₃.g
        G.sqT E J ≫ F.map (FiniteTripleProduct.externalMap A G.r G.t e₁₂ (𝟙 J)) ≫
          F.map eout)
      (by simpa only [FiniteTripleProduct.g12, FiniteTripleProduct.g23,
        FiniteTripleProduct.gL, FiniteTripleProduct.gR, geometry_cf, geometry_cg,
        compactification_g, Category.assoc, A, e₁₂, N₁₂,
        CategoryTheory.Functor.comp_obj, ObjectProperty.ι_obj] using h₁₂')
      (by simpa only [FiniteTripleProduct.g12, FiniteTripleProduct.g23,
        FiniteTripleProduct.gL, FiniteTripleProduct.gR, geometry_cf, geometry_cg,
        compactification_g, Category.assoc, A, G, H, J, F, eout, N₁₂,
        finiteProductTensorMapLeft, finiteProductTensorMapRight,
        FiniteTripleProduct.support, rightDerivedLowerShriekOfCompactification,
        CategoryTheory.Functor.comp_obj, ObjectProperty.ι_obj] using hL')
      (by simpa only [finiteProductTensorMapLeft, finiteProductTensorMapRight,
        FiniteTripleProduct.support, rightDerivedLowerShriekOfCompactification,
        compactification_g, CategoryTheory.Functor.comp_obj, ObjectProperty.ι_obj,
        Category.assoc, H, J, E, F, G, FiniteTripleProduct.e12Source,
        FiniteTripleProduct.e23Source, FiniteTripleProduct.g12, FiniteTripleProduct.g23,
        finiteProductExtendedTensor, geometry_cf, geometry_cg,
        FiniteTripleProduct.extend, finiteProductCompactification, FiniteTripleProduct.dL,
        FiniteTripleProduct.dR, FiniteTripleProduct.d12, FiniteTripleProduct.d23,
        FiniteTripleProduct.external, N₁₂, N₂₃] using
        congrArg (fun k ↦ k ≫ F.map eout) hn)
    simpa only [FiniteTripleProduct.thetaL, FiniteTripleProduct.sourceL,
      FiniteTripleProduct.ordinaryL, FiniteTripleProduct.eL, finiteProductTensorMapLeft,
      finiteProductTensorMapRight, Functor.map_comp, NatTrans.comp_app, Category.assoc,
      A, G, E, H, J, e₁₂, eout, F, N₁₂, FiniteTripleProduct.tensor,
      CategoryTheory.Functor.comp_obj, ObjectProperty.ι_obj,
      FiniteTripleProduct.support, rightDerivedLowerShriekOfCompactification,
      FiniteTripleProduct.gL, geometry_cg, FiniteTripleProduct.extend] using hb
  · let A := C.Coefficient
    let G := FiniteTripleProduct.gR c₁ c₂ c₃
    let E := FiniteTripleProduct.e23Source A c₂ c₃ M₂.obj M₃.obj
    let H := (FiniteTripleProduct.extend A c₁.i).obj M₁.obj
    let J := (FiniteTripleProduct.extend A
      (finiteProductCompactification (FiniteTripleProduct.g23 c₂ c₃)).i).obj N₂₃.obj
    let e₂₃ := finiteProductOpenTensor (FiniteTripleProduct.g23 c₂ c₃)
      (ModuleCat.{u + 1} A) M₂.obj M₃.obj
    let eout := finiteProductOpenTensor G (ModuleCat.{u + 1} A) M₁.obj N₂₃.obj
    let F := R(lowerStar (ModuleCat.{u + 1} A)
      (G.t ≫ (finiteProductCompactification (FiniteTripleProduct.g23 c₂ c₃)).g))
    have hn := finiteProductOrdinary_naturality A c₁.g
      (finiteProductCompactification (FiniteTripleProduct.g23 c₂ c₃)).g
      G.sqT (𝟙 H) e₂₃
    dsimp only [finiteProductTensorMapLeft] at hn
    simp only [CategoryTheory.Functor.map_id, NatTrans.id_app,
      Category.id_comp] at hn
    have hb := finiteTripleProduct_substitute_right (derivedTensor (ModuleCat.{u + 1} A) B)
      (FiniteTripleProduct.xi A (FiniteTripleProduct.g23 c₂ c₃)
        o₂ o₃ o₂₃ M₂.obj M₃.obj b₂₃.2.2.2.2.2)
      (FiniteTripleProduct.compare A o₂₃
        (finiteProductCompactification (FiniteTripleProduct.g23 c₂ c₃))
        N₂₃.obj b₂₃.2.2.2.2.2).hom
      (FiniteTripleProduct.compare A o₁ c₁ M₁.obj
        ⟨w₁.complex.obj, w₁.complex.property, ⟨w₁.iso⟩⟩).hom
      (finiteProductTensorMapLeft (ModuleCat.{u + 1} A) B
          (FiniteTripleProduct.compare A o₂ c₂ M₂.obj
            ⟨w₂.complex.obj, w₂.complex.property, ⟨w₂.iso⟩⟩).hom
          ((FiniteTripleProduct.support A o₃).obj M₃.obj) ≫
        finiteProductTensorMapRight (ModuleCat.{u + 1} A) B
          ((FiniteTripleProduct.support A c₂).obj M₂.obj)
          (FiniteTripleProduct.compare A o₃ c₃ M₃.obj
            ⟨w₃.complex.obj, w₃.complex.property, ⟨w₃.iso⟩⟩).hom)
      (finiteProductOrdinary A c₂.g c₃.g (FiniteTripleProduct.g23 c₂ c₃).sqT
        ((FiniteTripleProduct.extend A c₂.i).obj M₂.obj)
        ((FiniteTripleProduct.extend A c₃.i).obj M₃.obj))
      (R(lowerStar (ModuleCat.{u + 1} A)
        (finiteProductCompactification (FiniteTripleProduct.g23 c₂ c₃)).g).map e₂₃)
      (FiniteTripleProduct.xi A G o₁ o₂₃ oR M₁.obj N₂₃.obj bR.2.2.2.2.2)
      (FiniteTripleProduct.compare A oR (finiteProductCompactification G)
        (FiniteTripleProduct.dR A c₁ c₂ c₃ M₁.obj M₂.obj M₃.obj) bR.2.2.2.2.2).hom
      (finiteProductOrdinary A c₁.g
        (finiteProductCompactification (FiniteTripleProduct.g23 c₂ c₃)).g
        G.sqT H J ≫ F.map eout)
      (finiteProductOrdinary A c₁.g
        (finiteProductCompactification (FiniteTripleProduct.g23 c₂ c₃)).g
        G.sqT H E ≫ F.map (FiniteTripleProduct.externalMap A G.r G.t (𝟙 H) e₂₃) ≫
          F.map eout)
      (by simpa only [FiniteTripleProduct.g12, FiniteTripleProduct.g23,
        FiniteTripleProduct.gL, FiniteTripleProduct.gR, geometry_cf, geometry_cg,
        compactification_g, Category.assoc, A, e₂₃, N₂₃,
        CategoryTheory.Functor.comp_obj, ObjectProperty.ι_obj] using h₂₃')
      (by simpa only [FiniteTripleProduct.g12, FiniteTripleProduct.g23,
        FiniteTripleProduct.gL, FiniteTripleProduct.gR, geometry_cf, geometry_cg,
        compactification_g, Category.assoc, A, G, H, J, F, eout, N₂₃,
        finiteProductTensorMapLeft, finiteProductTensorMapRight,
        FiniteTripleProduct.support, rightDerivedLowerShriekOfCompactification,
        CategoryTheory.Functor.comp_obj, ObjectProperty.ι_obj] using hR')
      (by simpa only [finiteProductTensorMapLeft, finiteProductTensorMapRight,
        FiniteTripleProduct.support, rightDerivedLowerShriekOfCompactification,
        compactification_g, CategoryTheory.Functor.comp_obj, ObjectProperty.ι_obj,
        Category.assoc, H, J, E, F, G, FiniteTripleProduct.e12Source,
        FiniteTripleProduct.e23Source, FiniteTripleProduct.g12, FiniteTripleProduct.g23,
        finiteProductExtendedTensor, geometry_cf, geometry_cg,
        FiniteTripleProduct.extend, finiteProductCompactification, FiniteTripleProduct.dL,
        FiniteTripleProduct.dR, FiniteTripleProduct.d12, FiniteTripleProduct.d23,
        FiniteTripleProduct.external, N₁₂, N₂₃] using
        congrArg (fun k ↦ k ≫ F.map eout) hn)
    simpa only [FiniteTripleProduct.thetaR, FiniteTripleProduct.sourceR,
      FiniteTripleProduct.ordinaryR, FiniteTripleProduct.eR, finiteProductTensorMapLeft,
      finiteProductTensorMapRight, Functor.map_comp, NatTrans.comp_app, Category.assoc,
      A, G, E, H, J, e₂₃, eout, F, N₂₃, FiniteTripleProduct.tensor,
      CategoryTheory.Functor.comp_obj, ObjectProperty.ι_obj,
      FiniteTripleProduct.support, rightDerivedLowerShriekOfCompactification,
      FiniteTripleProduct.gR, geometry_cf] using hb

end AlgebraicGeometry.ProEtale
