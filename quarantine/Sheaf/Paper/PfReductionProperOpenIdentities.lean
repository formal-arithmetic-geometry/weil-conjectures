module

public import Sheaf.Paper.SixFunctorDatum
public import Sheaf.Paper.BasicOperationsCoefficientReduction
public import Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness
public import Sheaf.Paper.EtaleCompactSupportCoefficientChange
public import Sheaf.SixFunctors.OpenScalarTensorData
public import Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction
public import Sheaf.Paper.CompactSupportScalarCoordinates
public import WeilConjectures.Compactification.RefinementCategory
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
import all Sheaf.SixFunctors.OpenScalarTensorNormalization
import all Sheaf.Paper.RingedExchangeTensorCoherence
import Sheaf.SecSmoothPurity.ProperScalarCounitSquare
import Sheaf.Paper.OpenScalarCounitSquare
import Sheaf.SixFunctors.ScalarPullbackTensorCoherence
import Sheaf.SixFunctors.ScalarPullbackCompositionCoherence

/-! # Proper and open identities for coefficient reduction

Source: current blueprint main-20261015, sk-prop-sf-pf-reduction, transpose/counit
paragraph; Stacks Tags 0E48, 0GL1 and 0GL6
(blueprint: lem-sf-pf-reduction-proper-open-identities).

The helpers spell out the specified maps in normalized K-flat tensor presentations.
In particular the compact-support map is defined by its scalar adjunct, independently
of the proper/open factorization asserted in the theorem.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
open AlgebraicGeometry.ProEtale.OpenScalarTensor
namespace AlgebraicGeometry.ProEtale.PfReductionFactors


private theorem scalar_unit_of_counit
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {S : A ⥤ B} {U : B ⥤ A} {T : C ⥤ D} {V : D ⥤ C}
    (a : S ⊣ U) (b : T ⊣ V) (F : C ⥤ A) (G : D ⥤ B)
    (c : F ⋙ S ⟶ T ⋙ G) (v : V ⋙ F ⟶ G ⋙ U)
    (hc : ∀ N, S.map (v.app N) ≫ a.counit.app (G.obj N) =
      c.app (V.obj N) ≫ G.map (b.counit.app N)) (M : C) :
    a.unit.app (F.obj M) ≫ U.map (c.app M) =
      F.map (b.unit.app M) ≫ v.app (T.obj M) := by
  apply (a.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, S.map_comp, Category.assoc]
  rw [a.counit_naturality, ← Category.assoc, a.left_triangle_components (F.obj M)]
  dsimp only [Functor.comp_obj]
  rw [hc]
  have hn := c.naturality (b.unit.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
  erw [← Category.assoc, hn, Category.assoc, ← G.map_comp,
    b.left_triangle_components, G.map_id, Category.comp_id]
  exact Category.id_comp _

/-- The counit-defined proper projection, without an invertibility assertion.
Source: Stacks 0E48 (blueprint: lem-sf-pf-reduction-proper-open-identities). -/
def properProjection (m : Models.{u}) (A : Type u) [CommRing A]
    {Z Y : Scheme.{u}} (r : Z ⟶ Y)
    (M : proEtaleDerivedCategory Z A) (L : proEtaleDerivedCategory Y A) :
    (tensor.{u} m A Y).obj ((directImageConstantPush.{u} A r).obj M, L) ⟶
      (directImageConstantPush.{u} A r).obj
        ((tensor.{u} m A Z).obj (M, (constantPullback.{u} (A := A) r).obj L)) :=
  (directImageConstantAdjunction.{u} A r).homEquiv _ _
    ((restrictionTensor.{u} m A r).hom.app ((directImageConstantPush.{u} A r).obj M, L) ≫
      (tensor.{u} m A Z).map
        (Prod.mkHom ((directImageConstantAdjunction.{u} A r).counit.app M) (𝟙 _)))

/-- The specified proper coefficient map is the adjunction mate of inverse t_r.
Source: Stacks 07A7 (blueprint: lem-sf-pf-reduction-proper-open-identities). -/
def properScalar (m : Models.{u}) {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z Y : Scheme.{u}} (r : Z ⟶ Y) :
    directImageConstantPush.{u} A r ⋙ scalar.{u} m φ Y ⟶
      scalar.{u} m φ Z ⋙ directImageConstantPush.{u} B r :=
  (mateEquiv (directImageConstantAdjunction.{u} A r) (directImageConstantAdjunction.{u} B r)
    (lambda.{u} m φ r).hom).natTrans

private theorem properScalar_coordinates (m : Models.{u})
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    {Z Y : Scheme.{u}} (r : Z ⟶ Y) (M : proEtaleDerivedCategory Z A) :
    (properScalar m φ r).app M =
      (scalarIso m φ Y).hom.app ((directImageConstantPush A r).obj M) ≫
        (directImageScalarComparison φ r).app M ≫
          (directImageConstantPush B r).map ((scalarIso m φ Z).inv.app M) := by
  simp only [properScalar, lambda, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Iso.symm_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    directImageScalarComparison, mateEquiv_apply, TwoSquare.mk, TwoSquare.natTrans,
    Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.map_comp, Functor.comp_map, Functor.comp_obj, Category.id_comp,
    Category.assoc]
  dsimp only [Functor.comp_obj, Functor.id_obj]
  simp only [Category.comp_id]
  have hy := (directImageConstantAdjunction B r).unit.naturality
    ((scalarIso m φ Y).hom.app ((directImageConstantPush A r).obj M))
  dsimp only [Functor.comp_map, Functor.id_map] at hy
  rw [← reassoc_of% hy]
  have hz := (scalarIso m φ Z).inv.naturality
    ((directImageConstantAdjunction A r).counit.app M)
  dsimp only [Functor.comp_obj, Functor.id_obj] at hz
  simp only [← (directImageConstantPush B r).map_comp]
  erw [← hz]
  simp only [Functor.map_comp]
  erw [Category.id_comp]
  rfl

attribute [-instance] WeilConjectures.IntegralHom.derivedCategory in
private theorem properScalar_unit (m : Models.{u})
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Z Y : Scheme.{u}} (r : Z ⟶ Y)
    (M : proEtaleDerivedCategory Z A) :
    (scalarPair m φ Y).adjunction.unit.app ((directImageConstantPush A r).obj M) ≫
        (scalarRestriction φ Y).map ((properScalar m φ r).app M) =
      (directImageConstantPush A r).map ((scalarPair m φ Z).adjunction.unit.app M) ≫
        (directImageScalarRestrictionIso φ r).hom.app ((scalar m φ Z).obj M) := by
  let aY := directImageScalarAdjunction φ Y
  let aZ := directImageScalarAdjunction φ Z
  have hu := scalar_unit_of_counit aY aZ
    (directImageConstantPush A r) (directImageConstantPush B r)
    (directImageScalarComparison φ r) (directImageScalarRestrictionIso φ r).hom
    (fun N ↦ (properScalarCounitSquare φ r).2.2.1 N |>.2) M
  rw [properScalar_coordinates]
  simp only [Functor.map_comp, ← Category.assoc]
  erw [(scalarPair m φ Y).adjunction.unit_leftAdjointUniq_hom_app aY]
  try simp only [Category.assoc]
  erw [reassoc_of% hu]
  have hn := (directImageScalarRestrictionIso φ r).hom.naturality
    ((scalarIso m φ Z).inv.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
  erw [← hn, ← (directImageConstantPush A r).map_comp_assoc]
  congr 1
  have hz := aZ.unit_leftAdjointUniq_hom_app (scalarPair m φ Z).adjunction M
  simpa only [scalarIso, Adjunction.leftAdjointUniq_inv_app] using
    congrArg (fun h ↦ (directImageConstantPush A r).map h) hz

private theorem coordinate_paste
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (F F' : A ⥤ B) (G G' : C ⥤ D) (S S' : B ⥤ D) (T T' : A ⥤ C)
    (a : F ≅ F') (b : G ≅ G') (s : S ≅ S') (t : T ≅ T')
    (v : F' ⋙ S' ≅ T' ⋙ G') (K : A) :
    s.hom.app (F'.obj K) ≫ v.hom.app K ≫ G'.map (t.inv.app K) =
      S.map (a.inv.app K) ≫ s.hom.app (F.obj K) ≫
        S'.map (a.hom.app K) ≫ v.hom.app K ≫ b.inv.app (T'.obj K) ≫
          G.map (t.inv.app K) ≫ b.hom.app (T.obj K) := by
  rw [s.hom.naturality_assoc]
  simp only [← S'.map_comp_assoc, Iso.inv_hom_id_app, S'.map_id, Category.id_comp]
  rw [b.hom.naturality]
  simp only [Iso.inv_hom_id_app_assoc]

attribute [-instance] WeilConjectures.IntegralHom.derivedCategory in
private theorem openScalar_unit (m : Models.{u})
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (K : proEtaleDerivedCategory X A) :
    (scalarPair m φ Z).adjunction.unit.app ((openExtension (A := A) j).obj K) ≫
        (scalarRestriction φ Z).map ((beta m φ j).hom.app K) =
      (openExtension (A := A) j).map ((scalarPair m φ X).adjunction.unit.app K) ≫
        (reductionOpenModel A j).inv.app
          ((scalarRestriction φ X).obj ((scalar m φ X).obj K)) ≫
        (sfOpenRestrictionDerived j φ).hom.app ((scalar m φ X).obj K) ≫
        (scalarRestriction φ Z).map
          ((reductionOpenModel B j).hom.app ((scalar m φ X).obj K)) := by
  let F := (sfIntrinsicExtensionByZero j A).mapDerivedCategory
  let G := (sfIntrinsicExtensionByZero j B).mapDerivedCategory
  let aZ := directImageScalarAdjunction φ Z
  let aX := directImageScalarAdjunction φ X
  have hc (N : proEtaleDerivedCategory X B) := congr_app (openScalarCounitSquare φ j) N
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hc
  have hu := scalar_unit_of_counit aZ aX F G
    (reductionOpenScalarIso φ j).hom (sfOpenRestrictionDerived j φ).hom hc K
  have hcoord : (beta m φ j).hom.app K =
      (scalar m φ Z).map ((reductionOpenModel A j).inv.app K) ≫
        (scalarIso m φ Z).hom.app (F.obj K) ≫
        (reductionOpenScalarIso φ j).hom.app K ≫
        G.map ((scalarIso m φ X).inv.app K) ≫
        (reductionOpenModel B j).hom.app ((scalar m φ X).obj K) := by
    simpa only [beta, reductionOpenScalarIso, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Iso.symm_hom, Category.assoc, scalarExtensionFunctor] using
      coordinate_paste F (openExtension (A := A) j) G (openExtension (A := B) j)
        (scalar m φ Z) (scalarExtension φ Z) (scalar m φ X) (scalarExtension φ X)
        (reductionOpenModel A j) (reductionOpenModel B j)
        (scalarIso m φ Z) (scalarIso m φ X) (openScalarIso φ j) K
  dsimp only [scalarExtensionFunctor] at hu hcoord ⊢
  rw [hcoord]
  simp only [Functor.map_comp]
  have hn := (scalarPair m φ Z).adjunction.unit.naturality
    ((reductionOpenModel A j).inv.app K)
  dsimp only [Functor.id_map, Functor.comp_map, Functor.comp_obj] at hn
  erw [← reassoc_of% hn]
  try simp only [Category.assoc]
  erw [reassoc_of% ((scalarPair m φ Z).adjunction.unit_leftAdjointUniq_hom_app aZ)]
  try simp only [Category.assoc]
  erw [reassoc_of% hu]
  have hv := (sfOpenRestrictionDerived j φ).hom.naturality ((scalarIso m φ X).inv.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hv
  erw [← reassoc_of% hv, ← F.map_comp_assoc]
  have hx := aX.unit_leftAdjointUniq_hom_app (scalarPair m φ X).adjunction K
  have hx' : aX.unit.app K ≫
      (scalarRestriction φ X).map ((scalarIso m φ X).inv.app K) =
        (scalarPair m φ X).adjunction.unit.app K := by
    simpa only [scalarIso, Adjunction.leftAdjointUniq_inv_app] using hx
  erw [hx']
  have hf := (reductionOpenModel A j).inv.naturality
    ((scalarPair m φ X).adjunction.unit.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hf
  erw [reassoc_of% hf]

attribute [-instance] WeilConjectures.IntegralHom.derivedCategory in
private theorem compactScalar_factor (m : Models.{u})
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Z Y : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (r : Z ⟶ Y) (K : proEtaleDerivedCategory X A) :
    compactScalar m φ j r K =
      (properScalar m φ r).app ((openExtension (A := A) j).obj K) ≫
        (directImageConstantPush B r).map ((beta m φ j).hom.app K) := by
  apply ((scalarPair m φ Y).adjunction.homEquiv _ _).injective
  change ((scalarPair m φ Y).adjunction.homEquiv _ _)
      (((scalarPair m φ Y).adjunction.homEquiv _ _).symm _) = _
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit, Functor.map_comp]
  change _ = (scalarPair m φ Y).adjunction.unit.app
      ((directImageConstantPush A r).obj ((openExtension (A := A) j).obj K)) ≫
    (scalarRestriction φ Y).map ((properScalar m φ r).app ((openExtension j).obj K)) ≫
    (scalarRestriction φ Y).map
      ((directImageConstantPush B r).map ((beta m φ j).hom.app K))
  erw [reassoc_of% (properScalar_unit m φ r ((openExtension j).obj K))]
  have hn := (directImageScalarRestrictionIso φ r).hom.naturality
    ((beta m φ j).hom.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  erw [← hn]
  have ho := congrArg (fun h ↦ (directImageConstantPush A r).map h)
    (openScalar_unit m φ j K)
  simp only [Functor.map_comp] at ho
  erw [reassoc_of% ho]
  simp only [compactRestriction, intrinsicCompactSupportRestriction, Iso.trans_hom,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.symm_hom,
    Functor.map_comp, Category.assoc]
  have hv := (directImageScalarRestrictionIso φ r).hom.naturality
    ((reductionOpenModel B j).hom.app ((scalar m φ X).obj K))
  dsimp only [Functor.comp_map, Functor.comp_obj] at hv
  erw [hv]
  simp only [sfOpenRestrictionDerived, Iso.trans_hom, NatTrans.comp_app,
    Iso.symm_hom, Functor.map_comp, Category.assoc, directImageScalarRestrictionIso]

attribute [-instance] WeilConjectures.IntegralHom.derivedCategory in
/-- The comparison a^r is s followed by tensoring the inverse of lambda, namely t_r.
Source: blueprint displayed a^u
(blueprint: lem-sf-pf-reduction-proper-open-identities). -/
def mixedScalar (m : Models.{u}) (c : Choices.{u} m)
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    {Z Y : Scheme.{u}} (r : Z ⟶ Y)
    (M : proEtaleDerivedCategory Z A) (L : proEtaleDerivedCategory Y A) :
    (scalar.{u} m φ Z).obj
        ((tensor.{u} m A Z).obj (M, (constantPullback.{u} (A := A) r).obj L)) ≅
      (tensor.{u} m B Z).obj
        ((scalar.{u} m φ Z).obj M,
          (constantPullback.{u} (A := B) r).obj ((scalar.{u} m φ Y).obj L)) :=
  (c.scalarTensor φ Z).iso.app (M, (constantPullback.{u} (A := A) r).obj L) ≪≫
    (tensor.{u} m B Z).mapIso
      ((Iso.refl ((scalar.{u} m φ Z).obj M)).prod ((lambda.{u} m φ r).symm.app L))

/-- The specified open tensor map includes the canonical pullback compositor.
The supplied projection presentation fixes its inverse by its open-adjunction transpose.
Source: Stacks 0GL1 and blueprint gamma
(blueprint: lem-sf-pf-reduction-proper-open-identities). -/
def openTensor (m : Models.{u}) (A : Type u) [CommRing A]
    {X Z Y : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] (r : Z ⟶ Y)
    (p : Projection.{u} m A j)
    (K : proEtaleDerivedCategory X A) (L : proEtaleDerivedCategory Y A) :
    (tensor.{u} m A Z).obj
        ((openExtension.{u} (A := A) j).obj K, (constantPullback.{u} (A := A) r).obj L) ≅
      (openExtension.{u} (A := A) j).obj
        ((tensor.{u} m A X).obj (K, (constantPullback.{u} (A := A) (j ≫ r)).obj L)) :=
  p.iso.app (K, (constantPullback.{u} (A := A) r).obj L) ≪≫
    (openExtension.{u} (A := A) j).mapIso
      ((tensor.{u} m A X).mapIso
        ((Iso.refl K).prod ((proEtaleConstantRingPullbackComposition j r A).app L)))

attribute [-instance] WeilConjectures.IntegralHom.derivedCategory in
private theorem lambda_tensor_inverse (m : Models.{u}) (c : Choices m)
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Z Y : Scheme.{u}} (r : Z ⟶ Y)
    (P Q : proEtaleDerivedCategory Y A) :
    (tensor m B Z).map
        (Prod.mkHom ((lambda m φ r).inv.app P) ((lambda m φ r).inv.app Q)) ≫
      (restrictionTensor m B r).inv.app ((scalar m φ Y).obj P, (scalar m φ Y).obj Q) ≫
      (constantPullback (A := B) r).map ((c.scalarTensor φ Y).iso.inv.app (P, Q)) =
    (c.scalarTensor φ Z).iso.inv.app
        ((constantPullback (A := A) r).obj P, (constantPullback (A := A) r).obj Q) ≫
      (scalar m φ Z).map ((restrictionTensor m A r).inv.app (P, Q)) ≫
      (lambda m φ r).inv.app ((tensor m A Y).obj (P, Q)) := by
  let l := (lambda m φ r).app ((tensor m A Y).obj (P, Q)) ≪≫
    (scalar m φ Z).mapIso ((restrictionTensor m A r).app (P, Q)) ≪≫
      (c.scalarTensor φ Z).iso.app
        ((constantPullback (A := A) r).obj P, (constantPullback (A := A) r).obj Q)
  let t := (constantPullback (A := B) r).mapIso ((c.scalarTensor φ Y).iso.app (P, Q)) ≪≫
    (restrictionTensor m B r).app ((scalar m φ Y).obj P, (scalar m φ Y).obj Q) ≪≫
      (tensor m B Z).mapIso (((lambda m φ r).app P).prod ((lambda m φ r).app Q))
  have he : l = t := Iso.ext (scalarPullbackTensorCoherence m c φ r P Q)
  simpa only [l, t, Iso.trans_inv, Iso.app_inv, Functor.mapIso_inv, Iso.prod_inv,
    Category.assoc] using (congrArg (fun i ↦ i.inv) he).symm

attribute [-instance] WeilConjectures.IntegralHom.derivedCategory in
private theorem proper_tensor (m : Models.{u}) (c : Choices m)
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Z Y : Scheme.{u}} (r : Z ⟶ Y)
    (M : proEtaleDerivedCategory Z A) (L : proEtaleDerivedCategory Y A) :
    (scalar m φ Y).map (properProjection m A r M L) ≫
      (properScalar m φ r).app
        ((tensor m A Z).obj (M, (constantPullback (A := A) r).obj L)) ≫
      (directImageConstantPush B r).map (mixedScalar m c φ r M L).hom =
    (c.scalarTensor φ Y).iso.hom.app ((directImageConstantPush A r).obj M, L) ≫
      (tensor m B Y).map
        (Prod.mkHom ((properScalar m φ r).app M) (𝟙 ((scalar m φ Y).obj L))) ≫
      properProjection m B r ((scalar m φ Z).obj M) ((scalar m φ Y).obj L) := by
  exact tensor_mate_coherence
    (directImageConstantAdjunction A r) (directImageConstantAdjunction B r)
    (tensor m A Y) (tensor m A Z) (tensor m B Y) (tensor m B Z)
    (restrictionTensor m A r).hom (c.scalarTensor φ Y).iso.hom
    (c.scalarTensor φ Z).iso.hom (restrictionTensor m B r).hom
    (lambda m φ r) (scalarPullbackTensorCoherence m c φ r) M L

attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.mapDerivedCategoryFactors DerivedCategory.Q DerivedCategory.Qh

private theorem open_tensor_paste
    {UA ZA UB ZB : Type*} [Category UA] [Category ZA] [Category UB] [Category ZB]
    (eA : UA ⥤ ZA) (eB : UB ⥤ ZB) (JA : ZA ⥤ UA) (JB : ZB ⥤ UB)
    (SZ : ZA ⥤ ZB) (SU : UA ⥤ UB)
    (TA : ZA × ZA ⥤ ZA) (TU : UA × UA ⥤ UA)
    (TB : ZB × ZB ⥤ ZB) (TV : UB × UB ⥤ UB)
    (tZ : TA ⋙ SZ ≅ SZ.prod SZ ⋙ TB) (tU : TU ⋙ SU ≅ SU.prod SU ⋙ TV)
    (bet : eA ⋙ SZ ≅ SU ⋙ eB)
    (pB : eB.prod (𝟭 ZB) ⋙ TB ≅ (𝟭 UB).prod JB ⋙ TV ⋙ eB)
    (K : UA) (Q : ZA) (Q' : UA) (W : ZB) (T : UB)
    (p : TA.obj (eA.obj K, Q) ⟶ eA.obj (TU.obj (K, JA.obj Q)))
    (a : JA.obj Q ⟶ Q') (b : JB.obj W ⟶ T)
    (l : SU.obj (JA.obj Q) ⟶ JB.obj (SZ.obj Q))
    (v : SZ.obj Q ⟶ W) (w : SU.obj Q' ⟶ T)
    (hc : SU.map a ≫ w = l ≫ JB.map v ≫ b)
    (h : SZ.map p ≫ bet.hom.app (TU.obj (K, JA.obj Q)) ≫
        eB.map (tU.hom.app (K, JA.obj Q) ≫ TV.map (Prod.mkHom (𝟙 _) l)) =
      tZ.hom.app (eA.obj K, Q) ≫ TB.map (Prod.mkHom (bet.hom.app K) (𝟙 _)) ≫
        pB.hom.app (SU.obj K, SZ.obj Q)) :
    SZ.map (p ≫ eA.map (TU.map (Prod.mkHom (𝟙 K) a))) ≫
        bet.hom.app (TU.obj (K, Q')) ≫
        eB.map (tU.hom.app (K, Q') ≫ TV.map (Prod.mkHom (𝟙 _) w)) =
      tZ.hom.app (eA.obj K, Q) ≫ TB.map (Prod.mkHom (𝟙 _) v) ≫
        TB.map (Prod.mkHom (bet.hom.app K) (𝟙 W)) ≫
        pB.hom.app (SU.obj K, W) ≫ eB.map (TV.map (Prod.mkHom (𝟙 _) b)) := by
  have hb := bet.hom.naturality (TU.map (Prod.mkHom (𝟙 K) a))
  have hs := tU.hom.naturality (Prod.mkHom (𝟙 K) a)
  have hp := pB.hom.naturality (Prod.mkHom (𝟙 (SU.obj K)) v)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.prod_map,
    Functor.id_map] at hb hs hp
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hb]
  simp only [← eB.map_comp_assoc]
  rw [hs, SU.map_id]
  rw [← eB.map_comp]
  simp only [Category.assoc]
  rw [← TV.map_comp]
  dsimp only [CategoryTheory.prod_comp, Prod.mkHom, Prod.fst, Prod.snd]
  rw [Category.id_comp, hc]
  have hpair : (𝟙 (SU.obj K), l ≫ JB.map v ≫ b) =
      (Prod.mkHom (𝟙 (SU.obj K)) l ≫ Prod.mkHom (𝟙 (SU.obj K)) (JB.map v) ≫
        Prod.mkHom (𝟙 (SU.obj K)) b) := by
    ext <;> simp
  rw [hpair]
  simp only [Functor.map_comp] at h ⊢
  rw [reassoc_of% h]
  simp only [eB.map_id] at hp
  rw [← reassoc_of% hp]
  simp only [← TB.map_comp_assoc]
  congr 2
  congr 1
  ext <;> simp

attribute [-instance] WeilConjectures.IntegralHom.derivedCategory in
private theorem open_tensor (m : Models.{u}) (c : Choices m)
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Z Y : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (r : Z ⟶ Y) (pA : Projection m A j) (pB : Projection m B j)
    (K : proEtaleDerivedCategory X A) (L : proEtaleDerivedCategory Y A) :
    (scalar m φ Z).map (openTensor m A j r pA K L).hom ≫
      (beta m φ j).hom.app
        ((tensor m A X).obj (K, (constantPullback (A := A) (j ≫ r)).obj L)) ≫
      (openExtension (A := B) j).map (mixedScalar m c φ (j ≫ r) K L).hom =
    (mixedScalar m c φ r ((openExtension (A := A) j).obj K) L).hom ≫
      (tensor m B Z).map
        (Prod.mkHom ((beta m φ j).hom.app K)
          (𝟙 ((constantPullback (A := B) r).obj ((scalar m φ Y).obj L)))) ≫
      (openTensor m B j r pB ((scalar m φ X).obj K) ((scalar m φ Y).obj L)).hom := by
  have h := tensor_square (openAdj A j) (openAdj B j)
    (scalar m φ Z) (scalar m φ X)
    (tensor m A Z) (tensor m A X) (tensor m B Z) (tensor m B X)
    (c.scalarTensor φ Z).iso (c.scalarTensor φ X).iso
    (restrictionTensor m A j) (restrictionTensor m B j)
    (lambda m φ j) (beta m φ j) pA.iso pB.iso
    (beta_inverse_aux m φ j) pA.inverse_adjunct pB.inverse_adjunct
    (lambda_tensor_inverse m c φ j) K ((constantPullback (A := A) r).obj L)
  simpa only [openTensor, mixedScalar, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom, Iso.prod_hom, Iso.refl_hom, Iso.symm_hom, Category.assoc, Functor.id_obj] using
    open_tensor_paste (openExtension (A := A) j) (openExtension (A := B) j)
      (constantPullback (A := A) j) (constantPullback (A := B) j)
      (scalar m φ Z) (scalar m φ X)
      (tensor m A Z) (tensor m A X) (tensor m B Z) (tensor m B X)
      (c.scalarTensor φ Z).iso (c.scalarTensor φ X).iso (beta m φ j) pB.iso
      K ((constantPullback (A := A) r).obj L)
      ((constantPullback (A := A) (j ≫ r)).obj L)
      ((constantPullback (A := B) r).obj ((scalar m φ Y).obj L))
      ((constantPullback (A := B) (j ≫ r)).obj ((scalar m φ Y).obj L))
      (pA.iso.hom.app (K, (constantPullback (A := A) r).obj L))
      ((proEtaleConstantRingPullbackComposition j r A).hom.app L)
      ((proEtaleConstantRingPullbackComposition j r B).hom.app ((scalar m φ Y).obj L))
      ((lambda m φ j).inv.app ((constantPullback (A := A) r).obj L))
      ((lambda m φ r).inv.app L) ((lambda m φ (j ≫ r)).inv.app L)
      (scalarPullbackCompositionCoherence m φ j r L) h


attribute [-instance] WeilConjectures.IntegralHom.derivedCategory in
/-- The three clauses of the factor calculation, as equalities of B-linear maps.
The proper reduced input is scalar extension of j!K, before the d_K identification.
Source: blueprint proper/open displayed identities and compact-support factorization
(blueprint: lem-sf-pf-reduction-proper-open-identities). -/
def Identities (m : Models.{u}) (c : Choices.{u} m)
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Z Y : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (r : Z ⟶ Y) (pA : Projection.{u} m A j) (pB : Projection.{u} m B j)
    (K : proEtaleDerivedCategory X A) (L : proEtaleDerivedCategory Y A) : Prop :=
  (∀ (V W : proEtaleDerivedCategory Z A) (h : V ⟶ W),
    (scalar.{u} m φ Y).map ((directImageConstantPush A r).map h) ≫
        (properScalar m φ r).app W =
      (properScalar m φ r).app V ≫
        (directImageConstantPush B r).map ((scalar.{u} m φ Z).map h)) ∧
  (compactScalar m φ j r K =
    (properScalar m φ r).app ((openExtension (A := A) j).obj K) ≫
      (directImageConstantPush B r).map ((beta m φ j).hom.app K)) ∧
  (compactScalar m φ j r
      ((tensor.{u} m A X).obj (K, (constantPullback (A := A) (j ≫ r)).obj L)) =
    (properScalar m φ r).app ((openExtension (A := A) j).obj
      ((tensor.{u} m A X).obj (K, (constantPullback (A := A) (j ≫ r)).obj L))) ≫
      (directImageConstantPush B r).map ((beta m φ j).hom.app
        ((tensor.{u} m A X).obj (K, (constantPullback (A := A) (j ≫ r)).obj L)))) ∧
  ((scalar.{u} m φ Y).map
        (properProjection m A r ((openExtension (A := A) j).obj K) L) ≫
      (properScalar m φ r).app ((tensor.{u} m A Z).obj
        ((openExtension (A := A) j).obj K, (constantPullback (A := A) r).obj L)) ≫
      (directImageConstantPush B r).map
        (mixedScalar m c φ r ((openExtension (A := A) j).obj K) L).hom =
    (c.scalarTensor φ Y).iso.hom.app
        ((directImageConstantPush A r).obj ((openExtension (A := A) j).obj K), L) ≫
      (tensor.{u} m B Y).map
        (Prod.mkHom ((properScalar m φ r).app ((openExtension (A := A) j).obj K))
          (𝟙 ((scalar.{u} m φ Y).obj L))) ≫
      properProjection m B r
        ((scalar.{u} m φ Z).obj ((openExtension (A := A) j).obj K))
        ((scalar.{u} m φ Y).obj L)) ∧
  ((scalar.{u} m φ Z).map (openTensor m A j r pA K L).hom ≫
      (beta m φ j).hom.app
        ((tensor.{u} m A X).obj (K, (constantPullback (A := A) (j ≫ r)).obj L)) ≫
      (openExtension (A := B) j).map (mixedScalar m c φ (j ≫ r) K L).hom =
    (mixedScalar m c φ r ((openExtension (A := A) j).obj K) L).hom ≫
      (tensor.{u} m B Z).map
        (Prod.mkHom ((beta m φ j).hom.app K)
          (𝟙 ((constantPullback (A := B) r).obj ((scalar.{u} m φ Y).obj L)))) ≫
      (openTensor m B j r pB ((scalar.{u} m φ X).obj K) ((scalar.{u} m φ Y).obj L)).hom)

/-- The recorded fixed-module input transported by the canonical coefficient equivalence.
This is only a change of coordinates, retaining the very same derived complex.
Source: the ordinary constant-ring convention of the blueprint
(blueprint: lem-sf-pf-reduction-proper-open-identities). -/
def input (T : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    (K : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    proEtaleDerivedCategory T A :=
  (sfIntrinsicDerivedEquivalence T A).functor.obj K.obj

attribute [-instance] WeilConjectures.IntegralHom.derivedCategory in
/-- Proper and open coefficient identities for the chosen compactification.
The positive coefficient exponents are n+1 and m+1. The maps use normalized
K-flat tensor presentations and unit-normalized open projection presentations.
No flatness of the quotient and no invertibility of a proper projection is assumed.
Source: current blueprint main-20261015, sk-prop-sf-pf-reduction,
transpose/counit paragraph; Stacks Tags 0E48, 0GL1 and 0GL6
(blueprint: lem-sf-pf-reduction-proper-open-identities).

Proof:
1. Transpose the proper coefficient mate under the geometric adjunction.
Its counit equation and counit naturality give naturality of c.
2. Regard scalar change as the horizontal ringed morphisms over identity topoi.
The canonical scalar tensorators and pullback comparisons are the derived
monoidal and composition comparisons. No flatness of B over A is involved.
3. Specialize ringed exchange/tensor coherence (Stacks 0E48) to this square,
with M=j!K. The projections are precisely the counit-defined projections above.
This proves the proper factor identity with reduced input rho(M).
4. Apply the normalized open/scalar tensor square to Q=Lr*L.
5. Postcompose with the canonical j*/r* compositor and use its scalar cocycle.
Naturality of d and of the open tensor map yields exactly the open identity.
6. Under the scalar adjunction, c has transpose direct image of the scalar
unit followed by the canonical direct-image restriction comparison.
7. The common-right-adjoint definition of d gives the analogous open formula:
its scalar transpose is extension by zero of the unit followed by the
section-normalized open restriction comparison.
8. Paste these two scalar-unit equations. The transpose is exactly compact
support of the scalar unit followed by compactRestriction. Injectivity of the
scalar Hom bijection identifies the composite with compactScalar, for K and H.
The calculations hold on ordinary unbounded categories and thus apply to
the stated bounded constructible finite-Tor inputs with their retained witnesses. -/
theorem pfReductionProperOpenIdentities
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E] [FiniteDimensional (Padic C.l) E]
    (m n : ℕ) (_hmn : m ≤ n)
    (models : Models.{u}) (choices : Choices.{u} models)
    {X Y : SixFunctorSpace D} [IsSeparated X.obj.hom] [IsSeparated Y.obj.hom]
    (f : X ⟶ Y) [IsSeparated f.hom.left]
    [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (d : Compactification f.hom.left)
    (pA : Projection.{u} models (Padic.coefficientExtensionRing C.l E (n + 1)) d.i)
    (pB : Projection.{u} models (Padic.coefficientExtensionRing C.l E (m + 1)) d.i)
    (K : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X.obj.left)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing C.l E (n + 1))))))
    (L : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology Y.obj.left)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing C.l E (n + 1))))))
    (wK : FixedEtaleOriginWitness X.obj.left
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing C.l E (n + 1))) K)
    (wL : FixedEtaleOriginWitness Y.obj.left
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing C.l E (n + 1))) L)
    (_hK : finiteTorConstructible C.l E (n + 1) (Nat.succ_pos n) X.obj.left
      (input X.obj.left (Padic.coefficientExtensionRing C.l E (n + 1)) K))
    (_hL : finiteTorConstructible C.l E (n + 1) (Nat.succ_pos n) Y.obj.left
      (input Y.obj.left (Padic.coefficientExtensionRing C.l E (n + 1)) L))
    (_hwK : finiteTorConstructibleEtale C.l E (n + 1) (Nat.succ_pos n)
      X.obj.left wK.complex.obj)
    (_hwL : finiteTorConstructibleEtale C.l E (n + 1) (Nat.succ_pos n)
      Y.obj.left wL.complex.obj) :
    Identities models choices
      (Ideal.Quotient.factor
        (S := Padic.coefficientExtensionIdeal C.l E (n + 1))
        (T := Padic.coefficientExtensionIdeal C.l E (m + 1))
        (Ideal.pow_le_pow_right (Nat.succ_le_succ _hmn))) d.i d.g pA pB
      (input X.obj.left (Padic.coefficientExtensionRing C.l E (n + 1)) K)
      (input Y.obj.left (Padic.coefficientExtensionRing C.l E (n + 1)) L) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro V W h
    exact (properScalar models _ d.g).naturality h
  · exact compactScalar_factor models _ d.i d.g _
  · exact compactScalar_factor models _ d.i d.g _
  · exact proper_tensor models choices _ d.g _ _
  · exact open_tensor models choices _ d.i d.g pA pB _ _

end AlgebraicGeometry.ProEtale.PfReductionFactors
