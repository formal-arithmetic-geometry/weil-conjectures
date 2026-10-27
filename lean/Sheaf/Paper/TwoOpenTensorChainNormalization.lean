module

public import Sheaf.Paper.FiniteOpenProductSwap

import Sheaf.Paper.FiniteTensorPullCoherence
import Sheaf.Paper.FiniteOpenGammaRestriction

/-! # Normalized tensor chains for two open immersions

Source: Stacks Tags 0GL1 and 0E8I; blueprint main-20261015,
sec-six-functors/sk-thm-sf-kunneth-relative/lem-sf-kunneth-coherence.proof.md,
open-extension symmetry calculation (blueprint: lem-pur-two-open-tensor-chain-normalization).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open SheafOfModules.OpenTensorNormalization

namespace WeilConjectures.FiniteOpenProduct

variable (A : Type (u + 1)) [CommRing A] [Finite A]

omit [Finite A] in
private theorem tensorMap_comp (Y : Scheme.{u})
    {M₁ M₂ M₃ N₁ N₂ N₃ : FiniteD A Y}
    (f : M₁ ⟶ M₂) (f' : M₂ ⟶ M₃) (g : N₁ ⟶ N₂) (g' : N₂ ⟶ N₃) :
    tensorMap A Y f g ≫ tensorMap A Y f' g' = tensorMap A Y (f ≫ f') (g ≫ g') := by
  unfold tensorMap
  simp only [Functor.map_comp, NatTrans.comp_app, Category.assoc]
  rw [← Category.assoc (((ProEtale.derivedTensor (ModuleCat.{u + 1} A) Y).obj M₂).map g),
    ((ProEtale.derivedTensor (ModuleCat.{u + 1} A) Y).map f').naturality g]
  simp only [Category.assoc]

private theorem gamma_isIso {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (M : FiniteD A U) (N : FiniteD A X) : IsIso (gamma A j M N) := by
  unfold gamma finiteGamma
  infer_instance

private theorem sigma_isIso (Y : Scheme.{u}) (M N : FiniteD A Y) :
    IsIso (sigma A Y M N) := by
  exact ⟨sigma A Y N M,
    (finiteTensorPullCoherence A).1 Y M N, (finiteTensorPullCoherence A).1 Y N M⟩

private theorem rho_isIso {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (M : FiniteD A X) (N : FiniteD A U) : IsIso (rho A j M N) := by
  have := gamma_isIso A j N M
  have := sigma_isIso A X M ((finiteShriek A j).obj N)
  have := sigma_isIso A U N ((pull A j).obj M)
  unfold rho
  infer_instance

omit [Finite A] in
private theorem nestedRestriction {W V Y : Scheme.{u}} (w : W ⟶ V) (v : V ⟶ Y)
    [IsOpenImmersion w] [IsOpenImmersion v]
    (hc : ∀ S : FiniteD A W,
      (adj A w).unit.app S ≫
        (pull A w).map ((adj A v).unit.app ((finiteShriek A w).obj S)) ≫
        (pullComp A w v).inv.app
          ((finiteShriek A v).obj ((finiteShriek A w).obj S)) ≫
        (pull A (w ≫ v)).map ((comp A w v).hom.app S) =
          (adj A (w ≫ v)).unit.app S)
    {X : FiniteD A Y} {B : FiniteD A V} {S : FiniteD A W}
    (a : X ⟶ (finiteShriek A v).obj B) (f : B ⟶ (finiteShriek A w).obj S)
    (r : (pull A v).obj X ⟶ B) (s : (pull A w).obj B ⟶ S)
    (ha : (pull A v).map a = r ≫ (adj A v).unit.app B)
    (hf : (pull A w).map f = s ≫ (adj A w).unit.app S) :
    (pull A (w ≫ v)).map (a ≫ (finiteShriek A v).map f ≫ (comp A w v).hom.app S) =
      (pullComp A w v).hom.app X ≫ (pull A w).map r ≫ s ≫
        (adj A (w ≫ v)).unit.app S := by
  have hn := (pullComp A w v).hom.naturality (a ≫ (finiteShriek A v).map f)
  dsimp only [Functor.comp_map] at hn
  have he : (pull A (w ≫ v)).map (a ≫ (finiteShriek A v).map f) =
      (pullComp A w v).hom.app X ≫
        (pull A w).map ((pull A v).map (a ≫ (finiteShriek A v).map f)) ≫
        (pullComp A w v).inv.app
          ((finiteShriek A v).obj ((finiteShriek A w).obj S)) := by
    simpa only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id] using congrArg
        (fun z ↦ z ≫ (pullComp A w v).inv.app
          ((finiteShriek A v).obj ((finiteShriek A w).obj S))) hn
  have hf' : (pull A v).map (a ≫ (finiteShriek A v).map f) =
      r ≫ f ≫ (adj A v).unit.app ((finiteShriek A w).obj S) := by
    have hunit := (adj A v).unit.naturality f
    dsimp only [Functor.id_map, Functor.comp_map] at hunit
    rw [Functor.map_comp, ha, Category.assoc, ← hunit]
  rw [← Category.assoc, Functor.map_comp, he, hf']
  simp only [Functor.map_comp, hf, Category.assoc]
  rw [← hc S]

private theorem nestedTensorMap {W V Y : Scheme.{u}} (w : W ⟶ V) (v : V ⟶ Y)
    (M N : FiniteD A Y) {M' N' : FiniteD A V} {M'' N'' : FiniteD A W}
    (a : (pull A v).obj M ⟶ M') (b : (pull A v).obj N ⟶ N')
    (c : (pull A w).obj M' ⟶ M'') (d : (pull A w).obj N' ⟶ N'') :
    (pullComp A w v).hom.app (tensor A Y M N) ≫
        (pull A w).map ((tensorPullIso A v M N).hom ≫ tensorMap A V a b) ≫
        (tensorPullIso A w M' N').hom ≫ tensorMap A W c d =
      (tensorPullIso A (w ≫ v) M N).hom ≫
        tensorMap A W
          ((pullComp A w v).hom.app M ≫ (pull A w).map a ≫ c)
          ((pullComp A w v).hom.app N ≫ (pull A w).map b ≫ d) := by
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc ((pull A w).map (tensorMap A V a b)),
    (finiteTensorPullCoherence A).2.2.2.1 w a b]
  simp only [Category.assoc]
  rw [tensorMap_comp]
  have ht := (finiteTensorPullCoherence A).2.2.2.2 w v M N
  rw [← Category.assoc, ← Category.assoc]
  erw [← Category.assoc] at ht
  rw [ht]
  simp only [Category.assoc, tensorMap_comp]

/-- The actual open unit, packaged with its canonical inverse.
Source: Stacks 03DI, section-normalized exact open adjunction
(blueprint: lem-pur-two-open-tensor-chain-normalization). -/
def twoOpenUnitIso {T S : Scheme.{u}} (i : T ⟶ S) [IsOpenImmersion i]
    (L : FiniteD A T) : L ≅ (pull A i).obj ((finiteShriek A i).obj L) := by
  haveI : IsIso (adj A i).unit :=
    Adjunction.isIso_mapDerivedCategoryAdjunction_unit
      (ProEtale.openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) i)
  exact asIso ((adj A i).unit.app L)

/-- The first actual nested tensor chain, in extension-first order.
Source: Stacks 0GL1; node statement, displayed e_L
(blueprint: lem-pur-two-open-tensor-chain-normalization). -/
def twoOpenLeftChain {W V Y : Scheme.{u}} (w : W ⟶ V) (v : V ⟶ Y)
    [IsOpenImmersion w] [IsOpenImmersion v]
    (F : FiniteD A V) (H : FiniteD A Y) (Q : FiniteD A W)
    (δ : (pull A v).obj H ≅ (finiteShriek A w).obj Q) :
    tensor A Y ((finiteShriek A v).obj F) H ⟶
      (finiteShriek A (w ≫ v)).obj (tensor A W ((pull A w).obj F) Q) :=
  gamma A v F H ≫
    (finiteShriek A v).map (tensorMap A V (𝟙 F) δ.hom) ≫
    (finiteShriek A v).map (rho A w F Q) ≫
    (comp A w v).hom.app (tensor A W ((pull A w).obj F) Q)

/-- The second actual nested tensor chain, retaining the order Q tensor w-star F.
Source: Stacks 0GL1; node statement, displayed e_R
(blueprint: lem-pur-two-open-tensor-chain-normalization). -/
def twoOpenRightChain {W V Y : Scheme.{u}} (w : W ⟶ V) (v : V ⟶ Y)
    [IsOpenImmersion w] [IsOpenImmersion v]
    (F : FiniteD A V) (H : FiniteD A Y) (Q : FiniteD A W)
    (δ : (pull A v).obj H ≅ (finiteShriek A w).obj Q) :
    tensor A Y H ((finiteShriek A v).obj F) ⟶
      (finiteShriek A (w ≫ v)).obj (tensor A W Q ((pull A w).obj F)) :=
  rho A v H F ≫
    (finiteShriek A v).map (tensorMap A V δ.hom (𝟙 F)) ≫
    (finiteShriek A v).map (gamma A w Q F) ≫
    (comp A w v).hom.app (tensor A W Q ((pull A w).obj F))

/-- The isomorphism a, with restriction composition displayed explicitly.
Source: node statement, a = w-star of the inverse v-unit
(blueprint: lem-pur-two-open-tensor-chain-normalization). -/
def twoOpenFirstRestriction {W V Y : Scheme.{u}} (w : W ⟶ V) (v : V ⟶ Y)
    [IsOpenImmersion v] (F : FiniteD A V) :
    (pull A (w ≫ v)).obj ((finiteShriek A v).obj F) ≅ (pull A w).obj F :=
  (pullComp A w v).app ((finiteShriek A v).obj F) ≪≫
    (pull A w).mapIso (twoOpenUnitIso A v F).symm

/-- The isomorphism d = inverse w-unit after w-star delta, on iterated restriction.
Source: node statement, d (blueprint: lem-pur-two-open-tensor-chain-normalization). -/
def twoOpenDeltaRestriction {W V Y : Scheme.{u}} (w : W ⟶ V) (v : V ⟶ Y)
    [IsOpenImmersion w] (H : FiniteD A Y) (Q : FiniteD A W)
    (δ : (pull A v).obj H ≅ (finiteShriek A w).obj Q) :
    (pull A w).obj ((pull A v).obj H) ≅ Q :=
  (pull A w).mapIso δ ≪≫ (twoOpenUnitIso A w Q).symm

/-- The displayed r_L, using the actual pullback tensor and composition comparisons.
Source: node statement, r_L (blueprint: lem-pur-two-open-tensor-chain-normalization). -/
def twoOpenLeftRestriction {W V Y : Scheme.{u}} (w : W ⟶ V) (v : V ⟶ Y)
    [IsOpenImmersion w] [IsOpenImmersion v]
    (F : FiniteD A V) (H : FiniteD A Y) (Q : FiniteD A W)
    (δ : (pull A v).obj H ≅ (finiteShriek A w).obj Q) :
    (pull A (w ≫ v)).obj (tensor A Y ((finiteShriek A v).obj F) H) ⟶
      tensor A W ((pull A w).obj F) Q :=
  (tensorPullIso A (w ≫ v) ((finiteShriek A v).obj F) H).hom ≫
    tensorMap A W (twoOpenFirstRestriction A w v F).hom
      ((pullComp A w v).hom.app H ≫ (twoOpenDeltaRestriction A w v H Q δ).hom)

/-- The displayed r_R, with the two tensor coordinates in reverse order.
Source: node statement, r_R (blueprint: lem-pur-two-open-tensor-chain-normalization). -/
def twoOpenRightRestriction {W V Y : Scheme.{u}} (w : W ⟶ V) (v : V ⟶ Y)
    [IsOpenImmersion w] [IsOpenImmersion v]
    (F : FiniteD A V) (H : FiniteD A Y) (Q : FiniteD A W)
    (δ : (pull A v).obj H ≅ (finiteShriek A w).obj Q) :
    (pull A (w ≫ v)).obj (tensor A Y H ((finiteShriek A v).obj F)) ⟶
      tensor A W Q ((pull A w).obj F) :=
  (tensorPullIso A (w ≫ v) H ((finiteShriek A v).obj F)).hom ≫
    tensorMap A W
      ((pullComp A w v).hom.app H ≫ (twoOpenDeltaRestriction A w v H Q δ).hom)
      (twoOpenFirstRestriction A w v F).hom

/-- The right-extension comparison is invertible and restricts to identity under the
specified tensor comparison and the actual open unit.
Source: Stacks 0GL1 and 0E8I; node proof Steps 1--2
(blueprint: lem-pur-two-open-tensor-chain-normalization).

Proof: Step 1 specializes openTensorNormalization to the constant finite ring. Its
finite compatibility identifies the actual gamma, and its restriction formula is
eta after (inverse eta tensor identity) after the canonical tensor comparison.
Step 2 expands the existing rho as signed symmetry, gamma, and extension of signed
symmetry. Pullback respects that symmetry by derivedPullbackTensorIso. Naturality
of eta and symmetry puts both signed swaps adjacent: on degrees p,q their scalar
is (-1)^(pq+qp)=1. The resulting restriction is exactly the displayed equation.
Each factor is invertible, since gamma is invertible by openTensorNormalization. -/
theorem twoOpenRhoNormalization (P : PurityFiniteSetting.{u})
    (T S : Over (Spec (CommRingCat.of P.field.k)))
    [IsSeparated T.hom] [LocallyOfFiniteType T.hom] [QuasiCompact T.hom]
    [IsSeparated S.hom] [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
    (i : T ⟶ S) [IsOpenImmersion i.left]
    (K : FiniteD P.Coefficient S.left) (L : FiniteD P.Coefficient T.left) :
    IsIso (rho P.Coefficient i.left K L) ∧
      (pull P.Coefficient i.left).map (rho P.Coefficient i.left K L) =
        (tensorPullIso P.Coefficient i.left K
          ((finiteShriek P.Coefficient i.left).obj L)).hom ≫
        tensorMap P.Coefficient T.left (𝟙 ((pull P.Coefficient i.left).obj K))
          (twoOpenUnitIso P.Coefficient i.left L).inv ≫
        (adj P.Coefficient i.left).unit.app
          (tensor P.Coefficient T.left ((pull P.Coefficient i.left).obj K) L) := by
  refine ⟨rho_isIso P.Coefficient i.left K L, ?_⟩
  have hn := (adj P.Coefficient i.left).unit.naturality
    (sigma P.Coefficient T.left L ((pull P.Coefficient i.left).obj K))
  dsimp only [Functor.id_map, Functor.comp_map] at hn
  have hs := (finiteTensorPullCoherence P.Coefficient).2.1 T.left
    (inv ((adj P.Coefficient i.left).unit.app L))
    (𝟙 ((pull P.Coefficient i.left).obj K))
  dsimp only [Functor.id_obj, Functor.comp_obj] at hs
  have hp := (finiteTensorPullCoherence P.Coefficient).2.2.1 i.left K
    ((finiteShriek P.Coefficient i.left).obj L)
  have hi := (finiteTensorPullCoherence P.Coefficient).1 T.left
    ((pull P.Coefficient i.left).obj K) ((pull P.Coefficient i.left).obj
      ((finiteShriek P.Coefficient i.left).obj L))
  simp only [rho, Functor.map_comp, finiteOpenGammaRestriction, Category.assoc]
  rw [← hn]
  rw [← Category.assoc, hp]
  simp only [Category.assoc]
  rw [← Category.assoc (tensorMap _ _ _ _), hs]
  simp only [Category.assoc]
  rw [← Category.assoc (sigma _ _ _ _), hi, Category.id_comp]
  rfl

/-- Both specified nested tensor chains are invertible, with their actual restriction
formulas, and the actual open compositor respects the composite unit.
Source: Stacks 0GL1 and 0E8I; blueprint main-20261015, open-extension symmetry
calculation in lem-sf-kunneth-coherence.proof.md; node proof Steps 3--7
(blueprint: lem-pur-two-open-tensor-chain-normalization).

Proof: Step 3 uses Adjunction.comp: the composite unit is eta-w followed by
w-star eta-v. Transport its right adjoint by pullComp. The canonical comp is the
unique-left-adjoint comparison, whose defining Hom bijection gives precisely the
first equation below. Step 4 puts b=inverse eta-v, h=w-star delta, T=w-star F and
d=inverse eta-w after h. Naturality of the tensor comparison and Step 2 give
w-star(rho-w after (identity tensor delta)) = eta-w after (identity tensor d)
after mu-w. Step 5 applies w-star to the gamma-v normalization of Step 1. Move the
v-unit past the inner map by naturality; insert Step 4 and use composition
compatibility of mu from derivedPullbackTensorIso. The tensor part becomes r_L;
Step 3 then replaces the two units and the compositor by eta-u. Step 6 repeats
this calculation in the other order: gamma-w after (delta tensor identity)
restricts to eta-w after (d tensor identity) after mu-w. Apply the rho-v formula
of Step 2, move eta-v by naturality, and use composition compatibility of mu.
The tensor part is r_R, keeping Q tensor T throughout, and Step 3 gives its
restriction equation. Step 7: every gamma, rho, delta, tensor image of delta and
compositor is invertible. Functors preserve inverses, so both chains are
invertible. All steps apply to arbitrary unbounded complexes; none requires
constructibility, boundedness or finite Tor-amplitude. -/
theorem twoOpenTensorChainNormalization (P : PurityFiniteSetting.{u})
    (W V Y : Over (Spec (CommRingCat.of P.field.k)))
    [IsSeparated W.hom] [LocallyOfFiniteType W.hom] [QuasiCompact W.hom]
    [IsSeparated V.hom] [LocallyOfFiniteType V.hom] [QuasiCompact V.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (w : W ⟶ V) (v : V ⟶ Y) [IsOpenImmersion w.left] [IsOpenImmersion v.left]
    (F : FiniteD P.Coefficient V.left) (H : FiniteD P.Coefficient Y.left)
    (Q : FiniteD P.Coefficient W.left)
    (δ : (pull P.Coefficient v.left).obj H ≅ (finiteShriek P.Coefficient w.left).obj Q) :
    (∀ L : FiniteD P.Coefficient W.left,
      (adj P.Coefficient w.left).unit.app L ≫
        (pull P.Coefficient w.left).map
          ((adj P.Coefficient v.left).unit.app ((finiteShriek P.Coefficient w.left).obj L)) ≫
        (pullComp P.Coefficient w.left v.left).inv.app
          ((finiteShriek P.Coefficient v.left).obj
            ((finiteShriek P.Coefficient w.left).obj L)) ≫
        (pull P.Coefficient (w.left ≫ v.left)).map
          ((comp P.Coefficient w.left v.left).hom.app L) =
        (adj P.Coefficient (w.left ≫ v.left)).unit.app L) ∧
    IsIso (twoOpenLeftChain P.Coefficient w.left v.left F H Q δ) ∧
    IsIso (twoOpenRightChain P.Coefficient w.left v.left F H Q δ) ∧
    ((pull P.Coefficient (w.left ≫ v.left)).map
      (twoOpenLeftChain P.Coefficient w.left v.left F H Q δ) =
        twoOpenLeftRestriction P.Coefficient w.left v.left F H Q δ ≫
        (adj P.Coefficient (w.left ≫ v.left)).unit.app
          (tensor P.Coefficient W.left ((pull P.Coefficient w.left).obj F) Q)) ∧
    ((pull P.Coefficient (w.left ≫ v.left)).map
      (twoOpenRightChain P.Coefficient w.left v.left F H Q δ) =
        twoOpenRightRestriction P.Coefficient w.left v.left F H Q δ ≫
        (adj P.Coefficient (w.left ≫ v.left)).unit.app
          (tensor P.Coefficient W.left Q ((pull P.Coefficient w.left).obj F))) := by
  have hc (L : FiniteD P.Coefficient W.left) :
      (adj P.Coefficient w.left).unit.app L ≫
        (pull P.Coefficient w.left).map
          ((adj P.Coefficient v.left).unit.app ((finiteShriek P.Coefficient w.left).obj L)) ≫
        (pullComp P.Coefficient w.left v.left).inv.app
          ((finiteShriek P.Coefficient v.left).obj
            ((finiteShriek P.Coefficient w.left).obj L)) ≫
        (pull P.Coefficient (w.left ≫ v.left)).map
          ((comp P.Coefficient w.left v.left).hom.app L) =
        (adj P.Coefficient (w.left ≫ v.left)).unit.app L := by
    simpa only [comp, Adjunction.ofNatIsoRight_unit, Adjunction.comp_unit_app,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.comp_obj,
      Iso.symm_hom, Category.assoc] using
      ((((adj P.Coefficient w.left).comp (adj P.Coefficient v.left)).ofNatIsoRight
        (pullComp P.Coefficient w.left v.left).symm).unit_leftAdjointUniq_hom_app
          (adj P.Coefficient (w.left ≫ v.left)) L)
  have hl : IsIso (twoOpenLeftChain P.Coefficient w.left v.left F H Q δ) := by
    have := gamma_isIso P.Coefficient v.left F H
    have := rho_isIso P.Coefficient w.left F Q
    have ht : IsIso (tensorMap P.Coefficient V.left (𝟙 F) δ.hom) := by
      unfold tensorMap
      infer_instance
    unfold twoOpenLeftChain
    infer_instance
  have hr : IsIso (twoOpenRightChain P.Coefficient w.left v.left F H Q δ) := by
    have := rho_isIso P.Coefficient v.left H F
    have := gamma_isIso P.Coefficient w.left Q F
    have ht : IsIso (tensorMap P.Coefficient V.left δ.hom (𝟙 F)) := by
      unfold tensorMap
      infer_instance
    unfold twoOpenRightChain
    infer_instance
  refine ⟨hc, hl, hr, ?_, ?_⟩
  · let b := (twoOpenUnitIso P.Coefficient v.left F).inv
    let d := (pull P.Coefficient w.left).map δ.hom ≫ (twoOpenUnitIso P.Coefficient w.left Q).inv
    have hf : (pull P.Coefficient w.left).map
        (tensorMap P.Coefficient V.left (𝟙 F) δ.hom ≫ rho P.Coefficient w.left F Q) =
        ((tensorPullIso P.Coefficient w.left F ((pull P.Coefficient v.left).obj H)).hom ≫
          tensorMap P.Coefficient W.left (𝟙 ((pull P.Coefficient w.left).obj F)) d) ≫
          (adj P.Coefficient w.left).unit.app
            (tensor P.Coefficient W.left ((pull P.Coefficient w.left).obj F) Q) := by
      rw [Functor.map_comp, (twoOpenRhoNormalization P W V w F Q).2]
      simp only [Category.assoc]
      rw [← Category.assoc,
        (finiteTensorPullCoherence P.Coefficient).2.2.2.1 w.left (𝟙 F) δ.hom]
      simp only [Category.assoc]
      rw [← Category.assoc (tensorMap P.Coefficient W.left _ _), tensorMap_comp]
      erw [(pull P.Coefficient w.left).map_id F]
      erw [Category.id_comp]
    have ha : (pull P.Coefficient v.left).map (gamma P.Coefficient v.left F H) =
        ((tensorPullIso P.Coefficient v.left ((finiteShriek P.Coefficient v.left).obj F) H).hom ≫
          tensorMap P.Coefficient V.left b (𝟙 ((pull P.Coefficient v.left).obj H))) ≫
          (adj P.Coefficient v.left).unit.app
            (tensor P.Coefficient V.left F ((pull P.Coefficient v.left).obj H)) := by
      simpa only [Category.assoc, b, twoOpenUnitIso, asIso_inv] using
        finiteOpenGammaRestriction P.Coefficient v.left F H
    have he := nestedRestriction P.Coefficient w.left v.left hc (gamma P.Coefficient v.left F H)
      (tensorMap P.Coefficient V.left (𝟙 F) δ.hom ≫ rho P.Coefficient w.left F Q) _ _ ha hf
    have ht := nestedTensorMap P.Coefficient w.left v.left
      ((finiteShriek P.Coefficient v.left).obj F) H
      b (𝟙 ((pull P.Coefficient v.left).obj H)) (𝟙 ((pull P.Coefficient w.left).obj F)) d
    erw [(pull P.Coefficient w.left).map_id] at ht
    erw [Category.id_comp] at ht
    simp only [Category.comp_id, Functor.map_comp, Category.assoc] at ht
    simp only [twoOpenLeftChain, Functor.map_comp, Category.assoc] at he ⊢
    erw [he]
    have ht' := congrArg (fun z ↦ z ≫ (adj P.Coefficient (w.left ≫ v.left)).unit.app
      (tensor P.Coefficient W.left ((pull P.Coefficient w.left).obj F) Q)) ht
    simp only [Category.assoc] at ht'
    erw [ht']
    simp only [twoOpenLeftRestriction, twoOpenFirstRestriction,
      twoOpenDeltaRestriction, b, d, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
      Iso.symm_hom, Category.assoc]
  · let b := (twoOpenUnitIso P.Coefficient v.left F).inv
    let d := (pull P.Coefficient w.left).map δ.hom ≫ (twoOpenUnitIso P.Coefficient w.left Q).inv
    have hf : (pull P.Coefficient w.left).map
        (tensorMap P.Coefficient V.left δ.hom (𝟙 F) ≫ gamma P.Coefficient w.left Q F) =
        ((tensorPullIso P.Coefficient w.left ((pull P.Coefficient v.left).obj H) F).hom ≫
          tensorMap P.Coefficient W.left d (𝟙 ((pull P.Coefficient w.left).obj F))) ≫
          (adj P.Coefficient w.left).unit.app
            (tensor P.Coefficient W.left Q ((pull P.Coefficient w.left).obj F)) := by
      rw [Functor.map_comp, finiteOpenGammaRestriction]
      simp only [Category.assoc]
      rw [← Category.assoc,
        (finiteTensorPullCoherence P.Coefficient).2.2.2.1 w.left δ.hom (𝟙 F)]
      simp only [Category.assoc]
      rw [← Category.assoc (tensorMap P.Coefficient W.left _ _), tensorMap_comp]
      erw [(pull P.Coefficient w.left).map_id F]
      simp only [Category.comp_id, d, twoOpenUnitIso, asIso_inv]
    have ha : (pull P.Coefficient v.left).map (rho P.Coefficient v.left H F) =
        ((tensorPullIso P.Coefficient v.left H ((finiteShriek P.Coefficient v.left).obj F)).hom ≫
          tensorMap P.Coefficient V.left (𝟙 ((pull P.Coefficient v.left).obj H)) b) ≫
          (adj P.Coefficient v.left).unit.app
            (tensor P.Coefficient V.left ((pull P.Coefficient v.left).obj H) F) := by
      simpa only [Category.assoc] using (twoOpenRhoNormalization P V Y v H F).2
    have he := nestedRestriction P.Coefficient w.left v.left hc (rho P.Coefficient v.left H F)
      (tensorMap P.Coefficient V.left δ.hom (𝟙 F) ≫ gamma P.Coefficient w.left Q F) _ _ ha hf
    have ht := nestedTensorMap P.Coefficient w.left v.left H
      ((finiteShriek P.Coefficient v.left).obj F)
      (𝟙 ((pull P.Coefficient v.left).obj H)) b d (𝟙 ((pull P.Coefficient w.left).obj F))
    erw [(pull P.Coefficient w.left).map_id] at ht
    erw [Category.id_comp] at ht
    simp only [Category.comp_id, Functor.map_comp, Category.assoc] at ht
    simp only [twoOpenRightChain, Functor.map_comp, Category.assoc] at he ⊢
    erw [he]
    have ht' := congrArg (fun z ↦ z ≫ (adj P.Coefficient (w.left ≫ v.left)).unit.app
      (tensor P.Coefficient W.left Q ((pull P.Coefficient w.left).obj F))) ht
    simp only [Category.assoc] at ht'
    erw [ht']
    simp only [twoOpenRightRestriction, twoOpenFirstRestriction,
      twoOpenDeltaRestriction, b, d, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
      Iso.symm_hom, Category.assoc]

end WeilConjectures.FiniteOpenProduct
