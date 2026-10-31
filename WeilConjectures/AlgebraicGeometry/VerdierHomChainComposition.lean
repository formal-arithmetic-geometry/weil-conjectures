/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VerdierHomChainCompositionData
public import WeilConjectures.AlgebraicGeometry.SixFunctorOperationDatum
public import WeilConjectures.AlgebraicGeometry.ExceptionalAdjointAdmissibility
public import WeilConjectures.AlgebraicGeometry.TensorAdjunctionExchange
public import WeilConjectures.AlgebraicGeometry.CompactSupportProjectionFormula
public import WeilConjectures.AlgebraicGeometry.AdmissibleVerdierExchange
public import WeilConjectures.SixFunctors.VerdierExchangeData
public import WeilConjectures.AlgebraicGeometry.PodHomChainCounitFormula
public import WeilConjectures.AlgebraicGeometry.PodCtfPairingMaps
public import WeilConjectures.AlgebraicGeometry.CoefficientGammaRepresentatives
import WeilConjectures.AlgebraicGeometry.VerdierOrdinaryTensorTransport
import WeilConjectures.AlgebraicGeometry.VerdierProjectionExceptionalPaste
import WeilConjectures.AlgebraicGeometry.TensorHomCoefficientTransposes
import WeilConjectures.AlgebraicGeometry.VerdierIdentityProjection

/-! # Composition of the representing Hom chain for Verdier exchange

Source: literature/blueprint/latest/blueprint/sec-six-functors/
sk-thm-sf-compatibility/fix-prop-coherence.proof.md, the adjoint-mate sentence
and the following coefficient paragraph (blueprint: lem-sf-verdier-hom-chain-composition).

The chain is the inverse of the published PodHomChain.homEquiv. All composition
coordinates below are restrictions of the specified compositors, or their adjoint mates.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Opposite

namespace WeilConjectures.VerdierHomChainComposition
open TensorHomCoefficientTransposes

variable {D : FiniteFieldDatum.{u}} {B : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic B.l) E]
  [FiniteDimensional (Padic B.l) E] {n : ℕ} {hn : 1 ≤ n}
  (S : SixFunctorOperationDatum D B E n hn) (s : PodCoefficientStage)

section OneMap
variable {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left)
  [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
  (R : Domain S s f c)

/-- Identity tests are allowed: the source and target are objects of the same full
finite-Tor category. The two actual chain representatives are mutually inverse,
and every test arrow is sent to its postcomposition with the forward representative.
Source: proof steps 1--2 (blueprint: lem-sf-verdier-hom-chain-composition).
Proof: use lem-pod-hom-chain-ctf-domains for all intermediate objects and the
projection at both representing objects. By lem-pod-hom-chain-counit-formula,
the reverse chain is postcomposition with curry(p_N). Evaluate the bijection at
1_B to obtain forward. Naturality gives b*a=1_B; evaluate at A and use
injectivity to get a*b=1_A. Naturality of the inverse gives the test-arrow formula.
The same naturality in N and M gives the two functor-variable squares. -/
theorem representing_chain
    (M : (PodCoefficientStage.domain S s X).FullSubcategory)
    (N : (PodCoefficientStage.domain S s Y).FullSubcategory) :
    forward S s f c R M N ≫ (PodHomChain.homEquiv S s f c R M N _ (𝟙 _)) = 𝟙 _ ∧
    (PodHomChain.homEquiv S s f c R M N _ (𝟙 _)) ≫ forward S s f c R M N = 𝟙 _ ∧
    (∀ (T : (PodCoefficientStage.domain S s Y).FullSubcategory)
      (v : T ⟶ (PodHomChain.targetFunctor S s f c R M).obj N),
      chain S s f c R M N T v = v ≫ forward S s f c R M N) := by
  have hc := PodHomChain.counit_formula S s f c R M
  have ha : PodHomChain.homEquiv S s f c R M N _ (forward S s f c R M N) =
      𝟙 _ := (PodHomChain.homEquiv S s f c R M N _).apply_symm_apply _
  have ht (T : (PodCoefficientStage.domain S s Y).FullSubcategory)
      (v : T ⟶ (PodHomChain.targetFunctor S s f c R M).obj N) :
      PodHomChain.homEquiv S s f c R M N T (v ≫ forward S s f c R M N) = v := by
    rw [hc.2.1, ha, Category.comp_id]
  constructor
  · have h := hc.2.1 N _ _ (forward S s f c R M N) (𝟙 _)
    simpa only [Category.comp_id, ha] using h.symm
  constructor
  · apply (PodHomChain.homEquiv S s f c R M N _).injective
    rw [hc.2.1, ha, Category.comp_id]
  · intro T v
    exact (PodHomChain.homEquiv S s f c R M N T).injective
      (((PodHomChain.homEquiv S s f c R M N T).apply_symm_apply v).trans (ht T v).symm)

/-- Naturality of the displayed forward chain in tests and in the second input,
including the identity test used to identify its representing map.
Source: natural-chain clause and proof step 2
(blueprint: lem-sf-verdier-hom-chain-composition).
Proof: invert the natural bijections of lem-pod-hom-chain-counit-formula.
Each inverse has the same source and target naturality, so their composite does.
Evaluate on identity to obtain the representing-map naturality equation. -/
theorem chain_naturality
    (M : (PodCoefficientStage.domain S s X).FullSubcategory) :
    (∀ (N T T' : (PodCoefficientStage.domain S s Y).FullSubcategory)
      (a : T' ⟶ T) (v : T ⟶ (PodHomChain.targetFunctor S s f c R M).obj N),
      chain S s f c R M N T' (a ≫ v) = a ≫ chain S s f c R M N T v) ∧
    (∀ (N N' : (PodCoefficientStage.domain S s Y).FullSubcategory) (a : N ⟶ N'),
      (PodHomChain.targetFunctor S s f c R M).map a ≫ forward S s f c R M N' =
        forward S s f c R M N ≫ (PodHomChain.sourceFunctor S s f c R M).map a) := by
  have hc := PodHomChain.counit_formula S s f c R M
  constructor
  · intro N T T' a v
    rw [(representing_chain S s f c R M N).2.2,
      (representing_chain S s f c R M N).2.2, Category.assoc]
  · intro N N' a
    apply (PodHomChain.homEquiv S s f c R M N' _).injective
    rw [hc.2.1, hc.2.2]
    simp only [forward, chain, Equiv.apply_symm_apply, Category.comp_id, Category.id_comp]

/-- The canonical exchange is represented by the two identity-test arrows.
Only the inverse identities, already separately stated, are used as proof fields.
Source: proof step 2 (blueprint: lem-sf-verdier-hom-chain-composition). -/
def exchange (M : (PodCoefficientStage.domain S s X).FullSubcategory)
    (N : (PodCoefficientStage.domain S s Y).FullSubcategory) :
    (PodHomChain.targetFunctor S s f c R M).obj N ≅
      (PodHomChain.sourceFunctor S s f c R M).obj N where
  hom := forward S s f c R M N
  inv := (PodHomChain.homEquiv S s f c R M N _ (𝟙 _))
  hom_inv_id := (representing_chain S s f c R M N).1
  inv_hom_id := (representing_chain S s f c R M N).2.1

end OneMap


/-- Stagewise structure-map admissibility, using the finite-type proofs already
stored in the over-category object. Source: the three structure-map hypotheses
(blueprint: lem-sf-verdier-hom-chain-composition). -/
def structureAdmissible (X : SixFunctorSpace D)
    [IsSeparated (sixFunctorStructure X).hom.left]
    (c : Compactification (sixFunctorStructure X).hom.left) : Prop := by
  letI : LocallyOfFiniteType (sixFunctorStructure X).hom.left := X.property.1
  letI : QuasiCompact (sixFunctorStructure X).hom.left := X.property.2
  exact Admissible S s (sixFunctorStructure X) c

private theorem reverse_chain_formula
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (R : Domain S s f c)
    (M : (PodCoefficientStage.domain S s X).FullSubcategory)
    (N T : (PodCoefficientStage.domain S s Y).FullSubcategory)
    (z : T ⟶ (PodHomChain.sourceFunctor S s f c R M).obj N) :
    PodHomChain.homEquiv S s f c R M N T z =
      (R.tensorAdjunctionY (R.support.obj M)).homEquiv T N
        (PodHomChain.projection S s f c R M T ≫
          (R.exceptionalAdjunction.homEquiv _ N).symm
            (((R.tensorAdjunctionX M).homEquiv _ _).symm
              ((R.ordinaryAdjunction.homEquiv T _).symm z))) := by
  simp only [PodHomChain.homEquiv, Equiv.trans_apply, Iso.homCongr_apply,
    Iso.symm_inv, Iso.refl_hom, Category.comp_id, PodHomChain.projection]
  rfl

private theorem inverse_tensor_shared
    {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z)
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (Rf : Domain S s f cf) (Rg : Domain S s g cg)
    (hY : Rf.closedY = Rg.closedX)
    (M : (PodCoefficientStage.domain S s Y).FullSubcategory)
    (N T : (PodCoefficientStage.domain S s Y).FullSubcategory)
    (a : (tensorLeft Rf.closedY.closed.monoidal M).obj T ⟶ N) :
    ((Rg.tensorAdjunctionX M).homEquiv T N).symm
        ((Rf.tensorAdjunctionY M).homEquiv T N a) =
      (tensorCoordinate S s hY M T).inv ≫ a := by
  cases Rf with
  | mk pf df sf ef xf yf txf tyf =>
    cases Rg with
    | mk pg dg sg eg xg yg txg tyg =>
      dsimp only at hY
      subst xg
      simp only [PodCtfAdjunctionData.tensorAdjunctionX,
        PodCtfAdjunctionData.tensorAdjunctionY, Equiv.symm_apply_apply,
        tensorCoordinate, eqToIso_refl, Iso.refl_inv, Category.id_comp]

private theorem pairing_projection_eq
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (R : Domain S s f c)
    (M : (PodCoefficientStage.domain S s X).FullSubcategory)
    (T : (PodCoefficientStage.domain S s Y).FullSubcategory) :
    PodCtfPairing.projection S s f c R M T = PodHomChain.projection S s f c R M T :=
  rfl

private theorem reverse_chain_paste
    {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    [IsSeparated g.hom.left] [LocallyOfFiniteType g.hom.left] [QuasiCompact g.hom.left]
    [IsSeparated (f ≫ g).hom.left] [LocallyOfFiniteType (f ≫ g).hom.left]
    [QuasiCompact (f ≫ g).hom.left]
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (cx : Compactification (f ≫ g).hom.left)
    (Rf : Domain S s f cf) (Rg : Domain S s g cg) (Rx : Domain S s (f ≫ g) cx)
    (hX : Rf.closedX = Rx.closedX) (hY : Rf.closedY = Rg.closedX)
    (hZ : Rg.closedY = Rx.closedY)
    (tX : HEq Rf.tensorX Rx.tensorX) (tY : HEq Rf.tensorY Rg.tensorX)
    (tZ : HEq Rg.tensorY Rx.tensorY)
    (nX : TensorPresentationNatural S s X Rf.closedX Rf.tensorX)
    (nY : TensorPresentationNatural S s Y Rf.closedY Rf.tensorY)
    (nZ : TensorPresentationNatural S s Z Rg.closedY Rg.tensorY)
    (M : (PodCoefficientStage.domain S s X).FullSubcategory)
    (N T : (PodCoefficientStage.domain S s Z).FullSubcategory)
    (z : T ⟶ (PodHomChain.sourceFunctor S s (f ≫ g) cx Rx M).obj N) :
    PodHomChain.homEquiv S s g cg Rg (Rf.support.obj M) N T
        (z ≫ (sourceCoordinate S s f g cf cg cx Rf Rg Rx M N).hom ≫
          Rg.direct.map (PodHomChain.homEquiv S s f cf Rf M
            (Rg.exceptional.obj N) _ (𝟙 _))) =
      PodHomChain.homEquiv S s (f ≫ g) cx Rx M N T z ≫
        (targetCoordinate S s f g cf cg cx Rf Rg Rx M N).hom := by
  let y := (Rg.ordinaryAdjunction.homEquiv T _).symm
    (z ≫ (sourceCoordinate S s f g cf cg cx Rf Rg Rx M N).hom)
  let b := ((Rf.tensorAdjunctionX M).homEquiv _ _).symm
    ((Rf.ordinaryAdjunction.homEquiv _ _).symm y)
  have hp := projection_exceptional_paste S s f g cf cg cx Rf Rg Rx
    hX hY hZ tX tY tZ nX nY nZ M N T b
  simp only [pairing_projection_eq] at hp
  have ho := ordinary_tensor_transport S s f g cf cg cx Rf Rg Rx hX M N T z
  have ho' :
      (tensorCoordinate S s hX M (Rx.pull.obj T)).inv ≫
          (tensorLeft Rf.closedX.closed.monoidal M).map
            ((pullComposition S s f g cf cg cx Rf Rg Rx).hom.app T) ≫
          b ≫ (exceptionalComposition S s f g cf cg cx Rf Rg Rx).inv.app N =
        ((Rx.tensorAdjunctionX M).homEquiv _ _).symm
          ((Rx.ordinaryAdjunction.homEquiv T _).symm z) := by
    have hh := congrArg (fun a ↦
      (tensorCoordinate S s hX M (Rx.pull.obj T)).inv ≫ a ≫
        (exceptionalComposition S s f g cf cg cx Rf Rg Rx).inv.app N) ho
    simpa only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id,
      Iso.inv_hom_id_assoc, b, y, PodHomChain.sourceFunctor, PodHomChain.homX,
      Functor.comp_obj] using hh.symm
  rw [ho'] at hp
  rw [← reverse_chain_formula S s (f ≫ g) cx Rx M N T z] at hp
  rw [← hp, reverse_chain_formula S s g cg Rg]
  rw [← Category.assoc z, Rg.ordinaryAdjunction.homEquiv_naturality_right_symm]
  have hf := (PodHomChain.counit_formula S s f cf Rf M).2.1
    (Rg.exceptional.obj N) _ _ y (𝟙 _)
  simp only [Category.comp_id] at hf
  change (Rg.tensorAdjunctionY (Rg.support.obj (Rf.support.obj M))).homEquiv T N
    (PodHomChain.projection S s g cg Rg (Rf.support.obj M) T ≫
      (Rg.exceptionalAdjunction.homEquiv _ N).symm
        (((Rg.tensorAdjunctionX (Rf.support.obj M)).homEquiv _ _).symm
          (y ≫ PodHomChain.homEquiv S s f cf Rf M
            (Rg.exceptional.obj N) _ (𝟙 _)))) = _
  rw [← hf, reverse_chain_formula S s f cf Rf]
  rw [inverse_tensor_shared S s f g cf cg Rf Rg hY]


private theorem cancel_exchange
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B : C} (i : A ≅ B) {T U : D}
    (e : (T ⟶ F.obj A) ≃ (T ⟶ U))
    (u : T ⟶ F.obj B) (v : T ⟶ U)
    (h : e (u ≫ F.map i.inv) = v) : u = e.symm v ≫ F.map i.hom := by
  apply (cancel_mono (F.map i.inv)).1
  apply e.injective
  simpa only [Category.assoc, ← F.map_comp, i.hom_inv_id, F.map_id,
    Category.comp_id, Equiv.apply_symm_apply] using h

private theorem naturality_paste
    {C D E : Type*} [Category C] [Category D] [Category E]
    (Q : C ⥤ E) (F : C ⥤ D) (G : D ⥤ E) (d : Q ≅ F ⋙ G)
    {A₀ A₁ A₂ A₃ : C} {B₀ B₁ : D} {V W : E}
    (a : V ⟶ Q.obj A₀) (e : A₀ ⟶ A₁) (j : A₁ ⟶ A₂) (k : A₂ ⟶ A₃)
    (t : V ⟶ W) (b : W ⟶ G.obj B₀) (c : B₀ ⟶ F.obj A₁)
    (l : B₀ ⟶ B₁) (m : B₁ ⟶ F.obj A₂)
    (hc : a ≫ Q.map e ≫ d.hom.app A₁ = t ≫ b ≫ G.map c)
    (hn : l ≫ m = c ≫ F.map j) :
    a ≫ Q.map (e ≫ j ≫ k) ≫ d.hom.app A₃ =
      t ≫ b ≫ G.map l ≫ G.map (m ≫ F.map k) := by
  have hd := d.hom.naturality (j ≫ k)
  change Q.map (j ≫ k) ≫ d.hom.app A₃ =
    d.hom.app A₁ ≫ G.map (F.map (j ≫ k)) at hd
  calc
    _ = (a ≫ Q.map e ≫ d.hom.app A₁) ≫ G.map (F.map (j ≫ k)) := by
      rw [Q.map_comp, Category.assoc, hd]
      simp only [Category.assoc]
    _ = (t ≫ b ≫ G.map c) ≫ G.map (F.map (j ≫ k)) :=
      congrArg (fun z ↦ z ≫ G.map (F.map (j ≫ k))) hc
    _ = _ := by
      simp only [Functor.map_comp, Category.assoc]
      rw [← G.map_comp_assoc, ← hn]
      simp only [Functor.map_comp, Category.assoc]

private theorem verdier_of_chain
    {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    [IsSeparated g.hom.left] [LocallyOfFiniteType g.hom.left] [QuasiCompact g.hom.left]
    [IsSeparated (f ≫ g).hom.left] [LocallyOfFiniteType (f ≫ g).hom.left]
    [QuasiCompact (f ≫ g).hom.left]
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (cx : Compactification (f ≫ g).hom.left)
    (Rf : Domain S s f cf) (Rg : Domain S s g cg) (Rx : Domain S s (f ≫ g) cx)
    (h : ChainComposition S s f g cf cg cx Rf Rg Rx) :
    VerdierComposition S s f g cf cg cx Rf Rg Rx := by
  intro OX OY OZ df dg M
  let H := PodCtfPairing.homX S s f cf Rf M
  let K := PodCtfPairing.homY S s f cf Rf (Rf.support.obj M)
  let e := exceptionalComposition S s f g cf cg cx Rf Rg Rx
  let d := directComposition S s f g cf cg cx Rf Rg Rx
  let t := targetCoordinate S s f g cf cg cx Rf Rg Rx M OZ
  have hc := h M OZ _ (𝟙 _)
  rw [(representing_chain S s g cg Rg (Rf.support.obj M) OZ).2.2] at hc
  simp only [Category.id_comp, Category.assoc] at hc
  change forward S s (f ≫ g) cx Rx M OZ ≫
      (Rx.direct.map (H.map (e.hom.app OZ)) ≫ d.hom.app _) =
    t.hom ≫ forward S s g cg Rg (Rf.support.obj M) OZ ≫
      Rg.direct.map (forward S s f cf Rf M (Rg.exceptional.obj OZ)) at hc
  have hn := (chain_naturality S s f cf Rf M).2
    (Rg.exceptional.obj OZ) OY dg.hom
  change K.map dg.hom ≫ forward S s f cf Rf M OY =
    forward S s f cf Rf M (Rg.exceptional.obj OZ) ≫
      Rf.direct.map (H.map (Rf.exceptional.map dg.hom)) at hn
  simp only [epsilon, dualizingComposition, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom, Category.assoc]
  have hh := naturality_paste Rx.direct Rf.direct Rg.direct d
    (forward S s (f ≫ g) cx Rx M OZ) (H.map (e.hom.app OZ))
    (H.map (Rf.exceptional.map dg.hom)) (H.map df.hom)
    t.hom (forward S s g cg Rg (Rf.support.obj M) OZ)
    (forward S s f cf Rf M (Rg.exceptional.obj OZ))
    (K.map dg.hom) (forward S s f cf Rf M OY) hc hn
  simpa only [Functor.map_comp, Category.assoc, H, K, e, d, t,
    PodCtfPairing.homX, PodCtfPairing.homY, Functor.comp_obj] using hh

/-- The actual four-stage chain composition and its Verdier specialization.
The law holds for every supplied presentation, using one closed presentation and
one tensor comparison on each space. The equalities identify the entire closed
data (including monoidal structure, evaluation and symmetry); HEq identifies the
dependently typed tensor comparisons after these closed-data identifications.
The shared tensor comparison is natural in both variables: test naturality is
part of its natural isomorphisms, and factor naturality is stated explicitly. The six admissibility
hypotheses are exactly those in the node; the structure-map compactifications are
used only to state these predicates.

Source: proof steps 1--7 (blueprint: lem-sf-verdier-hom-chain-composition).
Proof: use the supplied restricted adjunctions, identifying their closed and tensor
data on each common space by the displayed equalities. Factor naturality transports
the tensor comparisons along support composition. The specified projection theorem gives
its associativity pentagon. Invert the chains of lem-pod-hom-chain-counit-formula.
On an arbitrary arrow, uncurry the successive chain to the f projection, the g
projection, F_g(epsilon_f), then epsilon_g. The exceptional compositor gives
precisely this pasted counit for the composite; ordinary transposition gives the
pasted ordinary counit. Substitute the projection pentagon and use naturality of
the support compositor. Injectivity of the transpositions proves ChainComposition.
By representing_chain it holds also at identity tests. Substitute omega_Z and
the exceptional structure-mate cocycle; naturality in the second Hom variable
gives VerdierComposition. This is the comparison of fix-cor-verdier-exchange,
by specialization below. Finite and integral coefficient passage preserves each
transpose, projection and evaluation by the coefficient lemmas. At rational
coefficients use the actual raw localization; at algebraically closed coefficients
represent the finite calculation at one common finite field, with independence
under enlargement from lem-sf-tensor-hom-coefficient-transposes. -/
theorem verdier_hom_chain_composition
    {X Y Z : SixFunctorSpace D}
    [IsSeparated (sixFunctorStructure X).hom.left]
    [IsSeparated (sixFunctorStructure Y).hom.left]
    [IsSeparated (sixFunctorStructure Z).hom.left]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    [IsSeparated g.hom.left] [LocallyOfFiniteType g.hom.left] [QuasiCompact g.hom.left]
    [IsSeparated (f ≫ g).hom.left] [LocallyOfFiniteType (f ≫ g).hom.left]
    [QuasiCompact (f ≫ g).hom.left]
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (cx : Compactification (f ≫ g).hom.left)
    (cX : Compactification (sixFunctorStructure X).hom.left)
    (cY : Compactification (sixFunctorStructure Y).hom.left)
    (cZ : Compactification (sixFunctorStructure Z).hom.left)
    (_hf : Admissible S s f cf) (_hg : Admissible S s g cg)
    (_hx : Admissible S s (f ≫ g) cx)
    (_haX : structureAdmissible S s X cX)
    (_haY : structureAdmissible S s Y cY)
    (_haZ : structureAdmissible S s Z cZ)
    (Rf : Domain S s f cf) (Rg : Domain S s g cg) (Rx : Domain S s (f ≫ g) cx)
    (_closedX : Rf.closedX = Rx.closedX) (_closedY : Rf.closedY = Rg.closedX)
    (_closedZ : Rg.closedY = Rx.closedY)
    (_tensorX : HEq Rf.tensorX Rx.tensorX) (_tensorY : HEq Rf.tensorY Rg.tensorX)
    (_tensorZ : HEq Rg.tensorY Rx.tensorY)
    (_naturalX : TensorPresentationNatural S s X Rf.closedX Rf.tensorX)
    (_naturalY : TensorPresentationNatural S s Y Rf.closedY Rf.tensorY)
    (_naturalZ : TensorPresentationNatural S s Z Rg.closedY Rg.tensorY) :
    ChainComposition S s f g cf cg cx Rf Rg Rx ∧
      VerdierComposition S s f g cf cg cx Rf Rg Rx := by
  have h : ChainComposition S s f g cf cg cx Rf Rg Rx := by
    intro M N T v
    have hp := reverse_chain_paste S s f g cf cg cx Rf Rg Rx
      _closedX _closedY _closedZ _tensorX _tensorY _tensorZ
      _naturalX _naturalY _naturalZ M N T
      (chain S s (f ≫ g) cx Rx M N T v)
    have hv : PodHomChain.homEquiv S s (f ≫ g) cx Rx M N T
        (chain S s (f ≫ g) cx Rx M N T v) = v :=
      (PodHomChain.homEquiv S s (f ≫ g) cx Rx M N T).apply_symm_apply v
    have hp' := hp.trans (congrArg (fun k ↦
      k ≫ (targetCoordinate S s f g cf cg cx Rf Rg Rx M N).hom) hv)
    apply cancel_exchange Rg.direct (exchange S s f cf Rf M (Rg.exceptional.obj N))
      (PodHomChain.homEquiv S s g cg Rg (Rf.support.obj M) N T)
    simpa only [Category.assoc, exchange, chain,
      PodHomChain.sourceFunctor, PodHomChain.targetFunctor, PodHomChain.homX,
      PodHomChain.homY, Functor.comp_obj] using hp'
  exact ⟨h, verdier_of_chain S s f g cf cg cx Rf Rg Rx h⟩

private theorem closed_inverse_transpose
    {A : Type*} [Category A] {H : Aᵒᵖ × A ⥤ A}
    (C : CoefficientClosedStructure H) (T P N : A) (v : T ⟶ H.obj (op P, N)) :
    (C.transpose T P N).symm v =
      C.tensor.map (Prod.mkHom v (𝟙 P)) ≫ C.evaluation P N := by
  let := C.monoidal
  have ht : C.tensor.map (Prod.mkHom v (𝟙 P)) =
      (@MonoidalCategory.tensorRight _ _ C.monoidal P).map v :=
    MonoidalCategory.tensorHom_id _ _
  rw [ht]
  exact (C.adjunction P).homEquiv_counit T N v

private theorem closed_transpose_source
    {A : Type*} [Category A] {H : Aᵒᵖ × A ⥤ A}
    (C : CoefficientClosedStructure H) {T T' : A} (P N : A) (v : T ⟶ T')
    (w : C.tensor.obj (T', P) ⟶ N) :
    C.transpose T P N (C.tensor.map (Prod.mkHom v (𝟙 P)) ≫ w) =
      v ≫ C.transpose T' P N w := by
  let := C.monoidal
  have ht : C.tensor.map (Prod.mkHom v (𝟙 P)) =
      (@MonoidalCategory.tensorRight _ _ C.monoidal P).map v :=
    MonoidalCategory.tensorHom_id _ _
  rw [ht]
  exact (C.adjunction P).homEquiv_naturality_left v w

section StageComparison
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  {X Y Z : Scheme.{u}} {t : Stage.{u} l}
  {F : Operation l Ω X Y t} {A : Operation l Ω Y Z t}
  {G : Operation l Ω X Z t} {unit : C l Ω Z t}
  (d : VerdierExchange.StageData l Ω t F A G unit)

/-- Forget the dualizing comparison in the dependency's stage data. This reuses
its tensor, Hom, projection and both adjunctions literally.
Source: first paragraph and proof step 5
(blueprint: lem-sf-verdier-hom-chain-composition). -/
def stageModel : TensorAdjunctionExchange.Model l Ω t F where
  homX := d.homX
  homY := d.homY
  closedX := d.closedX
  closedY := d.closedY
  pull := d.pull
  star := d.star
  adjunction := d.adjunction
  projection := d.projection

/-- The five forward bijections in the dependency's right-factor tensor coordinates.
Its projection arrow is the inverse of PF after the canonical signed interchange.
Source: displayed chain, proof step 1
(blueprint: lem-sf-verdier-hom-chain-composition). -/
def stageChain (M : C l Ω X t) (N T : C l Ω Y t) :
    (T ⟶ d.homY.obj (op (F.F.obj M), N)) ≃
      (T ⟶ d.star.obj (d.homX.obj (op M, F.G.obj N))) :=
  ((d.closedY.transpose T (F.F.obj M) N).symm.trans
    (Iso.homCongr (d.projection T M).symm (Iso.refl N))).trans
      ((F.adjunction.homEquiv _ N).trans
        ((d.closedX.transpose (d.pull.obj T) M (F.G.obj N)).trans
          (d.adjunction.homEquiv T _)))

/-- For a projection natural in the test object, the chain represents exactly
 tensor-adjunction exchange, and specialization is the published Verdier arrow,
including its specified dualizing comparison.
Source: proof steps 1--2 and 5
(blueprint: lem-sf-verdier-hom-chain-composition).
Proof: projection_natural makes the projection bijection natural in the test
object; all other bijections are adjunctions. Evaluating the five maps
on identity gives Model.inverseComponent: uncurrying the identity is evaluation,
and precomposition by inverse PF is d.projection.hom in these coordinates.
Naturality therefore gives postcomposition on every input arrow. The component
normalization of fix-lem-tensor-adjunction identifies its canonical inverse.
For N=A.G(unit), naturality of tensor-Hom transpose in the target moves
postcomposition by d.dualizing through the last two bijections. The result is
literally StageData.epsilon from def-sf-verdier-exchange-data, hence the canonical
comparison of fix-cor-verdier-exchange, with no arbitrary pullback-duality assertion. -/
theorem stage_specialization
    (projection_natural : ∀ (T T' : C l Ω Y t) (a : T ⟶ T') (M : C l Ω X t),
      F.F.map (d.closedX.tensor.map (Prod.mkHom (d.pull.map a) (𝟙 M))) ≫
          (d.projection T' M).hom =
        (d.projection T M).hom ≫
          d.closedY.tensor.map (Prod.mkHom a (𝟙 (F.F.obj M))))
    (M : C l Ω X t) :
    (∀ (N T : C l Ω Y t) (v : T ⟶ d.homY.obj (op (F.F.obj M), N)),
      stageChain l Ω d M N T v =
        v ≫ (stageModel l Ω d).inverseComponent l Ω M N) ∧
    (∀ h : TensorAdjunctionExchange.Conclusion l Ω (stageModel l Ω d),
      ∀ N : C l Ω Y t,
        (h.exchange.inv.app (op M)).app N = stageChain l Ω d M N _ (𝟙 _)) ∧
    d.epsilon l Ω M =
      stageChain l Ω d M (A.G.obj unit) _ (𝟙 _) ≫
        d.star.map (d.homX.map (Prod.mkHom (𝟙 (op M)) d.dualizing.hom)) := by
  have hid (N : C l Ω Y t) : stageChain l Ω d M N _ (𝟙 _) =
      (stageModel l Ω d).inverseComponent l Ω M N := by
    simp only [stageChain, Equiv.trans_apply, Iso.homCongr_apply, Iso.symm_inv,
      Iso.refl_hom, Category.comp_id]
    change d.adjunction.homEquiv _ _
      (d.closedX.transpose _ M _ (F.adjunction.homEquiv _ _
        ((d.projection _ M).hom ≫
          ((d.closedY.adjunction (F.F.obj M)).homEquiv _ N).symm (𝟙 _)))) = _
    rw [(d.closedY.adjunction (F.F.obj M)).homEquiv_symm_id]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · intro N T v
    have hv := closed_inverse_transpose d.closedY T (F.F.obj M) N v
    simp only [stageChain, Equiv.trans_apply, Iso.homCongr_apply, Iso.symm_inv,
      Iso.refl_hom, Category.comp_id]
    rw [hv, ← Category.assoc, ← projection_natural, Category.assoc]
    rw [F.adjunction.homEquiv_naturality_left]
    rw [closed_transpose_source, d.adjunction.homEquiv_naturality_left]
    rfl
  · intro h N
    rw [h.components, hid]
  · rw [hid]
    change d.adjunction.homEquiv _ _
      ((d.closedX.adjunction M).homEquiv _ _
        (F.adjunction.homEquiv _ _ ((d.projection _ M).hom ≫
          d.closedY.evaluation (F.F.obj M) (A.G.obj unit)) ≫ d.dualizing.hom)) =
      d.adjunction.homEquiv _ _
        ((d.closedX.adjunction M).homEquiv _ _
          (F.adjunction.homEquiv _ _ ((d.projection _ M).hom ≫
            d.closedY.evaluation (F.F.obj M) (A.G.obj unit)))) ≫
          d.star.map ((Prod.sectR (op M) _ ⋙ d.homX).map d.dualizing.hom)
    rw [(d.closedX.adjunction M).homEquiv_naturality_right,
      d.adjunction.homEquiv_naturality_right]

end StageComparison

section Identity
universe v
open MonoidalCategory BraidedCategory

private theorem identity_inverse_transpose
    {A : Type u} [Category.{v} A] {L Q : A ⥤ A} (adj : L ⊣ Q)
    (p : L ≅ 𝟭 A) (T N : A) (z : T ⟶ Q.obj N) :
    (adj.homEquiv T N).symm z =
      p.hom.app T ≫ z ≫
        (adj.rightAdjointUniq (Adjunction.id.ofNatIsoLeft p.symm)).hom.app N := by
  let adj' := Adjunction.id.ofNatIsoLeft p.symm
  have h := adj'.homEquiv_naturality_left_symm z
    ((adj.rightAdjointUniq adj').hom.app N)
  rw [Adjunction.homEquiv_symm_rightAdjointUniq_hom_app] at h
  rw [Adjunction.homEquiv_ofNatIsoLeft_symm_apply] at h
  simp only [Adjunction.homEquiv_counit, Adjunction.id_counit, Functor.id_map,
    NatTrans.id_app, Iso.symm_inv] at h
  erw [Category.comp_id] at h
  simpa only [Category.assoc, Adjunction.homEquiv_counit] using h.symm

private theorem transpose_factor
    {A : Type u} [Category.{v} A] {H : Aᵒᵖ × A ⥤ A}
    (C : CoefficientClosedStructure H) (T : A) {P P' N : A} (f : P' ⟶ P)
    (g : C.tensor.obj (T, P) ⟶ N) :
    C.transpose T P' N (C.tensor.map (Prod.mkHom (𝟙 T) f) ≫ g) =
      C.transpose T P N g ≫ H.map (Prod.mkHom f.op (𝟙 N)) := by
  let := C.monoidal
  apply (C.transpose T P' N).symm.injective
  rw [Equiv.symm_apply_apply]
  change _ = (tensorRight P').map
    (C.transpose T P N g ≫ H.map (Prod.mkHom f.op (𝟙 N))) ≫ C.evaluation P' N
  rw [Functor.map_comp, Category.assoc]
  change _ = (C.transpose T P N g ▷ P') ≫
    (H.map (Prod.mkHom f.op (𝟙 N)) ▷ P') ≫ C.evaluation P' N
  rw [show (H.map (Prod.mkHom f.op (𝟙 N)) ▷ P') ≫ C.evaluation P' N =
    (H.obj (op P, N) ◁ f) ≫ C.evaluation P N from C.evaluation_naturality P P' N f]
  rw [← Category.assoc, ← whisker_exchange, Category.assoc]
  change _ = (T ◁ f) ≫ (C.transpose T P N).symm (C.transpose T P N g)
  rw [Equiv.symm_apply_apply]
  simp only [CoefficientClosedStructure.tensor, tensor_map, id_tensorHom]

private theorem left_transpose_factor
    {A : Type u} [Category.{v} A] {H : Aᵒᵖ × A ⥤ A}
    (C : CoefficientClosedStructure H) (β : @SymmetricCategory A _ C.monoidal)
    (T : A) {P P' N : A} (f : P' ⟶ P)
    (g : (@MonoidalCategory.tensorLeft _ _ C.monoidal P).obj T ⟶ N) :
    (((C.adjunction P').ofNatIsoLeft
      (@tensorLeftIsoTensorRight _ _ C.monoidal β.toBraidedCategory P').symm).homEquiv T N)
        ((@whiskerRight _ _ C.monoidal.toMonoidalCategoryStruct _ _ f T) ≫ g) =
      (((C.adjunction P).ofNatIsoLeft
        (@tensorLeftIsoTensorRight _ _ C.monoidal β.toBraidedCategory P).symm).homEquiv T N)
          g ≫ H.map (Prod.mkHom f.op (𝟙 N)) := by
  let := C.monoidal
  let := β
  simp only [Adjunction.homEquiv_ofNatIsoLeft_apply, Iso.symm_hom,
    tensorLeftIsoTensorRight_inv_app]
  change C.transpose T P' N ((β_ P' T).inv ≫ (f ▷ T) ≫ g) =
    C.transpose T P N ((β_ P T).inv ≫ g) ≫ H.map (Prod.mkHom f.op (𝟙 N))
  rw [← Category.assoc, ← braiding_inv_naturality_right, Category.assoc]
  simpa only [CoefficientClosedStructure.tensor, tensor_map, id_tensorHom] using
    transpose_factor C T f ((β_ P T).inv ≫ g)

private def leftClosedAdjunction
    {A : Type u} [Category.{v} A] {H : Aᵒᵖ × A ⥤ A}
    (C : CoefficientClosedStructure H) (β : @SymmetricCategory A _ C.monoidal) (M : A) :=
  (C.adjunction M).ofNatIsoLeft
    (@tensorLeftIsoTensorRight _ _ C.monoidal β.toBraidedCategory M).symm

private theorem reverse_identity_chain
    {A : Type u} [Category.{v} A] {H : Aᵒᵖ × A ⥤ A}
    (C : CoefficientClosedStructure H) (β : @SymmetricCategory A _ C.monoidal)
    {P Q F G : A ⥤ A} (adjP : P ⊣ Q) (adjF : F ⊣ G)
    (p : P ≅ 𝟭 A) (q : F ≅ 𝟭 A)
    (proj : ∀ M T : A, (@MonoidalCategory.tensorLeft _ _ C.monoidal (F.obj M)).obj T ⟶
      F.obj ((@MonoidalCategory.tensorLeft _ _ C.monoidal M).obj (P.obj T)))
    (hproj : ∀ M T : A, proj M T ≫
      q.hom.app ((@MonoidalCategory.tensorLeft _ _ C.monoidal M).obj (P.obj T)) ≫
      (@MonoidalCategory.tensorLeft _ _ C.monoidal M).map (p.hom.app T) =
        @whiskerRight _ _ C.monoidal.toMonoidalCategoryStruct _ _ (q.hom.app M) T)
    (M N T : A) (z : T ⟶ Q.obj (H.obj (op M, G.obj N))) :
    (leftClosedAdjunction C β (F.obj M)).homEquiv T N
        (proj M T ≫ (adjF.homEquiv _ N).symm
          (((leftClosedAdjunction C β M).homEquiv _ _).symm
            ((adjP.homEquiv T _).symm z))) =
      z ≫ (adjP.rightAdjointUniq (Adjunction.id.ofNatIsoLeft p.symm)).hom.app
          (H.obj (op M, G.obj N)) ≫
        H.map (Prod.mkHom (𝟙 (op M))
          ((adjF.rightAdjointUniq (Adjunction.id.ofNatIsoLeft q.symm)).hom.app N)) ≫
        H.map (Prod.mkHom (q.hom.app M).op (𝟙 N)) := by
  rw [identity_inverse_transpose adjP p, identity_inverse_transpose adjF q]
  rw [(leftClosedAdjunction C β M).homEquiv_naturality_left_symm]
  simp only [Category.assoc]
  have hp := congrArg (fun k ↦ k ≫
    ((leftClosedAdjunction C β M).homEquiv T (G.obj N)).symm
      (z ≫ (adjP.rightAdjointUniq (Adjunction.id.ofNatIsoLeft p.symm)).hom.app
        (H.obj (op M, G.obj N))) ≫
      (adjF.rightAdjointUniq (Adjunction.id.ofNatIsoLeft q.symm)).hom.app N) (hproj M T)
  simp only [Category.assoc] at hp
  erw [hp]
  erw [left_transpose_factor C β T (q.hom.app M)]
  erw [(leftClosedAdjunction C β M).homEquiv_naturality_right]
  erw [Equiv.apply_symm_apply]
  simp only [Category.assoc]
  rfl


variable (X : SixFunctorSpace D)
  [IsSeparated (sixFunctorStructure X).hom.left]
  (R : Domain S s (𝟙 X) (.ofIsProper ((𝟙 X) : X ⟶ X).hom.left))

/-- The ordinary identity comparison is the unique adjoint mate of the pullback
unit comparison. Source: identity calculation, proof step 5
(blueprint: lem-sf-verdier-hom-chain-composition). -/
def identityDirect (p : R.pull ≅ 𝟭 _) : R.direct ≅ 𝟭 _ :=
  R.ordinaryAdjunction.rightAdjointUniq (Adjunction.id.ofNatIsoLeft p.symm)

/-- Identity compact support is its proper identification followed by the ordinary
identity mate, with no independently supplied compact-support unit.
Source: identity calculation, proof step 5
(blueprint: lem-sf-verdier-hom-chain-composition). -/
def identitySupport (p : R.pull ≅ 𝟭 _) : R.support ≅ 𝟭 _ :=
  ((PodCoefficientStage.domain S s X).fullyFaithfulι.whiskeringRight _).preimageIso
    (X := R.support) (Y := R.direct)
    (Functor.isoWhiskerLeft (PodCoefficientStage.domain S s X).ι
      ((PodCoefficientStage.operations S s).properIdentity (𝟙 X))) ≪≫
        identityDirect S s X R p

/-- The exceptional identity unit is conjugate to the compact-support unit under
its specified adjunction. Source: identity calculation, proof step 5
(blueprint: lem-sf-verdier-hom-chain-composition). -/
def identityExceptional (p : R.pull ≅ 𝟭 _) : R.exceptional ≅ 𝟭 _ :=
  R.exceptionalAdjunction.rightAdjointUniq
    (Adjunction.id.ofNatIsoLeft (identitySupport S s X R p).symm)

/-- The identity Verdier comparison is identity in canonical unit coordinates.
For every presentation whose two copies of the space have the same closed data
and tensor comparison, the pullback unit is normalized by the identity/self compositor, and
both other identity units are its prescribed ordinary/proper/exceptional mates.
Source: identity clause, proof step 5
(blueprint: lem-sf-verdier-hom-chain-composition).
Proof: identify the source and target closed/tensor data by the hypotheses.
Restrict the canonical identity pullback comparison to the finite-Tor
subcategory. Its identity/self composition law fixes the displayed normalization.
The projection pentagon for two identity maps then gives PF_id=PF_id squared
in these coordinates, so invertibility implies PF_id=1. The ordinary and
exceptional triangle identities cancel the remaining transpositions of the chain.
The dualizing structure comparison is the exceptional identity mate by its unit
cocycle. Thus epsilon becomes 1; the displayed formula includes the contravariant
support-unit and covariant ordinary-unit coordinate changes. Finite/integral
units are the normalized module units; localization and common-stage inclusion
carry this same calculation to the field stages. -/
theorem identity_exchange
    (_hId : Admissible S s (𝟙 X) (.ofIsProper ((𝟙 X) : X ⟶ X).hom.left))
    (cX : Compactification (sixFunctorStructure X).hom.left)
    (_hX : structureAdmissible S s X cX)
    (_closed : R.closedX = R.closedY) (_tensor : HEq R.tensorX R.tensorY)
    (_natural : TensorPresentationNatural S s X R.closedX R.tensorX) :
    ∃ p : R.pull ≅ 𝟭 _,
      (∀ K : (PodCoefficientStage.domain S s X).FullSubcategory,
        ((PodCoefficientStage.domain S s X).ι).map
            (R.pull.map (p.hom.app K)) =
          ((PodCoefficientStage.operations S s).pullComposition (𝟙 X) (𝟙 X)).inv.app
            K.obj) ∧
      ∀ (O M : (PodCoefficientStage.domain S s X).FullSubcategory),
        epsilon S s (𝟙 X) (.ofIsProper ((𝟙 X) : X ⟶ X).hom.left) R O O
            ((identityExceptional S s X R p).app O) M ≫
          (identityDirect S s X R p).hom.app
            ((PodCtfPairing.homX S s (𝟙 X) (.ofIsProper ((𝟙 X) : X ⟶ X).hom.left) R M).obj O) =
        (sixFunctorDomainHom _ _ _ R.closedY.homPermitted R.closedY.homDomain).map
          (Prod.mkHom ((identitySupport S s X R p).inv.app M).op (𝟙 O)) := by
  obtain ⟨p, hp, hproj⟩ := normalized_identity_projection S s X R _closed _tensor _natural
  refine ⟨p, hp, ?_⟩
  cases R with
  | mk pd dd sd ed CX CY tx ty =>
    dsimp only at _closed
    subst CY
    let R : Domain S s (𝟙 X) (.ofIsProper ((𝟙 X) : X ⟶ X).hom.left) :=
      ⟨pd, dd, sd, ed, CX, CX, tx, ty⟩
    intro O M
    let H := sixFunctorDomainHom _ _ _ CX.homPermitted CX.homDomain
    let r := identityDirect S s X R p
    let q := identitySupport S s X R p
    let e := identityExceptional S s X R p
    have hproj' (M T : (PodCoefficientStage.domain S s X).FullSubcategory) :
        PodHomChain.projection S s (𝟙 X) (.ofIsProper ((𝟙 X) : X ⟶ X).hom.left)
            R M T ≫
          q.hom.app ((tensorLeft CX.closed.monoidal M).obj (R.pull.obj T)) ≫
          (tensorLeft CX.closed.monoidal M).map (p.hom.app T) =
        @whiskerRight _ _ CX.closed.monoidal.toMonoidalCategoryStruct
          _ _ (q.hom.app M) T := by
      have h0 := hproj M T
      dsimp only [tensorCoordinate] at h0
      erw [Category.comp_id] at h0
      exact h0
    have h := reverse_identity_chain CX.closed CX.symmetric
      R.ordinaryAdjunction R.exceptionalAdjunction p q
      (PodHomChain.projection S s (𝟙 X) (.ofIsProper ((𝟙 X) : X ⟶ X).hom.left) R)
      hproj' M O _
      (forward S s (𝟙 X) (.ofIsProper ((𝟙 X) : X ⟶ X).hom.left) R M O)
    change (R.tensorAdjunctionY (R.support.obj M)).homEquiv _ O
        (PodHomChain.projection S s (𝟙 X) (.ofIsProper ((𝟙 X) : X ⟶ X).hom.left)
            R M _ ≫
          (R.exceptionalAdjunction.homEquiv _ O).symm
            (((R.tensorAdjunctionX M).homEquiv _ _).symm
              ((R.ordinaryAdjunction.homEquiv _ _).symm
                (forward S s (𝟙 X) (.ofIsProper ((𝟙 X) : X ⟶ X).hom.left) R M O)))) =
      forward S s (𝟙 X) (.ofIsProper ((𝟙 X) : X ⟶ X).hom.left) R M O ≫
        r.hom.app (H.obj (op M, R.exceptional.obj O)) ≫
        H.map (Prod.mkHom (𝟙 (op M)) (e.hom.app O)) ≫
        H.map (Prod.mkHom (q.hom.app M).op (𝟙 O)) at h
    rw [← reverse_chain_formula S s (𝟙 X)
      (.ofIsProper ((𝟙 X) : X ⟶ X).hom.left) R] at h
    have hf := (PodHomChain.homEquiv S s (𝟙 X)
      (.ofIsProper ((𝟙 X) : X ⟶ X).hom.left) R M O _).apply_symm_apply (𝟙 _)
    change PodHomChain.homEquiv S s (𝟙 X)
      (.ofIsProper ((𝟙 X) : X ⟶ X).hom.left) R M O _
      (forward S s (𝟙 X) (.ofIsProper ((𝟙 X) : X ⟶ X).hom.left) R M O) = 𝟙 _ at hf
    rw [hf] at h
    have hi : H.map (Prod.mkHom (q.hom.app M).op (𝟙 O)) ≫
        H.map (Prod.mkHom (q.inv.app M).op (𝟙 O)) = 𝟙 _ := by
      rw [← H.map_comp]
      change H.map (Prod.mkHom (((q.inv.app M) ≫ q.hom.app M).op) (𝟙 O ≫ 𝟙 O)) = _
      simp only [Iso.inv_hom_id_app, Category.id_comp, op_id]
      exact H.map_id _
    have hh := congrArg (fun a ↦ a ≫ H.map (Prod.mkHom (q.inv.app M).op (𝟙 O))) h
    simp only [Category.assoc, hi, Category.id_comp] at hh
    erw [Category.comp_id] at hh
    have hn := r.hom.naturality (H.map (Prod.mkHom (𝟙 (op M)) (e.hom.app O)))
    change R.direct.map (H.map (Prod.mkHom (𝟙 (op M)) (e.hom.app O))) ≫
        r.hom.app (H.obj (op M, O)) =
      r.hom.app (H.obj (op M, R.exceptional.obj O)) ≫
        H.map (Prod.mkHom (𝟙 (op M)) (e.hom.app O)) at hn
    dsimp only [epsilon]
    rw [Category.assoc]
    change forward S s (𝟙 X) (.ofIsProper ((𝟙 X) : X ⟶ X).hom.left) R M O ≫
        R.direct.map (H.map (Prod.mkHom (𝟙 (op M)) (e.hom.app O))) ≫
        r.hom.app (H.obj (op M, O)) =
      H.map (Prod.mkHom (q.inv.app M).op (𝟙 O))
    rw [hn]
    exact hh.symm

end Identity

private theorem transpose_comparison
    {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
    {L : A ⥤ B} {H : B ⥤ A} {L' : A' ⥤ B'} {H' : B' ⥤ A'}
    (adj : L ⊣ H) (adj' : L' ⊣ H') (T : A ⥤ A') (U : B ⥤ B')
    (left : L ⋙ U ≅ T ⋙ L') (right : H ⋙ T ⟶ U ⋙ H')
    (counit : ∀ K, L'.map (right.app K) ≫ adj'.counit.app (U.obj K) =
      left.inv.app (H.obj K) ≫ U.map (adj.counit.app K))
    (X : A) (K : B) (v : L.obj X ⟶ K) :
    T.map (adj.homEquiv X K v) ≫ right.app K =
      adj'.homEquiv (T.obj X) (U.obj K) (left.inv.app X ≫ U.map v) := by
  apply (adj'.homEquiv (T.obj X) (U.obj K)).symm.injective
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit, Functor.map_comp,
    Category.assoc, counit, ← Category.assoc]
  have h := left.inv.naturality (adj.homEquiv X K v)
  change L'.map (T.map (adj.homEquiv X K v)) ≫ left.inv.app (H.obj K) =
    left.inv.app X ≫ U.map (L.map (adj.homEquiv X K v)) at h
  rw [h, Category.assoc, ← Functor.map_comp]
  have hv := (adj.homEquiv X K).symm_apply_apply v
  change L.map (adj.homEquiv X K v) ≫ adj.counit.app K = v at hv
  rw [hv]

section Coefficients
variable {E' : Type u} [Field E'] [Algebra (Padic B.l) E']
  [FiniteDimensional (Padic B.l) E'] {n' : ℕ} {hn' : 1 ≤ n'}
  (S' : SixFunctorOperationDatum D B E' n' hn') (t : PodCoefficientStage)
  {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left)
  [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
  (R : Domain S s f c) (R' : Domain S' t f c)
  (TX : (PodCoefficientStage.domain S s X).FullSubcategory ⥤
    (PodCoefficientStage.domain S' t X).FullSubcategory)
  (TY : (PodCoefficientStage.domain S s Y).FullSubcategory ⥤
    (PodCoefficientStage.domain S' t Y).FullSubcategory)
  (d : Comparison S s S' t f c R R' TX TY)

/-- Every one of the five transpositions commutes with evaluation-defined coefficient
change, before pasting. The last equation is the forward-chain square in the node's
direction; the comparisons need only be defined on their stated finite-Tor domains.
Source: coefficient clause, proof steps 6--7
(blueprint: lem-sf-verdier-hom-chain-composition).
Proof: (1) expand ordinary inverse transposition as pull(v) followed by the
ordinary counit; use its preserved counit. (2) uncurry the tensor-Hom square:
the evaluation transpose defining tensorX.right makes both uncurried arrows
equal. (3) expand exceptional inverse transposition as support(v) followed by
its counit and use its normalization. (4) use the projection square of d;
invertibility of projection also gives the inverse square. (5) uncurry on Y
and use the evaluation transpose defining tensorY.right, including its support
input normalization. Paste these squares, inverting the bijections, to obtain
the last equality on every input arrow. This is the coefficient square of
lem-sf-tensor-hom-coefficient-transposes in the forward direction. In particular
it applies to finite quotients (including equal levels), integral reduction,
completed scalar extension (including identity embeddings), raw rationalization,
and common finite-field enlargement whenever their normalized comparisons are supplied. -/
theorem coefficient_transposes :
    (∀ (T : (PodCoefficientStage.domain S s Y).FullSubcategory)
      (K : (PodCoefficientStage.domain S s X).FullSubcategory)
      (v : R.pull.obj T ⟶ K),
      TY.map (R.ordinaryAdjunction.homEquiv T K v) ≫ d.ordinary.right.hom.app K =
        R'.ordinaryAdjunction.homEquiv (TY.obj T) (TX.obj K)
          (d.ordinary.left.inv.app T ≫ TX.map v)) ∧
    (∀ (M K : (PodCoefficientStage.domain S s X).FullSubcategory)
      (T : (PodCoefficientStage.domain S s X).FullSubcategory)
      (v : (tensorLeft R.closedX.closed.monoidal M).obj T ⟶ K),
      TX.map ((R.tensorAdjunctionX M).homEquiv T K v) ≫ (d.tensorX M).right.app K =
        (R'.tensorAdjunctionX (TX.obj M)).homEquiv (TX.obj T) (TX.obj K)
          ((d.tensorX M).left.inv.app T ≫ TX.map v)) ∧
    (∀ (K : (PodCoefficientStage.domain S s X).FullSubcategory)
      (N : (PodCoefficientStage.domain S s Y).FullSubcategory)
      (v : R.support.obj K ⟶ N),
      TX.map (R.exceptionalAdjunction.homEquiv K N v) ≫
          d.exceptional.right.hom.app N =
        R'.exceptionalAdjunction.homEquiv (TX.obj K) (TY.obj N)
          (d.exceptional.left.inv.app K ≫ TY.map v)) ∧
    (∀ (M : (PodCoefficientStage.domain S s X).FullSubcategory)
      (T : (PodCoefficientStage.domain S s Y).FullSubcategory),
      TY.map (PodCtfPairing.projection S s f c R M T) ≫
          d.exceptional.left.hom.app ((tensorLeft R.closedX.closed.monoidal M).obj
            (R.pull.obj T)) ≫
          R'.support.map ((d.tensorX M).left.hom.app (R.pull.obj T) ≫
            (tensorLeft R'.closedX.closed.monoidal (TX.obj M)).map
              (d.ordinary.left.hom.app T)) =
        (d.tensorY M).left.hom.app T ≫
          PodCtfPairing.projection S' t f c R' (TX.obj M) (TY.obj T)) ∧
    (∀ (M : (PodCoefficientStage.domain S s X).FullSubcategory)
      (N T : (PodCoefficientStage.domain S s Y).FullSubcategory)
      (v : (tensorLeft R.closedY.closed.monoidal (R.support.obj M)).obj T ⟶ N),
      TY.map ((R.tensorAdjunctionY (R.support.obj M)).homEquiv T N v) ≫
          (d.tensorY M).right.app N =
        (R'.tensorAdjunctionY (R'.support.obj (TX.obj M))).homEquiv (TY.obj T) (TY.obj N)
          ((d.tensorY M).left.inv.app T ≫ TY.map v)) ∧
    (∀ (M : (PodCoefficientStage.domain S s X).FullSubcategory)
      (N T : (PodCoefficientStage.domain S s Y).FullSubcategory)
      (v : T ⟶ (PodHomChain.targetFunctor S s f c R M).obj N),
      TY.map (chain S s f c R M N T v) ≫ d.source M N =
        chain S' t f c R' (TX.obj M) (TY.obj N) (TY.obj T)
          (TY.map v ≫ d.target M N)) := by
  refine ⟨?_, ?_, ?_, d.projection, ?_, ?_⟩
  · intro T K v
    exact transpose_comparison R.ordinaryAdjunction R'.ordinaryAdjunction TY TX
      d.ordinary.left d.ordinary.right.hom d.ordinary.counit T K v
  · intro M K T v
    exact transpose_comparison (R.tensorAdjunctionX M)
      (R'.tensorAdjunctionX (TX.obj M)) TX TX (d.tensorX M).left
      (d.tensorX M).right (d.tensorX M).counit T K v
  · intro K N v
    exact transpose_comparison R.exceptionalAdjunction R'.exceptionalAdjunction TX TY
      d.exceptional.left d.exceptional.right.hom d.exceptional.counit K N v
  · intro M N T v
    exact transpose_comparison (R.tensorAdjunctionY (R.support.obj M))
      (R'.tensorAdjunctionY (R'.support.obj (TX.obj M))) TY TY (d.tensorY M).left
      (d.tensorY M).right (d.tensorY M).counit T N v
  · intro M N T v
    have hs := TensorHomCoefficientTransposes.coefficient_square d M N T
      (chain S s f c R M N T v)
    apply (PodHomChain.homEquiv S' t f c R' (TX.obj M) (TY.obj N) (TY.obj T)).injective
    simpa only [chain, Equiv.apply_symm_apply] using hs.symm

end Coefficients

section Passage
variable {E' : Type u} [Field E'] [Algebra (Padic B.l) E']
  [FiniteDimensional (Padic B.l) E'] {n' : ℕ} {hn' : 1 ≤ n'}
  (S' : SixFunctorOperationDatum D B E' n' hn') (t : PodCoefficientStage)
  {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z)
  [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
  [IsSeparated g.hom.left] [LocallyOfFiniteType g.hom.left] [QuasiCompact g.hom.left]
  [IsSeparated (f ≫ g).hom.left] [LocallyOfFiniteType (f ≫ g).hom.left]
  [QuasiCompact (f ≫ g).hom.left]
  (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
  (cx : Compactification (f ≫ g).hom.left)
  (Rf : Domain S s f cf) (Rg : Domain S s g cg) (Rx : Domain S s (f ≫ g) cx)
  (Rf' : Domain S' t f cf) (Rg' : Domain S' t g cg) (Rx' : Domain S' t (f ≫ g) cx)
  (TX : (PodCoefficientStage.domain S s X).FullSubcategory ⥤
    (PodCoefficientStage.domain S' t X).FullSubcategory)
  (TZ : (PodCoefficientStage.domain S s Z).FullSubcategory ⥤
    (PodCoefficientStage.domain S' t Z).FullSubcategory)
  (d : Comparison S s S' t (f ≫ g) cx Rx Rx' TX TZ)

/-- The recalculated changed chain equals the transported successive chain, on
every input arrow and in the canonical composition coordinates. This expresses
preservation of the composition equation for the actual chains, not just the
existence of isomorphic endpoints. Specialization to the dualizing object gives
the same assertion for Verdier comparison.
Source: coefficient clause, proof steps 6--7
(blueprint: lem-sf-verdier-hom-chain-composition).
Proof: use ChainComposition for the original stage to replace its single chain
by its explicit successive chain. Apply TZ and cancel the invertible source
coordinate. The forward coefficient square of coefficient_transposes identifies
the resulting arrow with the recalculated changed chain; postcompose by the
changed source coordinate. Applying ChainComposition at the changed stage identifies
that same arrow with its successive changed chains. Units, counits, evaluations
and projection comparisons are those of d, so the individual squares give this
same equality for finite/integral change. Raw localization acts on every fraction
by its pure-tensor formula, and common-stage passage acts on an arbitrary common
representative; the field_coefficient_square theorem identifies those recalculated
chains and guarantees independence of enlarging the common finite field. -/
theorem composition_after_change
    (h : ChainComposition S s f g cf cg cx Rf Rg Rx)
    (M : (PodCoefficientStage.domain S s X).FullSubcategory)
    (N T : (PodCoefficientStage.domain S s Z).FullSubcategory)
    (v : T ⟶ (PodHomChain.targetFunctor S s (f ≫ g) cx Rx M).obj N) :
    chain S' t (f ≫ g) cx Rx' (TX.obj M) (TZ.obj N) (TZ.obj T)
        (TZ.map v ≫ d.target M N) ≫
        (sourceCoordinate S' t f g cf cg cx Rf' Rg' Rx' (TX.obj M) (TZ.obj N)).hom =
      TZ.map (chain S s g cg Rg (Rf.support.obj M) N T
          (v ≫ (targetCoordinate S s f g cf cg cx Rf Rg Rx M N).hom) ≫
          Rg.direct.map (forward S s f cf Rf M (Rg.exceptional.obj N))) ≫
        TZ.map (sourceCoordinate S s f g cf cg cx Rf Rg Rx M N).inv ≫
        d.source M N ≫
        (sourceCoordinate S' t f g cf cg cx Rf' Rg' Rx' (TX.obj M) (TZ.obj N)).hom := by
  have hs := TensorHomCoefficientTransposes.coefficient_square d M N T
    (chain S s (f ≫ g) cx Rx M N T v)
  have hs' :
      chain S' t (f ≫ g) cx Rx' (TX.obj M) (TZ.obj N) (TZ.obj T)
          (TZ.map v ≫ d.target M N) =
        TZ.map (chain S s (f ≫ g) cx Rx M N T v) ≫ d.source M N := by
    apply (PodHomChain.homEquiv S' t (f ≫ g) cx Rx'
      (TX.obj M) (TZ.obj N) (TZ.obj T)).injective
    simpa only [chain, Equiv.apply_symm_apply] using hs
  rw [hs']
  have hh := congrArg TZ.map (h M N T v)
  rw [Functor.map_comp] at hh
  rw [← hh]
  simp only [Category.assoc, Iso.map_hom_inv_id_assoc]

end Passage

end WeilConjectures.VerdierHomChainComposition
