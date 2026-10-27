/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q39
-/
module

public import Sheaf.Paper.FiniteOpenProductSwap
public import Sheaf.SixFunctors.ProperOpenProjectionMate
public import Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness
public import Sheaf.Paper.FiniteDirectImageComposition
public import WeilConjectures.Compactification.RefinementCategory
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.Paper.ProductOpenTensorProjectionData
import Sheaf.Paper.ProductOpenCounitNormalization
import Sheaf.Paper.ProductOpenSupportNormalization
import Sheaf.Paper.ExactProperOpenProjectionMate

/-! # Open tensor and projection identities for a product compactification

Source: blueprint main-20261015, sec-six-functors/sk-thm-sf-kunneth-relative/
lem-sf-kunneth-coherence.proof.md, symmetry paragraph, proper reduction.
(blueprint: lem-pur-product-open-tensor-projection).

All arrows below are composites of the recorded normalized open comparisons,
ordinary derived projection mates and their canonical exact-pullback transports.
No projection arrow or open counit is inverted. The only inverses of units are
those of the fully faithful open-extension adjunctions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open SheafOfModules.OpenTensorNormalization
open WeilConjectures.FiniteOpenProduct
open AlgebraicGeometry.ProEtale

namespace WeilConjectures.ProductOpenTensorProjection

variable (A : Type (u + 1)) [CommRing A] [Finite A]

omit [Finite A] in
private theorem tensorMap_comp {Y : Scheme.{u}}
    {L M N P Q R : FiniteD A Y} (f : L ⟶ M) (g : M ⟶ N)
    (h : P ⟶ Q) (i : Q ⟶ R) :
    tensorMap A Y (f ≫ g) (h ≫ i) =
      tensorMap A Y f h ≫ tensorMap A Y g i := by
  simp only [tensorMap, Functor.map_comp, NatTrans.comp_app, Category.assoc]
  rw [← NatTrans.naturality_assoc]

omit [Finite A] in
private theorem tensorMap_id_right {Y : Scheme.{u}} {Q R : FiniteD A Y}
    (f : Q ⟶ R) (N : FiniteD A Y) :
    tensorMap A Y f (𝟙 N) = ((ProperOpenTensor A Y).map f).app N := by
  unfold tensorMap
  exact (congrArg (fun z => ((ProperOpenTensor A Y).map f).app N ≫ z)
    (((ProperOpenTensor A Y).obj R).map_id N)).trans (Category.comp_id _)

omit [Finite A] in
private theorem tensorMap_id_left {Y : Scheme.{u}} (Q : FiniteD A Y)
    {N P : FiniteD A Y} (f : N ⟶ P) :
    tensorMap A Y (𝟙 Q) f = ((ProperOpenTensor A Y).obj Q).map f := by
  unfold tensorMap
  have h := NatTrans.congr_app ((ProperOpenTensor A Y).map_id Q) N
  exact (congrArg (fun z => z ≫ ((ProperOpenTensor A Y).obj Q).map f) h).trans
    (Category.id_comp _)

private theorem gamma_natural {U Y : Scheme.{u}} (k : U ⟶ Y) [IsOpenImmersion k]
    {Q R : FiniteD A U} (f : Q ⟶ R) (N : FiniteD A Y) :
    tensorMap A Y ((finiteShriek A k).map f) (𝟙 N) ≫ gamma A k R N =
      gamma A k Q N ≫ (finiteShriek A k).map
        (tensorMap A U f (𝟙 ((pull A k).obj N))) := by
  have h := NatTrans.congr_app
    ((derivedOpenImmersionLowerShriekProjectionIso (ModuleCat.{u + 1} A) k).inv.naturality
      f) N
  dsimp at h
  rw [tensorMap_id_right A ((finiteShriek A k).map f) N,
    tensorMap_id_right A f ((pull A k).obj N)]
  dsimp only [gamma, finiteGamma, tensor, finiteShriek, pull]
  rw [← Category.assoc, h]
  simp only [Category.assoc, ← Functor.map_comp]
  apply congrArg (fun z =>
    ((derivedOpenImmersionLowerShriekProjectionIso (ModuleCat.{u + 1} A) k).inv.app Q).app N ≫
      (finiteShriek A k).map z)
  exact (((ProperOpenTensor A U).map f).naturality
    ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) k).hom.app N)).symm

private theorem delta_natural {U Y : Scheme.{u}} (k : U ⟶ Y) [IsOpenImmersion k]
    {Q R : FiniteD A U} (f : Q ⟶ R) (N : FiniteD A U) :
    tensorMap A Y ((finiteShriek A k).map f) (𝟙 (J A k N)) ≫ delta A k R N =
      delta A k Q N ≫ (finiteShriek A k).map (tensorMap A U f (𝟙 N)) := by
  dsimp only [delta]
  rw [← Category.assoc, gamma_natural, Category.assoc, ← Functor.map_comp,
    Category.assoc, ← Functor.map_comp]
  apply congrArg (fun z => gamma A k Q (J A k N) ≫ (finiteShriek A k).map z)
  rw [tensorMap_id_right A f ((pull A k).obj (J A k N)), tensorMap_id_right A f N,
    tensorMap_id_left A R (openUnit A k N).inv,
    tensorMap_id_left A Q (openUnit A k N).inv]
  exact (((ProperOpenTensor A U).map f).naturality (openUnit A k N).inv).symm

omit [Finite A] in
private theorem open_fullyFaithful {U Y : Scheme.{u}} (k : U ⟶ Y)
    [IsOpenImmersion k] : Nonempty ((finiteShriek A k).FullyFaithful) := by
  have : IsIso (openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) k).unit :=
    (openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) k).unit_isIso_of_L_fully_faithful
  have : IsIso (derivedOpenImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) k).unit :=
    Adjunction.isIso_mapDerivedCategoryAdjunction_unit _
  have : IsIso (adj A k).unit := ‹IsIso
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) k).unit›
  exact ⟨(adj A k).fullyFaithfulLOfIsIsoUnit⟩

private theorem projection_pasting
    {Xb Zb B X Z : Scheme.{u}}
    (a : Xb ⟶ B) (b : Zb ⟶ B) (j : X ⟶ Xb) (k : Z ⟶ Zb)
    [IsOpenImmersion j] [IsOpenImmersion k] [IsProper a] [QuasiCompact k]
    (M : FiniteD A X) (N : FiniteD A Z) :
    delta A k ((ProperOpenPush A (second a (k ≫ b))).obj (K A a b j k M)) N ≫
        projectionTail A a b j k M N =
      tensorMap A Zb ((Gamma A a b k).app (K A a b j k M)) (𝟙 (J A k N)) ≫
        projection A (second a b) (m A a b j k M) (J A k N) ≫
        (ProperOpenPush A (second a b)).map (w A a b j k M N) := by
  have h := exactProperOpenProjectionMate A (rightOpen a b k)
    (second a (k ≫ b)) (second a b) k (iSquare a b k) (K A a b j k M) N
  have hn := (Gamma A a b k).naturality (d A a b j k M N)
  dsimp only [Functor.comp_map] at hn
  dsimp only [projectionTail, GammaD, w]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn]
  simp only [Functor.map_comp, Category.assoc] at h
  dsimp only [delta, Gamma, iTensorSecond, J, m]
  simp only [Category.assoc]
  rw [reassoc_of% h]

variable {Xb Zb B X Z : Scheme.{u}}
variable (a : Xb ⟶ B) (b : Zb ⟶ B) (j : X ⟶ Xb) (k : Z ⟶ Zb)
  [IsOpenImmersion j] [IsOpenImmersion k] [IsProper a] [QuasiCompact k]

/-- The compactification identities and all the stated supported-open normalizations.
This predicate only abbreviates the displayed conclusions; no map is supplied as data.
Source: all conclusion clauses of the node
(blueprint: lem-pur-product-open-tensor-projection). -/
def Assertion (M : FiniteD A X) (N : FiniteD A Z) : Prop :=
  IsIso (eta A a b j k M N) ∧
  eta A a b j k M N ≫ nu A a b j k M N =
    delta A k ((pull A k).obj (L0 A a b j M)) N ∧
  w A a b j k M N =
    tensorMap A (product a b) (chi A a b j k M)
      (𝟙 ((pull A (second a b)).obj (J A k N))) ≫ e A a b j k M N ∧
  delta A k ((ProperOpenPush A (second a (k ≫ b))).obj (K A a b j k M)) N ≫
      projectionTail A a b j k M N =
    tensorMap A Zb ((Gamma A a b k).app (K A a b j k M)) (𝟙 (J A k N)) ≫
      projection A (second a b) (m A a b j k M) (J A k N) ≫
      (ProperOpenPush A (second a b)).map (w A a b j k M N) ∧
  eta A a b j k M N ≫ nu A a b j k M N ≫ Psi A a b j k M N =
    tensorMap A Zb (s A a b j k M) (𝟙 (J A k N)) ≫
      projection A (second a b) (m A a b j k M) (J A k N) ≫
      (ProperOpenPush A (second a b)).map (w A a b j k M N) ∧
  (pull A k).map (eta A a b j k M N) ≫ (restrictNu A a b j k M N).hom =
    (restrictEta A a b j k M N).hom ∧
  (pull A k).map (nu A a b j k M N) ≫ (openUnit A k (T A a b j k M N)).inv =
    (restrictNu A a b j k M N).hom ∧
  (pull A k).map (delta A k ((pull A k).obj (L0 A a b j M)) N) ≫
      (openUnit A k (T A a b j k M N)).inv = (restrictEta A a b j k M N).hom ∧
  Nonempty ((finiteShriek A k).FullyFaithful) ∧
  Nonempty (tensor A Zb ((finiteShriek A k).obj ((pull A k).obj (L0 A a b j M)))
    (J A k N) ≅ (finiteShriek A k).obj (T A a b j k M N)) ∧
  Nonempty (tensor A Zb (L0 A a b j M) (J A k N) ≅
    (finiteShriek A k).obj (T A a b j k M N)) ∧
  Nonempty (tensor A (product a b) (m A a b j k M)
    ((pull A (second a b)).obj (J A k N)) ≅
      (finiteShriek A (productOpen a b j k)).obj (D A a b j k M N)) ∧
  IsIso (e A a b j k M N) ∧
  (restrictW A a b j k M N).inv ≫
      (pull A (productOpen a b j k)).map (w A a b j k M N) =
    (openUnit A (productOpen a b j k) (D A a b j k M N)).hom ∧
  (restrictW A a b j k M N).inv ≫
      (pull A (productOpen a b j k)).map
        (tensorMap A (product a b) (chi A a b j k M)
          (𝟙 ((pull A (second a b)).obj (J A k N))) ≫ e A a b j k M N) =
    (openUnit A (productOpen a b j k) (D A a b j k M N)).hom

/-- The open k in a finite-type field diagram is quasi-compact by Noetherianity.
This is a derived geometric fact, not an additional hypothesis in the statement.
Source: Stacks 01OX and the finite-type conventions
(blueprint: lem-pur-product-open-tensor-projection). -/
instance finiteTypeOpenQuasiCompact (S : PurityFiniteSetting.{u})
    (V : Over (Spec (CommRingCat.of S.field.k))) [LocallyOfFiniteType V.hom]
    {U : Scheme.{u}} (o : U ⟶ V.left) [IsOpenImmersion o] : QuasiCompact o :=
  letI : IsLocallyNoetherian V.left := LocallyOfFiniteType.isLocallyNoetherian V.hom
  inferInstance

set_option maxRecDepth 2048 in
/-- The actual four identities, with their supported-open and identity-restriction clauses.
The morphisms f and g are j followed by a and k followed by b; thus the displayed open
and proper factors are precisely arbitrary chosen compactifications. All objects and
morphisms are over the fixed field. Quasi-compactness of k is deduced from finite type,
not supplied as a further hypothesis. Tensor is ordinary unbounded derived tensor.
Source: blueprint main-20261015, lem-sf-kunneth-coherence.proof.md, symmetry paragraph;
the explicit five-step proof of lem-pur-product-open-tensor-projection
(blueprint: lem-pur-product-open-tensor-projection).

Proof: (1) Apply lem-sf-open-tensor-normalization to k. Both supported tensors are
in the fully faithful image of k_!. The restricted counit is the inverse open unit
by the adjunction triangle identity. The two signed symmetries in nu cancel.
Consequently eta, nu and delta restrict to identities, nu eta equals delta, and
eta is invertible, detected on that fully faithful image.
(2) Apply the same normalization to j_q and i, and compose extensions by
lem-cbc-extension-zero-composition. The d and delta_i factors identify the source
of w with u_!D. Restriction gives 1_D. The comparison e of
lem-pur-finite-open-product-swap is an isomorphism with that same normalization.
Restricting chi gives beta inverse, then restricting to P gives the identity;
this uses the counit triangle and the unit normalization of beta. Both w and
e(chi tensor 1) have supported source and target and restrict to 1_D, so full
faithfulness of u_! makes them equal. No inverse of chi is used.
(3) The second projections t and v are proper base changes of a, by
lem-weil-pbc-proper-base-change. Apply lem-sf-proper-open-tensor-compatibility
to (i,v,k,t) and (K,J), identifying P_k J with N. This gives its displayed
Gamma/projection equation, with the same counit-defined maps on unbounded objects.
(4) Postcompose by R_t i_!(d). Naturality of Gamma moves d through Gamma;
the definition of w then gives the third identity of this node.
(5) Precompose by k_!(B_0) tensor 1. Naturality of delta identifies the result
with Psi delta. Substitute delta=nu eta from Step 1 and s=Gamma k_!(B_0) to
obtain the fourth identity. No constructibility, Tor amplitude, or inversion
of projection maps has been used. Boundedness and the retained etale witnesses
are exactly the stated input domain and impose no additional step in this proof. -/
theorem productOpenTensorProjection (S : PurityFiniteSetting.{u})
    (Xb Zb B X Z : Over (Spec (CommRingCat.of S.field.k)))
    [IsSeparated Xb.hom] [LocallyOfFiniteType Xb.hom] [QuasiCompact Xb.hom]
    [IsSeparated Zb.hom] [LocallyOfFiniteType Zb.hom] [QuasiCompact Zb.hom]
    [IsSeparated B.hom] [LocallyOfFiniteType B.hom] [QuasiCompact B.hom]
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (a : Xb ⟶ B) (b : Zb ⟶ B) [IsProper a.left] [IsProper b.left]
    (j : X ⟶ Xb) (k : Z ⟶ Zb) [IsOpenImmersion j.left] [IsOpenImmersion k.left]
    (M : DerivedCategory.Plus (Sheaf (ProEt.topology X.left) (ModuleCat.{u + 1} S.Coefficient)))
    (N : DerivedCategory.Plus (Sheaf (ProEt.topology Z.left) (ModuleCat.{u + 1} S.Coefficient)))
    (_eM : FixedEtaleOriginWitness X.left S.Coefficient M)
    (_eN : FixedEtaleOriginWitness Z.left S.Coefficient N) :
    @Assertion S.Coefficient _ _ Xb.left Zb.left B.left X.left Z.left
      a.left b.left j.left k.left _ _ _
      (finiteTypeOpenQuasiCompact S Zb k.left) M.obj N.obj := by
  let A := S.Coefficient
  have hc := productOpenCounitNormalization A k.left
    (L0 A a.left b.left j.left M.obj) N.obj
  rcases hc with ⟨hη, hην, hrη, hrν, hsη, hsν⟩
  change eta A a.left b.left j.left k.left M.obj N.obj ≫
      nu A a.left b.left j.left k.left M.obj N.obj =
    delta A k.left ((pull A k.left).obj (L0 A a.left b.left j.left M.obj)) N.obj at hην
  change (pull A k.left).map (eta A a.left b.left j.left k.left M.obj N.obj) ≫
      (restrictNu A a.left b.left j.left k.left M.obj N.obj).hom =
    (restrictEta A a.left b.left j.left k.left M.obj N.obj).hom at hrη
  change (pull A k.left).map (nu A a.left b.left j.left k.left M.obj N.obj) ≫
      (openUnit A k.left (T A a.left b.left j.left k.left M.obj N.obj)).inv =
    (restrictNu A a.left b.left j.left k.left M.obj N.obj).hom at hrν
  have hw := productOpenSupportNormalization A a.left b.left j.left k.left M.obj N.obj
  rcases hw with ⟨hw, hsw, hrw⟩
  have he := (finiteOpenProductSwap S Xb Zb B X Z a b j k M.obj N.obj).1
  change IsIso (e A a.left b.left j.left k.left M.obj N.obj) at he
  change IsIso (eta A a.left b.left j.left k.left M.obj N.obj) at hη
  have hp := projection_pasting A a.left b.left j.left k.left M.obj N.obj
  have hlast :
      eta A a.left b.left j.left k.left M.obj N.obj ≫
        nu A a.left b.left j.left k.left M.obj N.obj ≫
          Psi A a.left b.left j.left k.left M.obj N.obj =
      tensorMap A Zb.left (s A a.left b.left j.left k.left M.obj) (𝟙 (J A k.left N.obj)) ≫
        projection A (second a.left b.left)
          (m A a.left b.left j.left k.left M.obj) (J A k.left N.obj) ≫
        (ProperOpenPush A (second a.left b.left)).map
          (w A a.left b.left j.left k.left M.obj N.obj) := by
    rw [← Category.assoc, hην]
    dsimp only [Psi]
    rw [← Category.assoc, ← delta_natural, Category.assoc, hp]
    dsimp only [s]
    rw [← Category.assoc, ← tensorMap_comp]
    simp only [Category.id_comp]
  have hrδ :
      (pull A k.left).map
          (delta A k.left ((pull A k.left).obj (L0 A a.left b.left j.left M.obj)) N.obj) ≫
        (openUnit A k.left (T A a.left b.left j.left k.left M.obj N.obj)).inv =
      (restrictEta A a.left b.left j.left k.left M.obj N.obj).hom := by
    rw [← hην, Functor.map_comp, Category.assoc, hrν, hrη]
  have hrwe :
      (restrictW A a.left b.left j.left k.left M.obj N.obj).inv ≫
        (pull A (productOpen a.left b.left j.left k.left)).map
          (tensorMap A (product a.left b.left) (chi A a.left b.left j.left k.left M.obj)
            (𝟙 ((pull A (second a.left b.left)).obj (J A k.left N.obj))) ≫
              e A a.left b.left j.left k.left M.obj N.obj) =
      (openUnit A (productOpen a.left b.left j.left k.left)
        (D A a.left b.left j.left k.left M.obj N.obj)).hom := by
    rw [← hw]
    exact hrw
  unfold Assertion
  refine And.intro hη ?_
  refine And.intro hην ?_
  refine And.intro hw ?_
  refine And.intro hp ?_
  refine And.intro hlast ?_
  refine And.intro hrη ?_
  refine And.intro hrν ?_
  refine And.intro hrδ ?_
  constructor
  · exact open_fullyFaithful A k.left
  refine And.intro hsη ?_
  refine And.intro hsν ?_
  exact ⟨hsw, he, hrw, hrwe⟩

end WeilConjectures.ProductOpenTensorProjection
