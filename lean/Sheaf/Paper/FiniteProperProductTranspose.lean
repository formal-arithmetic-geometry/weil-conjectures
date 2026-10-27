/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q88
-/
module

public import Sheaf.Paper.FiniteProperProductMaps
public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.DerivedPullbackTensorIso
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
public import Sheaf.Paper.FiniteDirectImageComposition
public import Sheaf.Paper.IntegralFinitePullbackComposition
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.Paper.OrdinaryDerivedProductLegTransposes
import Sheaf.Paper.FiniteProperCompositorMate
import Sheaf.Paper.FiniteProductEvaluationSwap
import Sheaf.Paper.FiniteProperTransportTranspose
import Sheaf.Paper.FiniteProductNormalForm

/-! # Counit transposes of the ordinary finite proper external product

Source: Stacks Project, sites-cohomology.tex, Tag 0E48 and the preceding
projection-formula-map; Tag 0D6E. The explicit seven-step counit calculation is
lem-pur-finite-proper-product-transpose, refining the symmetry paragraph of
blueprint main-20261015, lem-sf-kunneth-coherence.proof.md.
(blueprint: lem-pur-finite-proper-product-transpose).

All operations are the recorded ordinary unbounded intrinsic finite operations.
The helpers specialize canonical constructions and name the maps displayed in the node.
The index level-1 uses the existing positive-level API, whose exponent is index+1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace WeilConjectures.FiniteProperProduct

attribute [local irreducible] adj comp mu kappa sigma realization pushModel iteratedPushModel
  tensor pull push
  sfIntrinsicModuleEquivalence sfIntrinsicDerivedEquivalence canonicalFinitePullbackTensor
  finiteIntrinsicClosed finiteIntrinsicDerivedTensor

set_option linter.style.haveILetI false


private theorem successive_transpose
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {L : C ⥤ D} {R : D ⥤ C} {L' : D ⥤ E} {R' : E ⥤ D}
    (a : L ⊣ R) (b : L' ⊣ R') {M : C} {Q : D} {N : E}
    (w : M ⟶ R.obj Q) (v : Q ⟶ R'.obj N) :
    ((a.comp b).homEquiv M N).symm (w ≫ R.map v) =
      L'.map ((a.homEquiv _ _).symm w) ≫ (b.homEquiv _ _).symm v := by
  rw [Adjunction.comp_homEquiv]
  change (b.homEquiv _ _).symm ((a.homEquiv _ _).symm (w ≫ R.map v)) = _
  rw [Adjunction.homEquiv_naturality_right_symm]
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]

private theorem conjugate_transpose
    {C D : Type*} [Category* C] [Category* D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (α : L₂ ⟶ L₁)
    {M : C} {N : D} (u : M ⟶ R₁.obj N) :
    (a₂.homEquiv M N).symm (u ≫ (conjugateEquiv a₁ a₂ α).app N) =
      α.app M ≫ (a₁.homEquiv M N).symm u := by
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [conjugateEquiv_counit, α.naturality_assoc]

private theorem compositor_transpose (P : PurityFiniteSetting.{u})
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {M : D P Z} {Q : D P Y} {N : D P X}
    (w : M ⟶ (push P g).obj Q) (v : Q ⟶ (push P f).obj N) :
    ((adj P (f ≫ g)).homEquiv _ _).symm
        (w ≫ (push P g).map v ≫ (kappa P f g).inv.app N) =
      (comp P f g).hom.app M ≫
        (((adj P g).comp (adj P f)).homEquiv _ _).symm
          (w ≫ (push P g).map v) := by
  rw [finiteProperCompositorMate]
  simpa only [Category.assoc] using
    conjugate_transpose ((adj P g).comp (adj P f)) (adj P (f ≫ g))
      (comp P f g).hom (w ≫ (push P g).map v)

private theorem swap_transpose (P : PurityFiniteSetting.{u})
    {B Y Z : Scheme.{u}} (a : Y ⟶ B) (b : Z ⟶ B)
    (sY : Y ⟶ Spec (.of P.field.k)) (sZ : Z ⟶ Spec (.of P.field.k))
    (H : D P Y) (J : D P Z) {M : D P B}
    (u : M ⟶ (push P (pullback.snd b a ≫ a)).obj (external P b a J H)) :
    ((adj P (pullback.snd a b ≫ b)).homEquiv _ _).symm
        (u ≫ swapPush P a b sY sZ H J) =
      (swapPull P a b).hom.app M ≫
        (pull P (pullbackSymmetry a b).hom).map
          (((adj P (pullback.snd b a ≫ a)).homEquiv _ _).symm u) ≫
        swapTensor P a b sY sZ H J := by
  simpa only [swapPush, swapPull, objectwiseComparison, NatIso.ofComponents_hom_app,
    Iso.trans_hom, Iso.app_hom, Category.assoc] using
      finiteProperTransportTranspose P (pullbackSymmetry a b).hom
        (pullback.snd b a ≫ a) (pullback.snd a b ≫ b) (swapStructure a b)
        (swapTensor P a b sY sZ H J) u

private theorem combine_evaluations
    {C E : Type*} [Category* C] [Category* E] (L : C ⥤ E)
    {M N : E} {Q Q' : C}
    {α : M ⟶ L.obj Q} {t : M ⟶ N} {c : L.obj Q ⟶ N}
    {a a' : Q ⟶ Q'} {b b' : L.obj Q' ⟶ N} {wanted : M ⟶ N}
    (hcomp : t = α ≫ c) (hseq : c = L.map a ≫ b)
    (ha : a = a') (hb : b = b') (hn : α ≫ L.map a' ≫ b' = wanted) :
    t = wanted := by
  rw [hcomp, hseq, ha, hb]
  exact hn

private theorem normal (P : PurityFiniteSetting.{u})
    (B Y Z : Over (Spec (.of P.field.k))) (a : Y ⟶ B) (b : Z ⟶ B)
    [IsSeparated B.hom] [LocallyOfFiniteType B.hom] [QuasiCompact B.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    [IsProper a.left] [IsProper b.left] (H : D P Y.left) (J : D P Z.left) :
    ((adj P (pullback.snd a.left b.left ≫ b.left)).homEquiv _ _).symm
        (omega P a.left b.left B.hom Z.hom H J) =
      pairEvaluation P a.left b.left B.hom Z.hom _ _ H J
        ((adj P a.left).counit.app H) ((adj P b.left).counit.app J) := by
  have legs := ordinaryDerivedProductLegTransposes P B Y Z a b H J
  have hcomp := compositor_transpose P (pullback.snd a.left b.left) b.left
    (w P a.left b.left B.hom Z.hom H J) (v P a.left b.left Z.hom H J)
  have hseq := successive_transpose (adj P b.left)
    (adj P (pullback.snd a.left b.left))
    (w P a.left b.left B.hom Z.hom H J) (v P a.left b.left Z.hom H J)
  have hn := finiteProductNormalForm P a.left b.left B.hom Z.hom _ _ H J
    ((adj P a.left).counit.app H) ((adj P b.left).counit.app J)
  exact combine_evaluations (pull P (pullback.snd a.left b.left))
    (M := (pull P (pullback.snd a.left b.left ≫ b.left)).obj
      ((tensor P B.left).obj ((push P a.left).obj H, (push P b.left).obj J)))
    (N := external P a.left b.left H J)
    (Q := (pull P b.left).obj
      ((tensor P B.left).obj ((push P a.left).obj H, (push P b.left).obj J)))
    (Q' := (tensor P Z.left).obj ((pull P b.left).obj ((push P a.left).obj H), J))
    hcomp hseq legs.2 legs.1 hn

/-- Counit transpose and swap of the finite proper external product.
Source: Stacks sites-cohomology.tex, Tag 0E48 and projection-formula-map; Tag 0D6E;
blueprint main-20261015, lem-sf-kunneth-coherence.proof.md, symmetry paragraph.
(blueprint: lem-pur-finite-proper-product-transpose).

Proof: (1) The constant-ring structural maps compose, so the recorded canonical
pullback/tensor and K-injective pushforward compositors preserve the actual ordinary
adjunctions (lem-pur-proetale-constant-ring-composition and
lem-sfb-ringed-derived-monoidal-comparisons). The transported kappa is exactly that
of lem-weil-derived-direct-image-composition, with its K-injective normalization.
(2) Exchange transposes to theta followed by the pulled-back a-counit. Projection
transposes to mu followed by epsilon tensor identity. Naturality of mu therefore
identifies the transpose of v with Lr*(epsilon_a) tensor identity.
(3) For w, counit naturality moves the pushed-forward symmetry through transposition.
The projection transpose and signed symmetry naturality cancel the two symmetries,
leaving identity tensor epsilon_b. No Koszul sign is discarded.
(4) The compositor compatibility and the composite Hom bijection identify the transpose
of omega with Lt*(the transpose of w) followed by the transpose of v. This follows
also by moving v through the b-counit by naturality.
(5) Insert (2) and (3), use tensor naturality and the canonical pullback composition
comparisons. Bifunctorial composition gives Lr*(epsilon_a) tensor Lt*(epsilon_b).
(6) For the swap, expand swapPush: Rc'(eta_s), kappa inverse, then Rc(swapTensor).
Its transpose is swapTensor followed after pullback of the original transpose:
counit naturality moves eta_s left and the adjunction triangle cancels it.
(7) Apply (5) to the reversed pair. Naturality and involutivity of signed symmetry
make its transported transpose equal to (5). Injectivity of the ordinary adjunction
Hom bijection gives the forward-map equality. Arbitrary unbounded objects are used
throughout; neither exchange nor projection is assumed invertible. -/
theorem finiteProperProductTranspose (P : PurityFiniteSetting.{u})
    (B Y Z : Over (Spec (.of P.field.k))) (a : Y ⟶ B) (b : Z ⟶ B)
    [IsSeparated B.hom] [LocallyOfFiniteType B.hom] [QuasiCompact B.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    [IsProper a.left] [IsProper b.left] (H : D P Y.left) (J : D P Z.left) :
    ((adj P (pullback.snd a.left b.left)).homEquiv _ _).symm
        (v P a.left b.left Z.hom H J) =
      (mu P (pullback.snd a.left b.left) (pullback.snd a.left b.left ≫ Z.hom)
        Z.hom _ J).hom ≫
      (tensor P (pullback a.left b.left)).map
        (Prod.mkHom
          ((theta P a.left b.left).hom.app ((push P a.left).obj H) ≫
            (pull P (pullback.fst a.left b.left)).map ((adj P a.left).counit.app H))
          (𝟙 _)) ∧
    ((adj P b.left).homEquiv _ _).symm (w P a.left b.left B.hom Z.hom H J) =
      (mu P b.left Z.hom B.hom _ _).hom ≫
        (tensor P Z.left).map (Prod.mkHom (𝟙 _) ((adj P b.left).counit.app J)) ∧
    ((adj P (pullback.snd a.left b.left ≫ b.left)).homEquiv _ _).symm
        (omega P a.left b.left B.hom Z.hom H J) =
      (mu P (pullback.snd a.left b.left ≫ b.left)
        (pullback.snd a.left b.left ≫ Z.hom) B.hom _ _).hom ≫
      (tensor P (pullback a.left b.left)).map
        (Prod.mkHom
          ((eqToIso (congrArg
            (fun f ↦ (pull P f).obj ((push P a.left).obj H))
            (pullback.condition (f := a.left) (g := b.left)).symm)).hom ≫
            (comp P (pullback.fst a.left b.left) a.left).hom.app ((push P a.left).obj H) ≫
            (pull P (pullback.fst a.left b.left)).map ((adj P a.left).counit.app H))
          ((comp P (pullback.snd a.left b.left) b.left).hom.app ((push P b.left).obj J) ≫
            (pull P (pullback.snd a.left b.left)).map ((adj P b.left).counit.app J))) ∧
    ((adj P (pullback.snd a.left b.left ≫ b.left)).homEquiv _ _).symm
        (omega P a.left b.left B.hom Z.hom H J) =
      (comp P (pullback.snd a.left b.left) b.left).hom.app
        ((tensor P B.left).obj ((push P a.left).obj H, (push P b.left).obj J)) ≫
      (((adj P b.left).comp (adj P (pullback.snd a.left b.left))).homEquiv _ _).symm
        (w P a.left b.left B.hom Z.hom H J ≫
          (push P b.left).map (v P a.left b.left Z.hom H J)) ∧
    (((adj P b.left).comp (adj P (pullback.snd a.left b.left))).homEquiv _ _).symm
        (w P a.left b.left B.hom Z.hom H J ≫
          (push P b.left).map (v P a.left b.left Z.hom H J)) =
      (pull P (pullback.snd a.left b.left)).map
        (((adj P b.left).homEquiv _ _).symm (w P a.left b.left B.hom Z.hom H J)) ≫
      ((adj P (pullback.snd a.left b.left)).homEquiv _ _).symm
        (v P a.left b.left Z.hom H J) ∧
    omega P a.left b.left B.hom Z.hom H J =
      (sigma P B.left ((push P a.left).obj H) ((push P b.left).obj J)).hom ≫
        omega P b.left a.left B.hom Y.hom J H ≫
        swapPush P a.left b.left Y.hom Z.hom H J := by
  have hlegs := ordinaryDerivedProductLegTransposes P B Y Z a b H J
  refine ⟨hlegs.1, hlegs.2, normal P B Y Z a b H J, ?_, ?_, ?_⟩
  · simpa only [omega] using compositor_transpose P (pullback.snd a.left b.left) b.left
      (w P a.left b.left B.hom Z.hom H J)
      (v P a.left b.left Z.hom H J)
  · exact successive_transpose (adj P b.left) (adj P (pullback.snd a.left b.left))
      (w P a.left b.left B.hom Z.hom H J) (v P a.left b.left Z.hom H J)
  · apply ((adj P (pullback.snd a.left b.left ≫ b.left)).homEquiv _ _).symm.injective
    have hs := swap_transpose P a.left b.left Y.hom Z.hom H J
      (omega P b.left a.left B.hom Y.hom J H)
    have hn := congrArg
      (fun k ↦ (swapPull P a.left b.left).hom.app
        ((tensor P B.left).obj ((push P b.left).obj J, (push P a.left).obj H)) ≫
        (pull P (pullbackSymmetry a.left b.left).hom).map k ≫
        swapTensor P a.left b.left Y.hom Z.hom H J)
      (normal P B Z Y b a J H)
    have hnat := (adj P (pullback.snd a.left b.left ≫ b.left)).homEquiv_naturality_left_symm
      (sigma P B.left ((push P a.left).obj H) ((push P b.left).obj J)).hom
      (omega P b.left a.left B.hom Y.hom J H ≫
        swapPush P a.left b.left Y.hom Z.hom H J)
    have hr := hnat.trans (congrArg
      (fun k ↦ (pull P (pullback.snd a.left b.left ≫ b.left)).map
        (sigma P B.left ((push P a.left).obj H) ((push P b.left).obj J)).hom ≫ k)
      (hs.trans hn))
    have he := finiteProductEvaluationSwap P a.left b.left B.hom Y.hom Z.hom _ _ H J
      ((adj P a.left).counit.app H) ((adj P b.left).counit.app J)
    exact (normal P B Y Z a b H J).trans (he.symm.trans hr.symm)


end WeilConjectures.FiniteProperProduct
