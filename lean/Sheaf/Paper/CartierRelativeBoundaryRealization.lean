/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.Paper.PurityDivisorClass
public import Sheaf.AlgebraicGeometry.CartierReductionData
public import Sheaf.AlgebraicGeometry.RelativeTorsorCohomology
public import Sheaf.AlgebraicGeometry.PurityRelativeCone
public import Sheaf.AlgebraicGeometry.RawModuleScalarDerivedPullbackIso
public import Sheaf.AlgebraicGeometry.RelativeEtaleCohomology
public import Sheaf.AlgebraicGeometry.FiniteEtaleTateTwist
public import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Kummer
public import Sheaf.Paper.SupportedCupFunctoriality
public import Sheaf.AlgebraicGeometry.ClosedSupportHom
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.AlgebraicGeometry.Sites.GmPicard
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.AlgebraicGeometry.EffectiveCartier
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
import Sheaf.AlgebraicGeometry.ResidueFiniteRootMapIso
import all Sheaf.AlgebraicGeometry.CartierReductionSiteComparison
import all Sheaf.AlgebraicGeometry.PurityRelativeCone
import all Sheaf.AlgebraicGeometry.RelativeTorsorCohomology
import all WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
import WeilConjectures.Algebra.Homology.KernelShiftedMappingCone

/-!
# Signed relative Cartier boundaries and their module realization

Source: blueprint main-20261015, Cartier-map proof, paragraphs 1--3, and
localized top Chern class, Step 4 (L1)
(blueprint: lem-pur-cartier-relative-boundary-realization).

The integral supported Ext model retains the entire relative class. In particular,
`cartierPoleBoundary` specifies the frame torsor of the dual ideal and its actual
complementary section. Composition with the Kummer extension is the relative boundary.
It is not a class specified only by its image after forgetting support.

The cone comparison is stated in the unbounded derived category of abelian groups.
Its source is the underlying complex of the module-resolution section cone: forgetting
module structures commutes with sections, the finite sums in the cone, and shifts.
Every comparison lift is augmented by the identity, and its localized cone map is fixed.
-/

@[expose] public noncomputable section

set_option Elab.async false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Etale
open HomologicalComplex

namespace WeilConjectures.PurityFiniteSetting

-- Reuse the owner's named sheafification and small-Ext proofs when elaborating the
-- same coefficient categories, instead of regenerating large instance proofs.
attribute [instance] cartierEtaleAbSheafify cartierEtaleModuleSheafify
  cartierEtaleAbHasExt cartierEtaleModuleHasExt

/-- The relative Kummer boundary of the specified Cartier pair, in the supported
integral Ext model. The first factor is the relative frame-torsor class, not merely
its ordinary Picard image. Source: Cartier-map proof, paragraphs 1--3
(blueprint: lem-pur-cartier-relative-boundary-realization). -/
def cartierRelativeBoundary (P : PurityFiniteSetting.{u}) {D T : Scheme.{u}}
    (a : T ⟶ Spec (.of P.field.k)) (i : D ⟶ T) [IsClosedImmersion i]
    (hI : i.ker.IsInvertible) :
    Ext.{u + 1} ((Etale.lowerStar AddCommGrpCat.{u + 1} i).obj
      (supportedIntegralConstant D)) (T.rootsOfUnitySheaf P.diagonalExponent) 2 :=
  (cartierPoleBoundary i hI).comp
    (T.kummerSequence_shortExact P.diagonalExponent (P.diagonalExponent_isUnit a)).extClass
    (rfl : 1 + 1 = 2)

/-- The canonical finite-root module chart of the relative class. Its definition is
the existing uniquely normalized scalar adjunct, over the lifted ring Z/(ell^n).
Source: Cartier-map proof, first three paragraphs
(blueprint: lem-pur-cartier-relative-boundary-realization). -/
def cartierRelativeModuleBoundary (P : PurityFiniteSetting.{u}) {D T : Scheme.{u}}
    (a : T ⟶ Spec (.of P.field.k)) (i : D ⟶ T) [IsClosedImmersion i]
    (hI : i.ker.IsInvertible) :=
  letI : Finite (ProEtale.cartierResidueRing.{u} P.coefficients.l P.level) :=
    ProEtale.cartierResidue_finite P.coefficients.l P.coefficients.prime.out P.level
  ProEtale.cartierReducedEtale
    (ProEtale.cartierResidueRing.{u} P.coefficients.l P.level)
    P.diagonalExponent (pow_pos P.coefficients.prime.out.pos P.level)
    (ProEtale.cartierResidue_cast P.coefficients.l P.level) i hI
    (P.diagonalExponent_isUnit a)

/-- Extend the same relative boundary to A by the prescribed root projection chart.
This uses the existing canonical scalar adjunct; no flatness of A over Z/(ell^n)
is imposed. Source: Cartier-map proof, coefficient paragraph; def-pur-frame-class
(blueprint: lem-pur-cartier-relative-boundary-realization). -/
def cartierRelativeCoefficientBoundary (P : PurityFiniteSetting.{u}) {D T : Scheme.{u}}
    (a : T ⟶ Spec (.of P.field.k)) (i : D ⟶ T) [IsClosedImmersion i]
    (hI : i.ker.IsInvertible) :
    Ext.{u + 1}
      ((Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj (P.constantEtale D))
      (P.frameTwistEtale T 1) 2 :=
  ProEtale.cartierReducedEtale P.Coefficient P.diagonalExponent
    (pow_pos P.coefficients.prime.out.pos P.level) P.diagonalExponent_annihilates i hI
    (P.diagonalExponent_isUnit a)

/-- Forget scalars term by term on a nonnegative resolution, before taking sections.
Source: Cartier-map proof, injective-resolution computation
(blueprint: lem-pur-cartier-relative-boundary-realization). -/
abbrev cartierUnderlyingResolution (R : Type (u + 1)) [CommRing R] (T : Scheme.{u})
    {M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R)} (I : InjectiveResolution M) :=
  ((RawModuleScalarComparison.forget R T).mapHomologicalComplex (.up ℕ)).obj I.cocomplex

/-- Evaluated comparison of nonnegative resolutions, extended by zero.
Source: Cartier-map proof, comparison on the two section complexes
(blueprint: lem-pur-cartier-relative-boundary-realization). -/
def cartierSectionComparison (T : Scheme.{u}) (V : T.Etale)
    {I J : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ}
    (q : I ⟶ J) : relativeSections V I ⟶ relativeSections V J :=
  extendMap (((etaleSectionFunctor V).mapHomologicalComplex (.up ℕ)).map q)
    ComplexShape.embeddingUpNat

/-- Coordinate normalization of the supported kernel inclusion. In signed coordinates
these equations say exactly k maps to (k,0); the second cone summand is negated.
Source: Cartier-map proof, signed relative cone computation
(blueprint: lem-pur-cartier-relative-boundary-realization). -/
def CartierKernelNormalization {A B : CochainComplex AddCommGrpCat.{u + 1} ℤ}
    (r : A ⟶ B) (κ : kernel r ⟶ (CochainComplex.mappingCone r)⟦(-1 : ℤ)⟧) : Prop :=
  ∀ p : ℤ,
    κ.f p ≫ ((CochainComplex.mappingCone r).shiftFunctorObjXIso
      (-1) p (p - 1) (by omega)).hom ≫
        homotopyCofiber.sndX r (p - 1) = 0 ∧
    κ.f p ≫ ((CochainComplex.mappingCone r).shiftFunctorObjXIso
      (-1) p (p - 1) (by omega)).hom ≫
        homotopyCofiber.fstX r (p - 1) p (by change p - 1 + 1 = p; omega) =
      (kernel.ι r).f p

/-- The full derived cone comparison with its actual projection, localization boundary,
and supported-kernel square. The isomorphism is fixed by the diagonal resolution map.
Source: Cartier-map proof, paragraphs 2--3; signed normalization of
lem-pur-divisor-relative-cone
(blueprint: lem-pur-cartier-relative-boundary-realization). -/
def CartierRelativeConeComparison (T : Scheme.{u}) (W : T.Opens)
    (I J : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ)
    (q : I ⟶ J) : Prop :=
  ∃ iso : DerivedCategory.Q.obj (relativeSectionComplex T (Scheme.Etale.mk W.ι) I) ≅
      DerivedCategory.Q.obj (relativeSectionComplex T (Scheme.Etale.mk W.ι) J),
    iso.hom = DerivedCategory.Q.map (relativeSectionMap T (Scheme.Etale.mk W.ι) q) ∧
    relativeSectionMap T (Scheme.Etale.mk W.ι) q ≫
      relativeForgetComplex T (Scheme.Etale.mk W.ι) J =
        relativeForgetComplex T (Scheme.Etale.mk W.ι) I ≫
          cartierSectionComparison T (Scheme.Etale.mk (𝟙 T)) q ∧
    (shiftFunctor _ (-1 : ℤ)).map
        (cartierSectionComparison T (Scheme.Etale.mk W.ι) q) ≫
          RelativeCone.boundary (relativeSectionRestriction T (Scheme.Etale.mk W.ι) J) =
      RelativeCone.boundary (relativeSectionRestriction T (Scheme.Etale.mk W.ι) I) ≫
        relativeSectionMap T (Scheme.Etale.mk W.ι) q ∧
    ∃ (kernelI : kernel (relativeSectionRestriction T (Scheme.Etale.mk W.ι) I) ⟶
        relativeSectionComplex T (Scheme.Etale.mk W.ι) I)
      (kernelJ : kernel (relativeSectionRestriction T (Scheme.Etale.mk W.ι) J) ⟶
        relativeSectionComplex T (Scheme.Etale.mk W.ι) J),
      CartierKernelNormalization
        (relativeSectionRestriction T (Scheme.Etale.mk W.ι) I) kernelI ∧
      CartierKernelNormalization
        (relativeSectionRestriction T (Scheme.Etale.mk W.ι) J) kernelJ ∧
      QuasiIso kernelI ∧ QuasiIso kernelJ ∧
      ∃ kernelMap : kernel (relativeSectionRestriction T (Scheme.Etale.mk W.ι) I) ⟶
          kernel (relativeSectionRestriction T (Scheme.Etale.mk W.ι) J),
        kernelMap ≫ kernel.ι (relativeSectionRestriction T (Scheme.Etale.mk W.ι) J) =
          kernel.ι (relativeSectionRestriction T (Scheme.Etale.mk W.ι) I) ≫
            cartierSectionComparison T (Scheme.Etale.mk (𝟙 T)) q ∧
        kernelI ≫ relativeSectionMap T (Scheme.Etale.mk W.ι) q = kernelMap ≫ kernelJ

attribute [local irreducible] Scheme.finiteEtaleTateLine ProEtale.cartierReducedEtale
  Ext.homEquiv functorialCupCompare Coefficient coefficientCommRing cartierPoleBoundary
  ordinaryFiniteRootMap supportedIntegralGenerator

private theorem cartierModuleRestrictionSurjective
    (R : Type (u + 1)) [CommRing R] (T : Scheme.{u})
    (I : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R)) [Injective I]
    {U V : T.Etale} (m : U ⟶ V) [Mono m] :
    Function.Surjective (I.obj.map m.op) := by
  have : Injective I.obj :=
    (sheafificationAdjunction T.smallEtaleTopology (ModuleCat.{u + 1} R)).map_injective
      I inferInstance
  let P (W : T.Etale) := uliftYoneda.{u + 1}.obj W ⋙ ModuleCat.free R
  let a : P U ⟶ P V :=
    Functor.whiskerRight (uliftYoneda.{u + 1}.map m) (ModuleCat.free R)
  have ha (W : T.Etaleᵒᵖ) : Mono (a.app W) := by
    apply (ModuleCat.mono_iff_injective _).2
    change Function.Injective (Finsupp.mapDomain _)
    apply Finsupp.mapDomain_injective
    intro f g h
    apply ULift.ext
    exact (cancel_mono m).1 (congrArg ULift.down h)
  have : Mono a := NatTrans.mono_of_mono_app a
  intro x
  let b : P U ⟶ I.obj :=
    { app W := ModuleCat.freeDesc (↾fun (f : ULift.{u + 1} (W.unop ⟶ U)) ↦
        I.obj.map f.down.op x)
      naturality W W' f := by
        apply ModuleCat.free_hom_ext
        intro g
        change ModuleCat.freeDesc _
          ((ModuleCat.free R).map ((uliftYoneda.{u + 1}.obj U).map f)
            (ModuleCat.freeMk g)) = _
        rw [ModuleCat.free_map_apply, ModuleCat.freeDesc_apply, ModuleCat.comp_apply,
          ModuleCat.freeDesc_apply]
        change I.obj.map (f.unop ≫ g.down).op x =
          I.obj.map f (I.obj.map g.down.op x)
        rw [op_comp, I.obj.map_comp]
        rfl }
  let g := Injective.factorThru b a
  have hg : a ≫ g = b := Injective.comp_factorThru b a
  refine ⟨g.app (op V) (ModuleCat.freeMk (ULift.up (𝟙 V))), ?_⟩
  have hn := NatTrans.naturality_apply g m.op (ModuleCat.freeMk (ULift.up (𝟙 V)))
  have he := congrArg (fun f ↦ f.app (op U) (ModuleCat.freeMk (ULift.up (𝟙 U)))) hg
  have he' : g.app (op U) (ModuleCat.freeMk (ULift.up m)) = x := by
    change g.app (op U)
      ((ModuleCat.free R).map ((uliftYoneda.{u + 1}.map m).app (op U))
        (ModuleCat.freeMk (ULift.up (𝟙 U)))) =
      ModuleCat.freeDesc (↾fun (f : ULift.{u + 1} (U ⟶ U)) ↦ I.obj.map f.down.op x)
        (ModuleCat.freeMk (ULift.up (𝟙 U))) at he
    rw [ModuleCat.free_map_apply, ModuleCat.freeDesc_apply] at he
    simpa using he
  have hn' : I.obj.map m.op
      (g.app (op V) (ModuleCat.freeMk (ULift.up (𝟙 V)))) =
        g.app (op U) (ModuleCat.freeMk (ULift.up m)) := by
    simpa [P, ModuleCat.free_map_apply] using hn.symm
  exact hn'.trans he'

private theorem cartierEvaluationQuasiIso
    (R : Type (u + 1)) [CommRing R] (T : Scheme.{u})
    {M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R)}
    (I : InjectiveResolution M)
    (J : InjectiveResolution ((RawModuleScalarComparison.forget R T).obj M))
    (q : cartierUnderlyingResolution R T I ⟶ J.cocomplex) [QuasiIso q]
    (V : T.Etale) : QuasiIso (cartierSectionComparison T V q) := by
  have hI (n : ℕ) : (etaleSectionFunctor V).rightAcyclic
      ((cartierUnderlyingResolution R T I).X n) := by
    intro k
    exact moduleAbelianForget_injective_evaluation_acyclic R T (I.cocomplex.X n) V k
  have hJ (n : ℕ) : (etaleSectionFunctor V).rightAcyclic (J.cocomplex.X n) :=
    Functor.rightAcyclic_of_injective _
  have := (etaleSectionFunctor V).quasiIso_map_of_rightAcyclic_nat q hI hJ
  exact (quasiIso_extendMap_iff _ ComplexShape.embeddingUpNat).2 this

private theorem cartierRelativeQuasiIso (T : Scheme.{u}) (V : T.Etale)
    {I J : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ}
    (q : I ⟶ J) [QuasiIso (cartierSectionComparison T (Scheme.Etale.mk (𝟙 T)) q)]
    [QuasiIso (cartierSectionComparison T V q)] : QuasiIso (relativeSectionMap T V q) := by
  let r := relativeSectionRestriction T V I
  let r' := relativeSectionRestriction T V J
  let a := cartierSectionComparison T (Scheme.Etale.mk (𝟙 T)) q
  let b := cartierSectionComparison T V q
  let h := relativeSectionMap_square T V q
  let τ := DerivedCategory.Q.mapTriangle.map
    (CochainComplex.mappingCone.triangleMap r r' a b h.symm)
  have h₁ : IsIso τ.hom₁ := by
    change IsIso (DerivedCategory.Q.map a)
    infer_instance
  have h₂ : IsIso τ.hom₂ := by
    change IsIso (DerivedCategory.Q.map b)
    infer_instance
  have hi : IsIso τ.hom₃ := CategoryTheory.Pretriangulated.isIso₃_of_isIso₁₂ τ
    (DerivedCategory.mappingCone_triangle_distinguished r)
    (DerivedCategory.mappingCone_triangle_distinguished r') h₁ h₂
  have hq : QuasiIso (CochainComplex.mappingCone.map r r' a b h.symm) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).1 hi
  have he : homotopyCofiber.mapArrowHom r r'
      (fun j ↦ ⟨j - 1, sub_add_cancel j 1⟩) (Arrow.homMk a b h) =
        CochainComplex.mappingCone.map r r' a b h.symm := by
    ext n : 1
    apply homotopyCofiber.ext_from_X r (n + 1) n rfl
    · change _ = (CochainComplex.mappingCone.inl r).v (n + 1) n (by omega) ≫ _
      simp [homotopyCofiber.mapArrowHom, CochainComplex.mappingCone.map,
        homotopyCofiber.inrCompHomotopy_hom]
      rfl
    · change _ = (CochainComplex.mappingCone.inr r).f n ≫ _
      simp [homotopyCofiber.mapArrowHom, CochainComplex.mappingCone.map]
      rfl
  change QuasiIso ((shiftFunctor _ (-1 : ℤ)).map
    (homotopyCofiber.mapArrowHom r r'
      (fun j ↦ ⟨j - 1, sub_add_cancel j 1⟩) (Arrow.homMk a b h)))
  rw [he]
  infer_instance

private theorem cartierRestrictionEpi (T : Scheme.{u}) (V : T.Etale)
    (K : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ)
    (hs : ∀ n, Function.Surjective ((K.X n).obj.map
      ((MorphismProperty.Over.mkIdTerminal @Etale T).from V).op)) (p : ℤ) :
    Epi ((relativeSectionRestriction T V K).f p) := by
  cases p with
  | ofNat n =>
    have : Epi ((K.X n).obj.map
        ((MorphismProperty.Over.mkIdTerminal @Etale T).from V).op) :=
      (AddCommGrpCat.epi_iff_surjective _).2 (hs n)
    unfold relativeSectionRestriction
    rw [extendMap_f _ ComplexShape.embeddingUpNat (show
      ComplexShape.embeddingUpNat.f n = Int.ofNat n from rfl)]
    change Epi (_ ≫ (K.X n).obj.map _ ≫ _)
    infer_instance
  | negSucc n =>
    exact (isZero_extend_X
      (((etaleSectionFunctor V).mapHomologicalComplex (.up ℕ)).obj K)
      ComplexShape.embeddingUpNat (Int.negSucc n)
      (fun m hm ↦ by change (m : ℤ) = Int.negSucc n at hm; omega)).epi _

private theorem cartierConeComparison (T : Scheme.{u}) (W : T.Opens)
    {I J : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ}
    (q : I ⟶ J) [QuasiIso (relativeSectionMap T (Scheme.Etale.mk W.ι) q)]
    (hI : ∀ p, Epi ((relativeSectionRestriction T (Scheme.Etale.mk W.ι) I).f p))
    (hJ : ∀ p, Epi ((relativeSectionRestriction T (Scheme.Etale.mk W.ι) J).f p)) :
    CartierRelativeConeComparison T W I J q := by
  let V := Scheme.Etale.mk W.ι
  let r := relativeSectionRestriction T V I
  let r' := relativeSectionRestriction T V J
  let a := cartierSectionComparison T (Scheme.Etale.mk (𝟙 T)) q
  let b := cartierSectionComparison T V q
  let h := relativeSectionMap_square T V q
  obtain ⟨κ, hκ, hκq, _⟩ :=
    CochainComplex.exists_kernel_to_shifted_mappingCone_of_degreewise_epi r hI
  obtain ⟨κ', hκ', hκq', _⟩ :=
    CochainComplex.exists_kernel_to_shifted_mappingCone_of_degreewise_epi r' hJ
  let k := kernel.map r r' a b h.symm
  have hk : k ≫ kernel.ι r' = kernel.ι r ≫ a := by simp [k]
  have hs : κ ≫ relativeSectionMap T V q = k ≫ κ' := by
    change κ ≫ relativeFiberMap r r' a b h = k ≫ κ'
    ext p : 1
    apply (cancel_mono ((CochainComplex.mappingCone r').shiftFunctorObjXIso
      (-1) p (p - 1) (by omega)).hom).1
    apply homotopyCofiber.ext_to_X r' (p - 1) p (by change p - 1 + 1 = p; omega)
    · simp only [comp_f, Category.assoc, (hκ' p).2,
        RelativeCone.fiberMap_fst, reassoc_of% ((hκ p).2)]
      exact (congr_hom hk p).symm
    · simp only [comp_f, Category.assoc, (hκ' p).1,
        RelativeCone.fiberMap_snd, reassoc_of% ((hκ p).1), comp_zero, zero_comp]
  have sq := RelativeCone.triangleSquare r r' a b h
  refine ⟨asIso (DerivedCategory.Q.map (relativeSectionMap T V q)), rfl,
    sq.1, sq.2, κ, κ', hκ, hκ', hκq, hκq', k, hk, hs⟩

/-- The signed relative boundary has its canonical module realization and is the
general Cartier divisor class after the prescribed coefficient and site maps.

Source: blueprint main-20261015, Cartier-map proof, paragraphs 1--3; localized top
Chern class Step 4 (L1)
(blueprint: lem-pur-cartier-relative-boundary-realization).

Proof, following all five DAG steps:
1. The dual ideal has local dual basis e_a, and its canonical section is f_a e_a.
   Changing f_a to u f_a changes e_a to u inverse e_a, so this is one global
   section, a frame on the whole complement. The frame torsor and this section
   are exactly CartierPoleBoundarySpec, the extension model of the canonical
   relative torsor class (lem-amb-relative-torsor-cohomology). Compose with the
   Kummer extension (lem-amb-kummer-any-base). The exponent ell^n is invertible
   and kills A for every positive level, including ramified coefficients.
2. Lift the underlying module resolution to an abelian injective resolution,
   augmented by the identity: extend in degree zero, then along each differential
   image. The lift is a quasi-isomorphism. The three maps on terminal sections,
   open sections, and their kernel are quasi-isomorphisms by
   lem-pur-module-restriction-kernel-comparison. This does not assert that a
   forgotten injective module sheaf is an injective abelian sheaf.
3. In coordinates (a,b)=(x,-y) the cone differential is (da,res(a)-db).
   The diagonal lift respects the kernel map (k,0), projection to a, and boundary
   (0,-b). Both restriction maps are degreewise surjective. Apply
   lem-weil-degreewise-epi-kernel-cocone-qis to both kernels and cancel their
   quasi-isomorphisms to obtain the full derived cone isomorphism. Comparison
   independence follows from augmented-lift homotopy and the kernel square.
4. Apply lem-amb-closed-support-hom in degree two. Its normalized identification
   is evaluation at the constant generator one, by
   lem-asd-supported-kummer-support-hom-naturality. Thus the unique module
   adjunct has underlying relative class exactly beta, with its specified sign.
   The root map for R=Z/(ell^n) is the canonical identity-coefficient root chart.
5. The general divisor family of lem-pur-divisor-class starts with the identical
   global torsor and complementary section. Hence its relative boundary is beta.
   Extend by the root generator z maps to z tensor one, and apply the canonical
   etale/pro-etale comparison; this is exactly sigma rho of def-pur-frame-class.
   The resulting equality is on full supported classes, before forgetting support.
   All constructions apply to arbitrary Cartier pairs; no smoothness is used. -/
theorem cartier_relative_boundary_realization (P : PurityFiniteSetting.{u})
    {D T : Scheme.{u}} (a : T ⟶ Spec (.of P.field.k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    (i : D ⟶ T) [IsClosedImmersion i] (hI : i.ker.IsInvertible) :
    (∀ (I : InjectiveResolution
        (Scheme.finiteEtaleTateLine T P.diagonalExponent
          (ProEtale.cartierResidueRing.{u} P.coefficients.l P.level)
          (ProEtale.cartierResidue_cast P.coefficients.l P.level)))
      (J : InjectiveResolution
        ((RawModuleScalarComparison.forget
          (ProEtale.cartierResidueRing.{u} P.coefficients.l P.level) T).obj
          (Scheme.finiteEtaleTateLine T P.diagonalExponent
            (ProEtale.cartierResidueRing.{u} P.coefficients.l P.level)
            (ProEtale.cartierResidue_cast P.coefficients.l P.level)))),
      ∃ q : cartierUnderlyingResolution _ T I ⟶ J.cocomplex,
        (RawModuleScalarComparison.forget _ T).map (I.ι.f 0) ≫ q.f 0 = J.ι.f 0 ∧
        CartierRelativeConeComparison T i.openComplement
          (cartierUnderlyingResolution _ T I) J.cocomplex q ∧
        ∀ q' : cartierUnderlyingResolution _ T I ⟶ J.cocomplex,
          (RawModuleScalarComparison.forget _ T).map (I.ι.f 0) ≫ q'.f 0 = J.ι.f 0 →
          DerivedCategory.Q.map (relativeSectionMap T (Scheme.Etale.mk i.openComplement.ι) q') =
            DerivedCategory.Q.map
              (relativeSectionMap T (Scheme.Etale.mk i.openComplement.ι) q)) ∧
    IsIso (ordinaryFiniteRootMap
      (ProEtale.cartierResidueRing.{u} P.coefficients.l P.level) P.diagonalExponent
      (ProEtale.cartierResidue_cast P.coefficients.l P.level) T) ∧
    SupportedKummerBoundary
      (ProEtale.cartierResidueRing.{u} P.coefficients.l P.level) P.diagonalExponent
      (ProEtale.cartierResidue_cast P.coefficients.l P.level) i hI
      (P.diagonalExponent_isUnit a) (P.cartierRelativeModuleBoundary a i hI) ∧
    ((Ext.mk₀ (supportedIntegralGenerator
        (ProEtale.cartierResidueRing.{u} P.coefficients.l P.level) i)).comp
      ((P.cartierRelativeModuleBoundary a i hI).mapExactFunctor
        (RawModuleScalarComparison.forget
          (ProEtale.cartierResidueRing.{u} P.coefficients.l P.level) T)) (zero_add 2) =
      (P.cartierRelativeBoundary a i hI).comp
        (Ext.mk₀ (ordinaryFiniteRootMap
          (ProEtale.cartierResidueRing.{u} P.coefficients.l P.level) P.diagonalExponent
          (ProEtale.cartierResidue_cast P.coefficients.l P.level) T)) (add_zero 2)) ∧
    ((Ext.mk₀ (supportedIntegralGenerator P.Coefficient i)).comp
      ((P.cartierRelativeCoefficientBoundary a i hI).mapExactFunctor
        (RawModuleScalarComparison.forget P.Coefficient T)) (zero_add 2) =
      (P.cartierRelativeBoundary a i hI).comp
        (Ext.mk₀ (ordinaryFiniteRootMap P.Coefficient P.diagonalExponent
          P.diagonalExponent_annihilates T)) (add_zero 2)) ∧
    P.generalDivisorClass a i hI = P.functorialCupCompare i 2 1
      (P.cartierRelativeCoefficientBoundary a i hI).hom := by
  let : Finite (ProEtale.cartierResidueRing.{u} P.coefficients.l P.level) :=
    ProEtale.cartierResidue_finite P.coefficients.l P.coefficients.prime.out P.level
  have hn : 0 < P.diagonalExponent := pow_pos P.coefficients.prime.out.pos P.level
  have hR := ProEtale.reducedEtale_boundary
    (ProEtale.cartierResidueRing.{u} P.coefficients.l P.level)
    P.diagonalExponent hn (ProEtale.cartierResidue_cast P.coefficients.l P.level)
    i hI (P.diagonalExponent_isUnit a)
  have hA := ProEtale.reducedEtale_boundary P.Coefficient P.diagonalExponent hn
    P.diagonalExponent_annihilates i hI (P.diagonalExponent_isUnit a)
  have heq (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (P.diagonalExponent : A) = 0) :
      (Ext.mk₀ (supportedIntegralGenerator A i)).comp
        ((ProEtale.cartierReducedEtale A P.diagonalExponent hn hA i hI
          (P.diagonalExponent_isUnit a)).mapExactFunctor
            (RawModuleScalarComparison.forget A T)) (zero_add 2) =
      (P.cartierRelativeBoundary a i hI).comp
        (Ext.mk₀ (ordinaryFiniteRootMap A P.diagonalExponent hA T)) (add_zero 2) := by
    have h := (ProEtale.boundary_spec_iff A P.diagonalExponent hn hA i hI
      (P.diagonalExponent_isUnit a) _).1
        (ProEtale.reducedEtale_boundary A P.diagonalExponent hn hA i hI
          (P.diagonalExponent_isUnit a))
    unfold ProEtale.CartierEtaleReductionSpec ProEtale.cartierScalarBoundaryEquation
      ProEtale.cartierEtaleKummerUnit ProEtale.cartierKummerClass at h
    simpa only [cartierRelativeBoundary, Ext.comp_assoc] using h
  refine ⟨?_, residueFiniteRootMap_isIso T P.diagonalExponent _, hR,
    heq _ _, heq _ _, ?_⟩
  · intro I J
    let R := ProEtale.cartierResidueRing.{u} P.coefficients.l P.level
    let F := RawModuleScalarComparison.forget R T
    let ι := F.mapResolution I.ι
    let q := InjectiveResolution.descOfQuasiIso (𝟙 _) J ι
    have hq : F.map (I.ι.f 0) ≫ q.f 0 = J.ι.f 0 := by
      have h := congrArg (fun f ↦ f.f 0)
        (InjectiveResolution.descOfQuasiIso_commutes (𝟙 _) J ι)
      dsimp only [ι] at h
      simp only [comp_f, RelativeCone.mapResolution_f_zero,
        CochainComplex.single₀_map_f_zero] at h
      change F.map (I.ι.f 0) ≫ q.f 0 = (𝟙 _) ≫ J.ι.f 0 at h
      exact h.trans (Category.id_comp _)
    have : QuasiIso q := inferInstance
    have heval (V : T.Etale) : QuasiIso (cartierSectionComparison T V q) :=
      cartierEvaluationQuasiIso R T I J q V
    have : QuasiIso (relativeSectionMap T (Scheme.Etale.mk i.openComplement.ι) q) :=
      cartierRelativeQuasiIso T _ q
    let V := Scheme.Etale.mk i.openComplement.ι
    let m := (MorphismProperty.Over.mkIdTerminal @Etale T).from V
    have : Mono m := by
      apply (MorphismProperty.Over.forget @Etale ⊤ T ⋙ Over.forget T).mono_of_mono_map
      change Mono i.openComplement.ι
      infer_instance
    have hIres : ∀ n, Function.Surjective
        (((cartierUnderlyingResolution R T I).X n).obj.map m.op) :=
      fun n ↦ cartierModuleRestrictionSurjective R T (I.cocomplex.X n) m
    have hJres : ∀ n, Function.Surjective ((J.cocomplex.X n).obj.map m.op) :=
      fun n ↦ injective_sheaf_mono_restriction.{u + 1, u, u + 1}
        T.smallEtaleTopology (J.cocomplex.X n) m
    refine ⟨q, hq, cartierConeComparison T i.openComplement q
      (cartierRestrictionEpi T V _ hIres) (cartierRestrictionEpi T V _ hJres), ?_⟩
    intro q' hq'
    have hh : Homotopy q' q := CochainComplex.homotopyOfQuasiIso ι q' q
      (by
        dsimp only [ι]
        rw [RelativeCone.mapResolution_f_zero]
        exact hq'.trans hq.symm)
    obtain ⟨H⟩ := sectionMap_homotopy T V q' q hh
    exact DerivedCategory.Q_map_eq_of_homotopy _ H
  · have hC := (P.existsUnique_generalDivisorEtaleClasses T a).choose_spec.1 i hI
    have hc := ProEtale.reducedEtale_eq_of_boundary P.Coefficient P.diagonalExponent hn
      P.diagonalExponent_annihilates i hI (P.diagonalExponent_isUnit a)
      ((P.generalDivisorEtaleClasses T a).classOf i hI) hC
    have hh := (P.generalDivisorEtaleClasses T a).realizes i hI
    have he : ((P.generalDivisorEtaleClasses T a).classOf i hI).hom =
        (ProEtale.cartierReducedEtale P.Coefficient P.diagonalExponent hn
          P.diagonalExponent_annihilates i hI (P.diagonalExponent_isUnit a)).hom :=
      congrArg (fun c ↦ c.hom) hc
    change P.functorialCupCompare i 2 1 _ = P.functorialCupCompare i 2 1 _
    apply congrArg (P.functorialCupCompare i 2 1)
    exact (eq_of_heq hh).symm.trans he

end WeilConjectures.PurityFiniteSetting
