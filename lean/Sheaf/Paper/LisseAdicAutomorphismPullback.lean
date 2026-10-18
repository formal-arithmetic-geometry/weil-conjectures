/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.Paper.LisseIntegralSmallCoefficients
public import Sheaf.AlgebraicGeometry.PointedEtaleStalk
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction

/-! # Automorphism pullback of lisse adic sheaves

Source: Deligne, Weil II (1.1.1) b)-d), (1.1.10)(i); Stacks Tags 03Q1 and 095A
(blueprint: def-wf-lisse-adic-automorphism-pullback).

The site functor sends `(U,u)` to `(U,u ≫ h.hom)`. Sheaves and integral diagrams
are reindexed literally. Rational maps extend this operation on integral maps by
balanced tensors. Algebraic coefficients use the same operation on coefficient pairs.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

variable {Y : Scheme.{u}} (h : Y ≅ Y)

/-- Reindex the small etale site, leaving the scheme and its morphisms unchanged.
Source: Stacks 03Q1, automorphism case
(blueprint: def-wf-lisse-adic-automorphism-pullback). -/
def automorphismEtaleReindex : Y.Etale ⥤ Y.Etale :=
  MorphismProperty.Over.map (P := @Etale) ⊤ (inferInstance : Etale h.hom)

/-- The explicit site equivalence; its inverse reindexes with h.inv. The unit and
counit have the identity underlying scheme map.
Source: Stacks 03Q1 (blueprint: def-wf-lisse-adic-automorphism-pullback). -/
def automorphismEtaleReindexEquivalence : Y.Etale ≌ Y.Etale :=
  CategoryTheory.Equivalence.mk (automorphismEtaleReindex h) (automorphismEtaleReindex h.symm)
    ((MorphismProperty.Over.mapId (P := @Etale) ⊤ Y (h.hom ≫ h.inv)
      h.hom_inv_id).symm ≪≫
      MorphismProperty.Over.mapComp (P := @Etale) ⊤
        (inferInstance : Etale h.hom) (inferInstance : Etale h.inv))
    ((MorphismProperty.Over.mapComp (P := @Etale) ⊤
      (inferInstance : Etale h.inv) (inferInstance : Etale h.hom)).symm ≪≫
      MorphismProperty.Over.mapId (P := @Etale) ⊤ Y (h.inv ≫ h.hom) h.inv_hom_id)

/-- Reindexing preserves the sheaf condition.
Source: Stacks 03Q1 (blueprint: def-wf-lisse-adic-automorphism-pullback).
Proof: reindex a covering sieve and its matching family. The underlying maps of schemes
are unchanged, so joint surjectivity is unchanged. Reindex with h.inv to obtain the
inverse matching family; the two composites have the identity underlying scheme map.
Apply the sheaf condition of F and transport the unique amalgamation back. -/
theorem automorphismEtaleReindex_isSheaf (R : Type (u + 1)) [Ring R]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) :
    Presheaf.IsSheaf Y.smallEtaleTopology ((automorphismEtaleReindex h).op ⋙ F.obj) := by
  sorry

/-- Pullback at unchanged module coefficients: restrictions and morphisms are whiskered
by the same site reindexing. Source: Stacks 03Q1
(blueprint: def-wf-lisse-adic-automorphism-pullback). -/
def automorphismModuleSheafPullback (R : Type (u + 1)) [Ring R] :
    Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R) ⥤
      Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R) :=
  ObjectProperty.lift _
    (sheafToPresheaf _ _ ⋙
      (Functor.whiskeringLeft _ _ _).obj (automorphismEtaleReindex h).op)
    (automorphismEtaleReindex_isSheaf h R)

/-- The transported local trivializations have the same finite modules.
Source: Stacks 095A (blueprint: def-wf-lisse-adic-automorphism-pullback).
Proof: replace each trivializing (U,u) by (U,u ≫ h.inv). The reindexed sheaf there is
F(U,u), with the same restrictions and constant module. Joint surjectivity is preserved
by the scheme isomorphism. Stalks are reindexed by y ↦ y ≫ h.hom, preserving finiteness. -/
theorem automorphismModuleSheafPullback_isFiniteLocallyConstant
    (R : Type (u + 1)) [Ring R]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))
    (hF : IsFiniteLocallyConstantSheaf F) :
    IsFiniteLocallyConstantSheaf ((automorphismModuleSheafPullback h R).obj F) := by
  sorry

/-- Pullback of finite-coefficient lisse sheaves, with the coefficient ring unchanged.
Source: Weil II (1.1.1), Stacks 095A
(blueprint: def-wf-lisse-adic-automorphism-pullback). -/
def lisseFiniteAutomorphismPullback (A : Type (u + 1)) [Ring A] [Finite A] :
    LisseFiniteModuleSheaf Y A ⥤ LisseFiniteModuleSheaf Y A :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ automorphismModuleSheafPullback h A)
    (fun F => automorphismModuleSheafPullback_isFiniteLocallyConstant h A F.obj F.property)

set_option backward.isDefEq.respectTransparency false in
/-- The map on pointed neighbourhoods keeps the lift to U and changes u to h ∘ u.
Source: Stacks 03Q1(3) (blueprint: def-wf-lisse-adic-automorphism-pullback). -/
def automorphismPointedEtaleLift {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (U : Y.Etale) (z : (pointSmallEtale y).fiber.obj U) :
    (pointSmallEtale (y ≫ h.hom)).fiber.obj ((automorphismEtaleReindex h).obj U) :=
  Over.homMk z.left (by
    change z.left ≫ (U.hom ≫ h.hom) = y ≫ h.hom
    exact (Category.assoc z.left U.hom h.hom).symm.trans
      (congrArg (fun f => f ≫ h.hom) (Over.w z)))

/-- The finite-level fibre iso is fixed by its action on every pointed-neighbourhood
colimit injection. Source: Stacks 03Q1(3)
(blueprint: def-wf-lisse-adic-automorphism-pullback).
Proof: send the germ represented by (U,u,z,s) to the germ (U,h ∘ u,z,s).
Restrictions are the same, so this is a cocone and induces a unique colimit map.
Reindex with h.inv for the inverse. On germs their composites are identities, so the
maps are inverse. Colimit uniqueness also proves uniqueness of the prescribed iso. -/
theorem automorphismModuleStalkIso_exists (R : Type (u + 1)) [Ring R]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y) :
    ∃! φ : pointedEtaleStalk ((automorphismModuleSheafPullback h R).obj F) y ≅
        pointedEtaleStalk F (y ≫ h.hom),
      ∀ (U : Y.Etale) (z : (pointSmallEtale y).fiber.obj U),
        pointedEtaleGerm ((automorphismModuleSheafPullback h R).obj F) y U z ≫ φ.hom =
          pointedEtaleGerm F (y ≫ h.hom) ((automorphismEtaleReindex h).obj U)
            (automorphismPointedEtaleLift h y U z) := by
  sorry

/-- The uniquely specified fibre identification, using the recorded geometric stalk.
Source: Stacks 03Q1(3) (blueprint: def-wf-lisse-adic-automorphism-pullback). -/
def automorphismModuleStalkIso (R : Type (u + 1)) [Ring R]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y) :
    pointedEtaleStalk ((automorphismModuleSheafPullback h R).obj F) y ≅
      pointedEtaleStalk F (y ≫ h.hom) :=
  (automorphismModuleStalkIso_exists h R F y).exists.choose

/-- The same finite-level iso in the coefficient-size lift used by integral fibres.
Source: Stacks 03Q1(3), Weil II (1.1.1) b)
(blueprint: def-wf-lisse-adic-automorphism-pullback). -/
def automorphismModuleLiftedStalkIso (R : Type (u + 1)) [Ring R]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y) :
    (pointSmallEtale y).ulift.{u + 1}.sheafFiber.obj
        ((automorphismModuleSheafPullback h R).obj F) ≅
      (pointSmallEtale (y ≫ h.hom)).ulift.{u + 1}.sheafFiber.obj F :=
  ((pointSmallEtale y).uliftSheafFiberIso.{u + 1} (ModuleCat.{u + 1} R)).app _ ≪≫
    automorphismModuleStalkIso h R F y ≪≫
      (((pointSmallEtale (y ≫ h.hom)).uliftSheafFiberIso.{u + 1}
        (ModuleCat.{u + 1} R)).app F).symm

variable (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  [IsNoetherian Y] [Y.IsSeparated] [∀ x : Y, Invertible (l : Y.residueField x)]

/-- Integral diagrams are pulled back level by level, including every transition map.
Source: Weil II (1.1.1) b) (blueprint: def-wf-lisse-adic-automorphism-pullback). -/
def adicIntegralAutomorphismPullback : AdicIntegralDiagram l E Y ⥤
    AdicIntegralDiagram l E Y :=
  (Functor.whiskeringRight _ _ _).obj
    (automorphismModuleSheafPullback h (Padic.coefficientExtensionIntegers l E))

/-- The reindexed diagram satisfies the identical lisse reduction criterion.
Source: Weil II (1.1.1) b) (blueprint: def-wf-lisse-adic-automorphism-pullback).
Proof: transport local trivializations as above. Sectionwise annihilation is unchanged,
since every new section module is the old section module at (U,u ≫ h.hom). On pointed
neighbourhoods use (U,u,z) ↦ (U,u ≫ h.hom,z), an equivalence with inverse h.inv.
Thus each stalk transition is conjugate to the old transition. Surjectivity and the
specified uniformizer-power kernel are unchanged. -/
theorem adicIntegralAutomorphismPullback_isLisse (F : LisseIntegralSheaf l E Y) :
    IsLisseIntegralDiagram l E Y ((adicIntegralAutomorphismPullback h l E).obj F.obj) := by
  sorry

/-- Pullback of integral lisse systems and compatible families of their morphisms.
Source: Weil II (1.1.1) b) (blueprint: def-wf-lisse-adic-automorphism-pullback). -/
def lisseIntegralAutomorphismPullback :
    LisseIntegralSheaf l E Y ⥤ LisseIntegralSheaf l E Y :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ adicIntegralAutomorphismPullback h l E)
    (adicIntegralAutomorphismPullback_isLisse h l E)

/-- The rational object is the rationalization of the pulled-back integral model.
Source: Weil II (1.1.1) c) (blueprint: def-wf-lisse-adic-automorphism-pullback). -/
def lisseRationalAutomorphismPullbackObj (F : LisseRationalSheaf l E Y) :
    LisseRationalSheaf l E Y :=
  ⟨(lisseIntegralAutomorphismPullback h l E).obj F.integral⟩

/-- Rational pullback is characterized on objects and on every pure tensor, and is
additive. These conditions determine all its data, rather than merely an arbitrary
functor. Source: Weil II (1.1.1) c)
(blueprint: def-wf-lisse-adic-automorphism-pullback).
Proof: integral pullback is coefficient-linear, because each section map is merely
reindexed. Extend (a,f) ↦ a ⊗ h*f by the balanced tensor universal property. Additivity
and the pure-tensor formula determine this map uniquely. Functor laws follow on pure
tensors from the integral functor laws and the rational composition formula, and then
on arbitrary tensors by induction. Objects are the specified integral models. -/
theorem lisseRationalAutomorphismPullback_exists :
    ∃ T : LisseRationalSheaf l E Y ⥤ LisseRationalSheaf l E Y,
      ∃ e : ∀ F, T.obj F = lisseRationalAutomorphismPullbackObj h l E F,
        (∀ (F G : LisseRationalSheaf l E Y) (f g : F ⟶ G),
          T.map (f + g) = T.map f + T.map g) ∧
        (∀ (F G : LisseRationalSheaf l E Y) (a : E) (f : F.integral ⟶ G.integral),
          T.map (TensorProduct.tmul _ a f) = eqToHom (e F) ≫
            TensorProduct.tmul _ a ((lisseIntegralAutomorphismPullback h l E).map f) ≫
              eqToHom (e G).symm) := by
  sorry

/-- The unique additive rational pullback with the displayed tensor formula.
Source: Weil II (1.1.1) c) (blueprint: def-wf-lisse-adic-automorphism-pullback). -/
def lisseRationalAutomorphismPullback :
    LisseRationalSheaf l E Y ⥤ LisseRationalSheaf l E Y :=
  (lisseRationalAutomorphismPullback_exists h l E).choose

/-- The object identification retained by the prescribed rational pullback.
Source: Weil II (1.1.1) c) (blueprint: def-wf-lisse-adic-automorphism-pullback).
Proof: take the object clause of the existence theorem specifying this functor. -/
theorem lisseRationalAutomorphismPullbackObjEq (F : LisseRationalSheaf l E Y) :
    (lisseRationalAutomorphismPullback h l E).obj F =
      lisseRationalAutomorphismPullbackObj h l E F :=
  by sorry

section Fibres
variable {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)

/-- Integral fibre transport is the inverse limit of the finite-level fibre transports.
The projection equations uniquely characterize it.
Source: Weil II (1.1.1) b), Stacks 03Q1(3)
(blueprint: def-wf-lisse-adic-automorphism-pullback).
Proof: finite-level germ transport commutes with transition maps, since both apply the
same reindexing to the same section map. Compose each limit projection with that
finite-level transport. The resulting cone induces a unique limit map. The inverse
finite-level transports give its inverse, and the limit projection equations prove
both inverse identities and uniqueness. -/
theorem lisseIntegralAutomorphismFiberIso_exists (F : LisseIntegralSheaf l E Y) :
    ∃! φ : lisseIntegralFiber l E Y y
        ((lisseIntegralAutomorphismPullback h l E).obj F) ≅
      lisseIntegralFiber l E Y (y ≫ h.hom) F,
      ∀ n : ℕ, φ.hom ≫
        limit.π (F.obj ⋙ (pointSmallEtale (y ≫ h.hom)).ulift.{u + 1}.sheafFiber) (op n) =
        limit.π (((lisseIntegralAutomorphismPullback h l E).obj F).obj ⋙
          (pointSmallEtale y).ulift.{u + 1}.sheafFiber) (op n) ≫
        (automorphismModuleLiftedStalkIso h (Padic.coefficientExtensionIntegers l E)
          (F.obj.obj (op n)) y).hom := by
  sorry

/-- The unique inverse-limit fibre identification.
Source: Weil II (1.1.1) b) (blueprint: def-wf-lisse-adic-automorphism-pullback). -/
def lisseIntegralAutomorphismFiberIso (F : LisseIntegralSheaf l E Y) :
    lisseIntegralFiber l E Y y ((lisseIntegralAutomorphismPullback h l E).obj F) ≅
      lisseIntegralFiber l E Y (y ≫ h.hom) F :=
  (lisseIntegralAutomorphismFiberIso_exists h l E y F).exists.choose

/-- The rational fibre identification tensors the integral one with the identity of E.
Source: Weil II (1.1.1) c) (blueprint: def-wf-lisse-adic-automorphism-pullback). -/
def lisseRationalAutomorphismFiberIso (F : LisseRationalSheaf l E Y) :
    lisseRationalFiber l E Y y ((lisseRationalAutomorphismPullback h l E).obj F) ≅
      lisseRationalFiber l E Y (y ≫ h.hom) F :=
  eqToIso (congrArg (lisseRationalFiber l E Y y)
    (lisseRationalAutomorphismPullbackObjEq h l E F)) ≪≫
  (ModuleCat.extendScalars (algebraMap (Padic.coefficientExtensionIntegers l E) E)).mapIso
    (lisseIntegralAutomorphismFiberIso h l E y F.integral)
end Fibres

section ScalarExtension
variable (L : Type (u + 1)) [Field L] [Algebra ℚ_[l] L]
  [FiniteDimensional ℚ_[l] L] (ι : E →ₐ[ℚ_[l]] L)

/-- The recorded scalar level comparison, exposing the scalar functor's prescribed
underlying data. This is only a definitional transport, with no new choice.
Source: Weil II (1.1.1) d) (blueprint: def-wf-lisse-adic-automorphism-pullback). -/
def automorphismScalarLevelIso (F : LisseIntegralSheaf l E Y) (m : ℕ) :
    ((lisseIntegralScalarExtension l E Y L ι).obj F).obj.obj (op m) ≅
      lisseIntegralScalarLevel l E Y L ι F m := by
  unfold lisseIntegralScalarExtension
  exact (lisseIntegralScalarExtensionData l E Y L ι).levelIso F m

/-- The scalar comparison is prescribed by the identity on every local coefficient
and section tensor. Source: Weil II (1.1.1) d)
(blueprint: def-wf-lisse-adic-automorphism-pullback).
Proof: at level m, both sides sheafify the same balanced tensor at the reindexed U,
with the same ceiling index and coefficient map. Send a ⊗ s to a ⊗ s. This respects
balancing, restrictions and transitions, and the inverse has the identical formula.
Uniqueness follows because these local generators generate after sheafification. -/
theorem lisseIntegralAutomorphismScalarIso_exists :
    ∃! τ : lisseIntegralAutomorphismPullback h l E ⋙
        lisseIntegralScalarExtension l E Y L ι ≅
      lisseIntegralScalarExtension l E Y L ι ⋙ lisseIntegralAutomorphismPullback h l L,
      ∀ (F : LisseIntegralSheaf l E Y) (m : ℕ) (U : Y.Etale)
        (a : Padic.coefficientExtensionRing l L (m + 1))
        (s : (F.obj.obj (op (lisseScalarSourceIndex l E L ι m))).obj.obj
          (op ((automorphismEtaleReindex h).obj U))),
        (automorphismScalarLevelIso l E L ι F m).hom.hom.app
          (op ((automorphismEtaleReindex h).obj U))
            (((τ.hom.app F).hom.app (op m)).hom.app (op U)
              ((automorphismScalarLevelIso l E L ι
                ((lisseIntegralAutomorphismPullback h l E).obj F) m).inv.hom.app (op U)
                  (lisseIntegralScalarGenerator l E Y L ι
                    ((lisseIntegralAutomorphismPullback h l E).obj F) m U a s))) =
        lisseIntegralScalarGenerator l E Y L ι F m
          ((automorphismEtaleReindex h).obj U) a s := by
  sorry

/-- The uniquely prescribed identity-on-tensors integral scalar comparison.
Source: Weil II (1.1.1) d) (blueprint: def-wf-lisse-adic-automorphism-pullback). -/
def lisseIntegralAutomorphismScalarIso :
    lisseIntegralAutomorphismPullback h l E ⋙ lisseIntegralScalarExtension l E Y L ι ≅
      lisseIntegralScalarExtension l E Y L ι ⋙ lisseIntegralAutomorphismPullback h l L :=
  (lisseIntegralAutomorphismScalarIso_exists h l E L ι).exists.choose

/-- Rationalizing the integral comparison prescribes the rational comparison itself.
Source: Weil II (1.1.1) c)-d) (blueprint: def-wf-lisse-adic-automorphism-pullback).
Proof: use the integral comparison just constructed and tensor its component with 1.
Transport the two chosen rational-object equalities. On morphisms, naturality follows
on pure tensors from the identity-on-coefficients integral comparison, then by
additivity. The inverse is the rationalization of its inverse. The formula fixes it. -/
theorem lisseRationalAutomorphismScalarIso_exists :
    ∃! τ : lisseRationalAutomorphismPullback h l E ⋙
        lisseRationalScalarExtension l E Y L ι ≅
      lisseRationalScalarExtension l E Y L ι ⋙ lisseRationalAutomorphismPullback h l L,
      ∀ F : LisseRationalSheaf l E Y,
        τ.hom.app F =
          (lisseRationalScalarExtension l E Y L ι).map
            (eqToHom (lisseRationalAutomorphismPullbackObjEq h l E F)) ≫
          TensorProduct.tmul _ (1 : L)
            ((lisseIntegralAutomorphismScalarIso h l E L ι).hom.app F.integral) ≫
          eqToHom (lisseRationalAutomorphismPullbackObjEq h l L
            ((lisseRationalScalarExtension l E Y L ι).obj F)).symm := by
  sorry

/-- The rational scalar comparison, fixed by rationalizing the integral one.
Source: Weil II (1.1.1) c)-d) (blueprint: def-wf-lisse-adic-automorphism-pullback). -/
def lisseRationalAutomorphismScalarIso :
    lisseRationalAutomorphismPullback h l E ⋙ lisseRationalScalarExtension l E Y L ι ≅
      lisseRationalScalarExtension l E Y L ι ⋙ lisseRationalAutomorphismPullback h l L :=
  (lisseRationalAutomorphismScalarIso_exists h l E L ι).exists.choose
end ScalarExtension

section AlgebraicCoefficients
open scoped Pseudofunctor.StrongTrans
variable (K : Type (u + 1)) [Field K] [Algebra ℚ_[l] K] [IsAlgClosure ℚ_[l] K]

/-- Pullback in each actual coefficient-diagram category, using its recorded transport
from lisse rational sheaves. Source: Weil II (1.1.1) d)
(blueprint: def-wf-lisse-adic-automorphism-pullback). -/
def automorphismLisseCoefficientStage (E₀ : Padic.FiniteCoefficientFields l K) :
    (lisseCoefficientDiagramData l Y K).diagram.obj ⟨E₀⟩ ⥤
      (lisseCoefficientDiagramData l Y K).diagram.obj ⟨E₀⟩ :=
  (eqToHom ((lisseCoefficientDiagramData l Y K).obj_eq E₀)).toFunctor ⋙
    lisseRationalAutomorphismPullback h l E₀.val ⋙
      (eqToHom ((lisseCoefficientDiagramData l Y K).obj_eq E₀).symm).toFunctor

/-- The coefficient transformation has the specified stage functors and the canonical
identity-on-tensors scalar constraints, rather than arbitrary coherence isomorphisms.
Source: Weil II (1.1.1) d) (blueprint: def-wf-lisse-adic-automorphism-pullback).
Proof: the components are the displayed rational pullbacks transported to the diagram.
Transport the inverses of the rational scalar comparisons to give strong naturality.
Their identity and composition constraints hold because all integral comparisons send
a ⊗ s to a ⊗ s; this agrees with the coefficient diagram's tensor associativity.
Rationalization preserves these equalities. Thus the indicated transformation exists;
its components and all naturality constraints are completely specified. -/
theorem automorphismLisseCoefficientTransformation_exists :
    ∃ α : (lisseCoefficientDiagramData l Y K).diagram ⟶
        (lisseCoefficientDiagramData l Y K).diagram,
      (∀ E₀ : Padic.FiniteCoefficientFields l K,
        (α.app ⟨E₀⟩).toFunctor = automorphismLisseCoefficientStage h l K E₀) ∧
      ∀ (E₀ L₀ : Padic.FiniteCoefficientFields l K) (i : E₀ ≤ L₀),
        ∃ e₁ :
          (eqToHom ((lisseCoefficientDiagramData l Y K).obj_eq E₀).symm).toFunctor ⋙
            ((lisseCoefficientDiagramData l Y K).diagram.map (homOfLE i).toLoc).toFunctor ⋙
              (α.app ⟨L₀⟩).toFunctor ⋙
                (eqToHom ((lisseCoefficientDiagramData l Y K).obj_eq L₀)).toFunctor =
          lisseRationalScalarExtension l E₀.val Y L₀.val (IntermediateField.inclusion i) ⋙
            lisseRationalAutomorphismPullback h l L₀.val,
        ∃ e₂ :
          (eqToHom ((lisseCoefficientDiagramData l Y K).obj_eq E₀).symm).toFunctor ⋙
            (α.app ⟨E₀⟩).toFunctor ⋙
              ((lisseCoefficientDiagramData l Y K).diagram.map (homOfLE i).toLoc).toFunctor ⋙
                (eqToHom ((lisseCoefficientDiagramData l Y K).obj_eq L₀)).toFunctor =
          lisseRationalAutomorphismPullback h l E₀.val ⋙
            lisseRationalScalarExtension l E₀.val Y L₀.val (IntermediateField.inclusion i),
          (eqToIso e₁).symm ≪≫
            Functor.isoWhiskerLeft
              (eqToHom ((lisseCoefficientDiagramData l Y K).obj_eq E₀).symm).toFunctor
              (Functor.isoWhiskerRight (Cat.Hom.toNatIso (α.naturality (homOfLE i).toLoc))
                (eqToHom ((lisseCoefficientDiagramData l Y K).obj_eq L₀)).toFunctor) ≪≫
              eqToIso e₂ =
            (lisseRationalAutomorphismScalarIso h l E₀.val L₀.val
              (IntermediateField.inclusion i)).symm := by
  sorry

/-- The coefficient transformation fixed on components and scalar constraints.
Source: Weil II (1.1.1) d) (blueprint: def-wf-lisse-adic-automorphism-pullback). -/
def automorphismLisseCoefficientTransformation :
    (lisseCoefficientDiagramData l Y K).diagram ⟶
      (lisseCoefficientDiagramData l Y K).diagram :=
  (automorphismLisseCoefficientTransformation_exists h l K).choose

/-- Pullback of coefficient pairs: it fixes the field, applies rational pullback to
its sheaf, and applies finite-stage pullback to arrows after the scalar comparison.
Source: Weil II (1.1.1) d) (blueprint: def-wf-lisse-adic-automorphism-pullback). -/
def lisseCoefficientPairAutomorphismPullback :
    LisseCoefficientPairs l Y K ⥤ LisseCoefficientPairs l Y K :=
  Pseudofunctor.Grothendieck.map (automorphismLisseCoefficientTransformation h l K)

/-- Pullback carries cocartesian coefficient arrows to isomorphisms in the localization.
Source: Weil II (1.1.1) d) (blueprint: def-wf-lisse-adic-automorphism-pullback).
Proof: the fibre map of a cocartesian arrow is invertible. The Grothendieck pullback
map is a rational functor applied to this map composed with an invertible scalar
comparison. Hence it is again cocartesian. The localization inverts all such maps. -/
theorem lisseCoefficientPairAutomorphismPullback_inverts :
    (lisseCoefficientCocartesian l Y K).IsInvertedBy
      (lisseCoefficientPairAutomorphismPullback h l K ⋙
        (lisseCoefficientCocartesian l Y K).Q) := by
  sorry

/-- Algebraic-coefficient pullback, constructed by the localization universal property.
On a common finite extension its morphisms are exactly the finite-stage pullback, with
coefficient comparisons fixed by the identity on tensors.
Source: Weil II (1.1.1) d) (blueprint: def-wf-lisse-adic-automorphism-pullback). -/
def lisseAlgebraicAutomorphismPullback :
    LisseAlgebraicSheaf l Y K ⥤ LisseAlgebraicSheaf l Y K :=
  Localization.Construction.lift
    (lisseCoefficientPairAutomorphismPullback h l K ⋙
      (lisseCoefficientCocartesian l Y K).Q)
    (lisseCoefficientPairAutomorphismPullback_inverts h l K)
/-- The formula (E,F) ↦ (E,h*F) on algebraic objects, using the recorded pair model.
Source: Weil II (1.1.1) d) (blueprint: def-wf-lisse-adic-automorphism-pullback). -/
def lisseAlgebraicAutomorphismPullbackObj (F : LisseAlgebraicSheaf l Y K) :
    LisseAlgebraicSheaf l Y K :=
  lisseAlgebraicOfModel l Y K (lisseAlgebraicPair l Y K F).base
    ((lisseRationalAutomorphismPullback h l (lisseAlgebraicPair l Y K F).base.val).obj
      (lisseCoefficientPairModel l Y K (lisseAlgebraicPair l Y K F)))

/-- The localization construction has exactly the prescribed coefficient-pair objects.
Source: Weil II (1.1.1) d) (blueprint: def-wf-lisse-adic-automorphism-pullback).
Proof: localization keeps objects. The Grothendieck functor keeps the base field and
applies its component to the fibre. Substitute the specified component from the
coefficient-transformation existence theorem. The inverse category-value transports
cancel, leaving precisely the displayed pair. -/
theorem lisseAlgebraicAutomorphismPullback_obj (F : LisseAlgebraicSheaf l Y K) :
    (lisseAlgebraicAutomorphismPullback h l K).obj F =
      lisseAlgebraicAutomorphismPullbackObj h l K F := by
  sorry

variable {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)

/-- The pulled-back fibre written at the original coefficient stage, before tensoring
its rational fibre with K. This retains the same coefficient field.
Source: Weil II (1.1.1) d) (blueprint: def-wf-lisse-adic-automorphism-pullback). -/
def lisseAlgebraicAutomorphismFiberAtStage (F : LisseAlgebraicSheaf l Y K) :
    ModuleCat.{u + 1} K :=
  ModuleCat.of K (TensorProduct (lisseAlgebraicPair l Y K F).base.val K
    (lisseRationalFiber l (lisseAlgebraicPair l Y K F).base.val Y y
      ((lisseRationalAutomorphismPullback h l (lisseAlgebraicPair l Y K F).base.val).obj
        (lisseCoefficientPairModel l Y K (lisseAlgebraicPair l Y K F)))))

/-- The algebraic fibre is exactly the common-stage tensor in the node's formula.
Source: Weil II (1.1.1) d) (blueprint: def-wf-lisse-adic-automorphism-pullback).
Proof: substitute the object formula just stated into the recorded algebraic fibre.
The pair has the unchanged base and its pulled-back rational model. The category-value
transports cancel, so the fibre definition is the displayed tensor at that stage. -/
theorem lisseAlgebraicAutomorphismFiberAtStage_eq (F : LisseAlgebraicSheaf l Y K) :
    lisseAlgebraicFiber l Y K y ((lisseAlgebraicAutomorphismPullback h l K).obj F) =
      lisseAlgebraicAutomorphismFiberAtStage h l K y F := by
  sorry

/-- Algebraic fibre transport is the identity on K tensored with the rational fibre
transport, at the unchanged finite coefficient stage.
Source: Weil II (1.1.1) d), Stacks 03Q1(3)
(blueprint: def-wf-lisse-adic-automorphism-pullback). -/
def lisseAlgebraicAutomorphismFiberIso (F : LisseAlgebraicSheaf l Y K) :
    lisseAlgebraicFiber l Y K y ((lisseAlgebraicAutomorphismPullback h l K).obj F) ≅
      lisseAlgebraicFiber l Y K (y ≫ h.hom) F :=
  eqToIso (lisseAlgebraicAutomorphismFiberAtStage_eq h l K y F) ≪≫
    (ModuleCat.extendScalars (algebraMap (lisseAlgebraicPair l Y K F).base.val K)).mapIso
      (lisseRationalAutomorphismFiberIso h l (lisseAlgebraicPair l Y K F).base.val y
        (lisseCoefficientPairModel l Y K (lisseAlgebraicPair l Y K F)))

end AlgebraicCoefficients

end AlgebraicGeometry.Scheme
