/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q54
-/
module

public import Sheaf.CategoryTheory.RingedPresentationData
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.IsoAlgebra
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import Sheaf.CategoryTheory.FixedPairCreatedAbelianStructure
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian

/-! # Equivariant product sheaf Hom and quasi-isomorphisms

Source: Stacks Project, sites-cohomology.tex, Tags 0A8X and 0A95;
derived.tex, Tag 08BJ, with the fixed-pair conjugation construction
(blueprint: lem-sf-equivariant-hom-quasi-isomorphism).

The ringed-topos morphism describes s, its ring map is invertible, and `P` records
its induced module pullback. The tensor comparison is characterized on pure tensors
of generalized elements. Evaluation then fixes the internal Hom comparison.
The existential bifunctor and its projections specify the construction without
selecting data from an uncharacterized existence assertion.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  {R : Sheaf J CommRingCat.{u}}

/-- The section function of the ordinary pure-tensor pairing.
Source: Stacks 03EK (blueprint: lem-sf-equivariant-hom-quasi-isomorphism). -/
def equivariantHomTensorPairSection (M N : PresentationModules R) (X : Cᵒᵖ)
    (z : ((presentationForget R).obj M ⨯ (presentationForget R).obj N).obj.obj X) :
    ((presentationForget R).obj (M ⊗ N)).obj.obj X :=
  (SheafOfModules.tensorObjIsoSheafification.{u, u, u} M N).inv.val.app X
    (((PresheafOfModules.sheafificationAdjunction.{u}
      (𝟙 (localCoefficientRings R).obj)).unit.app (M.val ⊗ N.val)).app X
        (((prod.fst : (presentationForget R).obj M ⨯ (presentationForget R).obj N ⟶
            (presentationForget R).obj M).hom.app X z) ⊗ₜ[R.obj.obj X]
          ((prod.snd : (presentationForget R).obj M ⨯ (presentationForget R).obj N ⟶
            (presentationForget R).obj N).hom.app X z)))

/-- The pure tensor pairing commutes with restriction.
Source: Stacks 03EK (blueprint: lem-sf-equivariant-hom-quasi-isomorphism).
Proof: the presheaf tensor restriction sends x tensor y to their two restrictions;
then apply naturality of the sheafification unit and of the tensor comparison.
This is the sectionwise restriction check in step 3 of the node's construction. -/
theorem equivariantHomTensorPair_naturality (M N : PresentationModules R)
    (X Y : Cᵒᵖ) (f : X ⟶ Y) :
    ((presentationForget R).obj M ⨯ (presentationForget R).obj N).obj.map f ≫
        ↾(equivariantHomTensorPairSection M N Y) =
      ↾(equivariantHomTensorPairSection M N X) ≫
        ((presentationForget R).obj (M ⊗ N)).obj.map f := by
  ext z
  have hfst := ConcreteCategory.congr_hom (NatTrans.naturality
    (prod.fst : (presentationForget R).obj M ⨯ (presentationForget R).obj N ⟶
      (presentationForget R).obj M).hom f) z
  have hsnd := ConcreteCategory.congr_hom (NatTrans.naturality
    (prod.snd : (presentationForget R).obj M ⨯ (presentationForget R).obj N ⟶
      (presentationForget R).obj N).hom f) z
  dsimp [equivariantHomTensorPairSection]
  dsimp at hfst hsnd
  rw [hfst, hsnd]
  let b : M.val ⊗ N.val ⟶ (M ⊗ N).val :=
    (PresheafOfModules.sheafificationAdjunction.{u}
      (𝟙 (localCoefficientRings R).obj)).unit.app (M.val ⊗ N.val) ≫
        (SheafOfModules.tensorObjIsoSheafification.{u, u, u} M N).inv.val
  exact PresheafOfModules.naturality_apply b f
    (((prod.fst : (presentationForget R).obj M ⨯ (presentationForget R).obj N ⟶
      (presentationForget R).obj M).hom.app X z) ⊗ₜ[R.obj.obj X]
      ((prod.snd : (presentationForget R).obj M ⨯ (presentationForget R).obj N ⟶
        (presentationForget R).obj N).hom.app X z))

/-- Pure tensors as a map of underlying sheaves of sets, using the existing sheaf tensor.
Source: Stacks 03EK and 0A8X
(blueprint: lem-sf-equivariant-hom-quasi-isomorphism). -/
def equivariantHomTensorPair (M N : PresentationModules R) :
    (presentationForget R).obj M ⨯ (presentationForget R).obj N ⟶
      (presentationForget R).obj (M ⊗ N) :=
  ⟨{ app := fun X ↦ ↾(equivariantHomTensorPairSection M N X)
     naturality := equivariantHomTensorPair_naturality M N }⟩

/-- Evaluation for the existing sheaf internal Hom.
Source: Stacks 0A8X (blueprint: lem-sf-equivariant-hom-quasi-isomorphism). -/
def equivariantHomEvaluation (M N : PresentationModules R) :
    M ⊗ SheafOfModules.homObj (R := R) M N ⟶ N :=
  (SheafOfModules.tensorHomEquiv M (SheafOfModules.homObj (R := R) M N) N).symm (𝟙 _)

/-- The additive structure of the induced pullback, inherited from its equivalence.
Source: Stacks 03CR (blueprint: lem-sf-equivariant-hom-quasi-isomorphism). -/
instance equivariantHomPullback_additive
    (e : RingedToposMorphism (localCoefficientRings R) (localCoefficientRings R))
    (P : RingedPresentationAt e) : P.transport.modules.functor.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The pair on internal Hom has the specified conjugation structure. Its data are
composites of the supplied comparison and the two existing structure isomorphisms.
Source: Stacks 0A8X, equivariant conjugation
(blueprint: lem-sf-equivariant-hom-quasi-isomorphism). -/
def equivariantHomPair (T : PresentationModules R ⥤ PresentationModules R)
    (γ : ∀ M N : PresentationModules R,
      T.obj (SheafOfModules.homObj (R := R) M N) ≅
        SheafOfModules.homObj (R := R) (T.obj M) (T.obj N))
    (M N : IsoAlgebra T) : IsoAlgebra T :=
  mk (SheafOfModules.homObj (R := R) M.carrier N.carrier)
    (γ M.carrier N.carrier ≪≫
      ((SheafOfModules.homFunctor R).mapIso M.str.symm.op).app (T.obj N.carrier) ≪≫
      ((SheafOfModules.homFunctor R).obj (op M.carrier)).mapIso N.str)

/-- Forgetting creates the products, is exact, detects quasi-isomorphisms, and
preserves K-injectives.
Source: Stacks 03DB and 08BJ
(blueprint: lem-sf-equivariant-hom-quasi-isomorphism).

Proof, steps 1--2: module sheaves on this small site are Grothendieck abelian
(lem-pur-ringed-site-grothendieck-abelian). Limits are compatible section tuples,
with coordinatewise gluing. The additive autoequivalence creates the fixed-pair
abelian structure and limits (lem-sf-fixed-pair-created-abelian-structure).
Its exact conservative forgetful functor commutes with cohomology, detecting
quasi-isomorphisms. The exact integer-orbit left adjoint implies preservation of
K-injectives (lem-sf-fixed-pair-derived-forget-comparison, Stacks 08BJ). -/
theorem equivariantHom_forget_properties
    (e : RingedToposMorphism (localCoefficientRings R) (localCoefficientRings R))
    [e.inverse.IsEquivalence] [IsIso e.ringMap] (P : RingedPresentationAt e) :
    Nonempty (CreatesLimitsOfShape (Discrete ℤ) (forget P.transport.modules.functor)) ∧
      PreservesFiniteLimits (forget P.transport.modules.functor) ∧
      PreservesFiniteColimits (forget P.transport.modules.functor) ∧
      (forget P.transport.modules.functor).PreservesKInjectiveComplexes ∧
      (∀ (K L : CochainComplex (IsoAlgebra P.transport.modules.functor) ℤ) (f : K ⟶ L),
        QuasiIso f ↔ QuasiIso
          (((forget P.transport.modules.functor).mapHomologicalComplex (.up ℤ)).map f)) := by
  have : IsGrothendieckAbelian.{u} (PresentationModules R) :=
    (SheafOfModules.grothendieckAbelian_with_localized_generator J R).1
  obtain ⟨_, _, ⟨hcreates⟩, _⟩ :=
    fixedPairCreatedAbelianStructure.{u + 1, u, u} P.transport.modules.functor
  let := hcreates
  have : CreatesLimitsOfShape (Discrete ℤ) (forget P.transport.modules.functor) :=
    createsLimitsOfShapeOfEquiv
      (Discrete.equivalence (Equiv.ulift : ULift.{u} ℤ ≃ ℤ)) _
  refine ⟨⟨inferInstance⟩, inferInstance, inferInstance, inferInstance, ?_⟩
  intro K L f
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology f
    (forget P.transport.modules.functor)).symm

-- STATEMENT-DISPUTED: `P.underlying` need not preserve scalar multiplication.
-- On the classifying site of C₂ × C₂ over F₄, the natural involution
-- a_M = 1 + (k - 1)h fixes the unit module but need not be F₄-linear.
-- With T = id and N = R the pure-tensor clause forces a_M to be linear.
-- See the delivery report for the site, actions and explicit unbalanced tensor pair.
/-- The equivariant product Hom construction, its natural forgetful identification,
and quasi-isomorphism invariance in both variables.

Source: Stacks 0A8X, 0A95 and 08BJ
(blueprint: lem-sf-equivariant-hom-quasi-isomorphism).

Proof, all five steps of the node:
1. Apply the small-site Grothendieck assertion and create fixed-pair limits and
   abelian structure (lem-pur-ringed-site-grothendieck-abelian,
   lem-sf-fixed-pair-created-abelian-structure).
2. The forgetful functor is exact and conservative, detects quasi-isomorphisms,
   and preserves K-injectives by the exact orbit-sum adjunction
   (lem-sf-fixed-pair-derived-forget-comparison).
3. Transport pure tensors along the ringed-topos equivalence. The tensor-Hom
   adjunction gives the unique evaluation-compatible Hom comparison γ. Conjugate
   by θ_N and θ_M inverse. Naturality makes post- and precomposition equivariant.
   On the product terms the signed differential is d_I f - (-1)^n f d_K.
   Expanding its square cancels mixed terms. Created products give the natural
   chain isomorphism α, with identity on each underlying Hom projection.
4. On the p-th projection, pre- and postcomposition are v^(p+n) f_p t^p.
   The intertwining equations make this equivariant. The chain-map equations
   give d(vft) = v(df)t, so these are the components of a chain map.
5. Apply lem-pur-rhom-well-defined to the underlying t and v, whose targets are
   K-injective by step 2. Through α this is the underlying map of the displayed
   equivariant Hom morphism. Detection gives its quasi-isomorphism, and the
   ordinary derived localization inverts it (def-weil-abstract-derived-category).

`P` is a universally quantified presentation of the induced pullback, not an
extra existence assumption. All complexes and products are unbounded. -/
theorem exists_equivariantHom_quasiIso
    (e : RingedToposMorphism (localCoefficientRings R) (localCoefficientRings R))
    [e.inverse.IsEquivalence] [IsIso e.ringMap]
    (P : RingedPresentationAt e)
    [HasDerivedCategory.{w} (IsoAlgebra P.transport.modules.functor)] :
    ∃ (χ : ∀ M N : PresentationModules R,
        P.transport.modules.functor.obj (M ⊗ N) ≅
          P.transport.modules.functor.obj M ⊗ P.transport.modules.functor.obj N)
      (γ : ∀ M N : PresentationModules R,
        P.transport.modules.functor.obj (SheafOfModules.homObj (R := R) M N) ≅
          SheafOfModules.homObj (R := R)
            (P.transport.modules.functor.obj M) (P.transport.modules.functor.obj N)),
      (∀ M N : PresentationModules R,
        equivariantHomTensorPair
            (P.transport.modules.functor.obj M) (P.transport.modules.functor.obj N) ≫
          (presentationForget R).map (χ M N).inv ≫ P.underlying.hom.app (M ⊗ N) =
        prod.map (P.underlying.hom.app M) (P.underlying.hom.app N) ≫
          inv (prodComparison e.inverse
            ((presentationForget R).obj M) ((presentationForget R).obj N)) ≫
          e.inverse.map (equivariantHomTensorPair M N)) ∧
      (∀ M N : PresentationModules R,
        P.transport.modules.functor.map (equivariantHomEvaluation M N) =
          (χ M (SheafOfModules.homObj (R := R) M N)).hom ≫
            (𝟙 _ ⊗ₘ (γ M N).hom) ≫
              equivariantHomEvaluation
                (P.transport.modules.functor.obj M) (P.transport.modules.functor.obj N)) ∧
      ∃ (H : (CochainComplex (IsoAlgebra P.transport.modules.functor) ℤ)ᵒᵖ ⥤
          CochainComplex (IsoAlgebra P.transport.modules.functor) ℤ ⥤
            CochainComplex (IsoAlgebra P.transport.modules.functor) ℤ)
        (α : Functor.uncurry.obj H ⋙
            (forget P.transport.modules.functor).mapHomologicalComplex (.up ℤ) ≅
          (((forget P.transport.modules.functor).mapHomologicalComplex (.up ℤ)).op.prod
            ((forget P.transport.modules.functor).mapHomologicalComplex (.up ℤ))) ⋙
              Functor.uncurry.obj (homComplexFunctor (R := R)))
        (π : ∀ (K I : CochainComplex (IsoAlgebra P.transport.modules.functor) ℤ)
          (n p : ℤ), ((H.obj (op K)).obj I).X n ⟶
            equivariantHomPair P.transport.modules.functor γ (K.X p) (I.X (p + n))),
        (∀ (K I : CochainComplex (IsoAlgebra P.transport.modules.functor) ℤ) (n : ℤ),
          Nonempty (IsLimit (Fan.mk (((H.obj (op K)).obj I).X n) (π K I n)))) ∧
        (∀ (K I : CochainComplex (IsoAlgebra P.transport.modules.functor) ℤ) (n p : ℤ),
          (forget P.transport.modules.functor).map (π K I n p) =
            (α.hom.app (op K, I)).f n ≫
              homComplexπ
                (((forget P.transport.modules.functor).mapHomologicalComplex (.up ℤ)).obj K)
                (((forget P.transport.modules.functor).mapHomologicalComplex (.up ℤ)).obj I)
                n p (p + n) rfl) ∧
        (∀ (K' K I' I : CochainComplex (IsoAlgebra P.transport.modules.functor) ℤ)
          (t : K' ⟶ K) (v : I' ⟶ I),
          I'.IsKInjective → I.IsKInjective → QuasiIso t → QuasiIso v →
          QuasiIso (((H.map t.op).app I') ≫ (H.obj (op K')).map v) ∧
            IsIso (DerivedCategory.Q.map
              (((H.map t.op).app I') ≫ (H.obj (op K')).map v))) := by
  sorry

end CategoryTheory.Endofunctor.IsoAlgebra
