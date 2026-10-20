/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q116
-/
module

public import Sheaf.AlgebraicGeometry.FiniteOpenBaseChangeNormalized
public import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Functor.OfSequence
import Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage
import Sheaf.AlgebraicGeometry.ProEtaleConstantExact
import Sheaf.AlgebraicGeometry.ProEtaleDerivedExtensionZeroBaseChange
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZero
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import WeilConjectures.CategoryTheory.SiteMorphismComposition

/-!
# Finite open exchange and coefficient restriction

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-sf-cbc/
lem-cbc-completed-extension-zero-comparison.proof.md, finite exchange before derived limits;
Stacks Project, Tag 03DI, direct-sum adjunction construction
(blueprint: lem-cbc-finite-open-exchange-scalars).

We use the recorded constant-ring module coordinates and the recorded inverse open-unit
transpose. All complex functors below are termwise, before derived localization.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale.StrictTower.FiniteOpenScalars

attribute [local irreducible] Functor.leftAdjoint

private theorem mate_unit_iso
    {D₁ D₂ E₁ E₂ : Type*} [Category D₁] [Category D₂] [Category E₁] [Category E₂]
    {L₁ : D₁ ⥤ D₂} {R₁ : D₂ ⥤ D₁} {L₂ : E₁ ⥤ E₂} {R₂ : E₂ ⥤ E₁}
    {G : D₁ ⥤ E₁} {H : D₂ ⥤ E₂}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (e : R₁ ⋙ G ≅ H ⋙ R₂) (M : D₁) :
    adj₂.unit.app (G.obj M) ≫
        R₂.map (((mateEquiv adj₁ adj₂).symm (TwoSquare.mk _ _ _ _ e.hom)).app M) ≫
        e.inv.app (L₁.obj M) = G.map (adj₁.unit.app M) := by
  have hu := unit_mateEquiv_symm adj₁ adj₂ (TwoSquare.mk _ _ _ _ e.hom) M
  change G.map (adj₁.unit.app M) ≫ e.hom.app (L₁.obj M) =
    adj₂.unit.app (G.obj M) ≫
      R₂.map (((mateEquiv adj₁ adj₂).symm (TwoSquare.mk _ _ _ _ e.hom)).app M) at hu
  rw [← Category.assoc, ← hu, Category.assoc, Iso.hom_inv_id_app]
  change G.map (adj₁.unit.app M) ≫ 𝟙 _ = G.map (adj₁.unit.app M)
  exact Category.comp_id _

private theorem sequence_iso
    {C : Type*} [Category C] {X Y : ℕ → C}
    (s : ∀ n, X (n + 1) ⟶ X n) (t : ∀ n, Y (n + 1) ⟶ Y n)
    (e : ∀ n, X n ≅ Y n)
    (h : ∀ n, s n ≫ (e n).hom = (e (n + 1)).hom ≫ t n) :
    ∃ z : Functor.ofOpSequence s ≅ Functor.ofOpSequence t,
      (∀ n, z.hom.app (Opposite.op n) = (e n).hom) ∧
      (∀ n, z.inv.app (Opposite.op n) = (e n).inv) := by
  let f : Functor.ofOpSequence s ⟶ Functor.ofOpSequence t :=
    NatTrans.ofOpSequence (fun n ↦ (e n).hom) (by
      intro n
      simpa only [Functor.ofOpSequence_map_homOfLE_succ] using h n)
  let g : Functor.ofOpSequence t ⟶ Functor.ofOpSequence s :=
    NatTrans.ofOpSequence (fun n ↦ (e n).inv) (by
      intro n
      simp only [Functor.ofOpSequence_map_homOfLE_succ]
      apply (cancel_epi (e (n + 1)).hom).mp
      rw [← Category.assoc, ← h n]
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
        Iso.hom_inv_id_assoc])
  refine ⟨⟨f, g, ?_, ?_⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩
  · ext n
    exact (e n.unop).hom_inv_id
  · ext n
    exact (e n.unop).inv_hom_id

variable {B C : Type (u + 1)} [CommRing B] [CommRing C]

/-- The map of constant coefficient sheaves induced by a ring homomorphism.
Source: Stacks Tag 03CY (blueprint: lem-cbc-finite-open-exchange-scalars). -/
abbrev coefficientMap (a : B →+* C) (X : Scheme.{u}) :
    coefficients B X ⟶ coefficients C X :=
  (constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map (CommRingCat.ofHom a)

/-- The underlying ring sheaf of the recorded commutative constant coefficients.
Source: Stacks Tag 03CY (blueprint: lem-cbc-finite-open-exchange-scalars). -/
abbrev ringCoefficients (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :=
  (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (coefficients A X)

/-- The same coefficient homomorphism after forgetting commutativity.
Source: Stacks Tag 03CY (blueprint: lem-cbc-finite-open-exchange-scalars). -/
abbrev ringCoefficientMap (a : B →+* C) (X : Scheme.{u}) :
    ringCoefficients B X ⟶ ringCoefficients C X :=
  (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (coefficientMap a X)

/-- The recorded restriction of scalars, leaving the abelian sheaf unchanged.
Source: Stacks Tag 03CY (blueprint: lem-cbc-finite-open-exchange-scalars). -/
abbrev res (a : B →+* C) (X : Scheme.{u}) : Modules C X ⥤ Modules B X :=
  Scheme.proEtaleRingRestrictScalars (coefficientMap a X)

/-- The constant-preserving coefficient maps commute with a coefficient homomorphism.
Source: Stacks Tags 03D2 and 03CY
(blueprint: lem-cbc-finite-open-exchange-scalars).
Proof: transpose under the ring-sheaf adjunction. Both maps send each constant b to
the constant section a(b). The constant-presheaf sheafification property gives equality. -/
theorem coefficientSquare (a : B →+* C) {Y X : Scheme.{u}} (f : Y ⟶ X) :
    (constantRingIso B f).hom ≫ coefficientMap a Y =
      (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).map (coefficientMap a X) ≫
        (constantRingIso C f).hom := by
  exact (Scheme.proEtaleConstantInverseImageMap_naturality f (CommRingCat.ofHom a)).symm

/-- Canonical pullback/scalar identification, the mate of identity on direct-image sections.
Source: Stacks Tags 03D2 and 03CY
(blueprint: lem-cbc-finite-open-exchange-scalars). -/
def pullRes (a : B →+* C) {Y X : Scheme.{u}} (f : Y ⟶ X) :
    res a X ⋙ modulePullback B f ≅ modulePullback C f ⋙ res a Y :=
  @asIso _ _ _ _ (Scheme.proEtaleRingRestrictionPullbackInv f
    (coefficients B X) (coefficients C X) (coefficients B Y) (coefficients C Y)
    (coefficientMap a X) (coefficientMap a Y) (constantRingIso B f) (constantRingIso C f)
    (coefficientSquare a f))
    (Scheme.proEtaleRingRestrictionPullbackInv_isIso f
      (coefficients B X) (coefficients C X) (coefficients B Y) (coefficients C Y)
      (coefficientMap a X) (coefficientMap a Y) (constantRingIso B f) (constantRingIso C f)
      (coefficientSquare a f))

/-- Canonical direct-image/scalar identification, identity on every section.
Source: Stacks Tag 03CY (blueprint: lem-cbc-finite-open-exchange-scalars). -/
def pushRes (a : B →+* C) {Y X : Scheme.{u}} (f : Y ⟶ X) :
    moduleDirectImage C f ⋙ res a X ≅ res a Y ⋙ moduleDirectImage B f :=
  Scheme.proEtaleRingRestrictionDirectImage f
    (coefficients B X) (coefficients C X) (coefficients B Y) (coefficients C Y)
    (coefficientMap a X) (coefficientMap a Y) (constantRingIso B f) (constantRingIso C f)
    (coefficientSquare a f)

set_option backward.isDefEq.respectTransparency false in
private theorem pullRes_mate (a : B →+* C) {Y X : Scheme.{u}} (f : Y ⟶ X) :
    (mateEquiv (Scheme.proEtaleRingModuleAdjunction f
        (coefficients C X) (coefficients C Y) (constantRingIso C f))
      (Scheme.proEtaleRingModuleAdjunction f
        (coefficients B X) (coefficients B Y) (constantRingIso B f))
      (TwoSquare.mk _ _ _ _ (pullRes a f).hom)).natTrans = (pushRes a f).hom := by
  change (mateEquiv (Scheme.proEtaleRingModuleAdjunction f
      (coefficients C X) (coefficients C Y) (constantRingIso C f))
    (Scheme.proEtaleRingModuleAdjunction f
      (coefficients B X) (coefficients B Y) (constantRingIso B f)))
      (TwoSquare.mk _ _ _ _ (pullRes a f).hom) =
    TwoSquare.mk _ _ _ _ (pushRes a f).hom
  rw [← Equiv.eq_symm_apply]
  apply TwoSquare.ext
  intro M
  simp only [mateEquiv_symm_apply, pullRes, asIso_hom,
    Scheme.proEtaleRingRestrictionPullbackInv,
    Scheme.proEtaleRingRestrictionPullbackApp, pushRes, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app,
    Functor.comp_map, Category.id_comp]
  simp only [TwoSquare.mk, CategoryTheory.Functor.map_id]
  dsimp only [TwoSquare.natTrans, Functor.comp_obj]
  simp only [Category.id_comp]
  exact congrArg (fun k ↦ _ ≫ _ ≫ k) (Category.comp_id _).symm

/-- The scalar comparison for extension is the mate of the inverse pullback comparison.
Source: Stacks Tag 03DI, direct-sum adjunction construction
(blueprint: lem-cbc-finite-open-exchange-scalars). -/
def openResMap (a : B →+* C) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    res a U ⋙ moduleJ B j ⟶ moduleJ C j ⋙ res a X :=
  (mateEquiv (moduleJAdj C j) (moduleJAdj B j)).symm (pullRes a j).inv

/-- The normalized open scalar mate is invertible, including for the empty open.
Source: Stacks Tag 03DI (blueprint: lem-cbc-finite-open-exchange-scalars).
Proof: restriction changes only the scalar action. The extension presheaf is the same
direct sum on abelian groups and module sheafification extends the action uniquely.
Thus the identity on that construction is invertible. Its transpose is exactly the
restricted open unit, hence is openResMap by the adjunction bijection. -/
theorem openResMap_isIso [Finite B] [Finite C] (a : B →+* C)
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] : IsIso (openResMap a j) := by
  sorry

/-- The canonical scalar-restriction identification for open extension.
Source: Stacks Tag 03DI (blueprint: lem-cbc-finite-open-exchange-scalars). -/
def openRes [Finite B] [Finite C] (a : B →+* C)
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    res a U ⋙ moduleJ B j ≅ moduleJ C j ⋙ res a X :=
  @asIso _ _ _ _ (openResMap a j) (openResMap_isIso a j)

/-- The recorded canonical open exchange on sheaves, before degreewise extension.
Its inverse is exactly singleBetaInv, the pulled-back open-unit transpose.
Source: Stacks Tag 09AE (blueprint: lem-cbc-finite-open-exchange-scalars). -/
def beta (A : Type (u + 1)) [CommRing A] [Finite A]
    {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j] [IsOpenImmersion j']
    (h : gU ≫ j = j' ≫ g) (hsq : IsPullback gU j' j g) :
    moduleJ A j ⋙ modulePullback A g ≅ modulePullback A gU ⋙ moduleJ A j' :=
  (@asIso _ _ _ _ (singleBetaInv A gU j' j g h)
    (singleBetaInv_isIso A gU j' j g h hsq)).symm

/-- The scalar identification on the source of open exchange.
Source: Stacks Tags 03DI and 03CY
(blueprint: lem-cbc-finite-open-exchange-scalars). -/
def sourceRes [Finite B] [Finite C] (a : B →+* C)
    {U X' X : Scheme.{u}} (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j] :
    res a U ⋙ (moduleJ B j ⋙ modulePullback B g) ≅
      (moduleJ C j ⋙ modulePullback C g) ⋙ res a X' :=
  (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (openRes a j) _ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (pullRes a g) ≪≫
    (Functor.associator _ _ _).symm

/-- The scalar identification on the target of open exchange.
Source: Stacks Tags 03DI and 03CY
(blueprint: lem-cbc-finite-open-exchange-scalars). -/
def targetRes [Finite B] [Finite C] (a : B →+* C)
    {U' U X' : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X') [IsOpenImmersion j'] :
    res a U ⋙ (modulePullback B gU ⋙ moduleJ B j') ≅
      (modulePullback C gU ⋙ moduleJ C j') ⋙ res a X' :=
  (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (pullRes a gU) _ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (openRes a j') ≪≫
    (Functor.associator _ _ _).symm

/-- Scalar restriction on unbounded complexes, with all terms and differentials retained.
Source: blueprint finite exchange paragraph
(blueprint: lem-cbc-finite-open-exchange-scalars). -/
abbrev resC (a : B →+* C) (X : Scheme.{u}) :
    CochainComplex (Modules C X) ℤ ⥤ CochainComplex (Modules B X) ℤ :=
  (res a X).mapHomologicalComplex (.up ℤ)

/-- The complex-level exchange, from the recorded sheaf exchange term by term.
Source: Stacks Tag 09AE (blueprint: lem-cbc-finite-open-exchange-scalars). -/
def betaC (A : Type (u + 1)) [CommRing A] [Finite A]
    {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j] [IsOpenImmersion j']
    (h : gU ≫ j = j' ≫ g) (hsq : IsPullback gU j' j g) :
    (moduleJ A j ⋙ modulePullback A g).mapHomologicalComplex (.up ℤ) ≅
      (modulePullback A gU ⋙ moduleJ A j').mapHomologicalComplex (.up ℤ) :=
  NatIso.mapHomologicalComplex (beta A gU j' j g h hsq) (.up ℤ)

/-- The source identification on complexes.
Source: blueprint finite exchange paragraph
(blueprint: lem-cbc-finite-open-exchange-scalars). -/
def sourceResC [Finite B] [Finite C] (a : B →+* C)
    {U X' X : Scheme.{u}} (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j] :
    (res a U ⋙ (moduleJ B j ⋙ modulePullback B g)).mapHomologicalComplex (.up ℤ) ≅
      ((moduleJ C j ⋙ modulePullback C g) ⋙ res a X').mapHomologicalComplex (.up ℤ) :=
  NatIso.mapHomologicalComplex (sourceRes a j g) (.up ℤ)

/-- The target identification on complexes.
Source: blueprint finite exchange paragraph
(blueprint: lem-cbc-finite-open-exchange-scalars). -/
def targetResC [Finite B] [Finite C] (a : B →+* C)
    {U' U X' : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X') [IsOpenImmersion j'] :
    (res a U ⋙ (modulePullback B gU ⋙ moduleJ B j')).mapHomologicalComplex (.up ℤ) ≅
      ((modulePullback C gU ⋙ moduleJ C j') ⋙ res a X').mapHomologicalComplex (.up ℤ) :=
  NatIso.mapHomologicalComplex (targetRes a gU j') (.up ℤ)

/-- Degreewise scalar exchange for the finite open comparison.
Source: the finite open exchange argument, before lifting to cochain complexes
(blueprint: lem-cbc-finite-open-exchange-scalars).
Proof: unfold the termwise scalar restriction, source and target identifications, and the
finite open Beck--Chevalley comparison. The coefficient square and mate-unit equations
identify the two composites; uniqueness of adjunction mates gives the displayed equality.
(blueprint: lem-cbc-finite-open-exchange-scalars-component) -/
theorem exchange_restrictScalars_component [Finite B] [Finite C] (a : B →+* C)
    {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j] [IsOpenImmersion j']
    (h : gU ≫ j = j' ≫ g) (hsq : IsPullback gU j' j g)
    (M : Modules C U) :
    (sourceRes a j g).hom.app M ≫
        (res a X').map ((beta C gU j' j g h hsq).hom.app M) =
      (beta B gU j' j g h hsq).hom.app ((res a U).obj M) ≫
        (targetRes a gU j').hom.app M := by
  sorry

/-- Restriction carries the finite C-exchange to the finite B-exchange, for every complex.
Source: blueprint finite exchange paragraph; Stacks Tags 03DI and 03CY
(blueprint: lem-cbc-finite-open-exchange-scalars).
Proof: the coefficient square preserves constants. Pullback and extension scalar
comparisons preserve the units and counits. The recorded inverse exchange is the
transpose of the pulled-back open unit and the site-composition comparison. Restricting
this formula gives the B-formula, so uniqueness of adjuncts gives equality of inverses
and then equality of exchanges. Apply the equality degreewise; naturality supplies
compatibility with all differentials and chain maps. -/
theorem exchange_restrictScalars [Finite B] [Finite C] (a : B →+* C)
    {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j] [IsOpenImmersion j']
    (h : gU ≫ j = j' ≫ g) (hsq : IsPullback gU j' j g)
    (F : CochainComplex (Modules C U) ℤ) :
    (sourceResC a j g).hom.app F ≫
        (resC a X').map ((betaC C gU j' j g h hsq).hom.app F) =
      (betaC B gU j' j g h hsq).hom.app ((resC a U).obj F) ≫
        (targetResC a gU j').hom.app F := by
  ext i V x
  change (((sourceRes a j g).hom.app (F.X i)) ≫
      (res a X').map ((beta C gU j' j g h hsq).hom.app (F.X i))).val.app V x =
    (((beta B gU j' j g h hsq).hom.app ((res a U).obj (F.X i))) ≫
      (targetRes a gU j').hom.app (F.X i)).val.app V x
  exact congrArg (fun z ↦ z.val.app V x)
    (exchange_restrictScalars_component a gU j' j g h hsq (F.X i))

set_option backward.isDefEq.respectTransparency false in
/-- Scalar restriction preserves the specified open unit and counit.
Source: Stacks Tag 03DI, explicit summand adjunction
(blueprint: lem-cbc-finite-open-exchange-scalars).
Proof: the pullback comparison is the mate of identity on sections. The open comparison
is its mate under extension/restriction. The two mate equations are exactly the unit
and counit identities below; alternatively the summand formulas send s to the same s
before and after restriction of scalars. These identities hold in each complex degree. -/
theorem open_unit_counit [Finite B] [Finite C] (a : B →+* C)
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (∀ F : Modules C U,
      (moduleJAdj B j).unit.app ((res a U).obj F) ≫
          (modulePullback B j).map ((openRes a j).hom.app F) ≫
          (pullRes a j).hom.app ((moduleJ C j).obj F) =
        (res a U).map ((moduleJAdj C j).unit.app F)) ∧
    (∀ N : Modules C X,
      (openRes a j).hom.app ((modulePullback C j).obj N) ≫
          (res a X).map ((moduleJAdj C j).counit.app N) =
        (moduleJ B j).map ((pullRes a j).inv.app N) ≫
          (moduleJAdj B j).counit.app ((res a X).obj N)) := by
  constructor
  · intro F
    exact mate_unit_iso (moduleJAdj C j) (moduleJAdj B j) (pullRes a j).symm F
  · intro N
    exact (mateEquiv_counit_symm (moduleJAdj C j) (moduleJAdj B j)
      (TwoSquare.mk _ _ _ _ (pullRes a j).inv) N).symm

/-- Scalar restriction preserves the inverse-image/direct-image unit and counit.
Source: Stacks Tags 03D2 and 03CY
(blueprint: lem-cbc-finite-open-exchange-scalars).
Proof: direct image comparison is the identity on sections. The pullback comparison
was defined as its mate using the normalized module adjunctions. The mate unit and
counit equations give the two equalities; all constructions are applied degreewise. -/
theorem pull_unit_counit [Finite B] [Finite C] (a : B →+* C)
    {Y X : Scheme.{u}} (f : Y ⟶ X) :
    (∀ F : Modules C X,
      (res a X).map ((Scheme.proEtaleRingModuleAdjunction f
          (coefficients C X) (coefficients C Y) (constantRingIso C f)).unit.app F) ≫
          (pushRes a f).hom.app ((modulePullback C f).obj F) =
        (Scheme.proEtaleRingModuleAdjunction f
          (coefficients B X) (coefficients B Y) (constantRingIso B f)).unit.app
            ((res a X).obj F) ≫
          (moduleDirectImage B f).map ((pullRes a f).hom.app F)) ∧
    (∀ N : Modules C Y,
      (pullRes a f).hom.app ((moduleDirectImage C f).obj N) ≫
          (res a Y).map ((Scheme.proEtaleRingModuleAdjunction f
            (coefficients C X) (coefficients C Y) (constantRingIso C f)).counit.app N) =
        (modulePullback B f).map ((pushRes a f).hom.app N) ≫
          (Scheme.proEtaleRingModuleAdjunction f
            (coefficients B X) (coefficients B Y) (constantRingIso B f)).counit.app
              ((res a Y).obj N)) := by
  let adjC := Scheme.proEtaleRingModuleAdjunction f
    (coefficients C X) (coefficients C Y) (constantRingIso C f)
  let adjB := Scheme.proEtaleRingModuleAdjunction f
    (coefficients B X) (coefficients B Y) (constantRingIso B f)
  have hm := pullRes_mate a f
  constructor
  · intro F
    have hu := unit_mateEquiv adjC adjB (TwoSquare.mk _ _ _ _ (pullRes a f).hom) F
    change (res a X).map (adjC.unit.app F) ≫
      ((mateEquiv adjC adjB (TwoSquare.mk _ _ _ _ (pullRes a f).hom)).natTrans).app _ =
        adjB.unit.app _ ≫ (moduleDirectImage B f).map ((pullRes a f).hom.app F) at hu
    rw [hm] at hu
    exact hu
  · intro N
    have hc := mateEquiv_counit adjC adjB
      (TwoSquare.mk _ _ _ _ (pullRes a f).hom) N
    change (modulePullback B f).map
      ((mateEquiv adjC adjB (TwoSquare.mk _ _ _ _ (pullRes a f).hom)).natTrans.app N) ≫
        adjB.counit.app _ = (pullRes a f).hom.app _ ≫
          (res a Y).map (adjC.counit.app N) at hc
    rw [hm] at hc
    exact hc.symm

/-- The inverse exchange is the specified pulled-back open-unit transpose in every degree.
Source: Stacks Tag 09AE and the blueprint's inverse-mate normalization
(blueprint: lem-cbc-finite-open-exchange-scalars).
Proof: the recorded singleBetaInvApp is defined by exactly this adjunction transpose.
The inverse of beta is that recorded natural transformation. Mapping it termwise
retains its components, giving the equality for every integer degree. -/
theorem inverse_unit_transpose (A : Type (u + 1)) [CommRing A] [Finite A]
    {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j] [IsOpenImmersion j']
    (h : gU ≫ j = j' ≫ g) (hsq : IsPullback gU j' j g)
    (F : CochainComplex (Modules A U) ℤ) (i : ℤ) :
    ((betaC A gU j' j g h hsq).inv.app F).f i =
      ((moduleJAdj A j').homEquiv _ _).symm
        ((modulePullback A gU).map ((moduleJAdj A j).unit.app (F.X i)) ≫
          (moduleSquareG A gU j' j g h).inv.app ((moduleJ A j).obj (F.X i))) := by
  change (singleBetaInv A gU j' j g h).app (F.X i) = _
  rfl

/-- Every semilinear chain map commutes with the exchange and its inverse.
This includes successive strict tower transitions and every composite transition.
Source: blueprint finite exchange paragraph
(blueprint: lem-cbc-finite-open-exchange-scalars).
Proof: apply naturality of beta and its inverse to the strict B-linear map t.
Use exchange_restrictScalars at G and its inverse square to replace the restricted
C-exchange. Composition gives both displayed commuting squares without homotopy. -/
theorem exchange_transition [Finite B] [Finite C] (a : B →+* C)
    {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j] [IsOpenImmersion j']
    (h : gU ≫ j = j' ≫ g) (hsq : IsPullback gU j' j g)
    (F : CochainComplex (Modules B U) ℤ) (G : CochainComplex (Modules C U) ℤ)
    (t : F ⟶ (resC a U).obj G) :
    ((moduleJ B j ⋙ modulePullback B g).mapHomologicalComplex (.up ℤ)).map t ≫
          (sourceResC a j g).hom.app G ≫
          (resC a X').map ((betaC C gU j' j g h hsq).hom.app G) =
        (betaC B gU j' j g h hsq).hom.app F ≫
          ((modulePullback B gU ⋙ moduleJ B j').mapHomologicalComplex (.up ℤ)).map t ≫
          (targetResC a gU j').hom.app G ∧
    ((modulePullback B gU ⋙ moduleJ B j').mapHomologicalComplex (.up ℤ)).map t ≫
          (targetResC a gU j').hom.app G ≫
          (resC a X').map ((betaC C gU j' j g h hsq).inv.app G) =
        (betaC B gU j' j g h hsq).inv.app F ≫
          ((moduleJ B j ⋙ modulePullback B g).mapHomologicalComplex (.up ℤ)).map t ≫
          (sourceResC a j g).hom.app G := by
  have he := exchange_restrictScalars a gU j' j g h hsq G
  have hi : (targetResC a gU j').hom.app G ≫
      (resC a X').map ((betaC C gU j' j g h hsq).inv.app G) =
      (betaC B gU j' j g h hsq).inv.app ((resC a U).obj G) ≫
        (sourceResC a j g).hom.app G := by
    apply (cancel_epi ((betaC B gU j' j g h hsq).hom.app ((resC a U).obj G))).mp
    rw [← Category.assoc, ← he]
    simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app,
      Iso.hom_inv_id_app_assoc]
    exact Category.comp_id _
  constructor
  · rw [he, ← Category.assoc, (betaC B gU j' j g h hsq).hom.naturality t,
      Category.assoc]
  · rw [hi, ← Category.assoc, (betaC B gU j' j g h hsq).inv.naturality t,
      Category.assoc]

/-- Restriction along the identity has its unique identity-on-sections identification.
Source: Stacks Tag 03CY (blueprint: lem-cbc-finite-open-exchange-scalars).
Proof: identity scalar restriction leaves the action unchanged. Identity section maps
are linear and natural, and their inverses are identical. Sections determine uniqueness. -/
theorem resId_existsUnique (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    ∃! e : res (RingHom.id A) X ≅ 𝟭 (Modules A X),
      ∀ (M : Modules A X) (W : X.ProEtᵒᵖ) (m : M.val.obj W),
        (e.hom.app M).val.app W m = m := by
  have hid : ringCoefficientMap (RingHom.id A) X = 𝟙 _ := by
    change (sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map (𝟙 _)) = _
    exact (congrArg (fun k ↦ (sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map k)
      ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map_id
        (CommRingCat.of A))).trans
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map_id _)
  let e : res (RingHom.id A) X ≅ 𝟭 (Modules A X) :=
    NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun W ↦
        ModuleCat.restrictScalarsId'App _
          (congrArg (fun k ↦ (k.hom.app W).hom) hid) (M.val.obj W)) (by
        intro W W' f
        ext m
        rfl))) (by
      intro M N f
      apply SheafOfModules.hom_ext
      apply PresheafOfModules.hom_ext
      intro W
      ext m
      rfl)
  refine ⟨e, fun _ _ _ ↦ rfl, ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  ext m
  exact he' M W m

/-- The identity-on-sections identification for identity restriction.
Source: Stacks Tag 03CY (blueprint: lem-cbc-finite-open-exchange-scalars). -/
def resId (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    res (RingHom.id A) X ≅ 𝟭 (Modules A X) :=
  Classical.choose (resId_existsUnique A X)

/-- Compatible ambient coefficient actions give a unique identity-on-sections comparison.
Source: Stacks Tag 03CY (blueprint: lem-cbc-finite-open-exchange-scalars).
Proof: the equation on ring maps says the two restricted actions agree. Identity on
every section is therefore linear, natural, and its own inverse. Sectionwise faithfulness
makes the resulting natural isomorphism unique. -/
theorem ambientRes_existsUnique (a : B →+* C) (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) RingCat.{u + 1})
    (rB : R ⟶ ringCoefficients B X) (rC : R ⟶ ringCoefficients C X)
    (hr : rB ≫ ringCoefficientMap a X = rC) :
    ∃! e : res a X ⋙ SheafOfModules.restrictScalars.{u + 1} rB ≅
        SheafOfModules.restrictScalars.{u + 1} rC,
      ∀ (M : Modules C X) (W : X.ProEtᵒᵖ) (m : M.val.obj W),
        (e.hom.app M).val.app W m = m := by
  let e : res a X ⋙ SheafOfModules.restrictScalars.{u + 1} rB ≅
      SheafOfModules.restrictScalars.{u + 1} rC :=
    NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun W ↦
        (ModuleCat.restrictScalarsComp'App (rB.hom.app W).hom
          ((ringCoefficientMap a X).hom.app W).hom (rC.hom.app W).hom
          (congrArg (fun k ↦ (k.hom.app W).hom) hr.symm) (M.val.obj W)).symm) (by
        intro W W' f
        ext m
        rfl))) (by
      intro M N f
      apply SheafOfModules.hom_ext
      apply PresheafOfModules.hom_ext
      intro W
      ext m
      rfl)
  refine ⟨e, fun _ _ _ ↦ rfl, ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  ext m
  exact he' M W m

/-- The fixed comparison for restriction to compatible ambient actions.
Source: Stacks Tag 03CY (blueprint: lem-cbc-finite-open-exchange-scalars). -/
def ambientRes (a : B →+* C) (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) RingCat.{u + 1})
    (rB : R ⟶ ringCoefficients B X) (rC : R ⟶ ringCoefficients C X)
    (hr : rB ≫ ringCoefficientMap a X = rC) :
    res a X ⋙ SheafOfModules.restrictScalars.{u + 1} rB ≅
      SheafOfModules.restrictScalars.{u + 1} rC :=
  Classical.choose (ambientRes_existsUnique a X R rB rC hr)

/-- Constant coefficient maps respect composition.
Source: Stacks Tag 03CY (blueprint: lem-cbc-finite-open-exchange-scalars).
Proof: this is functoriality of constant-sheaf sheafification on ring maps. -/
theorem coefficientMap_comp {D : Type (u + 1)} [CommRing D]
    (a : B →+* C) (b : C →+* D) (X : Scheme.{u}) :
    ringCoefficientMap a X ≫ ringCoefficientMap b X = ringCoefficientMap (b.comp a) X := by
  change (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map _ ≫
      (sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map _ = _
  rw [← Functor.map_comp, ← Functor.map_comp]
  rfl

/-- The identity-on-sections comparison between successive and composite restriction.
Source: Stacks Tag 03CY (blueprint: lem-cbc-finite-open-exchange-scalars). -/
def resComp {D : Type (u + 1)} [CommRing D] (a : B →+* C) (b : C →+* D)
    (X : Scheme.{u}) : res b X ⋙ res a X ≅ res (b.comp a) X :=
  ambientRes b X (ringCoefficients B X) (ringCoefficientMap a X)
    (ringCoefficientMap (b.comp a) X)
    (coefficientMap_comp a b X)

section

set_option backward.isDefEq.respectTransparency false

private theorem resId_apply (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})
    (M : Modules A X) (W : X.ProEtᵒᵖ) (m : M.val.obj W) :
    ((resId A X).hom.app M).val.app W m = m :=
  (Classical.choose_spec (resId_existsUnique A X)).1 M W m

private theorem pushRes_apply {B C : Type (u + 1)} [CommRing B] [CommRing C]
    (a : B →+* C) {Y X : Scheme.{u}} (f : Y ⟶ X) (N : Modules C Y)
    (W : X.ProEtᵒᵖ) (m : N.val.obj ((Scheme.proEtaleBaseChange f).op.obj W)) :
    ((pushRes a f).hom.app N).val.app W m = m :=
  (Classical.choose_spec (Scheme.proEtaleRingRestrictionDirectImage_existsUnique f
    (coefficients B X) (coefficients C X) (coefficients B Y) (coefficients C Y)
    (coefficientMap a X) (coefficientMap a Y) (constantRingIso B f) (constantRingIso C f)
    (coefficientSquare a f))).1 N W m

private theorem push_identity (A : Type (u + 1)) [CommRing A]
    {Y X : Scheme.{u}} (f : Y ⟶ X) (N : Modules A Y) :
    (pushRes (RingHom.id A) f).hom.app N ≫
        (moduleDirectImage A f).map ((resId A Y).hom.app N) =
      (resId A X).hom.app ((moduleDirectImage A f).obj N) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  ext m
  change ((resId A Y).hom.app N).val.app ((Scheme.proEtaleBaseChange f).op.obj W)
    (((pushRes (RingHom.id A) f).hom.app N).val.app W m) = _
  rw [pushRes_apply, resId_apply]
  exact (resId_apply A X ((moduleDirectImage A f).obj N) W m).symm

private theorem left_square_identity
    {D E : Type*} [Category D] [Category E]
    {L : D ⥤ E} {R : E ⥤ D} (adj : L ⊣ R)
    {G : D ⥤ D} {H : E ⥤ E} (eG : G ⟶ 𝟭 D) (eH : H ⟶ 𝟭 E)
    (p : G ⋙ L ⟶ L ⋙ H) (d : R ⋙ G ⟶ H ⋙ R)
    (hu : ∀ M, G.map (adj.unit.app M) ≫ d.app (L.obj M) =
      adj.unit.app (G.obj M) ≫ R.map (p.app M))
    (hd : ∀ N, d.app N ≫ R.map (eH.app N) = eG.app (R.obj N)) (M : D) :
    p.app M ≫ eH.app (L.obj M) = L.map (eG.app M) := by
  apply (adj.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  rw [← Category.assoc, ← hu, Category.assoc, hd]
  exact (eG.naturality (adj.unit.app M)).trans (adj.unit.naturality (eG.app M))

private theorem pull_identity_aux (A : Type (u + 1)) [CommRing A] [Finite A]
    {Y X : Scheme.{u}} (f : Y ⟶ X) (M : Modules A X) :
    (pullRes (RingHom.id A) f).hom.app M ≫
        (resId A Y).hom.app ((modulePullback A f).obj M) =
      (modulePullback A f).map ((resId A X).hom.app M) := by
  exact left_square_identity (Scheme.proEtaleRingModuleAdjunction f
    (coefficients A X) (coefficients A Y) (constantRingIso A f))
    (resId A X).hom (resId A Y).hom (pullRes (RingHom.id A) f).hom
    (pushRes (RingHom.id A) f).hom
    (pull_unit_counit (RingHom.id A) f).1 (push_identity A f) M

/-- The canonical inverse-image and extension scalar identifications preserve identities.
Source: Stacks Tags 03D2 and 03DI
(blueprint: lem-cbc-finite-open-exchange-scalars).
Proof: the identity-on-sections direct-image comparison is the identity after resId.
Uniqueness of the unit-preserving mate gives the pullback equality. Transposing that
equality under the two open adjunctions gives the extension equality. -/
theorem scalar_identity (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (∀ M : Modules A X,
      (pullRes (RingHom.id A) j).hom.app M ≫
          (resId A U).hom.app ((modulePullback A j).obj M) =
        (modulePullback A j).map ((resId A X).hom.app M)) ∧
    (∀ F : Modules A U,
      (openRes (RingHom.id A) j).hom.app F ≫
          (resId A X).hom.app ((moduleJ A j).obj F) =
        (moduleJ A j).map ((resId A U).hom.app F)) := by
  constructor
  · exact pull_identity_aux A j
  · intro F
    apply left_square_identity (moduleJAdj A j)
      (resId A U).hom (resId A X).hom (openRes (RingHom.id A) j).hom
      (pullRes (RingHom.id A) j).inv
    · intro M
      exact unit_mateEquiv_symm (moduleJAdj A j) (moduleJAdj A j)
        (TwoSquare.mk _ _ _ _ (pullRes (RingHom.id A) j).inv) M
    · intro N
      apply (cancel_epi ((pullRes (RingHom.id A) j).hom.app N)).mp
      simpa only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp] using
        (pull_identity_aux A j N).symm

end

set_option backward.isDefEq.respectTransparency false in
private theorem left_square_composition
    {D₁ D₂ D₃ E₁ E₂ E₃ : Type*}
    [Category D₁] [Category D₂] [Category D₃]
    [Category E₁] [Category E₂] [Category E₃]
    {L₁ : D₁ ⥤ E₁} {R₁ : E₁ ⥤ D₁}
    {L₂ : D₂ ⥤ E₂} {R₂ : E₂ ⥤ D₂}
    {L₃ : D₃ ⥤ E₃} {R₃ : E₃ ⥤ D₃}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃)
    {G₁ : D₁ ⥤ D₂} {G₂ : D₂ ⥤ D₃} {G₃ : D₁ ⥤ D₃}
    {H₁ : E₁ ⥤ E₂} {H₂ : E₂ ⥤ E₃} {H₃ : E₁ ⥤ E₃}
    (eG : G₁ ⋙ G₂ ≅ G₃) (eH : H₁ ⋙ H₂ ≅ H₃)
    (p₁ : G₁ ⋙ L₂ ⟶ L₁ ⋙ H₁) (p₂ : G₂ ⋙ L₃ ⟶ L₂ ⋙ H₂)
    (p₃ : G₃ ⋙ L₃ ⟶ L₁ ⋙ H₃)
    (d₁ : R₁ ⋙ G₁ ⟶ H₁ ⋙ R₂) (d₂ : R₂ ⋙ G₂ ⟶ H₂ ⋙ R₃)
    (d₃ : R₁ ⋙ G₃ ⟶ H₃ ⋙ R₃)
    (hu₁ : ∀ M, G₁.map (adj₁.unit.app M) ≫ d₁.app (L₁.obj M) =
      adj₂.unit.app (G₁.obj M) ≫ R₂.map (p₁.app M))
    (hu₂ : ∀ M, G₂.map (adj₂.unit.app M) ≫ d₂.app (L₂.obj M) =
      adj₃.unit.app (G₂.obj M) ≫ R₃.map (p₂.app M))
    (hu₃ : ∀ M, G₃.map (adj₁.unit.app M) ≫ d₃.app (L₁.obj M) =
      adj₃.unit.app (G₃.obj M) ≫ R₃.map (p₃.app M))
    (hd : ∀ N, G₂.map (d₁.app N) ≫ d₂.app (H₁.obj N) ≫ R₃.map (eH.hom.app N) =
      eG.hom.app (R₁.obj N) ≫ d₃.app N) (M : D₁) :
    L₃.map (eG.inv.app M) ≫ p₂.app (G₁.obj M) ≫ H₂.map (p₁.app M) ≫
        eH.hom.app (L₁.obj M) = p₃.app M := by
  apply (cancel_epi (L₃.map (eG.hom.app M))).mp
  simp only [← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp]
  apply (adj₃.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Functor.comp_obj, Category.assoc]
  simp only [← Category.assoc]
  rw [← hu₂ (G₁.obj M)]
  simp only [Category.assoc]
  have hn := NatTrans.naturality_assoc d₂ (p₁.app M)
    (R₃.map (eH.hom.app (L₁.obj M)))
  dsimp only [Functor.comp_obj, Functor.comp_map] at hn
  rw [← hn]
  simp only [← Category.assoc, ← Functor.map_comp]
  rw [← hu₁ M]
  simp only [Functor.map_comp, Category.assoc]
  rw [hd, ← Category.assoc]
  have he := eG.hom.naturality (adj₁.unit.app M)
  dsimp only [Functor.comp_obj, Functor.comp_map] at he
  rw [he]
  simp only [Category.assoc]
  rw [hu₃]
  have ha := adj₃.unit.naturality (eG.hom.app M)
  dsimp only [Functor.id_map, Functor.comp_map] at ha
  simpa only [Functor.id_obj, Functor.comp_obj, Category.assoc] using
    congrArg (fun k ↦ k ≫ R₃.map (p₃.app M)) ha

set_option backward.isDefEq.respectTransparency false in
private theorem resComp_apply {D : Type (u + 1)} [CommRing D]
    (a : B →+* C) (b : C →+* D) (X : Scheme.{u})
    (M : Modules D X) (W : X.ProEtᵒᵖ) (m : M.val.obj W) :
    ((resComp a b X).hom.app M).val.app W m = m :=
  (Classical.choose_spec (ambientRes_existsUnique b X (ringCoefficients B X)
    (ringCoefficientMap a X) (ringCoefficientMap (b.comp a) X)
    (coefficientMap_comp a b X))).1 M W m

set_option backward.isDefEq.respectTransparency false in
private theorem push_composition {D : Type (u + 1)} [CommRing D]
    (a : B →+* C) (b : C →+* D) {Y X : Scheme.{u}} (f : Y ⟶ X)
    (N : Modules D Y) :
    (res a X).map ((pushRes b f).hom.app N) ≫
        (pushRes a f).hom.app ((res b Y).obj N) ≫
        (moduleDirectImage B f).map ((resComp a b Y).hom.app N) =
      (resComp a b X).hom.app ((moduleDirectImage D f).obj N) ≫
        (pushRes (b.comp a) f).hom.app N := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  ext m
  change ((resComp a b Y).hom.app N).val.app
      ((Scheme.proEtaleBaseChange f).op.obj W)
      (((pushRes a f).hom.app ((res b Y).obj N)).val.app W
        (((pushRes b f).hom.app N).val.app W m)) =
    ((pushRes (b.comp a) f).hom.app N).val.app W
      (((resComp a b X).hom.app ((moduleDirectImage D f).obj N)).val.app W m)
  simp only [resComp_apply, pushRes_apply]

set_option backward.isDefEq.respectTransparency false in
private theorem pull_composition_aux {D : Type (u + 1)} [CommRing D]
    [Finite B] [Finite C] [Finite D] (a : B →+* C) (b : C →+* D)
    {Y X : Scheme.{u}} (f : Y ⟶ X) (M : Modules D X) :
    (modulePullback B f).map ((resComp a b X).inv.app M) ≫
        (pullRes a f).hom.app ((res b X).obj M) ≫
        (res a Y).map ((pullRes b f).hom.app M) ≫
        (resComp a b Y).hom.app ((modulePullback D f).obj M) =
      (pullRes (b.comp a) f).hom.app M := by
  exact left_square_composition
    (Scheme.proEtaleRingModuleAdjunction f
      (coefficients D X) (coefficients D Y) (constantRingIso D f))
    (Scheme.proEtaleRingModuleAdjunction f
      (coefficients C X) (coefficients C Y) (constantRingIso C f))
    (Scheme.proEtaleRingModuleAdjunction f
      (coefficients B X) (coefficients B Y) (constantRingIso B f))
    (resComp a b X) (resComp a b Y)
    (pullRes b f).hom (pullRes a f).hom (pullRes (b.comp a) f).hom
    (pushRes b f).hom (pushRes a f).hom (pushRes (b.comp a) f).hom
    (pull_unit_counit b f).1 (pull_unit_counit a f).1
    (pull_unit_counit (b.comp a) f).1 (push_composition a b f) M

/-- Pullback and open-extension identifications compose along arbitrary coefficient maps.
Source: Stacks Tags 03D2 and 03DI
(blueprint: lem-cbc-finite-open-exchange-scalars).
Proof: all direct-image scalar identifications are identity on sections, so their
composite is the identity for the composite ring map under resComp. Mate pasting gives
the pullback equality; mate pasting once more under the open adjunctions gives the
extension equality. Applying degreewise gives the same identities for chain maps. -/
theorem scalar_composition {D : Type (u + 1)} [CommRing D]
    [Finite B] [Finite C] [Finite D] (a : B →+* C) (b : C →+* D)
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (∀ M : Modules D X,
      (modulePullback B j).map ((resComp a b X).inv.app M) ≫
          (pullRes a j).hom.app ((res b X).obj M) ≫
          (res a U).map ((pullRes b j).hom.app M) ≫
          (resComp a b U).hom.app ((modulePullback D j).obj M) =
        (pullRes (b.comp a) j).hom.app M) ∧
    (∀ F : Modules D U,
      (moduleJ B j).map ((resComp a b U).inv.app F) ≫
          (openRes a j).hom.app ((res b U).obj F) ≫
          (res a X).map ((openRes b j).hom.app F) ≫
          (resComp a b X).hom.app ((moduleJ D j).obj F) =
        (openRes (b.comp a) j).hom.app F) := by
  constructor
  · exact pull_composition_aux a b j
  · intro F
    apply left_square_composition (moduleJAdj D j) (moduleJAdj C j) (moduleJAdj B j)
      (resComp a b U) (resComp a b X)
      (openRes b j).hom (openRes a j).hom (openRes (b.comp a) j).hom
      (pullRes b j).inv (pullRes a j).inv (pullRes (b.comp a) j).inv
    · intro M
      exact unit_mateEquiv_symm (moduleJAdj D j) (moduleJAdj C j)
        (TwoSquare.mk _ _ _ _ (pullRes b j).inv) M
    · intro M
      exact unit_mateEquiv_symm (moduleJAdj C j) (moduleJAdj B j)
        (TwoSquare.mk _ _ _ _ (pullRes a j).inv) M
    · intro M
      exact unit_mateEquiv_symm (moduleJAdj D j) (moduleJAdj B j)
        (TwoSquare.mk _ _ _ _ (pullRes (b.comp a) j).inv) M
    · intro N
      apply (cancel_mono ((pullRes (b.comp a) j).hom.app N)).mp
      simp only [Category.assoc, Iso.inv_hom_id_app]
      conv_lhs => rw [← pull_composition_aux a b j N]
      simp only [Functor.comp_obj]
      slice_lhs 3 4 =>
        rw [← Functor.map_comp, Iso.hom_inv_id_app]
        erw [CategoryTheory.Functor.map_id]
      simp only [Category.id_comp, Category.assoc, Iso.inv_hom_id_app_assoc]
      slice_lhs 1 2 =>
        rw [← Functor.map_comp, Iso.inv_hom_id_app]
        erw [CategoryTheory.Functor.map_id]
      simp only [Category.id_comp, Category.comp_id]




/-- Pullback scalar identifications preserve the identity for arbitrary scheme maps.
Source: Stacks Tags 03D2 and 03CY
(blueprint: lem-cbc-finite-open-exchange-scalars).
Proof: the direct-image comparison is identity on every section after the identity
restriction comparison. Uniqueness of its adjunction mate gives this equation. -/
theorem pull_identity (A : Type (u + 1)) [CommRing A] [Finite A]
    {Y X : Scheme.{u}} (f : Y ⟶ X) (M : Modules A X) :
    (pullRes (RingHom.id A) f).hom.app M ≫
        (resId A Y).hom.app ((modulePullback A f).obj M) =
      (modulePullback A f).map ((resId A X).hom.app M) := by
  exact pull_identity_aux A f M

/-- Pullback scalar identifications compose for arbitrary scheme maps.
Source: Stacks Tags 03D2 and 03CY
(blueprint: lem-cbc-finite-open-exchange-scalars).
Proof: the successive direct-image identifications are identity on sections, hence
compose to the comparison for b composed with a. The adjunction mate pastes,
and resComp gives precisely the identity identifications at the two ends. -/
theorem pull_composition {D : Type (u + 1)} [CommRing D]
    [Finite B] [Finite C] [Finite D] (a : B →+* C) (b : C →+* D)
    {Y X : Scheme.{u}} (f : Y ⟶ X) (M : Modules D X) :
    (modulePullback B f).map ((resComp a b X).inv.app M) ≫
        (pullRes a f).hom.app ((res b X).obj M) ≫
        (res a Y).map ((pullRes b f).hom.app M) ≫
        (resComp a b Y).hom.app ((modulePullback D f).obj M) =
      (pullRes (b.comp a) f).hom.app M := by
  exact pull_composition_aux a b f M

/-- Forgetting the constant-ring action, using Mathlib's module-sheaf forgetful functor.
Source: Stacks Tag 03CY (blueprint: lem-cbc-finite-open-exchange-scalars). -/
abbrev forgetModules (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    Modules A X ⥤ Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} :=
  SheafOfModules.toSheaf _

/-- Restricting scalars leaves the underlying abelian sheaf literally unchanged.
Source: Stacks Tag 03CY (blueprint: lem-cbc-finite-open-exchange-scalars). -/
def resForget (a : B →+* C) (X : Scheme.{u}) :
    res a X ⋙ forgetModules B X ≅ forgetModules C X := Iso.refl _

/-- The source transition on underlying abelian sheaf complexes, with the canonical
scalar identification included. Source: blueprint strict transition assertion
(blueprint: lem-cbc-finite-open-exchange-scalars). -/
def sourceStep [Finite B] [Finite C] (a : B →+* C)
    {U X' X : Scheme.{u}} (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j]
    (F : CochainComplex (Modules B U) ℤ) (G : CochainComplex (Modules C U) ℤ)
    (t : F ⟶ (resC a U).obj G) :
    ((forgetModules B X').mapHomologicalComplex (.up ℤ)).obj
        (((moduleJ B j ⋙ modulePullback B g).mapHomologicalComplex (.up ℤ)).obj F) ⟶
      ((forgetModules C X').mapHomologicalComplex (.up ℤ)).obj
        (((moduleJ C j ⋙ modulePullback C g).mapHomologicalComplex (.up ℤ)).obj G) :=
  ((forgetModules B X').mapHomologicalComplex (.up ℤ)).map
    (((moduleJ B j ⋙ modulePullback B g).mapHomologicalComplex (.up ℤ)).map t ≫
      (sourceResC a j g).hom.app G) ≫
    (NatIso.mapHomologicalComplex (resForget a X') (.up ℤ)).hom.app
      (((moduleJ C j ⋙ modulePullback C g).mapHomologicalComplex (.up ℤ)).obj G)

/-- The target transition on underlying abelian sheaf complexes.
Source: blueprint strict transition assertion
(blueprint: lem-cbc-finite-open-exchange-scalars). -/
def targetStep [Finite B] [Finite C] (a : B →+* C)
    {U' U X' : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X') [IsOpenImmersion j']
    (F : CochainComplex (Modules B U) ℤ) (G : CochainComplex (Modules C U) ℤ)
    (t : F ⟶ (resC a U).obj G) :
    ((forgetModules B X').mapHomologicalComplex (.up ℤ)).obj
        (((modulePullback B gU ⋙ moduleJ B j').mapHomologicalComplex (.up ℤ)).obj F) ⟶
      ((forgetModules C X').mapHomologicalComplex (.up ℤ)).obj
        (((modulePullback C gU ⋙ moduleJ C j').mapHomologicalComplex (.up ℤ)).obj G) :=
  ((forgetModules B X').mapHomologicalComplex (.up ℤ)).map
    (((modulePullback B gU ⋙ moduleJ B j').mapHomologicalComplex (.up ℤ)).map t ≫
      (targetResC a gU j').hom.app G) ≫
    (NatIso.mapHomologicalComplex (resForget a X') (.up ℤ)).hom.app
      (((modulePullback C gU ⋙ moduleJ C j').mapHomologicalComplex (.up ℤ)).obj G)

section

attribute [local irreducible] sourceStep targetStep sourceResC targetResC betaC
  sourceRes targetRes openRes pullRes pushRes beta openResMap

set_option backward.isDefEq.respectTransparency false in
/-- Finite exchanges and their inverses form inverse maps of the actual strict towers.
The natural isomorphism is between towers of complexes, before any localization.
Source: blueprint strict reduction-tower assertion
(blueprint: lem-cbc-finite-open-exchange-scalars).
Proof: apply exchange_transition at every successor level, then forget the action.
The scalar-forget identification is identity on sections. These equalities give
naturality for adjacent arrows and hence for their composites. The degreewise inverse
exchanges give an inverse natural transformation, by the component inverse identities.
This constructs the displayed natural isomorphism with exactly the specified components. -/
theorem exchange_strict_towers
    (A : ℕ → Type (u + 1)) [∀ n, CommRing (A n)] [∀ n, Finite (A n)]
    (a : ∀ n, A (n + 1) →+* A n)
    {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j] [IsOpenImmersion j']
    (h : gU ≫ j = j' ≫ g) (hsq : IsPullback gU j' j g)
    (F : ∀ n, CochainComplex (Modules (A n) U) ℤ)
    (t : ∀ n, F (n + 1) ⟶ (resC (a n) U).obj (F n)) :
    ∃ e : (Functor.ofOpSequence
          (X := fun n ↦ ((forgetModules (A n) X').mapHomologicalComplex (.up ℤ)).obj
            (((moduleJ (A n) j ⋙ modulePullback (A n) g).mapHomologicalComplex (.up ℤ)).obj
              (F n)))
          (fun n ↦ sourceStep (a n) j g (F (n + 1)) (F n) (t n)) :
          ℕᵒᵖ ⥤ CochainComplex (Sheaf (Scheme.ProEt.topology X') AddCommGrpCat.{u + 1}) ℤ) ≅
        (Functor.ofOpSequence
          (X := fun n ↦ ((forgetModules (A n) X').mapHomologicalComplex (.up ℤ)).obj
            (((modulePullback (A n) gU ⋙ moduleJ (A n) j').mapHomologicalComplex (.up ℤ)).obj
              (F n)))
          (fun n ↦ targetStep (a n) gU j' (F (n + 1)) (F n) (t n)) :
          ℕᵒᵖ ⥤ CochainComplex (Sheaf (Scheme.ProEt.topology X') AddCommGrpCat.{u + 1}) ℤ),
      (∀ n, e.hom.app (Opposite.op n) =
        ((forgetModules (A n) X').mapHomologicalComplex (.up ℤ)).map
          ((betaC (A n) gU j' j g h hsq).hom.app (F n))) ∧
      (∀ n, e.inv.app (Opposite.op n) =
        ((forgetModules (A n) X').mapHomologicalComplex (.up ℤ)).map
          ((betaC (A n) gU j' j g h hsq).inv.app (F n))) := by
  let e n := ((forgetModules (A n) X').mapHomologicalComplex (.up ℤ)).mapIso
    ((betaC (A n) gU j' j g h hsq).app (F n))
  apply sequence_iso _ _ e
  intro n
  dsimp only [e, Functor.mapIso_hom, Iso.app_hom]
  rw [sourceStep, targetStep]
  let P := (forgetModules (A (n + 1)) X').mapHomologicalComplex (.up ℤ)
  let q := NatIso.mapHomologicalComplex (resForget (a n) X') (.up ℤ)
  have hn := congrArg P.map
    (exchange_transition (a n) gU j' j g h hsq (F (n + 1)) (F n) (t n)).1
  have hq := q.hom.naturality ((betaC (A n) gU j' j g h hsq).hom.app (F n))
  change P.map ((resC (a n) X').map
      ((betaC (A n) gU j' j g h hsq).hom.app (F n))) ≫ q.hom.app _ =
    q.hom.app _ ≫ ((forgetModules (A n) X').mapHomologicalComplex (.up ℤ)).map
      ((betaC (A n) gU j' j g h hsq).hom.app (F n)) at hq
  simp only [Functor.map_comp] at hn
  rw [Category.assoc, ← hq]
  simpa only [Functor.map_comp, Category.assoc] using
    congrArg (fun k ↦ k ≫ q.hom.app
      (((modulePullback (A n) gU ⋙ moduleJ (A n) j').mapHomologicalComplex
        (.up ℤ)).obj (F n))) hn

end

/-- The source transition, linear for a compatible ambient ring-sheaf action.
Source: blueprint final ambient-action clause
(blueprint: lem-cbc-finite-open-exchange-scalars). -/
def ambientSourceStep [Finite B] [Finite C] (a : B →+* C)
    {U X' X : Scheme.{u}} (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (Scheme.ProEt.topology X') RingCat.{u + 1})
    (rB : R ⟶ ringCoefficients B X') (rC : R ⟶ ringCoefficients C X')
    (hr : rB ≫ ringCoefficientMap a X' = rC)
    (F : CochainComplex (Modules B U) ℤ) (G : CochainComplex (Modules C U) ℤ)
    (t : F ⟶ (resC a U).obj G) :
    ((SheafOfModules.restrictScalars.{u + 1} rB).mapHomologicalComplex (.up ℤ)).obj
        (((moduleJ B j ⋙ modulePullback B g).mapHomologicalComplex (.up ℤ)).obj F) ⟶
      ((SheafOfModules.restrictScalars.{u + 1} rC).mapHomologicalComplex (.up ℤ)).obj
        (((moduleJ C j ⋙ modulePullback C g).mapHomologicalComplex (.up ℤ)).obj G) :=
  ((SheafOfModules.restrictScalars.{u + 1} rB).mapHomologicalComplex (.up ℤ)).map
    (((moduleJ B j ⋙ modulePullback B g).mapHomologicalComplex (.up ℤ)).map t ≫
      (sourceResC a j g).hom.app G) ≫
    (NatIso.mapHomologicalComplex (ambientRes a X' R rB rC hr) (.up ℤ)).hom.app
      (((moduleJ C j ⋙ modulePullback C g).mapHomologicalComplex (.up ℤ)).obj G)

/-- The target transition, linear for a compatible ambient ring-sheaf action.
Source: blueprint final ambient-action clause
(blueprint: lem-cbc-finite-open-exchange-scalars). -/
def ambientTargetStep [Finite B] [Finite C] (a : B →+* C)
    {U' U X' : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X') [IsOpenImmersion j']
    (R : Sheaf (Scheme.ProEt.topology X') RingCat.{u + 1})
    (rB : R ⟶ ringCoefficients B X') (rC : R ⟶ ringCoefficients C X')
    (hr : rB ≫ ringCoefficientMap a X' = rC)
    (F : CochainComplex (Modules B U) ℤ) (G : CochainComplex (Modules C U) ℤ)
    (t : F ⟶ (resC a U).obj G) :
    ((SheafOfModules.restrictScalars.{u + 1} rB).mapHomologicalComplex (.up ℤ)).obj
        (((modulePullback B gU ⋙ moduleJ B j').mapHomologicalComplex (.up ℤ)).obj F) ⟶
      ((SheafOfModules.restrictScalars.{u + 1} rC).mapHomologicalComplex (.up ℤ)).obj
        (((modulePullback C gU ⋙ moduleJ C j').mapHomologicalComplex (.up ℤ)).obj G) :=
  ((SheafOfModules.restrictScalars.{u + 1} rB).mapHomologicalComplex (.up ℤ)).map
    (((modulePullback B gU ⋙ moduleJ B j').mapHomologicalComplex (.up ℤ)).map t ≫
      (targetResC a gU j').hom.app G) ≫
    (NatIso.mapHomologicalComplex (ambientRes a X' R rB rC hr) (.up ℤ)).hom.app
      (((modulePullback C gU ⋙ moduleJ C j').mapHomologicalComplex (.up ℤ)).obj G)

section

attribute [local irreducible] ambientSourceStep ambientTargetStep ambientRes sourceStep targetStep
  sourceResC targetResC betaC sourceRes targetRes openRes pullRes

set_option backward.isDefEq.respectTransparency false in
/-- The same strict-tower isomorphism is linear over every compatible ambient ring sheaf.
Source: blueprint final ambient-action clause
(blueprint: lem-cbc-finite-open-exchange-scalars).
Proof: restrict exchange_transition along each ambient coefficient map. Its equality
remains an equality of linear chain maps; ambientRes is identity on sections and is
natural, so the next coefficient restriction agrees. The successor squares and their
inverse squares therefore hold over R. Compose them to obtain all tower arrows.
The component inverse identities give inverse tower maps with the displayed components. -/
theorem exchange_ambient_towers
    (A : ℕ → Type (u + 1)) [∀ n, CommRing (A n)] [∀ n, Finite (A n)]
    (a : ∀ n, A (n + 1) →+* A n)
    {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j] [IsOpenImmersion j']
    (h : gU ≫ j = j' ≫ g) (hsq : IsPullback gU j' j g)
    (R : Sheaf (Scheme.ProEt.topology X') RingCat.{u + 1})
    (r : ∀ n, R ⟶ ringCoefficients (A n) X')
    (hr : ∀ n, r (n + 1) ≫ ringCoefficientMap (a n) X' = r n)
    (F : ∀ n, CochainComplex (Modules (A n) U) ℤ)
    (t : ∀ n, F (n + 1) ⟶ (resC (a n) U).obj (F n)) :
    ∃ e : (Functor.ofOpSequence
          (X := fun n ↦
            ((SheafOfModules.restrictScalars.{u + 1} (r n)).mapHomologicalComplex (.up ℤ)).obj
              (((moduleJ (A n) j ⋙ modulePullback (A n) g).mapHomologicalComplex (.up ℤ)).obj
                (F n)))
          (fun n ↦ ambientSourceStep (a n) j g R (r (n + 1)) (r n) (hr n)
            (F (n + 1)) (F n) (t n)) :
          ℕᵒᵖ ⥤ CochainComplex (SheafOfModules.{u + 1} R) ℤ) ≅
        (Functor.ofOpSequence
          (X := fun n ↦
            ((SheafOfModules.restrictScalars.{u + 1} (r n)).mapHomologicalComplex (.up ℤ)).obj
              (((modulePullback (A n) gU ⋙ moduleJ (A n) j').mapHomologicalComplex (.up ℤ)).obj
                (F n)))
          (fun n ↦ ambientTargetStep (a n) gU j' R (r (n + 1)) (r n) (hr n)
            (F (n + 1)) (F n) (t n)) :
          ℕᵒᵖ ⥤ CochainComplex (SheafOfModules.{u + 1} R) ℤ),
      (∀ n, e.hom.app (Opposite.op n) =
        ((SheafOfModules.restrictScalars.{u + 1} (r n)).mapHomologicalComplex (.up ℤ)).map
          ((betaC (A n) gU j' j g h hsq).hom.app (F n))) ∧
      (∀ n, e.inv.app (Opposite.op n) =
        ((SheafOfModules.restrictScalars.{u + 1} (r n)).mapHomologicalComplex (.up ℤ)).map
          ((betaC (A n) gU j' j g h hsq).inv.app (F n))) := by
  let e n := ((SheafOfModules.restrictScalars.{u + 1} (r n)).mapHomologicalComplex
    (.up ℤ)).mapIso ((betaC (A n) gU j' j g h hsq).app (F n))
  apply sequence_iso _ _ e
  intro n
  dsimp only [e, Functor.mapIso_hom, Iso.app_hom]
  rw [ambientSourceStep, ambientTargetStep]
  let P := (SheafOfModules.restrictScalars.{u + 1} (r (n + 1))).mapHomologicalComplex
    (.up ℤ)
  let q := NatIso.mapHomologicalComplex
    (ambientRes (a n) X' R (r (n + 1)) (r n) (hr n)) (.up ℤ)
  have hn := congrArg P.map
    (exchange_transition (a n) gU j' j g h hsq (F (n + 1)) (F n) (t n)).1
  have hq := q.hom.naturality ((betaC (A n) gU j' j g h hsq).hom.app (F n))
  change P.map ((resC (a n) X').map
      ((betaC (A n) gU j' j g h hsq).hom.app (F n))) ≫ q.hom.app _ =
    q.hom.app _ ≫ ((SheafOfModules.restrictScalars.{u + 1} (r n)).mapHomologicalComplex
      (.up ℤ)).map ((betaC (A n) gU j' j g h hsq).hom.app (F n)) at hq
  simp only [Functor.map_comp] at hn
  rw [Category.assoc, ← hq]
  simpa only [Functor.map_comp, Category.assoc] using
    congrArg (fun k ↦ k ≫ q.hom.app
      (((modulePullback (A n) gU ⋙ moduleJ (A n) j').mapHomologicalComplex
        (.up ℤ)).obj (F n))) hn

end

end AlgebraicGeometry.ProEtale.StrictTower.FiniteOpenScalars
