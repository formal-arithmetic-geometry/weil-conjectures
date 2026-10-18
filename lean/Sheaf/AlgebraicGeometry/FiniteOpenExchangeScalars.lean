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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

/-- Restriction along the identity has its unique identity-on-sections identification.
Source: Stacks Tag 03CY (blueprint: lem-cbc-finite-open-exchange-scalars).
Proof: identity scalar restriction leaves the action unchanged. Identity section maps
are linear and natural, and their inverses are identical. Sections determine uniqueness. -/
theorem resId_existsUnique (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    ∃! e : res (RingHom.id A) X ≅ 𝟭 (Modules A X),
      ∀ (M : Modules A X) (W : X.ProEtᵒᵖ) (m : M.val.obj W),
        (e.hom.app M).val.app W m = m := by
  sorry

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
  sorry

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
  sorry

/-- The identity-on-sections comparison between successive and composite restriction.
Source: Stacks Tag 03CY (blueprint: lem-cbc-finite-open-exchange-scalars). -/
def resComp {D : Type (u + 1)} [CommRing D] (a : B →+* C) (b : C →+* D)
    (X : Scheme.{u}) : res b X ⋙ res a X ≅ res (b.comp a) X :=
  ambientRes b X (ringCoefficients B X) (ringCoefficientMap a X)
    (ringCoefficientMap (b.comp a) X)
    (coefficientMap_comp a b X)

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

end

end AlgebraicGeometry.ProEtale.StrictTower.FiniteOpenScalars
