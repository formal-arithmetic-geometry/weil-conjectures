/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientMaps
public import WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenTensorDefs
public import WeilConjectures.AlgebraicGeometry.Compact.CompactCoefficientComposition
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
import all WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactScalarCoherence
import WeilConjectures.AlgebraicGeometry.OpenScalarSite.OpenScalarSiteCoherence
import WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenTensor

/-! # Restriction of the structural coefficient mate

Source: main-20261015, sec-smooth-purity/sk-lem-sp-tower/
lem-coef-finite-dualizing.proof.md, paragraph 3, sentences 2--3
(blueprint: lem-coef-dualizing-open-mate).

The local structural adjunction is the composite of the exact open adjunction
and the structural adjunction on Y. Its dualizing object is therefore literally
the restriction of the global one. The local coefficient map is transported from
the actual compactification of U obtained by composing its open embedding with
that of Y. No exceptional-adjoint coefficient comparison is assumed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Etale.DualizingOpenMate

variable {A B : Type (u + 1)} [CommRing A] [CommRing B]
variable {U Y S : Scheme.{u}} {f : Y ⟶ S}

/-- The compactification of the open structural map, using the same proper part.
Source: main-20261015, dualizing proof paragraph 3
(blueprint: lem-coef-dualizing-open-mate). -/
def openCompactification (c : Compactification f) (j : U ⟶ Y) [IsOpenImmersion j] :
    Compactification (j ≫ f) where
  Z := c.Z
  i := j ≫ c.i
  g := c.g
  comm := (congrArg (j ≫ ·) c.comm).trans (Category.assoc j c.i c.g).symm
  isProper := inferInstance
  isOpenImmersion := inferInstance

/-- Canonical compact-support composition for an open followed by a structure map.
It is induced by the already defined composition of exact open extensions.
Source: main-20261015, dualizing proof paragraph 3; Stacks 0F7J
(blueprint: lem-coef-dualizing-open-mate). -/
def openComposition (R : Type (u + 1)) [CommRing R]
    (c : Compactification f) (j : U ⟶ Y) [IsOpenImmersion j] :
    derivedExtension (A := R) j ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) c ≅
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R)
        (openCompactification c j) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (mapDerivedCategoryOpenImmersionLowerShriekComp (ModuleCat.{u + 1} R) j c.i).symm _

/-- The specified inverse coefficient component on U, in composite-adjunction coordinates.
Both compositor factors are canonical. The middle arrow is the published coefficient
inverse; its zero fallback is never used on the theorem's finite-Tor domain.
Source: main-20261015, dualizing proof paragraph 3; Stacks 0GL6
(blueprint: lem-coef-dualizing-open-mate). -/
def localInverse (φ : A →+* B) (c : Compactification f)
    (j : U ⟶ Y) [IsOpenImmersion j] (L : DerivedCategoryModule A U) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c).obj
        ((derivedExtension (A := B) j).obj ((scalarExtension φ U).obj L)) ⟶
      (scalarExtension φ S).obj
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj
          ((derivedExtension (A := A) j).obj L)) :=
  (openComposition B c j).hom.app ((scalarExtension φ U).obj L) ≫
    ExceptionalCoefficients.comparisonInverse φ (openCompactification c j) L ≫
    (scalarExtension φ S).map ((openComposition A c j).inv.app L)

variable (φ : A →+* B) (c : Compactification f)
variable (GA : DerivedCategoryModule A S ⥤ DerivedCategoryModule A Y)
variable (GB : DerivedCategoryModule B S ⥤ DerivedCategoryModule B Y)
variable (aA : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ GA)
variable (aB : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c ⊣ GB)

/-- The global counit-defined map, for the named structural adjunctions.
This is the usual mate formula with arbitrary choices of the named right adjoints;
its unit identification is the already fixed scalar unit comparison.
Source: main-20261015, dualizing proof paragraph 1
(blueprint: lem-coef-dualizing-open-mate). -/
def globalMate :
    (scalarExtension φ Y).obj (GA.obj (constantComplex A S)) ⟶
      GB.obj (constantComplex B S) :=
  aB.homEquiv _ _
    (ExceptionalCoefficients.comparisonInverse φ c (GA.obj (constantComplex A S)) ≫
      (scalarExtension φ S).map (aA.counit.app (constantComplex A S)) ≫
      (ExceptionalCoefficients.unitIso φ S).hom)

/-- The counit-compatible structural adjunction on the open. Its counit is the
structural counit following the image of open evaluation, as specified in the node.
Source: main-20261015, dualizing proof paragraph 3
(blueprint: lem-coef-dualizing-open-mate). -/
def localAdjunction (j : U ⟶ Y) [IsOpenImmersion j] :
    derivedExtension (A := A) j ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣
      GA ⋙ derivedRestriction (A := A) j :=
  (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j).comp aA

/-- The local mate, defined using the actual local coefficient inverse and counit.
Source: main-20261015, dualizing proof paragraph 3
(blueprint: lem-coef-dualizing-open-mate). -/
def localMate (j : U ⟶ Y) [IsOpenImmersion j] :
    (scalarExtension φ U).obj
        ((derivedRestriction (A := A) j).obj (GA.obj (constantComplex A S))) ⟶
      (derivedRestriction (A := B) j).obj (GB.obj (constantComplex B S)) :=
  (localAdjunction c GB aB j).homEquiv _ _
    (localInverse φ c j
        ((derivedRestriction (A := A) j).obj (GA.obj (constantComplex A S))) ≫
      (scalarExtension φ S).map
        ((localAdjunction c GA aA j).counit.app (constantComplex A S)) ≫
      (ExceptionalCoefficients.unitIso φ S).hom)

/-- Restrict the global mate and precompose with the canonical scalar/pullback comparison.
Source: main-20261015, dualizing proof paragraph 3
(blueprint: lem-coef-dualizing-open-mate). -/
def restrictedMate (j : U ⟶ Y) [IsOpenImmersion j] :
    (scalarExtension φ U).obj
        ((derivedRestriction (A := A) j).obj (GA.obj (constantComplex A S))) ⟶
      (derivedRestriction (A := B) j).obj (GB.obj (constantComplex B S)) :=
  (openScalarRestriction φ j).hom.app (GA.obj (constantComplex A S)) ≫
    (derivedRestriction (A := B) j).map (globalMate φ c GA GB aA aB)

/-- The middle adjunct: inverse open tensor, image of A-evaluation, inverse global
coefficient comparison, scalar structural counit, and the fixed scalar unit map.
Source: main-20261015, expanded dualizing proof, steps 3--4
(blueprint: lem-coef-dualizing-open-mate). -/
def middleAdjunct (j : U ⟶ Y) [IsOpenImmersion j] :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c).obj
        ((derivedExtension (A := B) j).obj
          ((scalarExtension φ U).obj
            ((derivedRestriction (A := A) j).obj (GA.obj (constantComplex A S))))) ⟶
      constantComplex B S :=
  (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c).map
      ((ExceptionalCoefficients.openIso φ j).inv.app
        ((derivedRestriction (A := A) j).obj (GA.obj (constantComplex A S)))) ≫
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c).map
      ((scalarExtension φ Y).map
        ((derivedOpenImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} A) j).counit.app (GA.obj (constantComplex A S)))) ≫
    ExceptionalCoefficients.comparisonInverse φ c (GA.obj (constantComplex A S)) ≫
    (scalarExtension φ S).map (aA.counit.app (constantComplex A S)) ≫
    (ExceptionalCoefficients.unitIso φ S).hom

/-- All three asserted equalities, with the structural and tensor identifications explicit.
Source: main-20261015, dualizing proof paragraph 3 and expanded retained proof steps 3--5
(blueprint: lem-coef-dualizing-open-mate). -/
def Formula (j : U ⟶ Y) [IsOpenImmersion j] : Prop :=
  restrictedMate φ c GA GB aA aB j = localMate φ c GA GB aA aB j ∧
  ((derivedExtension (A := B) j ⋙
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c).map
        (restrictedMate φ c GA GB aA aB j) ≫
    (localAdjunction c GB aB j).counit.app (constantComplex B S) =
      middleAdjunct φ c GA aA j) ∧
  (middleAdjunct φ c GA aA j =
    localInverse φ c j
        ((derivedRestriction (A := A) j).obj (GA.obj (constantComplex A S))) ≫
      (scalarExtension φ S).map
        ((localAdjunction c GA aA j).counit.app (constantComplex A S)) ≫
      (ExceptionalCoefficients.unitIso φ S).hom)

/-- The four named dualizing objects have precisely the constructibility, boundedness,
and finite Tor amplitude required in the statement. The finite interval is ordered;
no flatness of the quotient coefficient ring is imposed.
Source: main-20261015, dualizing proof paragraphs 1--3
(blueprint: lem-coef-dualizing-open-mate). -/
def Domain [Finite A] [Finite B] (j : U ⟶ Y) [IsOpenImmersion j] : Prop :=
  (DerivedCategory.isBoundedConstructible A Y (GA.obj (constantComplex A S)) ∧
    ∃ a b : ℤ, a ≤ b ∧
      DerivedCategory.hasTorAmplitudeIn A Y a b (GA.obj (constantComplex A S))) ∧
  (DerivedCategory.isBoundedConstructible B Y (GB.obj (constantComplex B S)) ∧
    ∃ a b : ℤ, a ≤ b ∧
      DerivedCategory.hasTorAmplitudeIn B Y a b (GB.obj (constantComplex B S))) ∧
  (DerivedCategory.isBoundedConstructible A U
      ((derivedRestriction (A := A) j).obj (GA.obj (constantComplex A S))) ∧
    ∃ a b : ℤ, a ≤ b ∧ DerivedCategory.hasTorAmplitudeIn A U a b
      ((derivedRestriction (A := A) j).obj (GA.obj (constantComplex A S)))) ∧
  (DerivedCategory.isBoundedConstructible B U
      ((derivedRestriction (A := B) j).obj (GB.obj (constantComplex B S))) ∧
    ∃ a b : ℤ, a ≤ b ∧ DerivedCategory.hasTorAmplitudeIn B U a b
      ((derivedRestriction (A := B) j).obj (GB.obj (constantComplex B S))))

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

private theorem compactSupportMap_open_composition [Finite A] [Finite B]
    (j : U ⟶ Y) [IsOpenImmersion j] (L : DerivedCategoryModule A U) :
    (scalarExtension φ S).map ((openComposition A c j).hom.app L) ≫
        ExceptionalCoefficients.compactSupportMap φ (openCompactification c j) L =
      ExceptionalCoefficients.compactSupportMap φ c ((derivedExtension j).obj L) ≫
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c).map
          ((ExceptionalCoefficients.openIso φ j).hom.app L) ≫
        (openComposition B c j).hom.app ((scalarExtension φ U).obj L) := by
  have ho := ProEtale.OpenScalarSite.etale_scalar_comp φ j c.i L
  rw [← compactScalarOpen_eq φ j, ← compactScalarOpen_eq φ c.i,
    ← compactScalarOpen_eq φ (j ≫ c.i)] at ho
  have hn := (scalarMate φ c.g).naturality
    ((mapDerivedCategoryOpenImmersionLowerShriekComp
      (ModuleCat.{u + 1} A) j c.i).inv.app L)
  dsimp only [Functor.comp_map] at hn
  simp only [openComposition, openCompactification, Iso.trans_hom, Iso.symm_hom,
    Functor.associator_inv_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    NatTrans.comp_app, Category.id_comp, ExceptionalCoefficients.compactSupportMap,
    Functor.comp_map, Functor.comp_obj, Category.assoc]
  rw [← Category.assoc, hn]
  simp only [Category.assoc, ← Functor.map_comp]
  congr 1
  rw [← ho]
  erw [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp]

private theorem compactSupportMap_invertible [Finite A] [Finite B] [IsNoetherian S]
    {X : Scheme.{u}} {g : X ⟶ S} (d : Compactification g)
    (M : DerivedCategoryModule A X) :
    IsIso (ExceptionalCoefficients.compactSupportMap φ d M) := by
  have : IsLocallyNoetherian d.Z := LocallyOfFiniteType.isLocallyNoetherian d.g
  have : CompactSpace d.Z := QuasiCompact.compactSpace_of_compactSpace d.g
  have : IsNoetherian d.Z := ⟨⟩
  have := (properFiniteCoefficientExtension φ d.g).1
    ((derivedExtension d.i).obj M)
  unfold ExceptionalCoefficients.compactSupportMap
  infer_instance

private theorem inverse_naturality [Finite A] [Finite B] [IsNoetherian S]
    {M N : DerivedCategoryModule A Y} (h : M ⟶ N) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c).map
        ((scalarExtension φ Y).map h) ≫ ExceptionalCoefficients.comparisonInverse φ c N =
      ExceptionalCoefficients.comparisonInverse φ c M ≫
        (scalarExtension φ S).map
          ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map h) := by
  have := compactSupportMap_invertible φ c M
  have := compactSupportMap_invertible φ c N
  simp only [ExceptionalCoefficients.comparisonInverse, dif_pos (inferInstance : IsIso _)]
  apply (cancel_mono (ExceptionalCoefficients.compactSupportMap φ c N)).mp
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [compactScalarMap_naturality φ c h]
  simp only [IsIso.inv_hom_id_assoc]

private theorem localInverse_eq [Finite A] [Finite B] [IsNoetherian S]
    (j : U ⟶ Y) [IsOpenImmersion j] (L : DerivedCategoryModule A U) :
    localInverse φ c j L =
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c).map
          ((ExceptionalCoefficients.openIso φ j).inv.app L) ≫
        ExceptionalCoefficients.comparisonInverse φ c ((derivedExtension j).obj L) := by
  have := compactSupportMap_invertible φ c ((derivedExtension j).obj L)
  have := compactSupportMap_invertible φ (openCompactification c j) L
  let F := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c
  let q := (ExceptionalCoefficients.openIso φ j).app L
  apply (cancel_epi (F.map q.hom)).mp
  apply (cancel_epi (ExceptionalCoefficients.compactSupportMap φ c
    ((derivedExtension j).obj L))).mp
  dsimp only [localInverse]
  erw [← reassoc_of% (compactSupportMap_open_composition φ c j L)]
  simp only [ExceptionalCoefficients.comparisonInverse, dif_pos (inferInstance : IsIso _),
    IsIso.hom_inv_id_assoc]
  dsimp only [F, q, Iso.app_hom]
  erw [← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
  erw [← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
  simp only [Category.id_comp, IsIso.hom_inv_id]
  rfl

private theorem middleAdjunct_eq [Finite A] [Finite B] [IsNoetherian S]
    (j : U ⟶ Y) [IsOpenImmersion j] :
    middleAdjunct φ c GA aA j =
      localInverse φ c j ((derivedRestriction j).obj (GA.obj (constantComplex A S))) ≫
        (scalarExtension φ S).map
          ((localAdjunction c GA aA j).counit.app (constantComplex A S)) ≫
        (ExceptionalCoefficients.unitIso φ S).hom := by
  rw [localInverse_eq]
  unfold middleAdjunct localAdjunction
  rw [Adjunction.comp_counit_app]
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% (inverse_naturality φ c
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) j).counit.app (GA.obj (constantComplex A S))))]
  rfl

private theorem restrictedMate_adjunct (j : U ⟶ Y) [IsOpenImmersion j] :
    (derivedExtension (A := B) j ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c).map
        (restrictedMate φ c GA GB aA aB j) ≫
      (localAdjunction c GB aB j).counit.app (constantComplex B S) =
        middleAdjunct φ c GA aA j := by
  let W := GA.obj (constantComplex A S)
  let g := globalMate φ c GA GB aA aB
  let J := derivedExtension (A := B) j
  let F := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c
  let e := derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j
  have he := (etaleOpenTensorComparisons φ j).counit W
  rw [← compactScalarOpen_eq φ j] at he
  have he' : J.map ((openScalarRestriction φ j).hom.app W) ≫
      e.counit.app ((scalarExtension φ Y).obj W) =
        (ExceptionalCoefficients.openIso φ j).inv.app ((derivedRestriction j).obj W) ≫
          (scalarExtension φ Y).map
            ((derivedOpenImmersionLowerShriekUpperStarAdjunction
              (ModuleCat.{u + 1} A) j).counit.app W) := by
    rw [← he, Iso.inv_hom_id_app_assoc]
  have hn := e.counit.naturality g
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  have hg : F.map g ≫ aB.counit.app (constantComplex B S) =
      ExceptionalCoefficients.comparisonInverse φ c W ≫
        (scalarExtension φ S).map (aA.counit.app (constantComplex A S)) ≫
        (ExceptionalCoefficients.unitIso φ S).hom := by
    exact (aB.homEquiv_counit _ _ _).symm.trans
      ((aB.homEquiv _ _).symm_apply_apply _)
  have hi : J.map (restrictedMate φ c GA GB aA aB j) ≫
      e.counit.app (GB.obj (constantComplex B S)) =
        (ExceptionalCoefficients.openIso φ j).inv.app ((derivedRestriction j).obj W) ≫
          (scalarExtension φ Y).map
            ((derivedOpenImmersionLowerShriekUpperStarAdjunction
              (ModuleCat.{u + 1} A) j).counit.app W) ≫ g := by
    change J.map ((openScalarRestriction φ j).hom.app W ≫
      (derivedRestriction (A := B) j).map g) ≫ _ = _
    rw [J.map_comp, Category.assoc, hn, ← Category.assoc, he', Category.assoc]
  change F.map (J.map (restrictedMate φ c GA GB aA aB j)) ≫
    (e.comp aB).counit.app (constantComplex B S) = _
  rw [Adjunction.comp_counit_app, ← F.map_comp_assoc, hi]
  simp only [Functor.map_comp, Category.assoc]
  rw [hg]
  rfl

/-- The structural counit-defined coefficient mate restricts to the local mate,
including both displayed equalities of adjuncts. The named right adjoints are arbitrary
choices for the fixed actual compact-support functors; on U we use their canonical
composite-adjunction coordinates, so its counit is the specified evaluation composite.
Source: main-20261015, sec-smooth-purity/sk-lem-sp-tower/
lem-coef-finite-dualizing.proof.md, paragraph 3, sentences 2--3
(blueprint: lem-coef-dualizing-open-mate).

Proof:
1. Use lem-coef-dualizing-open-adjoint to identify the local structural adjunction
   with open extension followed by global compact support. Its right adjoint is
   global exceptional pullback followed by restriction. The counit on the unit is
   the global counit after the image of open evaluation; these are localAdjunction.
2. The affine open is quasi-compact and Y is Noetherian. By
   lem-coef-dualizing-open-tensor, extension of L = j*omega preserves constructibility,
   boundedness and its Tor interval. Thus lem-fix-compact-support-coefficient-change
   is invertible at W, L and j!L. All coefficient inverse components below are on
   that domain; none of the total inverse definitions uses its zero fallback.
3. By lem-coef-dualizing-open-tensor, the canonical open coefficient comparison d
   intertwines evaluation with scalar extension. Naturality of B-evaluation at the
   global mate and its defining structural-counit equation give the first adjunct
   equality: apply global B-compact-support to inverse d followed by scalar
   A-evaluation, then apply inverse c_Y,W and the scalar structural counit.
4. Naturality of c_Y at e_A,W moves scalar evaluation to the left of inverse c.
   Apply lem-sf-compact-coefficient-composition to j followed by a_Y at L. Its
   open-factor comparison is d: both restrict to the identity on U by pullback
   compatibility and lem-coef-etale-open-tensor; the open adjunction determines a
   map between open extensions from its restriction. Hence c_U,L is c_Y,j!L
   followed by F_Y,B(d). Cancel these invertible components. The normalized
   counit factorization in step 1 gives the second displayed adjunct equality.
5. The resulting adjunct is exactly that of localMate. Injectivity of the
   localAdjunction hom equivalence implies restrictedMate = localMate. Only the
   compact-support comparisons, exact open adjunction and scalar/pullback map enter;
   no exceptional-adjoint coefficient comparison or invertibility of u is assumed.
-/
theorem restriction
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n m : ℕ+) (hmn : m ≤ n)
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (CommRingCat.of D.k))
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (c : Compactification aY) (V : Y.Opens) (_hV : IsAffineOpen V)
    (GA : DerivedCategoryModule
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) (Spec (CommRingCat.of D.k)) ⥤
      DerivedCategoryModule (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) Y)
    (GB : DerivedCategoryModule
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E m)) (Spec (CommRingCat.of D.k)) ⥤
      DerivedCategoryModule (ULift.{u + 1} (Padic.coefficientExtensionRing l E m)) Y)
    (aA : rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E n))) c ⊣ GA)
    (aB : rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E m))) c ⊣ GB)
    (_hDualizing : Domain GA GB V.ι) :
    Formula (ProEtale.finiteCompositionReduction l E n m hmn) c GA GB aA aB V.ι := by
  let φ := ProEtale.finiteCompositionReduction l E n m hmn
  have h₁ := restrictedMate_adjunct φ c GA GB aA aB V.ι
  have h₂ := middleAdjunct_eq φ c GA aA V.ι
  refine ⟨?_, h₁, h₂⟩
  apply ((localAdjunction c GB aB V.ι).homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_counit, h₁, h₂]
  unfold localMate
  rw [Equiv.symm_apply_apply]

end AlgebraicGeometry.Etale.DualizingOpenMate
