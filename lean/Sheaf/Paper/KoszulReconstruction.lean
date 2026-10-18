/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q18
-/
module

public import Sheaf.Paper.CompletedAdicCoefficientDatum
public import Sheaf.Paper.CompletedAdicIntrinsicCompletion
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import Mathlib.CategoryTheory.Localization.Predicate
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimit
import Sheaf.Algebra.Homology.SiteDerivedTensorDescent

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
/-! # Koszul and quotient reconstruction over completed coefficients

Source: blueprint sec-proper-base-change/sk-thm-properbasechange, order 1248;
Stacks Project, Tags 091N, 091Z, 099L and 099M
(blueprint: prop-weil-pbc-koszul-reconstruction).

The Koszul functor extends the recorded explicit fibre model on maps; it introduces
no second coefficient sheaf or Koszul complex. The quotient unit is independently
normalized on all K-flat representatives by the ordinary quotient maps.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe t

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace AlgebraicGeometry.Scheme

variable (T : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)

/-- Strict towers of modules over the completed ring form a Grothendieck category.
Source: Stacks Tags 079B and 079Q (blueprint: prop-weil-pbc-koszul-reconstruction).
Proof: replace the pro-etale site by its small skeleton in universe t+1, apply the
Grothendieck theorem for small diagrams of module sheaves, then transport back along
that equivalence. Kernels, cokernels and filtered colimits of towers are levelwise. -/
theorem reconstructionTowers_grothendieck :
    IsGrothendieckAbelian.{t + 1} (CompletedAdicTowers T d) := by
  sorry

attribute [instance] reconstructionTowers_grothendieck

/-- The actual ordinary strict inverse-limit functor.
Source: Stacks Tag 0941 (blueprint: prop-weil-pbc-koszul-reconstruction). -/
abbrev reconstructionLimit : CompletedAdicTowers T d ⥤ CompletedAdicModules T d := lim

/-- Strict inverse limit is additive.
Source: Stacks Tag 0941 (blueprint: prop-weil-pbc-koszul-reconstruction).
Proof: limit projections jointly detect equality; after each projection additivity
is the limit lift equation and bilinearity of composition. -/
@[instance]
theorem reconstructionLimit_additive : (reconstructionLimit T d).Additive := by
  sorry

/-- The total right derived strict inverse limit with its universal comparison.
Source: Stacks Tag 0941 (blueprint: prop-weil-pbc-koszul-reconstruction). -/
abbrev reconstructionRlim : DerivedCategory (CompletedAdicTowers T d) ⥤
    DerivedCategory (CompletedAdicModules T d) := (reconstructionLimit T d).rightDerivedFunctor

/-- The universal derived-limit comparison on complexes of strict towers.
Source: Stacks Tag 0941 (blueprint: prop-weil-pbc-koszul-reconstruction). -/
def reconstructionRlimComparison (P : CochainComplex (CompletedAdicTowers T d) ℤ) :
    DerivedCategory.Q.obj
        (((reconstructionLimit T d).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ⟶
      (reconstructionRlim T d).obj (DerivedCategory.Q.obj P) :=
  (DerivedCategory.quotientCompQhIso _).inv.app
      (((reconstructionLimit T d).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
    DerivedCategory.Qh.map
      (((reconstructionLimit T d).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app P) ≫
    (reconstructionLimit T d).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P) ≫
    (reconstructionRlim T d).map ((DerivedCategory.quotientCompQhIso _).hom.app P)

/-- The canonical quotient module map sends one to one on every section.
Source: blueprint order 1248 (blueprint: prop-weil-pbc-koszul-reconstruction).
Proof: the coefficient projection is linear for its restricted scalar action and
commutes with restrictions. These section maps give the required module map.
Any module map from the unit is determined by the image of one, proving uniqueness. -/
theorem reconstructionQuotientUnit_exists (n : ℕ) :
    ∃! u : SheafOfModules.unit (completedAdicRing T d) ⟶ completedAdicFiniteModule T d n,
      ∀ U : T.ProEtᵒᵖ,
        u.val.app U (1 : (completedAdicRing T d).obj.obj U) =
          (1 : (completedAdicFiniteRing T d n).obj.obj U) := by
  sorry

/-- The residue-normalized module map from A_T to its n+1-st quotient.
Source: blueprint order 1248 (blueprint: prop-weil-pbc-koszul-reconstruction). -/
def reconstructionQuotientUnit (n : ℕ) :
    SheafOfModules.unit (completedAdicRing T d) ⟶ completedAdicFiniteModule T d n :=
  (reconstructionQuotientUnit_exists T d n).exists.choose

/-- The ordinary completion unit is determined by all quotient tensor maps.
Source: blueprint order 1248 (blueprint: prop-weil-pbc-koszul-reconstruction).
Proof: the maps x to x tensor one commute with quotient transitions, and hence form
a cone. Its limit lift is natural in the module. Joint monicity of the limit
projections proves uniqueness. The tensor formula fixes the completed scalar action. -/
theorem reconstructionOrdinaryUnit_exists :
    ∃! η : 𝟭 (CompletedAdicModules T d) ⟶
        completedAdicOrdinaryTower T d ⋙ reconstructionLimit T d,
      ∀ (M : CompletedAdicModules T d) (n : ℕ),
        η.app M ≫ limit.π ((completedAdicOrdinaryTower T d).obj M) (op n) =
          (ρ_ M).inv ≫ (M ◁ reconstructionQuotientUnit T d n) := by
  sorry

/-- The map to the ordinary limit induced by the actual quotient maps.
Source: blueprint order 1248 (blueprint: prop-weil-pbc-koszul-reconstruction). -/
def reconstructionOrdinaryUnit : 𝟭 (CompletedAdicModules T d) ⟶
    completedAdicOrdinaryTower T d ⋙ reconstructionLimit T d :=
  (reconstructionOrdinaryUnit_exists T d).exists.choose

/-- The universal reduction counit at the homotopy-category level.
Source: Stacks Tag 06YY (blueprint: prop-weil-pbc-koszul-reconstruction). -/
abbrev reconstructionReductionCounit := (completedAdicReduction_exists T d).choose_spec.choose

/-- The same reduction counit on a complex representative, with localization factors.
Source: Stacks Tag 06YY (blueprint: prop-weil-pbc-koszul-reconstruction). -/
def reconstructionReductionComplexCounit (P : CochainComplex (CompletedAdicModules T d) ℤ) :
    (completedAdicReduction T d).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj
        (((completedAdicOrdinaryTower T d).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :=
  (completedAdicReduction T d).map ((DerivedCategory.quotientCompQhIso _).inv.app P) ≫
    (reconstructionReductionCounit T d).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P) ≫
    DerivedCategory.Qh.map
      (((completedAdicOrdinaryTower T d).mapHomotopyCategoryFactors
        (ComplexShape.up ℤ)).hom.app P) ≫
    (DerivedCategory.quotientCompQhIso _).hom.app
      (((completedAdicOrdinaryTower T d).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)

/-- The strict reduction counit is invertible on every unbounded K-flat model.
Source: Stacks Tags 06XN and 06YY (blueprint: prop-weil-pbc-koszul-reconstruction).
Proof: the K-flat computation clause of completedAdicReduction_exists makes its
homotopy counit invertible. The other factors are localization isomorphisms. -/
theorem reconstructionTowerCounit_isIso
    (P : CochainComplex (CompletedAdicModules T d) ℤ)
    (hP : CochainComplex.IsAcyclicTensorKFlat (R := completedAdicCommRing T d) P) :
    IsIso (reconstructionReductionComplexCounit T d P) := by
  sorry

/-- The quotient completion unit on one K-flat representative at every tower level.
Source: blueprint order 1248 (blueprint: prop-weil-pbc-koszul-reconstruction). -/
def reconstructionUnitOnKFlat (P : CochainComplex (CompletedAdicModules T d) ℤ)
    (hP : CochainComplex.IsAcyclicTensorKFlat (R := completedAdicCommRing T d) P) :
    DerivedCategory.Q.obj P ⟶
      (reconstructionRlim T d).obj ((completedAdicReduction T d).obj (DerivedCategory.Q.obj P)) :=
  DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex (reconstructionOrdinaryUnit T d)
        (ComplexShape.up ℤ)).app P) ≫
    reconstructionRlimComparison T d
      (((completedAdicOrdinaryTower T d).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
    (reconstructionRlim T d).map
      (@inv _ _ _ _ (reconstructionReductionComplexCounit T d P)
        (reconstructionTowerCounit_isIso T d P hP))

/-- The canonical derived quotient unit is fixed by its value on all K-flat models.
Source: blueprint order 1248 (blueprint: prop-weil-pbc-koszul-reconstruction).
Proof: resolve representatives by K-flat complexes. Ordinary quotient units, the
universal reduction counit and the right-derived-limit comparison are natural.
Consequently these maps commute with roofs of K-flat models, and localization
descends them to a natural transformation. Every object has such a model, giving
uniqueness. This constructs the unit without using the reconstruction isomorphism. -/
theorem reconstructionCompletionUnit_exists :
    ∃! η : 𝟭 (DerivedCategory (CompletedAdicModules T d)) ⟶
        completedAdicReduction T d ⋙ reconstructionRlim T d,
      ∀ (P : CochainComplex (CompletedAdicModules T d) ℤ)
        (hP : CochainComplex.IsAcyclicTensorKFlat (R := completedAdicCommRing T d) P),
        η.app (DerivedCategory.Q.obj P) = reconstructionUnitOnKFlat T d P hP := by
  sorry

/-- The map comp_K induced by quotient maps, independently of chosen resolutions.
Source: blueprint order 1248 (blueprint: prop-weil-pbc-koszul-reconstruction). -/
def reconstructionCompletionUnit : 𝟭 (DerivedCategory (CompletedAdicModules T d)) ⟶
    completedAdicReduction T d ⋙ reconstructionRlim T d :=
  (reconstructionCompletionUnit_exists T d).exists.choose

/-- Tensoring a map of representatives and taking products gives the canonical product map.
Source: blueprint order 1248 (blueprint: prop-weil-pbc-koszul-reconstruction). -/
def reconstructionKoszulProductMap (r : ℕ) (a : Fin r → A)
    {C D : CochainComplex (CompletedAdicModules T d) ℤ} (h : C ⟶ D) :
    completedAdicKoszulProduct T d r a C ⟶ completedAdicKoszulProduct T d r a D :=
  letI := SheafOfModules.monoidalCategory (completedAdicCommRing T d)
  letI : (curriedTensor (CompletedAdicModules T d)).PreservesZeroMorphisms :=
    SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
      (completedAdicCommRing T d)
  letI : ∀ M : CompletedAdicModules T d,
      ((curriedTensor (CompletedAdicModules T d)).obj M).PreservesZeroMorphisms :=
    fun M ↦ SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
      (completedAdicCommRing T d) M
  Limits.Pi.map (fun m ↦ HomologicalComplex.mapBifunctorMap h
    (𝟙 (completedAdicKoszul T d r a m)) (curriedTensor _) (ComplexShape.up ℤ))

/-- Product maps commute with the actual one-minus-transition endomorphism.
Source: blueprint order 1248 (blueprint: prop-weil-pbc-koszul-reconstruction).
Proof: after every product projection this is the naturality square of tensoring h
with the fixed Koszul transition. Joint monicity gives the displayed square. -/
theorem reconstructionKoszulProductMap_comm (r : ℕ) (a : Fin r → A)
    {C D : CochainComplex (CompletedAdicModules T d) ℤ} (h : C ⟶ D) :
    reconstructionKoszulProductMap T d r a h ≫ (-completedAdicKoszulOneSubShift T d r a D) =
      (-completedAdicKoszulOneSubShift T d r a C) ≫
        reconstructionKoszulProductMap T d r a h := by
  sorry

/-- The canonical map of the recorded Koszul fibres, using the map of mapping cones.
Source: blueprint order 1248 (blueprint: prop-weil-pbc-koszul-reconstruction). -/
def reconstructionKoszulFiberMap (r : ℕ) (a : Fin r → A)
    {C D : CochainComplex (CompletedAdicModules T d) ℤ} (h : C ⟶ D) :
    completedAdicKoszulFibre T d r a C ⟶ completedAdicKoszulFibre T d r a D :=
  (HomologicalComplex.homotopyCofiber.mapArrowHom
    (-completedAdicKoszulOneSubShift T d r a C)
    (-completedAdicKoszulOneSubShift T d r a D)
    (fun j ↦ ⟨j - 1, sub_add_cancel j 1⟩)
    { left := reconstructionKoszulProductMap T d r a h
      right := reconstructionKoszulProductMap T d r a h
      w := reconstructionKoszulProductMap_comm T d r a h })⟦(-1 : ℤ)⟧'

/-- The induced fibre map preserves identities.
Source: blueprint order 1248 (blueprint: prop-weil-pbc-koszul-reconstruction).
Proof: tensor and product maps preserve identities; the induced mapping-cone map
and the shift functor preserve them as well. -/
theorem reconstructionKoszulFiberMap_id (r : ℕ) (a : Fin r → A)
    (C : CochainComplex (CompletedAdicModules T d) ℤ) :
    reconstructionKoszulFiberMap T d r a (𝟙 C) = 𝟙 _ := by
  sorry

/-- The induced fibre map preserves composition.
Source: blueprint order 1248 (blueprint: prop-weil-pbc-koszul-reconstruction).
Proof: tensor and product maps preserve composition; mapArrowHom_comp followed
by the shift functor gives the same equality for fibre maps. -/
theorem reconstructionKoszulFiberMap_comp (r : ℕ) (a : Fin r → A)
    {C D E : CochainComplex (CompletedAdicModules T d) ℤ} (h : C ⟶ D) (k : D ⟶ E) :
    reconstructionKoszulFiberMap T d r a (h ≫ k) =
      reconstructionKoszulFiberMap T d r a h ≫ reconstructionKoszulFiberMap T d r a k := by
  sorry

/-- Functoriality on complexes of the existing explicit Koszul fibre model.
Source: blueprint order 1248 (blueprint: prop-weil-pbc-koszul-reconstruction). -/
def reconstructionKoszulFiberFunctor (r : ℕ) (a : Fin r → A) :
    CochainComplex (CompletedAdicModules T d) ℤ ⥤ CochainComplex (CompletedAdicModules T d) ℤ where
  obj := completedAdicKoszulFibre T d r a
  map := reconstructionKoszulFiberMap T d r a
  map_id := reconstructionKoszulFiberMap_id T d r a
  map_comp := reconstructionKoszulFiberMap_comp T d r a

/-- The recorded Koszul model and its canonical maps descend through quasi-isomorphisms.
Source: blueprint order 1248 (blueprint: prop-weil-pbc-koszul-reconstruction).
Proof: each Koszul complex is bounded finite free. Tensoring an arbitrary complex
by it preserves quasi-isomorphisms. Exact countable products on the pro-etale site
preserve the resulting quasi-isomorphisms; the cone triangle then does so for the
mapping fibre. These are exactly the representative maps constructed above. -/
theorem reconstructionKoszulFiberFunctor_inverts (r : ℕ) (a : Fin r → A) :
    (HomologicalComplex.quasiIso (CompletedAdicModules T d) (ComplexShape.up ℤ)).IsInvertedBy
      (reconstructionKoszulFiberFunctor T d r a ⋙ DerivedCategory.Q) := by
  sorry

/-- The functor on the derived category induced by the existing Koszul fibre construction.
Source: blueprint order 1248 (blueprint: prop-weil-pbc-koszul-reconstruction). -/
abbrev reconstructionKoszulDerivedFunctor (r : ℕ) (a : Fin r → A) :
    DerivedCategory (CompletedAdicModules T d) ⥤ DerivedCategory (CompletedAdicModules T d) :=
  Localization.lift (reconstructionKoszulFiberFunctor T d r a ⋙ DerivedCategory.Q)
    (reconstructionKoszulFiberFunctor_inverts T d r a) DerivedCategory.Q

/-- The existing unit c to (u_C(c),0) is natural for the induced fibre maps.
Source: blueprint order 1248 (blueprint: prop-weil-pbc-koszul-reconstruction).
Proof: tensor units commute with chain maps; taking product projections proves the
same equality for u_C. The cone map is diagonal, so the zero second coordinate
remains zero. Shifting gives the displayed equality. -/
theorem reconstructionKoszulUnit_naturality (r : ℕ) (a : Fin r → A)
    {C D : CochainComplex (CompletedAdicModules T d) ℤ} (h : C ⟶ D) :
    h ≫ completedAdicKoszulUnitComplex T d r a D =
      completedAdicKoszulUnitComplex T d r a C ≫ reconstructionKoszulFiberMap T d r a h := by
  sorry

/-- The recorded degree-zero unit, assembled as a natural transformation of complexes.
Source: blueprint order 1248 (blueprint: prop-weil-pbc-koszul-reconstruction). -/
def reconstructionKoszulComplexUnit (r : ℕ) (a : Fin r → A) :
    𝟭 (CochainComplex (CompletedAdicModules T d) ℤ) ⟶
      reconstructionKoszulFiberFunctor T d r a where
  app := completedAdicKoszulUnitComplex T d r a
  naturality _ _ h := reconstructionKoszulUnit_naturality T d r a h

/-- Localization of the existing completion unit gives κ on the derived category.
Source: blueprint order 1248 (blueprint: prop-weil-pbc-koszul-reconstruction). -/
def reconstructionKoszulDerivedUnit (r : ℕ) (a : Fin r → A) :
    𝟭 (DerivedCategory (CompletedAdicModules T d)) ⟶
      reconstructionKoszulDerivedFunctor T d r a :=
  letI : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso (CompletedAdicModules T d) (ComplexShape.up ℤ))
      DerivedCategory.Q (𝟭 (DerivedCategory (CompletedAdicModules T d))) :=
    ⟨Functor.rightUnitor _⟩
  Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso (CompletedAdicModules T d) (ComplexShape.up ℤ))
    DerivedCategory.Q (reconstructionKoszulFiberFunctor T d r a ⋙ DerivedCategory.Q)
    (𝟭 _) (reconstructionKoszulDerivedFunctor T d r a)
    (Functor.whiskerRight (reconstructionKoszulComplexUnit T d r a) DerivedCategory.Q)

/-- The functorial model uses the recorded intrinsic completion and its same unit.
Source: blueprint order 1248 (blueprint: prop-weil-pbc-koszul-reconstruction).
Proof: the localization factorization identifies the value on a representative with
its explicit fibre. Apply completedAdicIntrinsicCompletion_comparison to the
localization's own representative and compose these identifications. The units
are both the localization of the same chain map, giving the equality. -/
theorem reconstructionKoszulIntrinsicComparison (r : ℕ) (a : Fin r → A)
    (K : DerivedCategory (CompletedAdicModules T d)) :
    ∃ j : (reconstructionKoszulDerivedFunctor T d r a).obj K ≅
        completedAdicIntrinsicCompletion T d r a K,
      (reconstructionKoszulDerivedUnit T d r a).app K ≫ j.hom =
        completedAdicIntrinsicUnit T d r a K := by
  sorry

/-- Koszul completion and the total derived inverse limit of strict quotient reductions
are naturally isomorphic, carrying the Koszul unit to the actual quotient completion unit.
Consequently the quotient unit is invertible for every derived I-complete object.

Source: blueprint order 1248; Stacks Tags 091N, 091Z, 099L and 099M
(blueprint: prop-weil-pbc-koszul-reconstruction).
Proof:
1. Apply lem-weil-pbc-completed-constant-sheaf-reduction to T, A and I. Finiteness of
all positive quotients identifies their constant sheaves with the finite coefficient
sheaves, canonically for the quotient maps, hence identifies their limits and projections.
2. Apply the completed-coefficient paragraph of lem-weil-pbc-constant-completion-equivalence
with O equal to that completed ring and arbitrary N. Its Koszul factors, transitions and
degree-zero units agree with the recorded intrinsic construction. Compute the entire
quotient tower on one K-flat model. Strict quotient augmentations give the comparison;
functorial total right derived inverse limit makes it natural. Exact countable products
identify the explicit Koszul fibre with that same strict-derived-limit model. This gives
the natural isomorphism and the equality of its composite with κ and the quotient unit.
3. If κ is invertible, compose it with the comparison isomorphism. The unit equality
identifies that invertible composite with comp_K; its inverse is the comparison inverse
followed by the inverse Koszul unit. -/
theorem koszulReconstruction (r : ℕ) (a : Fin r → A)
    (_ha : Ideal.span (Set.range a) = d.ideal) :
    ∃ c : reconstructionKoszulDerivedFunctor T d r a ≅
        completedAdicReduction T d ⋙ reconstructionRlim T d,
      (∀ K : DerivedCategory (CompletedAdicModules T d),
        (reconstructionKoszulDerivedUnit T d r a).app K ≫ c.hom.app K =
          (reconstructionCompletionUnit T d).app K) ∧
      (∀ K : DerivedCategory (CompletedAdicModules T d),
        IsIso ((reconstructionKoszulDerivedUnit T d r a).app K) →
          IsIso ((reconstructionCompletionUnit T d).app K)) := by
  sorry

end AlgebraicGeometry.Scheme
