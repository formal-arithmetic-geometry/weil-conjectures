/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.SecSmoothPurity.ProperFiniteCoefficientExtension
public import Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection
public import Sheaf.Paper.ExceptionalCoefficientComparison
public import Sheaf.Paper.ProperOpenCoefficientRefinement
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
import all Sheaf.Paper.EtaleProEtaleScalarMate
import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Scalar coherence for ordinary etale compact support

Source: Stacks Project, more-etale.tex, Tag 0GL6, with Tags 0F7I, 0F7J and 0F7L;
sites-cohomology.tex, Tags 07A4, 0GL1 and 0E48
(blueprint: lem-pur-etale-compact-scalar-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v₁ v₂ v₃ v₄ w₁ w₂ w₃ w₄
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

variable {A B : Type (u + 1)} [CommRing A] [CommRing B]

/-- The inverse of the published open balancing map has the specified open-unit transpose.
Source: Stacks 07A4, 0GL1 and 0GL6
(blueprint: lem-pur-etale-compact-scalar-coherence).
Proof: regard each exact open adjunction as an adjunction to the left-derived
pullback by transporting its right adjoint along the canonical exact-pullback comparison.
The published open comparison is a conjugate under the two composite adjunctions.
The iterated-mate identity identifies its inverse with the open mate of the inverse
scalar-restriction mate. The existing scalarPullback_eq identifies that inner mate with
the inverse of the normalized scalar/pullback comparison. The mate's unit equation
therefore computes its open-adjunction transpose. Naturality of the exact-pullback
comparison transports this equation back to the published exact open adjunction;
cancellation of its inverse and forward components yields exactly the transpose defining
properOpenCoefficientOpenInverse. Injectivity of the open adjunction's Hom equivalence
proves equality. This works without finite coefficients or boundedness. -/
theorem compactScalarOpen_normalization (φ : A →+* B) {U T : Scheme.{u}}
    (j : U ⟶ T) [IsOpenImmersion j] (M : DerivedCategoryModule A U) :
    (ExceptionalCoefficients.openIso φ j).inv.app M =
      properOpenCoefficientOpenInverse φ j M := by
  let a := (derivedOpenImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) j).ofNatIsoRight
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) j).symm
  let b := (derivedOpenImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} B) j).ofNatIsoRight
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) j).symm
  let x := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ)
  let u := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars U.smallEtaleTopology φ)
  let α := (mateEquiv x u).symm
    (TwoSquare.mk _ _ _ _ (scalarRestrictionPullbackIso φ j).hom)
  have he : α.natTrans = (scalarPullbackIso φ j).inv := by
    exact congrArg Iso.inv (scalarPullback_eq φ j)
  have h := congrArg TwoSquare.natTrans
    (iterated_mateEquiv_conjugateEquiv_symm a b u x
      (TwoSquare.mk _ _ _ _ (scalarRestrictionPullbackIso φ j).hom))
  change ((mateEquiv a b).symm α).natTrans = (ExceptionalCoefficients.openIso φ j).inv at h
  have ht := unit_mateEquiv_symm a b α M
  change (scalarExtension φ U).map (a.unit.app M) ≫ α.natTrans.app _ =
    b.unit.app _ ≫ (upperStar (ModuleCat.{u + 1} B) j).leftDerivedFunctor.map
      (((mateEquiv a b).symm α).natTrans.app M) at ht
  rw [h] at ht
  rw [he] at ht
  apply ((derivedOpenImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} B) j).homEquiv _ _).injective
  unfold properOpenCoefficientOpenInverse
  dsimp only [Functor.comp_obj]
  rw [Equiv.apply_symm_apply]
  simp only [Adjunction.homEquiv_unit]
  have htransport := congrArg (fun z ↦ z ≫
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) j).hom.app
      ((scalarExtension φ T).obj
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj M))) ht.symm
  simp only [a, b, Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Iso.symm_hom, Functor.comp_obj, Functor.map_comp,
    Category.assoc] at htransport
  erw [(leftDerivedUpperStarIsoMapDerivedCategory
    (ModuleCat.{u + 1} B) j).hom.naturality
      ((ExceptionalCoefficients.openIso φ j).inv.app M)] at htransport
  dsimp only [Functor.comp_obj] at htransport
  erw [Iso.inv_hom_id_app_assoc] at htransport
  simpa only [scalarExtension, ProEtale.pbcFixedScalarExtension,
    properOpenCoefficientPullbackIso, Iso.trans_inv,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, Iso.symm_inv,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.assoc] using htransport

/-- Naturality of the published proper/open scalar components.
Source: Stacks 0GL6 (blueprint: lem-pur-etale-compact-scalar-coherence).
Proof: expand compactSupportMap. Naturality of scalarMate moves the open-extension
map past the proper scalar component. Naturality of openIso moves it past the open
component. Functoriality of proper direct image gives the displayed equality. -/
theorem compactScalarMap_naturality (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) {M N : DerivedCategoryModule A X} (a : M ⟶ N) :
    (scalarExtension φ Y).map
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map a) ≫
        ExceptionalCoefficients.compactSupportMap φ c N =
      ExceptionalCoefficients.compactSupportMap φ c M ≫
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c).map
          ((scalarExtension φ X).map a) := by
  let J := (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory
  let R := (lowerStar (ModuleCat.{u + 1} B) c.g).rightDerivedFunctor
  change (scalarExtension φ Y).map
      ((lowerStar (ModuleCat.{u + 1} A) c.g).rightDerivedFunctor.map (J.map a)) ≫
      (scalarMate φ c.g).app (J.obj N) ≫ R.map ((ExceptionalCoefficients.openIso φ c.i).hom.app N) =
    ((scalarMate φ c.g).app (J.obj M) ≫ R.map
      ((ExceptionalCoefficients.openIso φ c.i).hom.app M)) ≫
        R.map ((openImmersionLowerShriek (ModuleCat.{u + 1} B) c.i).mapDerivedCategory.map
          ((scalarExtension φ X).map a))
  have h := (scalarMate φ c.g).naturality (J.map a)
  dsimp only [Functor.comp_map] at h
  rw [← Category.assoc, h]
  simp only [Category.assoc]
  rw [← R.map_comp, ← R.map_comp]
  congr 1
  have h' := (ExceptionalCoefficients.openIso φ c.i).hom.naturality a
  dsimp only [Functor.comp_map] at h'
  exact congrArg R.map h'


/-- Package the published proper/open scalar components as a natural transformation.
Source: Stacks 0GL6 (blueprint: lem-pur-etale-compact-scalar-coherence). -/
def compactScalarMap (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) :
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⋙
        scalarExtension φ Y ⟶ scalarExtension φ X ⋙
          rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c where
  app := ExceptionalCoefficients.compactSupportMap φ c
  naturality _ _ a := compactScalarMap_naturality φ c a

/-- The proper-counit/open-tensor projection, in coefficient-first order.
Source: Stacks 0GL6, preceding projection lemma
(blueprint: lem-pur-etale-compact-scalar-coherence). -/
def compactScalarProjection (R : Type (u + 1)) [CommRing R]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategoryModule R Y) (M : DerivedCategoryModule R X) :
    ((derivedTensor (ModuleCat.{u + 1} R) Y).obj K).obj
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) c).obj M) ⟶
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) c).obj
        (((derivedTensor (ModuleCat.{u + 1} R) X).obj
          ((upperStar (ModuleCat.{u + 1} R) f).leftDerivedFunctor.obj K)).obj M) :=
  ((derivedTensorSymmetry (ModuleCat.{u + 1} R) Y).hom.app K).app
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) c).obj M) ≫
    ((projectionMapOfCompactification (ModuleCat.{u + 1} R) c).app M).app K ≫
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) c).map
      (((derivedTensorSymmetry (ModuleCat.{u + 1} R) X).hom.app M).app
        ((upperStar (ModuleCat.{u + 1} R) f).leftDerivedFunctor.obj K))

/-- Scalar identification of the target of the ordered projection map.
Source: Stacks 07A4 (blueprint: lem-pur-etale-compact-scalar-coherence). -/
def compactScalarProjectionTarget (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategoryModule A Y) (M : DerivedCategoryModule A X) :
    (scalarExtension φ X).obj
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj
          ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K)).obj M) ⟶
      ((derivedTensor (ModuleCat.{u + 1} B) X).obj
        ((upperStar (ModuleCat.{u + 1} B) f).leftDerivedFunctor.obj
          ((scalarExtension φ Y).obj K))).obj ((scalarExtension φ X).obj M) :=
  (ExceptionalCoefficients.tensorIso φ X).hom.app
      ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K, M) ≫
    ((derivedTensor (ModuleCat.{u + 1} B) X).map
      ((scalarPullbackIso φ f).inv.app K)).app ((scalarExtension φ X).obj M)

/-- The specified scalar map for the chosen compactification.
Source: Stacks 0GL6 (blueprint: lem-pur-etale-compact-scalar-coherence). -/
def compactScalarChosenMap (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] :=
  compactScalarMap φ (HasCompactification.compactification f)

/-- Scalar coherence for the fixed compactification: natural invertibility, the ordered
projection square on every derived input, and proper-refinement compatibility on precisely
the bounded-below pair of inputs specified in the node.
Source: Stacks 0GL6, 0E48 and 0F7I
(blueprint: lem-pur-etale-compact-scalar-coherence).
Proof: step 4 combines the proper scalar isomorphism with the open balancing isomorphism.
The ambient compactification is Noetherian by finite type over its Noetherian target.
Step 5 applies ringed exchange/tensor coherence to the identity-topos coefficient square,
then the two tensor symmetries give the ordered proper projection square. Step 6 checks
the open square on K-flat total tensor generators, including the identical Koszul signs.
Step 7 substitutes the proper/open definitions and uses naturality to paste those squares.
Step 8 proves proper composition by counit mate pasting and open composition by open-unit
transposes. Step 9 applies properOpenComparison_coefficient_refinement to M and Q M in D+,
then proper composition and common-refinement coherence give the displayed comparison
for every pair of compactifications. No flatness or Tor bound is used. -/
theorem etaleCompactScalarCoherence
    [Finite A] [Finite B] (φ : A →+* B)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) :
    (∀ M : DerivedCategoryModule A X, IsIso ((compactScalarMap φ c).app M)) ∧
    (∀ (K : DerivedCategoryModule A Y) (M : DerivedCategoryModule A X),
      (scalarExtension φ Y).map (compactScalarProjection A c K M) ≫
          (compactScalarMap φ c).app
            (((derivedTensor (ModuleCat.{u + 1} A) X).obj
              ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K)).obj M) ≫
          (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c).map
            (compactScalarProjectionTarget φ f K M) =
        (ExceptionalCoefficients.tensorIso φ Y).hom.app
            (K, (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj M) ≫
          ((derivedTensor (ModuleCat.{u + 1} B) Y).obj
            ((scalarExtension φ Y).obj K)).map ((compactScalarMap φ c).app M) ≫
          compactScalarProjection B c ((scalarExtension φ Y).obj K)
            ((scalarExtension φ X).obj M)) ∧
    (∀ (d : Compactification f)
      (M : _root_.DerivedCategory.Plus
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))),
      (∃ N : _root_.DerivedCategory.Plus
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)),
        N.obj = (scalarExtension φ X).obj M.obj) →
      (scalarExtension φ Y).map
          ((rightDerivedLowerShriekOfCompactificationIso A c d).hom.app M.obj) ≫
          (compactScalarMap φ d).app M.obj =
        (compactScalarMap φ c).app M.obj ≫
          (rightDerivedLowerShriekOfCompactificationIso B c d).hom.app
            ((scalarExtension φ X).obj M.obj)) := by
  sorry

/-- The normalized proper/open composition square for scalar extension.
Source: Stacks 0F7J and 0GL6 (blueprint: lem-pur-etale-compact-scalar-coherence).
Proof: step 10 chooses the proper/open tower of the compact-support comparison theorem.
Apply the coefficient mate theorem to its cartesian proper/open square. Its input j_!M
and its scalar extension are bounded below by exactness of open extension and the two
assumed bounds. Paste with the scalar squares for the outer proper map and inner open.
Step 8 supplies composition of the proper and open scalar maps. Step 9 transfers the
result to the chosen compactifications. For the outer compactification this is valid
because F_f M and Q F_f M are bounded below: use bounded-below injective resolutions,
exact open extension, and Q F_f M = F_f Q M from the scalar isomorphism. This is exactly
the specified normalized composition equation, with no claim that arbitrary Q preserves D+. -/
theorem etaleCompactScalarComposition
    [Finite A] [Finite B] (φ : A →+* B)
    {X Y Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (M : _root_.DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (_hQM : ∃ N : _root_.DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)),
      N.obj = (scalarExtension φ X).obj M.obj) :
    (scalarExtension φ Z).map
        ((unboundedEtaleLowerShriekCompIso A f g).hom.app M.obj) ≫
        (compactScalarChosenMap φ (f ≫ g)).app M.obj =
      (compactScalarChosenMap φ g).app
          ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj M.obj) ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} B) g).map
          ((compactScalarChosenMap φ f).app M.obj) ≫
        (unboundedEtaleLowerShriekCompIso B f g).hom.app
          ((scalarExtension φ X).obj M.obj) := by
  sorry

/-- The open-restriction scalar square, using the restricted compactification.
Source: Stacks 0F7L, 0GL6 and 0E48
(blueprint: lem-pur-etale-compact-scalar-coherence).
Proof: step 11 identifies proper open-restriction exchange by its counit transpose.
Ringed exchange/tensor coherence applied to the coefficient square gives its scalar square.
Step 12 checks the open-extension base-change scalar square on K-flat representatives:
on the unique open summand both maps are scalar tensor; elsewhere both are zero. The
inverse comparison has the prescribed open-unit transpose. Step 13 expands compact-support
exchange into proper exchange and open exchange, substitutes the scalar proper/open
formula, and pastes the squares using naturality. Everything works on unbounded inputs. -/
theorem etaleCompactScalarOpenRestriction
    [Finite A] [Finite B] (φ : A →+* B)
    {X XV Y V : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {fv : XV ⟶ V} {v : V ⟶ Y} {vx : XV ⟶ X} [IsOpenImmersion v]
    (sq : IsPullback vx fv f v) (c : Compactification f)
    (M : DerivedCategoryModule A X) :
    (upperStar (ModuleCat.{u + 1} B) v).mapDerivedCategory.map
        ((compactScalarMap φ c).app M) ≫
        (unboundedEtaleCompactSupportExchange B sq c).app
          ((scalarExtension φ X).obj M) ≫
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B)
          (c.ofIsPullback sq)).map ((properOpenCoefficientPullbackIso φ vx).hom.app M) =
      (properOpenCoefficientPullbackIso φ v).hom.app
          ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj M) ≫
        (scalarExtension φ V).map
          ((unboundedEtaleCompactSupportExchange A sq c).app M) ≫
        (compactScalarMap φ (c.ofIsPullback sq)).app
          ((upperStar (ModuleCat.{u + 1} A) vx).mapDerivedCategory.obj M) := by
  sorry

/-- The left unit equation, with the monoidal data shared before specialization.
Source: Stacks 07A4 (blueprint: lem-pur-etale-compact-scalar-coherence). -/
def CompactScalarTensorUnitLaw
    {C : Type w₁} {D : Type w₂} [Category.{v₁} C] [Category.{v₂} D]
    [MonoidalCategory C] [MonoidalCategory D] (Q : C ⥤ D)
    (δ : Functor.uncurry.obj (curriedTensor C) ⋙ Q ≅
      Q.prod Q ⋙ Functor.uncurry.obj (curriedTensor D)) (e : Q.obj (𝟙_ C) ≅ 𝟙_ D) : Prop :=
  ∀ M : C, δ.hom.app (𝟙_ C, M) ≫ e.hom ▷ Q.obj M ≫ (λ_ (Q.obj M)).hom =
    Q.map (λ_ M).hom

/-- The pullback/scalar coefficient-unit equation, with shared categorical endpoints.
Source: Stacks 07A4 (blueprint: lem-pur-etale-compact-scalar-coherence). -/
def CompactScalarPullUnitLaw
    {C : Type w₁} {D : Type w₂} {E : Type w₃} {F : Type w₄}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Category.{v₄} F]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E] [MonoidalCategory F]
    (Q : C ⥤ D) (Q' : E ⥤ F) (L : C ⥤ E) (L' : D ⥤ F)
    (δ : Q ⋙ L' ≅ L ⋙ Q') (e : Q.obj (𝟙_ C) ≅ 𝟙_ D)
    (e' : Q'.obj (𝟙_ E) ≅ 𝟙_ F) (l : L.obj (𝟙_ C) ≅ 𝟙_ E)
    (l' : L'.obj (𝟙_ D) ≅ 𝟙_ F) : Prop :=
  δ.hom.app (𝟙_ C) ≫ Q'.map l.hom ≫ e'.hom = L'.map e.hom ≫ l'.hom

/-- The structural comparisons preserve the actual multiplication coefficient unit.
Together with the projection square at K = A_Y[0], this is its canonical unit normalization.
Source: Stacks 07A4 and 0B56 (blueprint: lem-pur-etale-compact-scalar-coherence).
Proof: step 14 evaluates the K-flat representative comparisons at the unit. Multiplication
is a tensor b maps to φ(a)b. The scalar tensor and pullback paths agree on pure tensors.
Open balancing is that same map on the open and zero elsewhere; the proper projection
against the unit is the identity by the unital projection-mate theorem. The counit and
open-unit transposes consequently retain this coefficient-unit identification in all
projection, composition and refinement squares. The raw tensor comparison here is the
same one as the site's comparison, by ExceptionalCoefficients.siteTensorIso_existsUnique. -/
theorem etaleCompactScalarUnit (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    CompactScalarTensorUnitLaw (scalarExtension φ Y)
      (ExceptionalCoefficients.tensorIso_existsUnique φ Y).choose
      (ExceptionalCoefficients.unitIso φ Y) ∧
    CompactScalarPullUnitLaw (scalarExtension φ Y) (scalarExtension φ X)
      (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor
      (upperStar (ModuleCat.{u + 1} B) f).leftDerivedFunctor
      (scalarPullbackIso φ f) (ExceptionalCoefficients.unitIso φ Y)
      (ExceptionalCoefficients.unitIso φ X)
      (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) f)
      (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} B) f) := by
  sorry

end AlgebraicGeometry.Etale
