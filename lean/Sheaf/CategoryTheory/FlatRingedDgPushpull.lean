module

public import Sheaf.CategoryTheory.SheafDgModuleLocalization
public import Sheaf.CategoryTheory.SheafDgHomotopicalInjectivity
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Shift.Adjunction
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Sheaf.CategoryTheory.GrothendieckAbelian.ObjectsSmall
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.CategoryTheory.Localization.Triangulated
import Mathlib.CategoryTheory.Triangulated.Orthogonal

/-! # Flat ringed dg push-pull

Source: Stacks Project, sdga.tex, Tags 0FT0, 0FRU, 0FTR and 0FTW, with the
K-flat forgetful refinement (blueprint: lem-sfb-flat-ringed-dg-pushpull).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u wX wZ

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry TopologicalSpace Opposite CategoryTheory.Pretriangulated

namespace CategoryTheory.SheafDg

variable {X Z : RingedSpace.{u}} (f : X ⟶ Z)

/-- Ordinary module pullback, the existing sheaf tensor-pullback left adjoint.
Source: Stacks, 0FRU (blueprint: lem-sfb-flat-ringed-dg-pushpull). -/
abbrev coefficientPullback :
    SheafOfModules.{u} (moduleRings Z) ⥤ SheafOfModules.{u} (moduleRings X) :=
  SheafOfModules.pullback (F := Opens.map f.hom.base)
    (R := moduleRings X) (S := moduleRings Z)
    ⟨Functor.whiskerRight f.hom.c (forget₂ CommRingCat RingCat)⟩

/-- The ordinary tensor-pullback/direct-image adjunction, including its specified maps.
Source: Stacks, 0FRU (blueprint: lem-sfb-flat-ringed-dg-pushpull). -/
abbrev coefficientAdjunction : coefficientPullback f ⊣ RingedSpace.moduleDirectImage f :=
  SheafOfModules.pullbackPushforwardAdjunction
    (F := Opens.map f.hom.base) (R := moduleRings X) (S := moduleRings Z)
    ⟨Functor.whiskerRight f.hom.c (forget₂ CommRingCat RingCat)⟩

/-- Additivity needed for termwise pullback of arbitrary integer complexes.
Source: Stacks, 0FRU (blueprint: lem-sfb-flat-ringed-dg-pushpull).
Proof: the left adjoint preserves finite coproducts, hence finite biproducts in
these additive categories. Preservation of biproducts is equivalent to additivity. -/
@[instance] theorem coefficientPullback_additive : (coefficientPullback f).Additive := by
  sorry

/-- Termwise ordinary pullback, with no degree bound.
Source: Stacks, 0FRU (blueprint: lem-sfb-flat-ringed-dg-pushpull). -/
abbrev pullComplex : Complex Z.sheaf ⥤ Complex X.sheaf :=
  (coefficientPullback f).mapHomologicalComplex (.up ℤ)

/-- Termwise ordinary pushforward, with its coefficient action through f-sharp.
Source: Stacks, 0FRU (blueprint: lem-sfb-flat-ringed-dg-pushpull). -/
abbrev pushComplex : Complex X.sheaf ⥤ Complex Z.sheaf :=
  (RingedSpace.moduleDirectImage f).mapHomologicalComplex (.up ℤ)

/-- Pull a section over V to the inverse-image open, through the ordinary adjunction unit.
Source: Stacks, 0FRU (blueprint: lem-sfb-flat-ringed-dg-pushpull). -/
def pullSection (M : SheafOfModules.{u} (moduleRings Z)) (V : (Opens Z)ᵒᵖ)
    (m : M.val.obj V) :
    ((coefficientPullback f).obj M).val.obj ((Opens.map f.hom.base).op.obj V) :=
  ((coefficientAdjunction f).unit.app M).val.app V m

variable (A : Algebra Z.sheaf)

/-- Multiplication on the actual pulled-back complex is obtained by tensoring:
the pullback-unit images of a and b multiply to the pullback-unit image of ab.
These images generate the pullback locally over O_X. The unit is determined by
multiplication and the unital monoid axioms.
Source: Stacks, 0FRU (blueprint: lem-sfb-flat-ringed-dg-pushpull). -/
def IsPullbackAlgebra (a : MonObj ((pullComplex f).obj A.X)) : Prop :=
  ∀ (p q : ℤ) (V : (Opens Z)ᵒᵖ)
    (x : (A.X.X p).val.obj V) (y : (A.X.X q).val.obj V),
    actionSection (algebraOn _ a) (regular (algebraOn _ a)) p q
        ((Opens.map f.hom.base).op.obj V)
        (pullSection f (A.X.X p) V x) (pullSection f (A.X.X q) V y) =
      pullSection f (A.X.X (p + q)) V (actionSection A (regular A) p q V x y)

/-- The tensor formula fixes the pulled-back dg algebra uniquely.
Source: Stacks, 0FRU (blueprint: lem-sfb-flat-ringed-dg-pushpull).
Proof: inverse image followed by extension of scalars is strong monoidal.
Apply it to multiplication and unit, and sum its tensor comparison over bidegrees.
The chain-map condition is the pulled-back Leibniz identity. Locally, pullback-unit
images generate over O_X, so the displayed bilinear formula determines multiplication.
A unital associative multiplication has a unique unit. -/
theorem existsUnique_pullbackAlgebra :
    ∃! a : MonObj ((pullComplex f).obj A.X), IsPullbackAlgebra f A a := by
  sorry

/-- The algebra B=f^*C, on the actual termwise pullback complex.
Source: Stacks, 0FRU (blueprint: lem-sfb-flat-ringed-dg-pushpull). -/
def pullbackAlgebra : Algebra X.sheaf :=
  algebraOn _ (existsUnique_pullbackAlgebra f A).choose

/-- The pulled-back action is fixed on the local generators by a times m.
Source: Stacks, 0FRU (blueprint: lem-sfb-flat-ringed-dg-pushpull). -/
def IsPullbackAction (M : LeftModule A)
    (a : ModObj (pullbackAlgebra f A).X ((pullComplex f).obj M.X)) : Prop :=
  ∀ (p q : ℤ) (V : (Opens Z)ᵒᵖ)
    (x : (A.X.X p).val.obj V) (m : (M.X.X q).val.obj V),
    actionSection (pullbackAlgebra f A) (moduleOn _ _ a) p q
        ((Opens.map f.hom.base).op.obj V)
        (pullSection f (A.X.X p) V x) (pullSection f (M.X.X q) V m) =
      pullSection f (M.X.X (p + q)) V (actionSection A M p q V x m)

/-- The pulled-back module action is uniquely specified by tensoring the old action.
Source: Stacks, 0FRU (blueprint: lem-sfb-flat-ringed-dg-pushpull).
Proof: use the same strong monoidal comparison as for the pulled-back algebra.
The old action equations give the new unital and associative action. The Leibniz
identity gives a chain map. Local pullback generators determine it uniquely. -/
theorem existsUnique_pullbackAction (M : LeftModule A) :
    ∃! a : ModObj (pullbackAlgebra f A).X ((pullComplex f).obj M.X),
      IsPullbackAction f A M a := by
  sorry

/-- Pullback of a dg module, on the degreewise ordinary module pullback.
Source: Stacks, 0FRU (blueprint: lem-sfb-flat-ringed-dg-pushpull). -/
def pullModule (M : LeftModule A) : LeftModule (pullbackAlgebra f A) :=
  moduleOn _ _ (existsUnique_pullbackAction f A M).choose

/-- The induced C-action on f_*M: act by the pullback-unit image of c over f^-1(V).
Source: Stacks, 0FRU (blueprint: lem-sfb-flat-ringed-dg-pushpull). -/
def IsPushforwardAction (M : LeftModule (pullbackAlgebra f A))
    (a : ModObj A.X ((pushComplex f).obj M.X)) : Prop :=
  ∀ (p q : ℤ) (V : (Opens Z)ᵒᵖ) (x : (A.X.X p).val.obj V)
    (m : (M.X.X q).val.obj ((Opens.map f.hom.base).op.obj V)),
    actionSection A (moduleOn _ _ a) p q V x m =
      actionSection (pullbackAlgebra f A) M p q ((Opens.map f.hom.base).op.obj V)
        (pullSection f (A.X.X p) V x) m

/-- The sectionwise formula gives exactly one pushforward action.
Source: Stacks, 0FRU (blueprint: lem-sfb-flat-ringed-dg-pushpull).
Proof: the ordinary tensor-sheaf universal property assembles the displayed bilinear
maps. Restrictions commute with them. The pulled algebra formula and the old module
axioms give associativity and unit; the Leibniz identities give differential compatibility.
Pure tensors locally generate the tensor sheaf, proving uniqueness. -/
theorem existsUnique_pushforwardAction (M : LeftModule (pullbackAlgebra f A)) :
    ∃! a : ModObj A.X ((pushComplex f).obj M.X), IsPushforwardAction f A M a := by
  sorry

/-- Degreewise dg direct image with the induced C-action.
Source: Stacks, 0FRU (blueprint: lem-sfb-flat-ringed-dg-pushpull). -/
def pushModule (M : LeftModule (pullbackAlgebra f A)) : LeftModule A :=
  moduleOn _ _ (existsUnique_pushforwardAction f A M).choose

/-- Termwise pullback maps preserve the specified pulled-back actions.
Source: Stacks, 0FRU (blueprint: lem-sfb-flat-ringed-dg-pushpull).
Proof: check on the pullback-unit generators. Naturality of the ordinary unit and
the old module-map equation give the equality there; bilinearity gives it locally everywhere. -/
theorem pullMap_linear {M N : LeftModule A} (g : M ⟶ N) :
    IsModHom (pullbackAlgebra f A).X
      (@id ((pullModule f A M).X ⟶ (pullModule f A N).X) ((pullComplex f).map g.hom)) := by
  sorry

/-- Termwise pushforward maps preserve the induced actions.
Source: Stacks, 0FRU (blueprint: lem-sfb-flat-ringed-dg-pushpull).
Proof: substitute the sectionwise action formula and apply the old module-map equation. -/
theorem pushMap_linear {M N : LeftModule (pullbackAlgebra f A)} (g : M ⟶ N) :
    IsModHom A.X
      (@id ((pushModule f A M).X ⟶ (pushModule f A N).X) ((pushComplex f).map g.hom)) := by
  sorry

/-- The exact degreewise dg pullback before localization.
Source: Stacks, 0FRU (blueprint: lem-sfb-flat-ringed-dg-pushpull). -/
def pullModules : LeftModule A ⥤ LeftModule (pullbackAlgebra f A) where
  obj := pullModule f A
  map g := { hom := (pullComplex f).map g.hom, isModHom := pullMap_linear f A g }
  map_id M := Mod.hom_ext _ _ ((pullComplex f).map_id M.X)
  map_comp g h := Mod.hom_ext _ _ ((pullComplex f).map_comp g.hom h.hom)

/-- Degreewise dg direct image before deriving.
Source: Stacks, 0FRU (blueprint: lem-sfb-flat-ringed-dg-pushpull). -/
def pushModules : LeftModule (pullbackAlgebra f A) ⥤ LeftModule A where
  obj := pushModule f A
  map g := { hom := (pushComplex f).map g.hom, isModHom := pushMap_linear f A g }
  map_id M := Mod.hom_ext _ _ ((pushComplex f).map_id M.X)
  map_comp g h := Mod.hom_ext _ _ ((pushComplex f).map_comp g.hom h.hom)

/-- The underived dg adjunction is precisely the ordinary termwise adjunction on maps.
Source: Stacks, 0FRU (blueprint: lem-sfb-flat-ringed-dg-pushpull).
Proof: the ordinary Hom bijection restricts to action-preserving maps by the two
action formulas. Its inverse restricts as well. Naturality is inherited from the
ordinary adjunction. These restricted bijections determine the adjunction uniquely. -/
theorem existsUnique_moduleAdjunction :
    ∃! a : pullModules f A ⊣ pushModules f A,
      ∀ (M : LeftModule A) (N : LeftModule (pullbackAlgebra f A))
        (g : (pullModules f A).obj M ⟶ N),
        ((a.homEquiv M N) g).hom =
          (((coefficientAdjunction f).mapHomologicalComplex (.up ℤ)).homEquiv M.X N.X)
            g.hom := by
  sorry

/-- The canonical dg adjunction, determined by the ordinary tensor Hom bijection.
Source: Stacks, 0FRU (blueprint: lem-sfb-flat-ringed-dg-pushpull). -/
def moduleAdjunction : pullModules f A ⊣ pushModules f A :=
  (existsUnique_moduleAdjunction f A).choose

/-- Direct image carries signed dg homotopies to signed dg homotopies.
Source: Stacks, 0FRU (blueprint: lem-sfb-flat-ringed-dg-pushpull).
Proof: apply termwise direct image to the homotopy. It preserves addition and
composition, hence the homotopy equation. The induced C-action preserves the signed
linearity equation, checked on sections over inverse-image opens. -/
theorem pushModules_homotopy {M N : LeftModule (pullbackAlgebra f A)}
    (g h : M ⟶ N) (e : homotopyRel (pullbackAlgebra f A) g h) :
    (q A).map ((pushModules f A).map g) = (q A).map ((pushModules f A).map h) := by
  sorry

/-- Direct image on the dg homotopy quotient, obtained by its actual quotient lift.
Source: Stacks, 0FRU (blueprint: lem-sfb-flat-ringed-dg-pushpull). -/
def pushHomotopy : Homotopy (pullbackAlgebra f A) ⥤ Homotopy A :=
  Quotient.lift (homotopyRel (pullbackAlgebra f A)) (pushModules f A ⋙ q A)
    (fun _ _ g h e ↦ pushModules_homotopy f A g h e)

section Flat

variable [PreservesFiniteLimits (coefficientPullback f)]

/-- Exact degreewise dg pullback descends uniquely through the two localizations.
Source: Stacks, 0FRU and 0FTR (blueprint: lem-sfb-flat-ringed-dg-pushpull).
Proof: apply the additive pullback to a signed homotopy and use the pulled action
formula. Exactness preserves all cohomology sheaves, hence quasi-isomorphisms.
The quotient and the finite-word localization therefore give a unique strict lift. -/
theorem existsUnique_derivedPullback :
    ∃! L : Derived A ⥤ Derived (pullbackAlgebra f A),
      moduleQ A ⋙ L = pullModules f A ⋙ moduleQ (pullbackAlgebra f A) := by
  sorry

/-- The derived dg pullback, determined on every module map and formal inverse.
Source: Stacks, 0FTR (blueprint: lem-sfb-flat-ringed-dg-pushpull). -/
def derivedPullback : Derived A ⥤ Derived (pullbackAlgebra f A) :=
  (existsUnique_derivedPullback f A).choose

/-- Its canonical factorization through degreewise pullback.
Source: Stacks, 0FTR (blueprint: lem-sfb-flat-ringed-dg-pushpull). -/
def derivedPullbackFactors :
    moduleQ A ⋙ derivedPullback f A ≅ pullModules f A ⋙ moduleQ (pullbackAlgebra f A) :=
  eqToIso (existsUnique_derivedPullback f A).choose_spec.1

variable [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X))]
  [HasDerivedCategory.{wZ} (SheafOfModules.{u} (moduleRings Z))]

/-- The ordinary exact-pullback/derived-pushforward adjunction, normalized by the
ordinary underived adjunction and the existing right-derived comparison.
Source: Stacks, 0FTR and 0FTW, ordinary specialization
(blueprint: lem-sfb-flat-ringed-dg-pushpull).
Proof: termwise pullback is exact, so its localization is its own left derived functor.
Direct image has K-injective resolutions. Its comparison is invertible on such
resolutions. Derive the ordinary adjunction using those comparisons. The displayed
unit equation follows from the derived adjunction construction. Every object of the
ordinary derived category is the localization of a complex, and its factorization
comparison is invertible, so that equation determines the unit and hence the adjunction. -/
theorem existsUnique_ordinaryDerivedAdjunction :
    ∃! a : (coefficientPullback f).mapDerivedCategory ⊣ RingedSpace.derivedModuleDirectImage f,
      ∀ K : HomotopyCategory (SheafOfModules.{u} (moduleRings Z)) (.up ℤ),
        a.unit.app (DerivedCategory.Qh.obj K) ≫
            (RingedSpace.derivedModuleDirectImage f).map
              ((coefficientPullback f).mapDerivedCategoryFactorsh.hom.app K) =
          DerivedCategory.Qh.map
              (((coefficientAdjunction f).mapHomotopyCategory (.up ℤ)).unit.app K) ≫
            (RingedSpace.moduleDirectImage f).rightDerivedFunctorUnit.app
              (((coefficientPullback f).mapHomotopyCategory (.up ℤ)).obj K) := by
  sorry

/-- The ordinary adjunction with the specified unit and evaluation counit.
Source: Stacks, 0FTR, 0FTW (blueprint: lem-sfb-flat-ringed-dg-pushpull). -/
def ordinaryDerivedAdjunction :
    (coefficientPullback f).mapDerivedCategory ⊣ RingedSpace.derivedModuleDirectImage f :=
  (existsUnique_ordinaryDerivedAdjunction f).choose

/-- Flat ringed dg push-pull, injective representatives, and the normalized underlying
ordinary derived comparison, with no boundedness condition.

Source: Stacks, 0FT0, 0FRU, 0FTR, 0FTW and the K-flat refinement
(blueprint: lem-sfb-flat-ringed-dg-pushpull).

Proof:
1. Use lem-sfb-sheaf-dg-grothendieck and lem-sfb-sheaf-dg-injectivity-tests.
Attach coproducts of their acyclic monomorphisms to M by pushouts. The quotient
is the coproduct of their acyclic cokernels; the cohomology long exact sequence
(lem-weil-pbc-complex-ses-homology-long-exact) makes each attachment a quasi-isomorphism.
2. Iterate through a limit ordinal of cofinality above all test-object subobject
cardinals. Exact filtered colimits preserve these monic quasi-isomorphisms.
prop-pur-kinjective-objects-small factors every test map through a prior stage,
where the next attachment extends it. Thus the limit I is homotopically injective.
3. The free/forgetful specialization of lem-sfb-sheaf-dg-pushpull-hom identifies
Hom(L,U I) with Hom(B tensor L,I). K-flatness of B makes the free input acyclic,
so U I is K-injective. The same argument applies to C on Z.
4. lem-sfb-sheaf-dg-homotopy-system and lem-pur-localization-triangles-05r6 give
the triangulated localization. Homotopically injective modules are right orthogonal
to acyclics, so lem-sfb-right-orthogonal-localization-hom identifies homotopy and
derived Hom into I. Together with step 2 this is an exact equivalence on injectives.
5. Exact pullback preserves acyclics. The Hom-complex adjunction shows that f_*I
is homotopically injective. Apply f_* on injective representatives, then localize:
this constructs R and preserves signed shifts and cones.
6. The localization has right adjoint given by injective replacement. Its unit and
invertible counit give the Kan-extension bijection by composition. Triangle identities
show its two directions inverse, proving the right-derived universal property for beta.
7. Compose localized Hom into I, the underived Hom adjunction, and localized Hom into
f_*I. This gives the exact derived adjunction with the displayed unit/counit formulas.
8. Pullback has literally the same underlying complex. For pushforward, step 3 makes
every dg injective resolution an ordinary K-injective resolution. The two composites
are represented by the same f_*U I; their comparison is the identity on representatives.
lem-weil-pbc-kinjective-hom-derived makes this comparison natural in derived maps.
9. After forgetting, f_*U I is ordinary K-injective, by exact pullback and the ordinary
Hom adjunction. The Hom correspondence in step 7 therefore becomes the ordinary one.
Applying it to identities identifies both units and both evaluation counits. This gives
the last two equations. Every complex and every degree used above is unbounded. -/
theorem flat_ringed_dg_pushpull
    (hA : A.X.IsKFlatIndependentCoefficients)
    (hB : (pullbackAlgebra f A).X.IsKFlatIndependentCoefficients) :
    (∀ M : LeftModule (pullbackAlgebra f A),
      ∃ (I : LeftModule (pullbackAlgebra f A)) (s : M ⟶ I),
        QuasiIso s.hom ∧ IsHomotopicallyInjective (pullbackAlgebra f A) I) ∧
    (∀ I : LeftModule (pullbackAlgebra f A),
      IsHomotopicallyInjective (pullbackAlgebra f A) I → I.X.IsKInjective) ∧
    ∃ (R : Derived (pullbackAlgebra f A) ⥤ Derived A)
      (β : pushHomotopy f A ⋙ Q A ⟶ Q (pullbackAlgebra f A) ⋙ R)
      (sL : (derivedPullback f A).CommShift ℤ) (sR : R.CommShift ℤ)
      (a : derivedPullback f A ⊣ R)
      (lcmp : derivedPullback f A ⋙ forget (pullbackAlgebra f A) ≅
        forget A ⋙ (coefficientPullback f).mapDerivedCategory)
      (rcmp : R ⋙ forget A ≅ forget (pullbackAlgebra f A) ⋙
        RingedSpace.derivedModuleDirectImage f),
      R.IsRightDerivedFunctor β (quasiIsomorphisms (pullbackAlgebra f A)) ∧
      (∀ I : LeftModule (pullbackAlgebra f A),
        IsHomotopicallyInjective (pullbackAlgebra f A) I →
          IsIso (β.app ((q (pullbackAlgebra f A)).obj I))) ∧
      (∀ t : Triangle (Derived A), IsConeTriangle A t →
        IsConeTriangle (pullbackAlgebra f A)
          ((@Functor.mapTriangle _ _ _ _ _ _ (derivedPullback f A) sL).obj t)) ∧
      (∀ t : Triangle (Derived (pullbackAlgebra f A)),
        IsConeTriangle (pullbackAlgebra f A) t →
          IsConeTriangle A ((@Functor.mapTriangle _ _ _ _ _ _ R sR).obj t)) ∧
      (@Adjunction.CommShift _ _ _ _ (derivedPullback f A) R a ℤ _ _ _ sL sR) ∧
      (∀ M : LeftModule A,
        a.unit.app ((moduleQ A).obj M) ≫ R.map ((derivedPullbackFactors f A).hom.app M) =
          (moduleQ A).map ((moduleAdjunction f A).unit.app M) ≫
            β.app ((q (pullbackAlgebra f A)).obj ((pullModules f A).obj M))) ∧
      (∀ I : LeftModule (pullbackAlgebra f A),
        (derivedPullback f A).map (β.app ((q (pullbackAlgebra f A)).obj I)) ≫
            a.counit.app ((moduleQ (pullbackAlgebra f A)).obj I) =
          (derivedPullbackFactors f A).hom.app ((pushModules f A).obj I) ≫
            (moduleQ (pullbackAlgebra f A)).map ((moduleAdjunction f A).counit.app I)) ∧
      (∀ M : LeftModule A,
        lcmp.hom.app ((moduleQ A).obj M) ≫
            (coefficientPullback f).mapDerivedCategoryFactorsh.hom.app
              ((HomotopyCategory.quotient _ (.up ℤ)).obj M.X) =
          (forget (pullbackAlgebra f A)).map ((derivedPullbackFactors f A).hom.app M)) ∧
      (∀ I : LeftModule (pullbackAlgebra f A),
        (forget A).map (β.app ((q (pullbackAlgebra f A)).obj I)) ≫
            rcmp.hom.app ((moduleQ (pullbackAlgebra f A)).obj I) =
          (RingedSpace.moduleDirectImage f).rightDerivedFunctorUnit.app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj I.X)) ∧
      (∀ N : Derived A,
        (forget A).map (a.unit.app N) ≫ rcmp.hom.app ((derivedPullback f A).obj N) ≫
            (RingedSpace.derivedModuleDirectImage f).map (lcmp.hom.app N) =
          (ordinaryDerivedAdjunction f).unit.app ((forget A).obj N)) ∧
      (∀ M : Derived (pullbackAlgebra f A),
        (coefficientPullback f).mapDerivedCategory.map (rcmp.inv.app M) ≫
            lcmp.inv.app (R.obj M) ≫ (forget (pullbackAlgebra f A)).map (a.counit.app M) =
          (ordinaryDerivedAdjunction f).counit.app ((forget (pullbackAlgebra f A)).obj M)) := by
  sorry

end Flat

end CategoryTheory.SheafDg
