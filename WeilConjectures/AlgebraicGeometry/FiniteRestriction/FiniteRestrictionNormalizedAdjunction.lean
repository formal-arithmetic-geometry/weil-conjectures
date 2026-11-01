/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteCompactSupportEncoding
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedFiniteTorConstructible
public import WeilConjectures.AlgebraicGeometry.SixFunctors.SpecifiedExceptionalClassHom
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.CategoryTheory.Shift.Adjunction
import WeilConjectures.AlgebraicGeometry.SixFunctors.SpecifiedExceptionalRealizationShift
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEquivalence
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleEncoding
import WeilConjectures.AlgebraicGeometry.Finite.FiniteCtfTriangulated
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import WeilConjectures.Mathlib.CategoryTheory.Sites.GlobalSections
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Defs
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import WeilConjectures.Compactification.Refinement
import WeilConjectures.Compactification.RefinementCategory
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ModuleDerivedCategory
import Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Mathlib.AlgebraicGeometry.Over
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # The normalized finite restriction adjunction

Source: latest blueprint, sk-thm-sf-tensor-hom, Complement; Zheng, Proposition 2.23.
(blueprint: lem-sf-finite-restriction-normalized-adjunction).

The normalized section-action encodings are explicit inputs specifying the coefficient
coordinates. Intrinsic objects are native modules over the pulled-back condensed ring.
The support comparison is constructed from the existing open and proper comparisons.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.FiniteRestriction

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- The current intrinsic bounded constructible finite-Tor predicate.
Source: blueprint det-def-sf-operations (vi), finite domain.
(blueprint: lem-sf-finite-restriction-normalized-adjunction). -/
abbrev property (T : Scheme.{u}) :=
  CondensedRing.condensedConstructibleFiniteTor (coefficient A) T

/-- The actual full intrinsic finite-Tor category, with no replacement by fixed modules.
Source: blueprint det-def-sf-operations (vi), finite domain.
(blueprint: lem-sf-finite-restriction-normalized-adjunction). -/
abbrev Category (T : Scheme.{u}) := (property A T).FullSubcategory

/-- The fixed scalar derived presentation in the site's coefficient universe.
Source: blueprint sk-thm-sf-tensor-hom, Complement, coefficient coordinates.
(blueprint: lem-sf-finite-restriction-normalized-adjunction). -/
abbrev Fixed (T : Scheme.{u}) :=
  DerivedCategory (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A)))

/-- The full inclusion followed by q, the termwise section-action encoding.
Source: blueprint sk-thm-sf-tensor-hom, Complement, R=qI.
(blueprint: lem-sf-finite-restriction-normalized-adjunction). -/
abbrev realization (E : ∀ T : Scheme.{u}, Encoding A T) (T : Scheme.{u}) :=
  (property A T).ι ⋙ (E T).fixedDerived.functor

/-- Native compact support at the specified compactification, not a conjugate definition.
Source: blueprint sk-def-sfb-module-derived-lower-shriek.
(blueprint: lem-sf-finite-restriction-normalized-adjunction). -/
abbrev support {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  CondensedRing.rightDerivedLowerShriekOfCompactification (coefficient A) c

/-- Fixed scalar compact support for the very same compactification.
Source: blueprint sk-thm-sf-tensor-hom, Complement.
(blueprint: lem-sf-finite-restriction-normalized-adjunction). -/
abbrev fixedSupport {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} (ULift.{u + 1} A)) c

/-- The normalized native-to-fixed comparison, constructed using the already specified
open-extension and K-injective direct-image comparisons, not chosen from Nonempty.
Source: blueprint finite coefficient identification, steps 11--12.
(blueprint: lem-sf-finite-restriction-normalized-adjunction). -/
def supportCoordinates (E : ∀ T : Scheme.{u}, Encoding A T)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    support A c ⋙ (E Y).fixedDerived.functor ≅
      (E X).fixedDerived.functor ⋙ fixedSupport A c :=
  encodingCompactificationIso A E c

/-- The source's cmp : e_X S ≅ P e_Y, obtained by coefficient cancellation.
Source: blueprint sk-thm-sf-tensor-hom, Complement, specified support comparison.
(blueprint: lem-sf-finite-restriction-normalized-adjunction). -/
def comparison (E : ∀ T : Scheme.{u}, Encoding A T)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    (E X).fixedDerived.inverse ⋙ support A c ≅
      fixedSupport A c ⋙ (E Y).fixedDerived.inverse :=
  Iso.isoCompInverse (Functor.associator _ _ _ ≪≫
    Iso.inverseCompIso (supportCoordinates A E c))

/-- Exactly q_Y S(epsilon_X inverse);q_Y(cmp);eta_Y inverse, with associators.
Source: blueprint sk-thm-sf-tensor-hom, Complement, displayed s_B.
(blueprint: lem-sf-finite-restriction-normalized-adjunction). -/
def inverseComparison (E : ∀ T : Scheme.{u}, Encoding A T)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    support A c ⋙ (E Y).fixedDerived.functor ≅
      (E X).fixedDerived.functor ⋙ fixedSupport A c :=
  (Iso.inverseCompIso
    ((Iso.compInverseIso (H := (E Y).fixedDerived.symm) (comparison A E c)).symm ≪≫
      Functor.associator _ _ _)
    (G := (E X).fixedDerived.symm)).symm

/-- Coefficient conjugation of a specified fixed exceptional functor; no native
exceptional inverse-image identification is part of this definition.
Source: blueprint sk-thm-sf-tensor-hom, Complement, Htr=e_X J q_Y.
(blueprint: lem-sf-finite-restriction-normalized-adjunction). -/
abbrev conjugate (E : ∀ T : Scheme.{u}, Encoding A T)
    {X Y : Scheme.{u}} (J : Fixed A Y ⥤ Fixed A X) :=
  ((E Y).fixedDerived.functor ⋙ J) ⋙ (E X).fixedDerived.inverse

/-- The prescribed left realization for a literal restriction, including equality transport.
Source: blueprint sk-thm-sf-tensor-hom, Complement, r_F.
(blueprint: lem-sf-finite-restriction-normalized-adjunction). -/
def leftRealization (E : ∀ T : Scheme.{u}, Encoding A T)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (F : Category A X ⥤ Category A Y)
    (eF : F ⋙ (property A Y).ι = (property A X).ι ⋙ support A c) :
    F ⋙ realization A E Y ≅ realization A E X ⋙ fixedSupport A c :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (eqToIso eF) _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (inverseComparison A E c) ≪≫
    (Functor.associator _ _ _).symm

/-- The prescribed right realization, cancelling exactly eta_X and retaining associators.
Source: blueprint sk-thm-sf-tensor-hom, Complement, r_G.
(blueprint: lem-sf-finite-restriction-normalized-adjunction). -/
def rightRealization (E : ∀ T : Scheme.{u}, Encoding A T)
    {X Y : Scheme.{u}} (J : Fixed A Y ⥤ Fixed A X)
    (G : Category A Y ⥤ Category A X)
    (eG : G ⋙ (property A X).ι = (property A Y).ι ⋙ conjugate A E J) :
    G ⋙ realization A E X ≅ realization A E Y ⋙ J :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (eqToIso eG) _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Iso.compInverseIso
      (H := (E X).fixedDerived.symm) (Iso.refl _)) ≪≫
    (Functor.associator _ _ _).symm

/-- The fixed Hom-chain type, retaining every bounded-below input and every origin.
Source: blueprint thm-sf-ambient-adjoint-class (2).
(blueprint: lem-sf-finite-restriction-normalized-adjunction). -/
abbrev HomChain {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (J : Fixed A Y ⥤ Fixed A X) :=
  ∀ (M : DerivedCategory.Plus
      (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} A))))
    (_W : FixedEtaleOriginWitness X (ULift.{u + 1} A) M)
    (N : DerivedCategory.Plus
      (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1} A)))),
    ((fixedSupport A c).obj M.obj ⟶ N.obj) ≃ (M.obj ⟶ J.obj N.obj)

/-- The complete normalized conclusion, including the second formula with the actual
coefficient unit. The equality transports make the full-subcategory formulas well typed.
The triangulated structures are conclusions, rather than additional assumptions.
Source: blueprint sk-thm-sf-tensor-hom, Complement, normalized finite restriction.
(blueprint: lem-sf-finite-restriction-normalized-adjunction). -/
def Conclusion (E : ∀ T : Scheme.{u}, Encoding A T)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (J : Fixed A Y ⥤ Fixed A X) [J.CommShift ℤ] (Phi : HomChain A c J)
    (F : Category A X ⥤ Category A Y) (G : Category A Y ⥤ Category A X)
    (eF : F ⋙ (property A Y).ι = (property A X).ι ⋙ support A c)
    (eG : G ⋙ (property A X).ι = (property A Y).ι ⋙ conjugate A E J) : Prop :=
  ∃ (triX : (property A X).IsTriangulated) (triY : (property A Y).IsTriangulated),
  letI := triX
  letI := triY
  ∃ (_add : F.Additive) (_shift : F.CommShift ℤ) (adj : F ⊣ G),
  letI := adj.rightAdjointCommShift ℤ
  F.IsTriangulated ∧
    (leftRealization A E c F eF).hom.CommShift ℤ ∧
    (rightRealization A E J G eG).hom.CommShift ℤ ∧
  ∃ (hX : ∀ K : Category A X,
      DerivedCategory.TStructure.t.plus ((realization A E X).obj K))
    (hY : ∀ L : Category A Y,
      DerivedCategory.TStructure.t.plus ((realization A E Y).obj L)),
    (∀ K : Category A X, Nonempty (FixedEtaleOriginWitness X (ULift.{u + 1} A)
      ⟨(realization A E X).obj K, hX K⟩)) ∧
    (∀ (K : Category A X) (L : Category A Y)
      (W : FixedEtaleOriginWitness X (ULift.{u + 1} A)
        ⟨(realization A E X).obj K, hX K⟩) (a : F.obj K ⟶ L),
      (realization A E X).map (adj.homEquiv K L a) ≫
          (rightRealization A E J G eG).hom.app L =
        Phi ⟨(realization A E X).obj K, hX K⟩ W
          ⟨(realization A E Y).obj L, hY L⟩
          ((leftRealization A E c F eF).inv.app K ≫ (realization A E Y).map a)) ∧
    (∀ (M : DerivedCategory.Plus
        (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} A))))
      (N : DerivedCategory.Plus
        (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1} A))))
      (hM : property A X ((E X).fixedDerived.inverse.obj M.obj))
      (hN : property A Y ((E Y).fixedDerived.inverse.obj N.obj))
      (W : FixedEtaleOriginWitness X (ULift.{u + 1} A) M)
      (v : (fixedSupport A c).obj M.obj ⟶ N.obj),
      let K : Category A X := ⟨(E X).fixedDerived.inverse.obj M.obj, hM⟩
      let L : Category A Y := ⟨(E Y).fixedDerived.inverse.obj N.obj, hN⟩
      (property A X).ι.map (adj.homEquiv K L
        (ObjectProperty.homMk
          (eqToHom (congrArg (fun H => H.obj K) eF) ≫
            (comparison A E c).hom.app M.obj ≫ (E Y).fixedDerived.inverse.map v))) ≫
        eqToHom (congrArg (fun H => H.obj L) eG) =
      (E X).fixedDerived.inverse.map
        (Phi M W N v ≫ J.map ((E Y).fixedDerived.counitIso.inv.app N.obj)))

/-- The fixed exceptional composite for any specified ordinary etale right adjoint.
Source: blueprint sk-thm-sf-tensor-hom, Complement, change of right adjoint.
(blueprint: lem-sf-finite-restriction-normalized-adjunction). -/
abbrev exceptional {X Y : Scheme.{u}}
    (JEt : DerivedCategory (Sheaf Y.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} A))) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} A)))) :=
  (comparisonLowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) Y).rightDerivedFunctor ⋙
    JEt ⋙ (comparisonUpperStar
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) X).mapDerivedCategory

/-- The integer shifts use exactly the chosen ordinary etale adjunction.
Source: blueprint sk-thm-sf-tensor-hom, Complement, adjoint shifts.
(blueprint: lem-sf-finite-restriction-normalized-adjunction). -/
@[instance_reducible]
def exceptionalShift {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (JEt : DerivedCategory (Sheaf Y.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} A))) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} A))))
    (ad : Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) c ⊣ JEt) :
    (exceptional A JEt).CommShift ℤ := by
  letI := ad.rightAdjointCommShift ℤ
  unfold exceptional
  infer_instance

/-- The canonical comparison theta:Jprime -> J, by uniqueness of the ordinary etale
right adjoint and whiskering with the derived comparison functors.
Source: blueprint sk-thm-sf-tensor-hom, Complement, final paragraph.
(blueprint: lem-sf-finite-restriction-normalized-adjunction). -/
def exceptionalComparison [Finite A] {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f)
    [(Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) c).IsLeftAdjoint]
    (JEt : DerivedCategory (Sheaf Y.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} A))) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} A))))
    (ad : Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) c ⊣ JEt) :
    exceptional A JEt ≅ sfFiniteExceptionalAt (ULift.{u + 1} A) c :=
  Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight
    (ad.rightAdjointUniq (Adjunction.ofIsLeftAdjoint
      (Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1} A)) c))) _)

/-- The alternate Hom chain is exactly Phi followed by theta inverse.
Source: blueprint sk-thm-sf-tensor-hom, Complement, final displayed formula.
(blueprint: lem-sf-finite-restriction-normalized-adjunction). -/
def alternateHomChain [Finite A] {X Y : Scheme.{u}} {f : X ⟶ Y}
    [QuasiCompact f] [CompactSpace Y] (c : Compactification f)
    [(Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) c).IsLeftAdjoint]
    (JEt : DerivedCategory (Sheaf Y.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} A))) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} A))))
    (ad : Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) c ⊣ JEt) :
    HomChain A c (exceptional A JEt) :=
  fun M W N => (specifiedExceptionalHomEquiv (ULift.{u + 1} A) c M W N).trans
    ((exceptionalComparison A c JEt ad).app N.obj).symm.homToEquiv

/-- Normalized adjunction for literal restrictions in internal condensed coefficients,
including both displayed normalizations and every choice of ordinary etale adjoint.
No preservation assertion is an input or an output, and F and G are universally given.
The encodings specify precisely the normalized section-action coefficient coordinates;
they are not arbitrary derived equivalences or arbitrary natural comparisons.

Source: latest blueprint sk-thm-sf-tensor-hom, Complement; Zheng, Proposition 2.23.
(blueprint: lem-sf-finite-restriction-normalized-adjunction).

Proof: finite coefficient encoding is an exact termwise equivalence. It carries
constructible cohomology and bounds to the fixed scalar presentation. Constructible
etale origins and bounded-complex descent give the bounded-below assertions and an
origin for every source realization, without requiring a separated structure map.
Apply the ambient etale-origin Hom chain at the specified compactification; its
naturality and independence of origins allow full faithful realization to restrict
it to the given F and G. Transport through the prescribed left and right realization
maps, and use the natural-Hom-bijection construction of adjunctions. This gives the
first equation for every witness. Substitution of the inverse support comparison and
cancellation of the coefficient unit and counit gives the second equation, retaining
J(eta_N). The intrinsic finite-Tor property is triangulated; reflect the compact-support
shift structure, additivity and distinguished triangles through the fully faithful
realization. Use exactly the adjoint shifts on G. The proved fixed-scalar specified
exceptional realization shift theorem gives right shift compatibility. For another
ordinary etale adjoint, whisker its unique right-adjoint comparison. The Hom formula
is Phi followed by theta inverse. Uniqueness of adjoint shifts makes this comparison
shift-compatible, and naturality at eta_N gives exactly the alternate second formula.
Empty schemes and zero objects use the same full subcategories and Hom identities. -/
theorem normalizedRestrictionAdjunction (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (_hell : ell ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic ell) E]
    [FiniteDimensional (Padic ell) E] (n : ℕ) (hn : 1 ≤ n)
    {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) :
    let A := Padic.coefficientExtensionRing ell E n
    letI : TopologicalSpace A := ⊥
    letI : DiscreteTopology A := ⟨rfl⟩
    letI : IsTopologicalRing A := inferInstance
    letI : Finite A := Padic.finite_coefficientExtensionRing ell E n hn
    letI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace
      (Y ↘ Spec (.of D.k))
    letI := Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification
      (ULift.{u + 1} A) c
    ∀ encoding : ∀ T : Scheme.{u}, Encoding A T,
    (let JEt := (Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1} A)) c).rightAdjoint
     let ad := Adjunction.ofIsLeftAdjoint
       (Etale.rightDerivedLowerShriekOfCompactification
         (ModuleCat.{u + 1} (ULift.{u + 1} A)) c)
     letI : (sfFiniteExceptionalAt (ULift.{u + 1} A) c).CommShift ℤ :=
       exceptionalShift A c JEt ad
     ∀ (F : Category A X ⥤ Category A Y) (G : Category A Y ⥤ Category A X)
       (eF : F ⋙ (property A Y).ι = (property A X).ι ⋙ support A c)
       (eG : G ⋙ (property A X).ι = (property A Y).ι ⋙
         conjugate A encoding (sfFiniteExceptionalAt (ULift.{u + 1} A) c)),
       Conclusion A encoding c (sfFiniteExceptionalAt (ULift.{u + 1} A) c)
         (specifiedExceptionalHomEquiv (ULift.{u + 1} A) c) F G eF eG) ∧
    (∀ (JEt : DerivedCategory (Sheaf Y.smallEtaleTopology
          (ModuleCat.{u + 1} (ULift.{u + 1} A))) ⥤
        DerivedCategory (Sheaf X.smallEtaleTopology
          (ModuleCat.{u + 1} (ULift.{u + 1} A))))
       (ad : Etale.rightDerivedLowerShriekOfCompactification
         (ModuleCat.{u + 1} (ULift.{u + 1} A)) c ⊣ JEt),
     letI := exceptionalShift A c JEt ad
     ∀ (F : Category A X ⥤ Category A Y) (G : Category A Y ⥤ Category A X)
       (eF : F ⋙ (property A Y).ι = (property A X).ι ⋙ support A c)
       (eG : G ⋙ (property A X).ι = (property A Y).ι ⋙ conjugate A encoding
         (exceptional A JEt)),
       Conclusion A encoding c (exceptional A JEt)
         (alternateHomChain A c JEt ad) F G eF eG) := by
  sorry

end AlgebraicGeometry.ProEtale.FiniteRestriction
