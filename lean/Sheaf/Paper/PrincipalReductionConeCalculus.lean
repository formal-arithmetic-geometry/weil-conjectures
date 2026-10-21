/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Sheaf.SixFunctors.ProEtale.DerivedCompletion
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import Sheaf.Paper.DerivedNakayamaResolution
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# Strict principal reduction and its compatible cone comparisons

Source: blueprint main-20261015, sec-proetale-coefficients,
`sk-lem-pe-derived-nakayama/sk-lem-pe-derived-nakayama-first-reduction.proof.md`,
Cones paragraph; Stacks Tag 014E, definition-cone
(blueprint: lem-pe-principal-reduction-cone-calculus).

Positive level n+1 is indexed by n : ℕ, as in AdicCompletion. Cone coordinates
are ordered target, shifted source. The comparison is one natural family,
including its quotient transitions and its specified reduction coaugmentations.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

universe u vC uC

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite Pretriangulated
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The standard cone coordinates in target, shifted-source order.
Source: Stacks Tag 014E, definition-cone
(blueprint: lem-pe-principal-reduction-cone-calculus). -/
def principalConeCoordinates {C : Type uC} [Category.{vC} C] [Preadditive C]
    [HasBinaryBiproducts C] {A B : CochainComplex C ℤ} (f : A ⟶ B) (q : ℤ) :
    (CochainComplex.mappingCone f).X q ≅ B.X q ⊞ A.X (q + 1) :=
  HomologicalComplex.homotopyCofiber.XIsoBiprod f q (q + 1) rfl ≪≫
    biprod.braiding _ _

/-- The signed four-coordinate interchange (b,a,b',a') to (b,b',a,-a').
Source: blueprint Cones paragraph, explicit cone interchange
(blueprint: lem-pe-principal-reduction-cone-calculus). -/
def principalConeInterchange {C : Type uC} [Category.{vC} C] [Preadditive C]
    [HasBinaryBiproducts C] (B A B' A' : C) :
    (B ⊞ A) ⊞ (B' ⊞ A') ⟶ (B ⊞ B') ⊞ (A ⊞ A') :=
  biprod.lift
    (biprod.lift (biprod.fst ≫ biprod.fst) (biprod.snd ≫ biprod.fst))
    (biprod.lift (biprod.fst ≫ biprod.snd) (-(biprod.snd ≫ biprod.snd)))

namespace PrincipalReduction

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

/-- Multiplication by the (n+1)-st power of the specified uniformizer on a complex.
Source: blueprint Cones paragraph and the scalar construction in the resolution
(blueprint: lem-pe-principal-reduction-cone-calculus). -/
abbrev scalar (d : End (Mod.regular (DerivedNakayama.integerRing l E))) (n : ℕ)
    (M : CochainComplex (AdicCompletion.Modules l E X) ℤ) : M ⟶ M :=
  DerivedNakayama.scalarOnComplex l E X (d ^ (n + 1)) M

/-- The canonical derived reduction followed by integral scalar restriction.
Source: blueprint Cones paragraph, underlying integral-module reductions
(blueprint: lem-pe-principal-reduction-cone-calculus). -/
abbrev reductionFunctor (n : ℕ) : DerivedCategory (AdicCompletion.Modules l E X) ⥤
    DerivedCategory (AdicCompletion.Modules l E X) :=
  AdicCompletion.derivedReduction l E X n ⋙ AdicCompletion.restrict l E X n

open AlgebraicGeometry.ProEtale.AdicCompletion

/-- Strict principal reductions, with the signed cone and shift comparisons and their
canonical derived interpretation, simultaneously at all positive levels.

Source: blueprint main-20261015, first-reduction proof, Cones paragraph;
Stacks Tag 014E, definition-cone
(blueprint: lem-pe-principal-reduction-cone-calculus).

Proof plan (the ten steps of the node):
1. Use the scalar differential (dx + pi^(n+1)y,-dy). Diagonal maps are functorial;
   (x,pi y) is a chain map by pi^(n+1)pi=pi^(n+2), and (m,0) is the coaugmentation.
2. Morphisms of scalar cone triangles and lem-sf-triangle-morphism-iso show
   quasi-isomorphism preservation. Localization descends the functor and its maps;
   the direct-sum coordinates prove additivity after localization.
3. The two-term resolution of det-pe-derived-nakayama-resolution has flat rank-one
   terms; lem-weil-pbc-independent-bounded-flat-kflat makes it K-flat.
4. Resolve M using lem-pc-kflat-resolution. The signed tensor interchange identifies
   its tensor with that two-term resolution with this scalar cone. The localization
   and transformation-extension clauses of lem-weil-pbc-site-derived-tensor-descent
   give one natural comparison on all unbounded complexes.
5. Lift coefficient transitions by (pi,id) and reduction by the degree-zero identity.
   Tensoring identifies them with the specified transition and coaugmentation, so
   their localizations are the canonical maps of sk-def-pe-derived-completion.
6. Expand the four-coordinate differentials. The map (b,a,b',a') to (b,b',a,-a')
   is a chain isomorphism with inverse (u,v,w,z) to (u,w,v,-z).
7. The shift differential is (-1)^r d. The map (x,y) to (x,(-1)^r y) intertwines
   the differentials, is its own inverse, and is coherent under addition of integers.
8. Diagonal chain maps commute with both formulas. Multiplication by pi on the
   second coordinate commutes with the permutation and sign, giving all tower squares.
9. Cone inclusion becomes inclusion; the negative-projection boundary becomes
   (-a,a') after the shift comparison. Coaugmentations become the cone map of the
   two coaugmentations and the shifted coaugmentation, respectively.
10. The cone and boundary squares identify images of cone triangles with cone
    triangles. Every distinguished derived triangle has a cone representative, so
    the localized functor with this shift structure is additive and exact. -/
theorem principal_reduction_cone_calculus :
    ∃ d : End (Mod.regular (DerivedNakayama.integerRing l E)),
      (∀ (S : Profinite.{u}ᵒᵖ) (a : (DerivedNakayama.integerRing l E).obj.obj S)
        (s : S.unop), ((d.hom.hom.app S) a).down s =
          Padic.coefficientExtensionUniformizer l E * a.down s) ∧
      ∃ (D : ℕ → CochainComplex (Modules l E X) ℤ ⥤ CochainComplex (Modules l E X) ℤ)
        (hobj : ∀ (n : ℕ) (M : CochainComplex (Modules l E X) ℤ),
          (D n).obj M = CochainComplex.mappingCone (scalar l E X d n M))
        (χ : ∀ (n : ℕ) (M : CochainComplex (Modules l E X) ℤ) (q : ℤ),
          ((D n).obj M).X q ≅ M.X q ⊞ M.X (q + 1))
        (T : ∀ n : ℕ, D (n + 1) ⟶ D n)
        (j : ∀ n : ℕ, 𝟭 (CochainComplex (Modules l E X) ℤ) ⟶ D n)
        (sD : ∀ n : ℕ, (D n).CommShift ℤ)
        (sF : ∀ n : ℕ, (reductionFunctor l E X n).CommShift ℤ)
        (κ : ∀ n : ℕ, D n ⋙ DerivedCategory.Q ≅
          DerivedCategory.Q ⋙ reductionFunctor l E X n)
        (Φ : ∀ (n : ℕ) {A B : CochainComplex (Modules l E X) ℤ} (f : A ⟶ B),
          (D n).obj (CochainComplex.mappingCone f) ≅
            CochainComplex.mappingCone ((D n).map f)),
        (∀ (n : ℕ) (M : CochainComplex (Modules l E X) ℤ) (q : ℤ),
          χ n M q = eqToIso (congrArg (fun K ↦ K.X q) (hobj n M)) ≪≫
            principalConeCoordinates (scalar l E X d n M) q) ∧
        (∀ (n : ℕ) {M N : CochainComplex (Modules l E X) ℤ} (g : M ⟶ N) (q : ℤ),
          ((D n).map g).f q ≫ (χ n N q).hom =
            (χ n M q).hom ≫ biprod.map (g.f q) (g.f (q + 1))) ∧
        (∀ (n : ℕ) (M : CochainComplex (Modules l E X) ℤ) (q : ℤ),
          ((T n).app M).f q ≫ (χ n M q).hom =
            (χ (n + 1) M q).hom ≫ biprod.map (𝟙 _)
              ((DerivedNakayama.scalarOnComplex l E X d M).f (q + 1))) ∧
        (∀ (n : ℕ) (M : CochainComplex (Modules l E X) ℤ) (q : ℤ),
          ((j n).app M).f q ≫ (χ n M q).hom = biprod.inl) ∧
        (∀ (n : ℕ) (M : CochainComplex (Modules l E X) ℤ),
          (j (n + 1)).app M ≫ (T n).app M = (j n).app M) ∧
        (∀ (n : ℕ) {M N : CochainComplex (Modules l E X) ℤ} (g : M ⟶ N),
          QuasiIso g → QuasiIso ((D n).map g)) ∧
        (∀ n : ℕ, (reductionFunctor l E X n).Additive ∧
          @Functor.IsTriangulated _ _ _ _ _ _ (reductionFunctor l E X n)
            (sF n) _ _ _ _ _ _ _ _) ∧
        (∀ (n : ℕ) (M : CochainComplex (Modules l E X) ℤ),
          DerivedCategory.Q.map ((T n).app M) ≫ (κ n).hom.app M =
            (κ (n + 1)).hom.app M ≫ integralStep l E X (DerivedCategory.Q.obj M) n) ∧
        (∀ (n : ℕ) (M : CochainComplex (Modules l E X) ℤ),
          DerivedCategory.Q.map ((j n).app M) ≫ (κ n).hom.app M =
            (Mod.derivedExtendMapDerivedCategoryAdjunction (quotient l E X n)).unit.app
              (DerivedCategory.Q.obj M)) ∧
        (∀ (n : ℕ) {A B : CochainComplex (Modules l E X) ℤ} (f : A ⟶ B) (q : ℤ),
          (Φ n f).hom.f q ≫ (principalConeCoordinates ((D n).map f) q).hom ≫
              biprod.map (χ n B q).hom (χ n A (q + 1)).hom =
            (χ n (CochainComplex.mappingCone f) q).hom ≫
              biprod.map (principalConeCoordinates f q).hom
                (principalConeCoordinates f (q + 1)).hom ≫
              principalConeInterchange (B.X q) (A.X (q + 1)) (B.X (q + 1))
                (A.X (q + 1 + 1))) ∧
        (∀ (n : ℕ) (r : ℤ) (M : CochainComplex (Modules l E X) ℤ) (q : ℤ),
          ((Functor.commShiftIso (self := sD n) (D n) r).hom.app M).f q ≫
              (((D n).obj M).shiftFunctorObjXIso r q (q + r) rfl).hom ≫
              (χ n M (q + r)).hom =
            (χ n (M⟦r⟧) q).hom ≫
              biprod.map (M.shiftFunctorObjXIso r q (q + r) rfl).hom
                (r.negOnePow •
                  (M.shiftFunctorObjXIso r (q + 1) (q + r + 1)
                    (add_right_comm q r 1)).hom)) ∧
        (∀ (n : ℕ) {A B A' B' : CochainComplex (Modules l E X) ℤ}
          (f : A ⟶ B) (f' : A' ⟶ B') (a : A ⟶ A') (b : B ⟶ B')
          (h : f ≫ b = a ≫ f')
          (h' : (D n).map f ≫ (D n).map b = (D n).map a ≫ (D n).map f'),
          (D n).map (CochainComplex.mappingCone.map f f' a b h) ≫ (Φ n f').hom =
            (Φ n f).hom ≫ CochainComplex.mappingCone.map
              ((D n).map f) ((D n).map f') ((D n).map a) ((D n).map b) h') ∧
        (∀ (n : ℕ) {A B : CochainComplex (Modules l E X) ℤ} (f : A ⟶ B),
          (T n).app (CochainComplex.mappingCone f) ≫ (Φ n f).hom =
            (Φ (n + 1) f).hom ≫ CochainComplex.mappingCone.map
              ((D (n + 1)).map f) ((D n).map f) ((T n).app A) ((T n).app B)
              ((T n).naturality f)) ∧
        (∀ (n : ℕ) (r : ℤ) (M : CochainComplex (Modules l E X) ℤ),
          (T n).app (M⟦r⟧) ≫ (Functor.commShiftIso (self := sD n) (D n) r).hom.app M =
            (Functor.commShiftIso (self := sD (n + 1)) (D (n + 1)) r).hom.app M ≫
              ((T n).app M)⟦r⟧') ∧
        (∀ (n : ℕ) {A B : CochainComplex (Modules l E X) ℤ} (f : A ⟶ B),
          (D n).map (CochainComplex.mappingCone.inr f) ≫ (Φ n f).hom =
            CochainComplex.mappingCone.inr ((D n).map f)) ∧
        (∀ (n : ℕ) {A B : CochainComplex (Modules l E X) ℤ} (f : A ⟶ B),
          (D n).map (CochainComplex.mappingCone.triangle f).mor₃ ≫
              (Functor.commShiftIso (self := sD n) (D n) (1 : ℤ)).hom.app A =
            (Φ n f).hom ≫ (CochainComplex.mappingCone.triangle ((D n).map f)).mor₃) ∧
        (∀ (n : ℕ) {A B : CochainComplex (Modules l E X) ℤ} (f : A ⟶ B),
          (j n).app (CochainComplex.mappingCone f) ≫ (Φ n f).hom =
            CochainComplex.mappingCone.map f ((D n).map f) ((j n).app A) ((j n).app B)
              ((j n).naturality f)) ∧
        (∀ (n : ℕ) (r : ℤ) (M : CochainComplex (Modules l E X) ℤ),
          (j n).app (M⟦r⟧) ≫ (Functor.commShiftIso (self := sD n) (D n) r).hom.app M =
            ((j n).app M)⟦r⟧') ∧
        (∀ (n : ℕ) (r : ℤ) (M : CochainComplex (Modules l E X) ℤ),
          DerivedCategory.Q.map
              ((Functor.commShiftIso (self := sD n) (D n) r).hom.app M) ≫
              (DerivedCategory.Q.commShiftIso r).hom.app ((D n).obj M) ≫
              ((κ n).hom.app M)⟦r⟧' =
            (κ n).hom.app (M⟦r⟧) ≫
              (reductionFunctor l E X n).map ((DerivedCategory.Q.commShiftIso r).hom.app M) ≫
              (Functor.commShiftIso (self := sF n) (reductionFunctor l E X n) r).hom.app
                (DerivedCategory.Q.obj M)) := by
  sorry

end PrincipalReduction
end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.PrincipalReduction

open AlgebraicGeometry.ProEtale.AdicCompletion

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

/-- The strict data of the simultaneous principal calculus. Its canonical predicate
also retains all existential comparison data and equations of the node.
Its strict objects, maps, transitions and units are fixed
by the scalar and coordinate equations; the comparisons retain all normalizations.
Source: blueprint first-reduction proof, Cones paragraph; Stacks Tag 014E
(blueprint: lem-pe-principal-reduction-cone-calculus). -/
structure PrincipalReductionConeData where
  d : End (Mod.regular (DerivedNakayama.integerRing l E))
  D : ℕ → CochainComplex (Modules l E X) ℤ ⥤ CochainComplex (Modules l E X) ℤ
  hobj : ∀ (n : ℕ) (M : CochainComplex (Modules l E X) ℤ),
    (D n).obj M = CochainComplex.mappingCone (scalar l E X d n M)
  χ : ∀ (n : ℕ) (M : CochainComplex (Modules l E X) ℤ) (q : ℤ),
    ((D n).obj M).X q ≅ M.X q ⊞ M.X (q + 1)
  T : ∀ n : ℕ, D (n + 1) ⟶ D n
  j : ∀ n : ℕ, 𝟭 (CochainComplex (Modules l E X) ℤ) ⟶ D n

/-- Exact canonical characterization of the simultaneous principal calculus.
The conjunction is under the scalar test binders. This is equivalent to placing
its remaining clauses outside them: use the one-point profinite test and the zero
section. Keeping these binders shared avoids repeated closed-proof abstraction.
Source: blueprint first-reduction proof, Cones paragraph; Stacks Tag 014E
(blueprint: lem-pe-principal-reduction-cone-calculus). -/
def PrincipalReductionConeData.IsCanonical (data : PrincipalReductionConeData l E X) : Prop :=
  ∀ (S : Profinite.{u}ᵒᵖ)
    (a : (DerivedNakayama.integerRing l E).obj.obj S) (s : S.unop),
    ((data.d.hom.hom.app S) a).down s = Padic.coefficientExtensionUniformizer l E * a.down s ∧
    ∃ (sD : ∀ n : ℕ, (data.D n).CommShift ℤ)
      (sF : ∀ n : ℕ, (reductionFunctor l E X n).CommShift ℤ)
      (κ : ∀ n : ℕ, data.D n ⋙ DerivedCategory.Q ≅
        DerivedCategory.Q ⋙ reductionFunctor l E X n)
      (Φ : ∀ (n : ℕ) {A B : CochainComplex (Modules l E X) ℤ} (f : A ⟶ B),
        (data.D n).obj (CochainComplex.mappingCone f) ≅
          CochainComplex.mappingCone ((data.D n).map f)),
    (∀ (n : ℕ) (M : CochainComplex (Modules l E X) ℤ) (q : ℤ),
      data.χ n M q = eqToIso (congrArg (fun K ↦ K.X q) (data.hobj n M)) ≪≫
        principalConeCoordinates (scalar l E X data.d n M) q) ∧
    (∀ (n : ℕ) {M N : CochainComplex (Modules l E X) ℤ} (g : M ⟶ N) (q : ℤ),
      ((data.D n).map g).f q ≫ (data.χ n N q).hom =
        (data.χ n M q).hom ≫ biprod.map (g.f q) (g.f (q + 1))) ∧
    (∀ (n : ℕ) (M : CochainComplex (Modules l E X) ℤ) (q : ℤ),
      ((data.T n).app M).f q ≫ (data.χ n M q).hom =
        (data.χ (n + 1) M q).hom ≫ biprod.map (𝟙 _)
          ((DerivedNakayama.scalarOnComplex l E X data.d M).f (q + 1))) ∧
    (∀ (n : ℕ) (M : CochainComplex (Modules l E X) ℤ) (q : ℤ),
      ((data.j n).app M).f q ≫ (data.χ n M q).hom = biprod.inl) ∧
    (∀ (n : ℕ) (M : CochainComplex (Modules l E X) ℤ),
      (data.j (n + 1)).app M ≫ (data.T n).app M = (data.j n).app M) ∧
    (∀ (n : ℕ) {M N : CochainComplex (Modules l E X) ℤ} (g : M ⟶ N),
      QuasiIso g → QuasiIso ((data.D n).map g)) ∧
    (∀ n : ℕ, (reductionFunctor l E X n).Additive ∧
      @Functor.IsTriangulated _ _ _ _ _ _ (reductionFunctor l E X n)
        (sF n) _ _ _ _ _ _ _ _) ∧
    (∀ (n : ℕ) (M : CochainComplex (Modules l E X) ℤ),
      DerivedCategory.Q.map ((data.T n).app M) ≫ (κ n).hom.app M =
        (κ (n + 1)).hom.app M ≫ integralStep l E X (DerivedCategory.Q.obj M) n) ∧
    (∀ (n : ℕ) (M : CochainComplex (Modules l E X) ℤ),
      DerivedCategory.Q.map ((data.j n).app M) ≫ (κ n).hom.app M =
        (Mod.derivedExtendMapDerivedCategoryAdjunction (quotient l E X n)).unit.app
          (DerivedCategory.Q.obj M)) ∧
    (∀ (n : ℕ) {A B : CochainComplex (Modules l E X) ℤ} (f : A ⟶ B) (q : ℤ),
      (Φ n f).hom.f q ≫ (principalConeCoordinates ((data.D n).map f) q).hom ≫
          biprod.map (data.χ n B q).hom (data.χ n A (q + 1)).hom =
        (data.χ n (CochainComplex.mappingCone f) q).hom ≫
          biprod.map (principalConeCoordinates f q).hom
            (principalConeCoordinates f (q + 1)).hom ≫
          principalConeInterchange (B.X q) (A.X (q + 1)) (B.X (q + 1))
            (A.X (q + 1 + 1))) ∧
    (∀ (n : ℕ) (r : ℤ) (M : CochainComplex (Modules l E X) ℤ) (q : ℤ),
      ((Functor.commShiftIso (self := sD n) (data.D n) r).hom.app M).f q ≫
          (((data.D n).obj M).shiftFunctorObjXIso r q (q + r) rfl).hom ≫
          (data.χ n M (q + r)).hom =
        (data.χ n (M⟦r⟧) q).hom ≫
          biprod.map (M.shiftFunctorObjXIso r q (q + r) rfl).hom
            (r.negOnePow •
              (M.shiftFunctorObjXIso r (q + 1) (q + r + 1)
                (add_right_comm q r 1)).hom)) ∧
    (∀ (n : ℕ) {A B A' B' : CochainComplex (Modules l E X) ℤ}
      (f : A ⟶ B) (f' : A' ⟶ B') (a : A ⟶ A') (b : B ⟶ B')
      (h : f ≫ b = a ≫ f')
      (h' : (data.D n).map f ≫ (data.D n).map b = (data.D n).map a ≫ (data.D n).map f'),
      (data.D n).map (CochainComplex.mappingCone.map f f' a b h) ≫ (Φ n f').hom =
        (Φ n f).hom ≫ CochainComplex.mappingCone.map
          ((data.D n).map f) ((data.D n).map f') ((data.D n).map a) ((data.D n).map b) h') ∧
    (∀ (n : ℕ) {A B : CochainComplex (Modules l E X) ℤ} (f : A ⟶ B),
      (data.T n).app (CochainComplex.mappingCone f) ≫ (Φ n f).hom =
        (Φ (n + 1) f).hom ≫ CochainComplex.mappingCone.map
          ((data.D (n + 1)).map f) ((data.D n).map f) ((data.T n).app A) ((data.T n).app B)
          ((data.T n).naturality f)) ∧
    (∀ (n : ℕ) (r : ℤ) (M : CochainComplex (Modules l E X) ℤ),
      (data.T n).app (M⟦r⟧) ≫ (Functor.commShiftIso (self := sD n) (data.D n) r).hom.app M =
        (Functor.commShiftIso (self := sD (n + 1)) (data.D (n + 1)) r).hom.app M ≫
          ((data.T n).app M)⟦r⟧') ∧
    (∀ (n : ℕ) {A B : CochainComplex (Modules l E X) ℤ} (f : A ⟶ B),
      (data.D n).map (CochainComplex.mappingCone.inr f) ≫ (Φ n f).hom =
        CochainComplex.mappingCone.inr ((data.D n).map f)) ∧
    (∀ (n : ℕ) {A B : CochainComplex (Modules l E X) ℤ} (f : A ⟶ B),
      (data.D n).map (CochainComplex.mappingCone.triangle f).mor₃ ≫
          (Functor.commShiftIso (self := sD n) (data.D n) (1 : ℤ)).hom.app A =
        (Φ n f).hom ≫ (CochainComplex.mappingCone.triangle ((data.D n).map f)).mor₃) ∧
    (∀ (n : ℕ) {A B : CochainComplex (Modules l E X) ℤ} (f : A ⟶ B),
      (data.j n).app (CochainComplex.mappingCone f) ≫ (Φ n f).hom =
        CochainComplex.mappingCone.map f ((data.D n).map f) ((data.j n).app A) ((data.j n).app B)
          ((data.j n).naturality f)) ∧
    (∀ (n : ℕ) (r : ℤ) (M : CochainComplex (Modules l E X) ℤ),
      (data.j n).app (M⟦r⟧) ≫ (Functor.commShiftIso (self := sD n) (data.D n) r).hom.app M =
        ((data.j n).app M)⟦r⟧') ∧
    (∀ (n : ℕ) (r : ℤ) (M : CochainComplex (Modules l E X) ℤ),
      DerivedCategory.Q.map
          ((Functor.commShiftIso (self := sD n) (data.D n) r).hom.app M) ≫
          (DerivedCategory.Q.commShiftIso r).hom.app ((data.D n).obj M) ≫
          ((κ n).hom.app M)⟦r⟧' =
        (κ n).hom.app (M⟦r⟧) ≫
          (reductionFunctor l E X n).map ((DerivedCategory.Q.commShiftIso r).hom.app M) ≫
          (Functor.commShiftIso (self := sF n) (reductionFunctor l E X n) r).hom.app
            (DerivedCategory.Q.obj M))

/-- Strict principal reductions, with the signed cone and shift comparisons and their
canonical derived interpretation, simultaneously at all positive levels.

Source: blueprint main-20261015, first-reduction proof, Cones paragraph;
Stacks Tag 014E, definition-cone
(blueprint: lem-pe-principal-reduction-cone-calculus).

Proof plan (the ten steps of the node):
1. Use the scalar differential (dx + pi^(n+1)y,-dy). Diagonal maps are functorial;
   (x,pi y) is a chain map by pi^(n+1)pi=pi^(n+2), and (m,0) is the coaugmentation.
2. Morphisms of scalar cone triangles and lem-sf-triangle-morphism-iso show
   quasi-isomorphism preservation. Localization descends the functor and its maps;
   the direct-sum coordinates prove additivity after localization.
3. The two-term resolution of det-pe-derived-nakayama-resolution has flat rank-one
   terms; lem-weil-pbc-independent-bounded-flat-kflat makes it K-flat.
4. Resolve M using lem-pc-kflat-resolution. The signed tensor interchange identifies
   its tensor with that two-term resolution with this scalar cone. The localization
   and transformation-extension clauses of lem-weil-pbc-site-derived-tensor-descent
   give one natural comparison on all unbounded complexes.
5. Lift coefficient transitions by (pi,id) and reduction by the degree-zero identity.
   Tensoring identifies them with the specified transition and coaugmentation, so
   their localizations are the canonical maps of sk-def-pe-derived-completion.
6. Expand the four-coordinate differentials. The map (b,a,b',a') to (b,b',a,-a')
   is a chain isomorphism with inverse (u,v,w,z) to (u,w,v,-z).
7. The shift differential is (-1)^r d. The map (x,y) to (x,(-1)^r y) intertwines
   the differentials, is its own inverse, and is coherent under addition of integers.
8. Diagonal chain maps commute with both formulas. Multiplication by pi on the
   second coordinate commutes with the permutation and sign, giving all tower squares.
9. Cone inclusion becomes inclusion; the negative-projection boundary becomes
   (-a,a') after the shift comparison. Coaugmentations become the cone map of the
   two coaugmentations and the shifted coaugmentation, respectively.
10. The cone and boundary squares identify images of cone triangles with cone
    triangles. Every distinguished derived triangle has a cone representative, so
    the localized functor with this shift structure is additive and exact. -/
theorem principalReductionConeData :
    ∃ data : PrincipalReductionConeData l E X, data.IsCanonical l E X := by
  sorry

end AlgebraicGeometry.ProEtale.PrincipalReduction
