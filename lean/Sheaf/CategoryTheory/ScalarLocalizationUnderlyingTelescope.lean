/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q49
-/
module

public import Sheaf.CategoryTheory.ScalarLocalizationDerivedHom
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.RingedSectionLocalizationRing
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
public import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.Algebra.Homology.ComplexColimitHomotopyColimit
import Mathlib.CategoryTheory.Localization.Predicate
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.CategoryTheory.RingedSectionLocalizationOfUniverses

/-!
# The underlying telescope for scalar localization

Source: Bhatt--Scholze, Lemma 6.8.2 and Proposition 6.8.14(2), with the telescope
model expanded using Stacks Project, Derived Categories, Lemma 0949 and Lemma 093W
(blueprint: lem-weil-pbc-scalar-localization-underlying-telescope).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option maxRecDepth 2048

universe u v w uD vD uT vT

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open DirectSum
open scoped ChangeOfRings

namespace CategoryTheory

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}

/-- The section formula for the scalar-extension unit, using the existing tensor
sheafification. The equality identifies the supplied presentation of the extension object.
Source: Stacks Project, Modules on Sites, Tag 03EK
(blueprint: lem-weil-pbc-scalar-localization-underlying-telescope). -/
def scalarLocalizationTelescopeUnitSections
    {R S : Sheaf J CommRingCat.{u}} (φ : R ⟶ S)
    (M : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (N : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
    (e : N = SheafOfModules.changeOfRings φ M)
    (η : M ⟶ (SheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj N) : Prop :=
  ∀ (V : Cᵒᵖ) (x : M.val.obj V),
    (η ≫ (SheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).map (eqToHom e)).val.app V x =
      (toSheafify J (SheafOfModules.changeOfRingsPresheaf φ M).presheaf).app V
        ((1 : S.obj.obj V) ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] x)

/-- The nth scalar-localization leg, for a specified adjunction and scalar action.
The theorem below supplies the canonical derived action and the normalized unit.
Source: Bhatt--Scholze, Lemma 6.8.2 and Proposition 6.8.14(2)
(blueprint: lem-weil-pbc-scalar-localization-underlying-telescope). -/
def scalarLocalizationTelescopeLeg
    (A : Type v) [CommRing A] (t : A)
    {D : Type uD} [Category.{vD} D]
    {T : Type uT} [Category.{vT} T] [Preadditive T] [Linear (Localization.Away t) T]
    (F : D ⥤ T) (U : T ⥤ D) (adj : F ⊣ U) (L : D) (n : ℕ) : L ⟶ U.obj (F.obj L) :=
  adj.unit.app L ≫ U.map
    (((IsLocalization.Away.invSelf t : Localization.Away t) ^ n) • 𝟙 (F.obj L))

/-- The derived unit is the class of the specified termwise unit on every complex,
after the canonical exact-functor factorization isomorphisms.
Source: Stacks Project, Derived Categories, Tags 05RU and 015F
(blueprint: lem-weil-pbc-scalar-localization-underlying-telescope). -/
def scalarLocalizationTelescopeDerivedUnit
    {B : Type uD} [Category.{vD} B] [Abelian B] [HasDerivedCategory.{w} B]
    {B' : Type uT} [Category.{vT} B'] [Abelian B'] [HasDerivedCategory.{w} B']
    (E : B ⥤ B') [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (U : B' ⥤ B) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (unitComplex : ∀ (K : CochainComplex B ℤ),
      K ⟶ (U.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
    (adj : E.mapDerivedCategory ⊣ U.mapDerivedCategory) : Prop :=
  ∀ (K : CochainComplex B ℤ),
    adj.unit.app (DerivedCategory.Q.obj K) ≫
      U.mapDerivedCategory.map (E.mapDerivedCategoryFactors.hom.app K) ≫
      U.mapDerivedCategoryFactors.hom.app
        ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) =
      DerivedCategory.Q.map (unitComplex K)

/-- The telescope triangle with all its specified legs, naturality and shift equations.
The predicate P records which source objects need the telescope comparison; the theorem
below substitutes the bounded-below predicate and the canonical derived scalar actions.
Source: Stacks Project, Derived Categories, Tags 093W, 0949 and 014A
(blueprint: lem-weil-pbc-scalar-localization-underlying-telescope). -/
def scalarLocalizationTelescopeProperty
    (A : Type v) [CommRing A] (t : A)
    {D : Type uD} [Category.{vD} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
    [∀ k : ℤ, (shiftFunctor D k).Additive] [Pretriangulated D] [Linear A D]
    {T : Type uT} [Category.{vT} T] [Preadditive T] [HasShift T ℤ]
    [Linear (Localization.Away t) T]
    (F : D ⥤ T) [F.CommShift ℤ] (U : T ⥤ D) [U.CommShift ℤ]
    (adj : F ⊣ U) (P : D → Prop) : Prop :=
  ∀ (L : D), P L →
    ∃ (A₀ : D) (ι : ∀ _n : ℕ, L ⟶ A₀) (_hc : IsColimit (Cofan.mk A₀ ι))
      (s : A₀ ⟶ A₀) (_hs : ∀ n : ℕ, ι n ≫ s = (t • 𝟙 L) ≫ ι (n + 1))
      (H : D) (g : A₀ ⟶ H) (h : H ⟶ A₀⟦(1 : ℤ)⟧),
      (Triangle.mk (𝟙 A₀ - s) g h ∈ distTriang D ∧
        ∃ e : H ≅ U.obj (F.obj L),
          ∀ n : ℕ, ι n ≫ g ≫ e.hom = scalarLocalizationTelescopeLeg A t F U adj L n) ∧
      (∀ (K L : D) (f : K ⟶ L) (n : ℕ),
        f ≫ scalarLocalizationTelescopeLeg A t F U adj L n =
          scalarLocalizationTelescopeLeg A t F U adj K n ≫ U.map (F.map f)) ∧
      (∀ (L : D) (n : ℕ) (k : ℤ),
        scalarLocalizationTelescopeLeg A t F U adj (L⟦k⟧) n ≫
          ((F ⋙ U).commShiftIso k).hom.app L =
        (scalarLocalizationTelescopeLeg A t F U adj L n)⟦k⟧')

/--
Source: Bhatt--Scholze, Lemma 6.8.2 and Proposition 6.8.14(2), and Stacks Project,
Derived Categories, Lemmas 0949 and 093W.
(blueprint: lem-weil-pbc-scalar-localization-underlying-telescope).

Proof (the eight steps of the DAG node):
1. The maps lambda_n : R → R[1/t], r ↦ r/t^n, exhibit R[1/t] as the sheaf colimit
of repeated multiplication by t. For a compatible family a_n, send r/t^n to a_n(r).
If r/t^n = r'/t^m, some t^k kills t^m r - t^n r'; the two representatives agree
at stage n+m+k. This proves well-definedness even with t-torsion. Common stages
prove additivity, linearity and uniqueness. The maps commute with restrictions;
module sheafification gives the sheaf universal property. Use
 def-weil-pbc-module-localization, def-weil-pbc-ringed-section-localization and
 def-weil-presheaf-modules-sheafification.
2. Tensor symmetry and tensor--Hom adjunction identify maps R[1/t] tensor M → N
with compatible families M → N for the t-sequence, using step 1 on internal Hom.
Thus restricted scalar extension is its colimit, with leg m ↦ t^(-n) tensor m.
Use lem-pc-sheaf-modules-tensor-closed, def-pur-sheaf-tensor-product and
 def-pc-sheaf-restrict-scalars.
3. Filtered colimits of module sheaves are exact by
 lem-pur-ringed-site-grothendieck-abelian. The faithful exact forgetful functor of
 lem-weil-pbc-module-sheaves-colimits-forgetful detects exactness. Restriction
changes no underlying abelian sheaf, hence is exact and reflects exactness.
Step 2 then proves extension exact. Apply
 lem-weil-pbc-exact-functor-derived-factorization: both derived functors are
termwise with their canonical shift comparisons.
4. Choose a complex K representing L. The degreewise colimit B of its t-sequence
is isomorphic to restricted E(K), sending the nth colimit leg to t^(-n) tensor x.
This commutes with differentials since d(t^(-n) tensor x) = t^(-n) tensor dx;
the inverse commutes by cancellation. Step 3 and
 def-weil-abstract-derived-category identify Q B with U F L. No bounded
representative or injectivity of t is required.
5. Apply lem-kun-complex-colimit-hocolim to the constant sequence K with map t.
Its cone comparison p : Cone(1-s) → B is a quasi-isomorphism whose restriction
to the unshifted summand is the colimit map. Its actual coprojections remain a
coproduct after Q. Transport the distinguished cone triangle along Q p and the
isomorphism of step 4. The second map has precisely the mapped colimit legs.
6. The zeroth leg is the termwise unit x ↦ 1 tensor x, equal to x tensor 1 after
symmetry. The other legs are t^(-n) times it. Since t is a unit in R[1/t], these
are inverse powers of multiplication by t. The two unit normalizations below
identify their derived images with adj.unit, including n=0. Use
 def-pur-sheaf-tensor-product, def-weil-pbc-ringed-section-localization and
 def-pc-sheaf-restrict-scalars.
7. For any other telescope cone, identify its coproduct vertices with those of
step 5. TR3 completes the identity on these vertices to a triangle map. Its
third component is an isomorphism by lem-sf-triangle-morphism-iso. The second
square gives the required formula for every leg. Use
 def-weil-triangulated-category; no uniqueness or functorial cone is claimed.
8. The termwise legs commute with chain maps because both composites send x to
t^(-n) tensor f(x). They commute with shifts: in degree r both are the original
leg in degree r+k, and the same sign multiplies both differentials. Descend
these equations through Q using lem-weil-pbc-localization-universal-property
and lem-weil-pbc-exact-functor-derived-factorization. This gives naturality on
all derived morphisms and the displayed CommShift equation for every integer k.
-/
theorem scalarLocalization_underlyingTelescope
    (A : Type v) [CommRing A]
    (R : Sheaf J CommRingCat.{u})
    (a : A →+* RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat))
    (t : A)
    [HasDerivedCategory.{w}
      (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    [HasDerivedCategory.{w}
      (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
        (ringedLocalizationRing R (a t))))]
    (E : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
      ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
        (ringedLocalizationRing R (a t))))
    (hE : ∀ M, E.obj M =
      SheafOfModules.changeOfRings (ringedLocalizationRingUnit R (a t)) M)
    (hmap : ∀ {M N} (f : M ⟶ N), E.map f = eqToHom (hE M) ≫
      SheafOfModules.changeOfRingsHom (ringedLocalizationRingUnit R (a t)) M f ≫
        eqToHom (hE N).symm)
    [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (U₀ : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
        (ringedLocalizationRing R (a t))) ⥤
      ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (hU₀ : U₀ = SheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map
        (ringedLocalizationRingUnit R (a t))))
    [U₀.Additive] [PreservesFiniteLimits U₀] [PreservesFiniteColimits U₀]
    (unitComplex : ∀ (K : CochainComplex (ringedSiteModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ),
      K ⟶ (U₀.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
    (unitSections : ∀ (K : CochainComplex (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ) (i : ℤ),
      scalarLocalizationTelescopeUnitSections (ringedLocalizationRingUnit R (a t))
        (K.X i) (E.obj (K.X i)) (hE (K.X i))
        ((unitComplex K).f i ≫
          eqToHom (congrArg (fun T ↦ T.obj (E.obj (K.X i))) hU₀)))
    (adj : E.mapDerivedCategory ⊣ U₀.mapDerivedCategory)
    (derivedUnit : scalarLocalizationTelescopeDerivedUnit E U₀ unitComplex adj) :
    (fun [_iA : Linear A (DerivedCategory
      (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)))]
      [_iT : Linear (Localization.Away t) (DerivedCategory
        (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
          (ringedLocalizationRing R (a t)))))] ↦
      scalarLocalizationTelescopeProperty A t E.mapDerivedCategory U₀.mapDerivedCategory adj
        (fun L ↦ ∃ b : ℤ, L.IsGE b))
      (_iA := scalarLocalizationDerivedLinear A R a)
      (_iT := scalarLocalizationDerivedLinear (Localization.Away t)
        (ringedLocalizationRing R (a t)) (scalarLocalizationCoefficientMap A R a t)) := by
  sorry

end CategoryTheory
