/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedColimitBar
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.Algebra.Category.ModuleCat.DerivedBaseChange
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.CategoryTheory.ExactFunctorDerivedFunctor
import WeilConjectures.CategoryTheory.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.AdjointFunctors
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Cones
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import WeilConjectures.CategoryTheory.PreDerivedAdjointFunctorsGeneral
import WeilConjectures.CategoryTheory.DerivedCategory.EverywhereDefinedDerivedFunctors
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic

/-!
# Derived colimits and change of coefficient rings

Source: Stacks Project, Cohomology on Sites, Tags 08Q8, 08PG and 08PH
(blueprint: lem-trf-derived-colimit-change-rings).

The records below expand one existence assertion. They never select data from an
unproved existence theorem. Scalar tensors use Mathlib's convention `S ⊗[R] M`,
which is the symmetric version of the source's `M ⊗[R] S`.
-/

@[expose] public section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace CategoryTheory

/-- Sectionwise extension on the identity-cover site. Source: Stacks 08Q8
(blueprint: lem-trf-derived-colimit-change-rings). -/
noncomputable abbrev categoryBarExtend {E : Type u} [SmallCategory E]
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) :
    (Eᵒᵖ ⥤ ModuleCat.{u} R) ⥤ (Eᵒᵖ ⥤ ModuleCat.{u} S) :=
  (Functor.whiskeringRight Eᵒᵖ (ModuleCat.{u} R) (ModuleCat.{u} S)).obj
    (ModuleCat.extendScalars φ)

/-- Sectionwise restriction on the identity-cover site. Source: Stacks 08Q8
(blueprint: lem-trf-derived-colimit-change-rings). -/
noncomputable abbrev categoryBarRestrict {E : Type u} [SmallCategory E]
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) :
    (Eᵒᵖ ⥤ ModuleCat.{u} S) ⥤ (Eᵒᵖ ⥤ ModuleCat.{u} R) :=
  (Functor.whiskeringRight Eᵒᵖ (ModuleCat.{u} S) (ModuleCat.{u} R)).obj
    (ModuleCat.restrictScalars φ)

/-- The identity commuting constants with coefficient restriction, descended to derived
categories. Source: Stacks 08Q8 (blueprint: lem-trf-derived-colimit-change-rings). -/
noncomputable def categoryBarRestrictConstant {E : Type u} [SmallCategory E]
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) :
    (Functor.const Eᵒᵖ : ModuleCat.{u} S ⥤ _).mapDerivedCategory ⋙
        (categoryBarRestrict (E := E) φ).mapDerivedCategory ≅
      (ModuleCat.restrictScalars φ).mapDerivedCategory ⋙
        (Functor.const Eᵒᵖ : ModuleCat.{u} R ⥤ _).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (NatIso.ofComponents
        (F := (Functor.const Eᵒᵖ : ModuleCat.{u} S ⥤ _) ⋙ categoryBarRestrict φ)
        (G := ModuleCat.restrictScalars φ ⋙ (Functor.const Eᵒᵖ : ModuleCat.{u} R ⥤ _))
        (fun _ ↦ Iso.refl _) (by intro X Y f; rfl)) ≪≫
      Functor.mapDerivedCategoryCompIso (ModuleCat.restrictScalars φ) (Functor.const Eᵒᵖ)

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- A universal derived extension together with the adjunction induced from ordinary
extension. This is the coefficient-category presentation of the dependency's universal
cochain model. Source: Stacks 06YY and 07A6
(blueprint: lem-trf-derived-colimit-change-rings). -/
structure CategoryBarDerivedExtension
    {A B : Type (u + 1)} [Category.{u} A] [Category.{u} B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{u + 1} A] [HasDerivedCategory.{u + 1} B]
    (e : A ⥤ B) (r : B ⥤ A) [e.Additive] [r.Additive]
    [PreservesFiniteLimits r] [PreservesFiniteColimits r] (adj : e ⊣ r) where
  functor : DerivedCategory A ⥤ DerivedCategory B
  counit : DerivedCategory.Q ⋙ functor ⟶
    e.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  universal : functor.IsLeftDerivedFunctor counit (HomologicalComplex.quasiIso A (.up ℤ))
  pointwise : Functor.HasPointwiseLeftDerivedFunctor
    (e.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (HomologicalComplex.quasiIso A (.up ℤ))
  adjunction : functor ⊣ r.mapDerivedCategory
  transpose : ∀ (P : CochainComplex A ℤ) (N : CochainComplex B ℤ)
    (a : (e.mapHomologicalComplex (.up ℤ)).obj P ⟶ N),
    adjunction.homEquiv (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj N)
      (counit.app P ≫ DerivedCategory.Q.map a) =
        DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).homEquiv P N a) ≫
          r.mapDerivedCategoryFactors.inv.app N

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- The comparison for a fixed coefficient map, including its canonical normalization and
flat-presheaf representatives. Source: Stacks 08Q8, 08PG, 08PH
(blueprint: lem-trf-derived-colimit-change-rings). -/
structure CategoryColimitChangeRings
    (B : CategoryColimitBarSystem.{u}) (E : Type u) [SmallCategory E]
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) where
  point : CategoryBarDerivedExtension (ModuleCat.extendScalars φ)
    (ModuleCat.restrictScalars φ) (ModuleCat.extendRestrictScalarsAdj φ)
  presheaf : CategoryBarDerivedExtension (categoryBarExtend (E := E) φ)
    (categoryBarRestrict (E := E) φ) ((ModuleCat.extendRestrictScalarsAdj φ).whiskerRight Eᵒᵖ)
  comparison : presheaf.functor ⋙ (B.models E S).derived ⟶
    (B.models E R).derived ⋙ point.functor
  iso : ∀ (M : CochainComplex (Eᵒᵖ ⥤ ModuleCat.{u} R) ℤ) (b : ℤ)
    (_hM : M.IsStrictlyLE b),
    (B.models E S).derived.obj (presheaf.functor.obj (DerivedCategory.Q.obj M)) ≅
      point.functor.obj ((B.models E R).derived.obj (DerivedCategory.Q.obj M))
  iso_hom : ∀ (M : CochainComplex (Eᵒᵖ ⥤ ModuleCat.{u} R) ℤ) (b : ℤ)
    (hM : M.IsStrictlyLE b), (iso M b hM).hom = comparison.app (DerivedCategory.Q.obj M)
  normalization : ∀ (M : DerivedCategory (Eᵒᵖ ⥤ ModuleCat.{u} R))
    (N : DerivedCategory (ModuleCat.{u} S))
    (a : point.functor.obj ((B.models E R).derived.obj M) ⟶ N),
    (presheaf.adjunction.comp (B.models E S).adjunction).homEquiv M N
        (comparison.app M ≫ a) ≫ (categoryBarRestrictConstant (E := E) φ).hom.app N =
      ((B.models E R).adjunction.comp point.adjunction).homEquiv M N a
  barIso : ∀ (F : Eᵒᵖ ⥤ ModuleCat.{u} R),
    (∀ U : Eᵒᵖ, Module.Flat R (F.obj U)) →
    ((B.models E S).bar.obj ((categoryBarExtend φ).obj F) ≅
      ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj
        ((B.models E R).bar.obj F))
  formula : ∀ (F : Eᵒᵖ ⥤ ModuleCat.{u} R)
    (hF : ∀ U : Eᵒᵖ, Module.Flat R (F.obj U))
    (n : ℕ) (c : ComposableArrows E n) (x : F.obj (op c.right)) (s : S),
    ((barIso F hF).hom.f (-(n : ℤ)))
        ((B.models E S).generator ((categoryBarExtend φ).obj F) n c (s ⊗ₜ[R,φ] x)) =
      s ⊗ₜ[R,φ] ((B.models E R).generator F n c x)
  barFlat : ∀ (F : Eᵒᵖ ⥤ ModuleCat.{u} R),
    (∀ U : Eᵒᵖ, Module.Flat R (F.obj U)) →
    ∀ q : ℤ, Module.Flat R (((B.models E R).bar.obj F).X q)
  flatPresheaf : ∀ (F : Eᵒᵖ ⥤ ModuleCat.{u} R),
    (∀ U : Eᵒᵖ, Module.Flat R (F.obj U)) →
    IsIso (presheaf.counit.app
      ((CochainComplex.singleFunctor (Eᵒᵖ ⥤ ModuleCat.{u} R) 0).obj F))
  flatBar : ∀ (F : Eᵒᵖ ⥤ ModuleCat.{u} R),
    (∀ U : Eᵒᵖ, Module.Flat R (F.obj U)) →
    IsIso (point.counit.app ((B.models E R).bar.obj F))
  represents : ∀ (F : Eᵒᵖ ⥤ ModuleCat.{u} R)
    (hF : ∀ U : Eᵒᵖ, Module.Flat R (F.obj U)),
    comparison.app (DerivedCategory.Q.obj
        ((CochainComplex.singleFunctor (Eᵒᵖ ⥤ ModuleCat.{u} R) 0).obj F)) ≫
      point.functor.map ((B.models E R).model.hom.app F) ≫
        point.counit.app ((B.models E R).bar.obj F) =
    (B.models E S).derived.map (presheaf.counit.app
        ((CochainComplex.singleFunctor (Eᵒᵖ ⥤ ModuleCat.{u} R) 0).obj F)) ≫
      (B.models E S).derived.map (DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex (categoryBarExtend φ)
          (.up ℤ) 0).hom.app F)) ≫
      (B.models E S).model.hom.app ((categoryBarExtend φ).obj F) ≫
        DerivedCategory.Q.map (barIso F hF).hom

/-- Coefficient extension commutes canonically with bounded-above derived category homology,
with the displayed flat-presheaf bar comparison. The normalization specifies the common
Hom bijection, hence all derived naturality under indexing functors and coefficient squares.
The tensor-generator formula specifies the same naturality for the explicit representatives.
Source: Stacks 08Q8 (with the typed order corrected), 08PG and 08PH
(blueprint: lem-trf-derived-colimit-change-rings).

Proof:
1. Restriction of scalars is exact objectwise. Apply the module adjunction, the derived
change-of-rings theorem, exact-functor descent and derived adjoint functors to obtain the
point and presheaf derived extensions and their adjunctions. The pre-derived Hom bijection
fixes their transpose on complexes: on K-flat models it is `s tensor x` sent to `s a(x)`.
2. Constants commute with restriction, on objects, maps and differentials. The bar theorem
identifies derived colimits as left adjoints to constants. Compose the adjunctions; the two
composites are left adjoints to the same right adjoint. Unit-normalized uniqueness gives
the comparison and its normalization, and makes it invertible on every bounded-above input.
3. Objectwise flat F is tensor-flat. Module categories and module-presheaf categories are
Grothendieck abelian with closed tensor preserving the required colimits. The bounded-above
flat K-flat criterion applies to F in degree zero and to the bar complex: every bar term is
a coproduct of flat modules and the positive terms vanish. Derived change of rings therefore
makes the two displayed counits invertible, and gives `barFlat`, `flatPresheaf`, `flatBar`.
4. Tensor commutes with the bar coproducts. On generators send `(sigma, s tensor x)` to
`s tensor (sigma, x)`. Its inverse distributes tensor into the finite sum of generators.
These maps are balanced and inverse; each face commutes with them, including the last
face, which restricts x. Thus they give `barIso` and `formula`.
5. The coefficient unit sends x to `1 tensor x`. Its semilinear bar map, provided by the
bar theorem, sends `(sigma,x)` to `(sigma,1 tensor x)`. Transposition under the derived
extension adjunction gives the inverse of the bar comparison. The unit equation of the
common adjunction identifies this map with `comparison`, proving `represents`.
6. For a functor u and a semilinear t over a commutative coefficient square (a,b), both
routes on generators send `(sigma,s tensor x)` to `b(s) tensor (u sigma,t(x))`.
For derived inputs, both routes have the same Hom transpose: compose t with the colimit
unit and restrict scalars. Uniqueness in the common adjunction gives the same square.
This includes coefficient identities, composites, identity functors and presheaf maps.
No step assumes S flat over R. -/
theorem categoryColimitChangeRings_exists (B : CategoryColimitBarSystem.{u})
    (E : Type u) [SmallCategory E] {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) : Nonempty (CategoryColimitChangeRings B E φ) := by
  sorry

/-- Naturality of the explicit comparison for indexing functors, semilinear presheaf maps
and commutative coefficient squares. Both tensor maps are supplied, with their full pure
tensor formulas; none is an arbitrary chosen comparison. Source: Stacks 08PG and 08PH
(blueprint: lem-trf-derived-colimit-change-rings).

Proof: for tS transpose the coefficient unit followed by t under the ordinary extension
adjunction, using the commuting coefficient square to identify the restricted actions.
For kS do the same termwise with the bar map B.map u a t. The formulas are balanced by
semilinearity and the coefficient-square equation; they commute with differentials by
functoriality of the bar map. Every element is a finite sum of pure tensors. On a bar
generator both routes send (sigma,s tensor x) to b(s) tensor (u sigma,t(x)). The two
barIso generator formulas and B.formula therefore give the displayed equality in every
nonpositive degree. Positive degrees are zero by the bar model's positive field. Taking
identity coefficient maps or identity indexing functors gives the corresponding special
naturality assertions. This is the explicit calculation of proof step 8 of the node. -/
theorem categoryColimitChangeRings_bar_naturality
    (B : CategoryColimitBarSystem.{u}) {E D : Type u} [SmallCategory E] [SmallCategory D]
    {R S R' S' : Type u} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    (φ : R →+* S) (ψ : R' →+* S') (a : R →+* R') (b : S →+* S')
    (hab : b.comp φ = ψ.comp a) (u : E ⥤ D)
    (C : CategoryColimitChangeRings B E φ) (C' : CategoryColimitChangeRings B D ψ)
    (F : Eᵒᵖ ⥤ ModuleCat.{u} R) (G : Dᵒᵖ ⥤ ModuleCat.{u} R')
    (hF : ∀ U : Eᵒᵖ, Module.Flat R (F.obj U))
    (hG : ∀ U : Dᵒᵖ, Module.Flat R' (G.obj U))
    (t : F ⟶ u.op ⋙ G ⋙ ModuleCat.restrictScalars a) :
    ∃ (tS : (categoryBarExtend φ).obj F ⟶
        u.op ⋙ (categoryBarExtend ψ).obj G ⋙ ModuleCat.restrictScalars b)
      (kS : ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj
          ((B.models E R).bar.obj F) ⟶
        ((ModuleCat.restrictScalars b).mapHomologicalComplex (.up ℤ)).obj
          (((ModuleCat.extendScalars ψ).mapHomologicalComplex (.up ℤ)).obj
            ((B.models D R').bar.obj G))),
      (∀ (U : Eᵒᵖ) (x : F.obj U) (s : S),
        tS.app U (s ⊗ₜ[R,φ] x) =
          b s ⊗ₜ[R',ψ] (@id (G.obj (u.op.obj U)) (t.app U x))) ∧
      (∀ (q : ℤ) (x : ((B.models E R).bar.obj F).X q) (s : S),
        kS.f q (s ⊗ₜ[R,φ] x) =
          b s ⊗ₜ[R',ψ] (@id (((B.models D R').bar.obj G).X q) (((B.map u a t).f q) x))) ∧
      (∀ (q : ℤ) (z : ((B.models E S).bar.obj ((categoryBarExtend φ).obj F)).X q),
        ((C'.barIso G hG).hom.f q) (((B.map u b tS).f q) z) =
          kS.f q (((C.barIso F hF).hom.f q) z)) := by
  sorry

end CategoryTheory
