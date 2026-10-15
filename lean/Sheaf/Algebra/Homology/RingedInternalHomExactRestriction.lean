/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.Algebra.Homology.DerivedInternalHom
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.KFlat
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Sheaf.Algebra.Homology.KFlatResolution
import Sheaf.Algebra.Homology.HomComplex
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions
import Sheaf.Algebra.Homology.KInjectiveHomComplex
import Sheaf.Algebra.Homology.QuasiIsoHomComplexMap
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import Sheaf.Algebra.Homology.KInjectiveRestrictLocalized
import Sheaf.Algebra.Homology.DerivedInternalHomShiftLeft
import Sheaf.Algebra.Homology.DerivedInternalHomShiftRight
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.CategoryTheory.Triangulated.Triangulated
public import Sheaf.Algebra.Homology.KFlatCoefficientUniverse
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses

/-!
# Internal derived Hom calculus on small ringed sites

Source: Stacks Project, Cohomology on Sites, Tags 08J9, 08JB and 08JC
(blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction).

The tensor functor is specified by its natural total-tensor comparison on K-flat
representatives. Restriction uses Mathlib's slice functors and their induced functors
on unbounded derived categories. The opposite triangulated structure reverses shifts.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Pretriangulated.Opposite

namespace CategoryTheory

/-- The overFunctor slice restriction is additive.

Source: Stacks Project, Tag 08JB, restriction to a localized ringed site.
(blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction).

Proof: Restriction evaluates a sectionwise linear natural transformation on the slice site.
    Addition of such transformations is sectionwise, so restriction preserves addition. -/
@[instance]
theorem ringedSite_overFunctor_additive
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u}) (U :
    C) : (SheafOfModules.overFunctor.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
    RingCat.{u})).obj R) U).Additive := by
  sorry

/-- The overFunctor slice restriction preserves finite limits.

Source: Stacks Project, Tag 08JB, restriction to a localized ringed site.
(blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction).

Proof: Kernels and finite products of module sheaves are computed sectionwise. Evaluation along
    the forgetful functor from the slice preserves these constructions. The ring transport in
    overMap is the canonical identity on sections. -/
@[instance]
theorem ringedSite_overFunctor_limits
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u}) (U :
    C) : PreservesFiniteLimits (SheafOfModules.overFunctor.{u} ((sheafCompose J (forget₂
    CommRingCat.{u} RingCat.{u})).obj R) U) := by
  sorry

/-- The overFunctor slice restriction preserves finite colimits.

Source: Stacks Project, Tag 08JB, restriction to a localized ringed site.
(blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction).

Proof: Finite sums are sectionwise and cokernels are sheafified sectionwise cokernels. Coverings
    of an object of a slice are exactly coverings of its domain with the given structural arrow.
    Thus restriction commutes with sheafification and with these cokernels. The same argument
    applies to overMap. -/
@[instance]
theorem ringedSite_overFunctor_colimits
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u}) (U :
    C) : PreservesFiniteColimits (SheafOfModules.overFunctor.{u} ((sheafCompose J (forget₂
    CommRingCat.{u} RingCat.{u})).obj R) U) := by
  sorry

/-- The overMap slice restriction is additive.

Source: Stacks Project, Tag 08JB, restriction to a localized ringed site.
(blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction).

Proof: Restriction evaluates a sectionwise linear natural transformation on the slice site.
    Addition of such transformations is sectionwise, so restriction preserves addition. -/
@[instance]
theorem ringedSite_overMap_additive
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u}) {U V
    : C} (f : V ⟶ U) : (SheafOfModules.overMap.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
    RingCat.{u})).obj R) f).Additive := by
  sorry

/-- The overMap slice restriction preserves finite limits.

Source: Stacks Project, Tag 08JB, restriction to a localized ringed site.
(blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction).

Proof: Kernels and finite products of module sheaves are computed sectionwise. Evaluation along
    the forgetful functor from the slice preserves these constructions. The ring transport in
    overMap is the canonical identity on sections. -/
@[instance]
theorem ringedSite_overMap_limits
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u}) {U V
    : C} (f : V ⟶ U) : PreservesFiniteLimits (SheafOfModules.overMap.{u} ((sheafCompose J (forget₂
    CommRingCat.{u} RingCat.{u})).obj R) f) := by
  sorry

/-- The overMap slice restriction preserves finite colimits.

Source: Stacks Project, Tag 08JB, restriction to a localized ringed site.
(blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction).

Proof: Finite sums are sectionwise and cokernels are sheafified sectionwise cokernels. Coverings
    of an object of a slice are exactly coverings of its domain with the given structural arrow.
    Thus restriction commutes with sheafification and with these cokernels. The same argument
    applies to overMap. -/
@[instance]
theorem ringedSite_overMap_colimits
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u}) {U V
    : C} (f : V ⟶ U) : PreservesFiniteColimits (SheafOfModules.overMap.{u} ((sheafCompose J
    (forget₂ CommRingCat.{u} RingCat.{u})).obj R) f) := by
  sorry

/-- The tensor--Hom currying isomorphism is natural in all three derived objects.
The parameters P, hP, T and r specify the derived tensor in the node: total
tensor on K-flat representatives. They impose no condition on K, L or M.

Source: Stacks Project, Tag 08J9 (lemma-internal-hom).
(blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction).

Proof: Choose a K-flat representative B of L (lem-pc-kflat-resolution) and a K-injective I of M
    (prop-pur-kinjective-resolutions-exist). Currying identifies Hom(A, Hom(B,I)) with Hom(Tot(A
    tensor B),I): Hom out of a direct sum is a product. Expanding the differential gives d_I
    f(a,b) - (-1)^n f(d_A a,b) - (-1)^(n+p) f(a,d_B b) on both sides. The inverse is uncurrying.
    Hom(B,I) is K-injective by lem-pur-hom-kflat-into-kinjective; K-flatness computes derived
    tensor. The representative comparisons of def-pur-derived-internal-hom and
    lem-pur-rhom-well-defined descend the chain isomorphism to the localization. Its formula
    commutes with precomposition in A,B and postcomposition in I, giving the displayed naturality
    equation. -/
theorem ringedInternalHom_tensor_adjunction
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
    RingCat.{u})).obj R))]
    (P : ObjectProperty (CochainComplex (ringedSiteModules.{u} ((sheafCompose J (forget₂
    CommRingCat.{u} RingCat.{u})).obj R)) ℤ))
    (hP : ∀ X, P X ↔ X.IsKFlat)
    (T : (DerivedCategory (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
    RingCat.{u})).obj R))) × (DerivedCategory (ringedSiteModules.{u} ((sheafCompose J (forget₂
    CommRingCat.{u} RingCat.{u})).obj R))) ⥤ (DerivedCategory (ringedSiteModules.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))))
    (r : (P.ι.prod P.ι) ⋙ Functor.uncurry.obj
    ((@CategoryTheory.MonoidalCategory.curriedTensor (ringedSiteModules.{u} ((sheafCompose J
    (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) _
    (SheafOfModules.monoidalCategory R)).map₂HomologicalComplex
    (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q ≅
    ((P.ι ⋙ DerivedCategory.Q).prod (P.ι ⋙ DerivedCategory.Q)) ⋙ T) :
    ∃ e : ∀ K L M : (DerivedCategory (ringedSiteModules.{u} ((sheafCompose J (forget₂
    CommRingCat.{u} RingCat.{u})).obj R))),
    (derivedInternalHom.{u, w} J R).obj (op K, (derivedInternalHom.{u, w} J R).obj (op L, M)) ≅
    (derivedInternalHom.{u, w} J R).obj (op (T.obj (K, L)), M),
    ∀ (K L M K' L' M' : (DerivedCategory (ringedSiteModules.{u} ((sheafCompose J (forget₂
    CommRingCat.{u} RingCat.{u})).obj R)))) (a : K' ⟶ K) (b : L' ⟶ L) (c : M ⟶ M'),
    (e K L M).hom ≫ (derivedInternalHom.{u, w} J R).map ((T.map (a, b)).op, c) =
    (derivedInternalHom.{u, w} J R).map (a.op, (derivedInternalHom.{u, w} J R).map (b.op, c)) ≫ (e
    K' L' M').hom := by
  sorry

/-- Derived internal Hom commutes naturally with slice restriction, compatibly
with successive restrictions. The comparison for V to U, followed by transport
along the canonical derived overFunctorMap, equals direct restriction to V.

Source: Stacks Project, Tag 08JB (lemma-restriction-RHom-to-U).
(blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction).

Proof: Represent M by a K-injective I and L by A. The sections of Hom(A,I) restricted to U, over
    each arrow W to U, are the same families of local maps as the sections of Hom(A restricted to
    U, I restricted to U); their differentials coincide. Restriction preserves K-injectivity
    (lem-pur-kinjective-restrict-localized), so these complexes compute derived internal Hom. The
    same construction for Over.map f gives s. On every object mapping to V both successive and
    direct comparisons are identity on these families, after the canonical overFunctorMap
    transport. This proves the displayed equation; pre- and postcomposition give naturality.
    Independence of representatives follows from lem-pur-rhom-well-defined. -/
theorem ringedInternalHom_restriction
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
    RingCat.{u})).obj R))] [hDCU : ∀ U : C, HasDerivedCategory.{w} (ringedSiteModules.{u}
    (((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R).over U))] :
    ∃ (e : ∀ U : C, (derivedInternalHom.{u, w} J R) ⋙ (SheafOfModules.overFunctor.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) U).mapDerivedCategory ≅
    ((SheafOfModules.overFunctor.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj
    R) U).mapDerivedCategory.op.prod (SheafOfModules.overFunctor.{u} ((sheafCompose J (forget₂
    CommRingCat.{u} RingCat.{u})).obj R) U).mapDerivedCategory) ⋙ (@derivedInternalHom.{u, w}
    (Over U) inferInstance (J.over U) (R.over U) (hDCU U)))
    (s : ∀ (U V : C) (f : V ⟶ U), (@derivedInternalHom.{u, w} (Over U) inferInstance (J.over U)
    (R.over U) (hDCU U)) ⋙ (SheafOfModules.overMap.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
    RingCat.{u})).obj R) f).mapDerivedCategory ≅
    ((SheafOfModules.overMap.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
    f).mapDerivedCategory.op.prod (SheafOfModules.overMap.{u} ((sheafCompose J (forget₂
    CommRingCat.{u} RingCat.{u})).obj R) f).mapDerivedCategory) ⋙ (@derivedInternalHom.{u, w}
    (Over V) inferInstance (J.over V) (R.over V) (hDCU V))),
    ∀ (U V : C) (f : V ⟶ U) (L M : (DerivedCategory (ringedSiteModules.{u} ((sheafCompose J
    (forget₂ CommRingCat.{u} RingCat.{u})).obj R)))),
    (SheafOfModules.overMap.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
    f).mapDerivedCategory.map ((e U).hom.app (op L, M)) ≫
    (s U V f).hom.app (op ((SheafOfModules.overFunctor.{u} ((sheafCompose J (forget₂
    CommRingCat.{u} RingCat.{u})).obj R) U).mapDerivedCategory.obj L),
    (SheafOfModules.overFunctor.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
    U).mapDerivedCategory.obj M) ≫
    (@derivedInternalHom.{u, w} (Over V) inferInstance (J.over V) (R.over V) (hDCU V)).map
    (X := (op ((SheafOfModules.overMap.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
    RingCat.{u})).obj R) f).mapDerivedCategory.obj ((SheafOfModules.overFunctor.{u} ((sheafCompose
    J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) U).mapDerivedCategory.obj L)),
    (SheafOfModules.overMap.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
    f).mapDerivedCategory.obj ((SheafOfModules.overFunctor.{u} ((sheafCompose J (forget₂
    CommRingCat.{u} RingCat.{u})).obj R) U).mapDerivedCategory.obj M)))
    (Y := (op ((SheafOfModules.overFunctor.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
    RingCat.{u})).obj R) V).mapDerivedCategory.obj L), (SheafOfModules.overFunctor.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) V).mapDerivedCategory.obj M))
    (((((Functor.mapDerivedCategoryCompIso (SheafOfModules.overFunctor.{u} ((sheafCompose J
    (forget₂ CommRingCat.{u} RingCat.{u})).obj R) U) (SheafOfModules.overMap.{u} ((sheafCompose J
    (forget₂ CommRingCat.{u} RingCat.{u})).obj R) f)).symm ≪≫ Functor.mapDerivedCategoryNatIso
    (SheafOfModules.overFunctorMap ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
    f))).inv.app L).op, (((Functor.mapDerivedCategoryCompIso (SheafOfModules.overFunctor.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) U) (SheafOfModules.overMap.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) f)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (SheafOfModules.overFunctorMap ((sheafCompose J (forget₂
    CommRingCat.{u} RingCat.{u})).obj R) f))).hom.app M) =
    (((Functor.mapDerivedCategoryCompIso (SheafOfModules.overFunctor.{u} ((sheafCompose J (forget₂
    CommRingCat.{u} RingCat.{u})).obj R) U) (SheafOfModules.overMap.{u} ((sheafCompose J (forget₂
    CommRingCat.{u} RingCat.{u})).obj R) f)).symm ≪≫ Functor.mapDerivedCategoryNatIso
    (SheafOfModules.overFunctorMap ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
    f))).hom.app ((derivedInternalHom.{u, w} J R).obj (op L, M)) ≫
    (e V).hom.app (op L, M) := by
  sorry

/-- Internal derived Hom preserves distinguished triangles in each variable
and commutes with shifts. The first variable is a functor from the opposite
triangulated category, whose shift by m is the original shift by -m.

Source: Stacks Project, Tag 08JC (lemma-RHom-triangulated).
(blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction).

Proof: For the first variable fix a K-injective I representing M. The graded splitting of the cone
    gives Hom(C(f),I) as Hom(B,I) plus Hom(A[1],I). Put X=Hom(B,I), Y=Hom(A,I), h=f*. In degree n
    its differential is (d_X x, d_Y y+(-1)^(n+1)h(x)); (x,y) maps to ((-1)^(n-1)y,x) in C(h)[-1].
    Rotation gives the reversed distinguished triangle. For the second variable choose K-injective
    representatives J,I; lem-weil-pbc-kinjective-hom-derived represents the morphism by a chain
    map g. TR3 and lem-sf-triangle-morphism-iso identify its cone triangle with the given
    triangle. Its cone is K-injective: Hom from any acyclic test complex is the cone of two
    acyclic ordinary Hom complexes, hence acyclic. Then Hom(A,C(g)) is the cone of Hom(A,g), with
    differential (dx+Hom(A,g)y,-dy). These cone calculations descend by
    lem-pur-homotopy-category-triangulated and lem-pur-rhom-well-defined. The natural shift
    identifications from lem-pur-derived-internal-hom-shift-left and
    lem-pur-derived-internal-hom-shift-right give H(P[m],Q)=H(P,Q)[-m] and H(P,Q[n])=H(P,Q)[n].
    The cone signs give the required triangulated structures. Only finite splittings occur, so no
    boundedness or finite-generation hypothesis is used. -/
theorem ringedInternalHom_exact
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
    RingCat.{u})).obj R))] :
    (∀ L : (DerivedCategory (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
    RingCat.{u})).obj R))), ∃ _ : ((Functor.curry.obj (derivedInternalHom.{u, w} J R)).obj (op
    L)).CommShift ℤ,
    ((Functor.curry.obj (derivedInternalHom.{u, w} J R)).obj (op L)).IsTriangulated) ∧
    (∀ M : (DerivedCategory (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
    RingCat.{u})).obj R))), ∃ _ : ((Functor.curry.obj (derivedInternalHom.{u, w} J R)).flip.obj
    M).CommShift ℤ,
    ((Functor.curry.obj (derivedInternalHom.{u, w} J R)).flip.obj M).IsTriangulated) := by
  sorry

end CategoryTheory
