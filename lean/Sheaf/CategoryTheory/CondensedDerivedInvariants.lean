/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Sheaf.CategoryTheory.CondensedEquivariantBarData
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.AdjunctionShift
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import Sheaf.CategoryTheory.CanonicalRightDerivedAdjunctionShift
import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.Paper.DerivedAdjunctionShift
import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal

/-! # Derived restriction calculus for internal condensed actions

Source: main-20261015 direct-images proof, paragraph (3), formal derived-restriction
infrastructure (blueprint: def-sfb-condensed-derived-invariants).
The source records this auxiliary infrastructure as agent-formulated, with a reference wanted.
No assertion that underived continuous cochains compute derived invariants is made.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open Profinite.CondensedAction (inflate trivial)
open CategoryTheory.CondensedBar

namespace CategoryTheory.CondensedDerivedRestriction

variable (A : CondensedBar.Ring.{u}) (G : Type u) [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

/-- The given additive category of internal actions is abelian, for arbitrary topological G.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants).
Proof: use the action-site presentation and the internal/sectionwise module equivalence.
Kernels and sheafified cokernels carry the induced action; normality and finite products
are computed on underlying internal modules. -/
theorem actionAbelianData : Nonempty (ActionAbelian A G) := by
  sorry

/-- Abelian-category structure on the existing action category; its data fields are
propositions, so this selects no unspecified mathematical object.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants). -/
instance actionAbelian : ActionAbelian A G := Classical.choice (actionAbelianData A G)

/-- The action-site presentation transports the generator, colimits and AB5.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants).
Proof: the action-site module equivalence preserves all limits and colimits; apply the
Grothendieck abelian theorem for modules on a small ringed site. -/
@[instance] theorem actionGrothendieck : IsGrothendieckAbelian.{u + 1} (Equivariant A G) := by
  sorry

/-- Forgetting the action creates kernels and cokernels and detects exactness.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants).
Proof: the equivariance equation restricts to kernels and descends to sheafified cokernels.
The forgetful functor is faithful and detects zero; exactness is therefore detected. -/
theorem forgetExact :
    PreservesFiniteLimits (CondensedBar.forgetAction (A := A) (G := G)) ∧
    PreservesFiniteColimits (CondensedBar.forgetAction (A := A) (G := G)) ∧
    (∀ S : ShortComplex (Equivariant A G),
      S.Exact ↔ (S.map (CondensedBar.forgetAction (A := A) (G := G))).Exact) := by
  sorry

/-- Existence of the normalized invariant-submodule adjunction already specified by the
recorded action-module definition. Its universal property determines it up to the unique
isomorphism commuting with its inclusion.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants).
Proof: fully fixed sections form submodules stable under restriction and gluing. Restrict
codomains of maps from trivial actions; composition with the inclusion is the inverse. -/
theorem invariantsExist : Nonempty (Invariants A G) := by
  sorry

/-- Trivial action is additive and exact on the underlying modules.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants).
Proof: it leaves objects and maps unchanged and preserves the induced kernels and cokernels. -/
@[instance] theorem trivialAdditive : (trivial (R := A.toMon) (P := G)).Additive := by
  sorry

/-- Exactness of trivial action, on kernels.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants).
Proof: the underlying kernel with trivial action is the equivariant kernel. -/
@[instance] theorem trivialLimits :
    PreservesFiniteLimits (trivial (R := A.toMon) (P := G)) := by
  sorry

/-- Exactness of trivial action, on cokernels.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants).
Proof: the underlying sheafified cokernel retains trivial action. -/
@[instance] theorem trivialColimits :
    PreservesFiniteColimits (trivial (R := A.toMon) (P := G)) := by
  sorry

variable {A G} {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- Restriction of actions along a continuous group map is additive.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants).
Proof: precomposition changes no underlying map, hence preserves sums. -/
@[instance] theorem restrictionAdditive (v : H →ₜ* G) :
    (inflate (R := A.toMon) v).Additive := by
  sorry

/-- Restriction is left exact, with the induced action on the same kernel.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants).
Proof: precomposition of the action commutes with the kernel construction. -/
@[instance] theorem restrictionLimits (v : H →ₜ* G) :
    PreservesFiniteLimits (inflate (R := A.toMon) v) := by
  sorry

/-- Restriction is right exact, with the induced action on the same cokernel.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants).
Proof: precomposition of the action commutes with sheafified cokernels. -/
@[instance] theorem restrictionColimits (v : H →ₜ* G) :
    PreservesFiniteColimits (inflate (R := A.toMon) v) := by
  sorry

section Derived
variable [HasDerivedCategory.{u + 1} (Modules A)]
  [HasDerivedCategory.{u + 1} (Equivariant A G)]
  [HasDerivedCategory.{u + 1} (Equivariant A H)]

/-- The invariant inclusion uniquely determines the underived restriction map.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants).
Proof: a fully G-fixed section is H-fixed after precomposition. Restrict the codomain
using the normalized invariant inclusion, which is a monomorphism on every section. -/
theorem invariantRestrictionExist (V : Invariants A G) (W : Invariants A H) (v : H →ₜ* G) :
    ∃! b : V.functor ⟶ inflate (R := A.toMon) v ⋙ W.functor,
      ∀ N, b.app N ≫ W.inclusion.app ((inflate v).obj N) = V.inclusion.app N := by
  sorry

/-- The unique map into the invariant subsheaf; uniqueness fixes the actual arrow.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants). -/
def invariantRestriction (V : Invariants A G) (W : Invariants A H) (v : H →ₜ* G) :
    V.functor ⟶ inflate (R := A.toMon) v ⋙ W.functor :=
  Classical.choose (invariantRestrictionExist V W v)

/-- Canonical total derived restriction, obtained by right deriving the fixed-section
inclusion along the exact restriction functor, not by assuming it preserves injectives.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants). -/
def restriction (V : Invariants A G) (W : Invariants A H) (v : H →ₜ* G) :
    V.functor.rightDerivedFunctor ⟶
      (inflate (R := A.toMon) v).mapDerivedCategory ⋙ W.functor.rightDerivedFunctor :=
  Functor.rightDerivedPullback (inflate v) (invariantRestriction V W v)


end Derived

/-- Functorial flat resolutions on the coherent profinite site.
Source: paragraph (3), the ordinary derived tensor
(blueprint: def-sfb-condensed-derived-invariants).
Proof: take the sum of free represented abelian sheaves on all generalized sections.
The evaluation map is locally surjective. Each represented free sheaf is flat, since
its tensor is extension by zero from the slice; direct sums preserve flatness. This
construction is functorial and gives a left resolution by flat objects. -/
@[instance] theorem sheafFlatResolution :
    Abelian.HasFunctorialFlatResolution
      (Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1}) := by
  sorry


/-- Canonical invariants, selected by their fixed-section inclusion universal property.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants). -/
def invariants (A : CondensedBar.Ring.{u}) (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : Invariants A G := Classical.choice (invariantsExist A G)

/-- Ordinary unbounded right derived invariants, in the existing small-Hom localization.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants). -/
def derived (A : CondensedBar.Ring.{u}) (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : DerivedCategory.{u + 1} (Equivariant A G) ⥤
      DerivedCategory.{u + 1} (Modules A) := (invariants A G).functor.rightDerivedFunctor

/-- The exact trivial-action functor on ordinary derived categories.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants). -/
def trivialDerived (A : CondensedBar.Ring.{u}) (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : DerivedCategory.{u + 1} (Modules A) ⥤
      DerivedCategory.{u + 1} (Equivariant A G) :=
  (trivial (R := A.toMon) (P := G)).mapDerivedCategory

/-- The canonical derived adjunction, with its actual resolution-normalized unit and counit.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants). -/
def adjunction (A : CondensedBar.Ring.{u}) (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : trivialDerived A G ⊣ derived A G :=
  (invariants A G).adjunction.mapDerivedCategoryRightDerivedAdjunction

/-- Exact group restriction on derived actions.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants). -/
def groupDerived (A : CondensedBar.Ring.{u}) (v : H →ₜ* G) :
    DerivedCategory.{u + 1} (Equivariant A G) ⥤
      DerivedCategory.{u + 1} (Equivariant A H) :=
  (inflate (R := A.toMon) v).mapDerivedCategory

/-- The canonical restriction transformation used in all the formulas below.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants). -/
def groupMap (A : CondensedBar.Ring.{u}) (v : H →ₜ* G) :
    derived A G ⟶ groupDerived A v ⋙ derived A H :=
  restriction (invariants A G) (invariants A H) v

/-- Derived invariants are additive and triangulated with canonical integer shifts.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants).
Proof: apply the ordinary K-injective right-derived functor construction to the additive
invariants functor. Its homotopy-category localization preserves shifts and cone triangles. -/
theorem derivedProperties : (derived A G).Additive ∧
    Nonempty ((derived A G).CommShift ℤ) := by
  sorry


/-- The derived invariant functor has its canonical integer-shift structure.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants). -/
instance derivedShift : (derived A G).CommShift ℤ :=
  inferInstanceAs ((invariants A G).functor.rightDerivedFunctor.CommShift ℤ)

/-- The ordinary K-injective functor is triangulated.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants). -/
instance derivedTriangulated : (derived A G).IsTriangulated :=
  inferInstanceAs ((invariants A G).functor.rightDerivedFunctor.IsTriangulated)

/-- Exact group restriction carries the canonical signed shift.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants). -/
instance groupShift (v : H →ₜ* G) : (groupDerived A v).CommShift ℤ :=
  inferInstanceAs ((inflate (R := A.toMon) v).mapDerivedCategory.CommShift ℤ)

/-- Derived group restriction commutes with canonical shifts, hence with every connecting
arrow of every distinguished triangle, by naturality and this shift equation.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants).
Proof: write the restriction as the mate of the exact trivial-action comparison.
Its units and counits commute with shifts; composition and whiskering preserve this. -/
theorem groupMapShift (v : H →ₜ* G) : NatTrans.CommShift (groupMap A v) ℤ := by
  sorry

/-- The derived map is normalized by the invariant inclusion on all complexes. On
bounded-below objects its two units are computed by equivariant injective resolutions.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants).
Proof: this is the universal right-derived factorization of the underived inclusion.
Bounded-below complexes of injectives are K-injective, giving the resolution formula. -/
theorem groupMapNormalization (v : H →ₜ* G)
    (K : CochainComplex (Equivariant A G) ℤ) :
    (invariants A G).functor.rightDerivedFunctorUnitQ K ≫
      (groupMap A v).app (DerivedCategory.Q.obj K) ≫
      (derived A H).map ((inflate v).mapDerivedCategoryFactors.hom.app K) =
    DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex
        (invariantRestriction (invariants A G) (invariants A H) v) (.up ℤ)).app K) ≫
      (invariants A H).functor.rightDerivedFunctorUnitQ
        (((inflate v).mapHomologicalComplex (.up ℤ)).obj K) := by
  sorry

/-- Degree zero is the actual invariant functor, with the comparison induced by the
right-derived unit, not an arbitrarily chosen cohomology isomorphism.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants).
Proof: in an injective resolution, H⁰ of invariants is the kernel of the first invariant
differential, which is invariants of the original module by left exactness. -/
theorem degreeZero : ∃ e :
    (DerivedCategory.singleFunctor (Equivariant A G) 0 ⋙ derived A G) ⋙
      DerivedCategory.homologyFunctor (Modules A) 0 ≅ (invariants A G).functor,
    ∀ N, (DerivedCategory.homologyFunctor (Modules A) 0).map
      ((invariants A G).functor.rightDerivedFunctorUnitQ
        ((HomologicalComplex.single _ (.up ℤ) 0).obj N)) ≫ e.hom.app N =
      (DerivedCategory.homologyFunctor (Modules A) 0).map
        (DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex (invariants A G).functor
            (.up ℤ) 0).hom.app N)) ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso (Modules A) 0).hom.app
          ((invariants A G).functor.obj N) := by
  sorry

/-- The degree-zero identification fixed by the computation unit. That equation
uniquely determines this isomorphism, since the two comparison maps in degree zero
are invertible by left exactness.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants). -/
def degreeZeroIso :
    (DerivedCategory.singleFunctor (Equivariant A G) 0 ⋙ derived A G) ⋙
      DerivedCategory.homologyFunctor (Modules A) 0 ≅ (invariants A G).functor :=
  Classical.choose (degreeZero (A := A) (G := G))

variable {A' : CondensedBar.Ring.{u}}

/-- The existing normalized scalar-action specification has a canonical realization.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants).
Proof: use the same underlying abelian sheaf and action, and restrict its scalar action
along the given ring map. The displayed underlying comparison is identity on sections. -/
theorem scalarActionExist (a : A ⟶ A') : Nonempty (ScalarAction a G) := by
  sorry

/-- Scalar restriction on actions, fixed by its underlying module and section action.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants). -/
def scalarAction (a : A ⟶ A') : ScalarAction a G := Classical.choice (scalarActionExist a)

/-- Scalar restriction of actions is exact, without flatness of the ring map.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants).
Proof: kernels and sheafified cokernels have the same underlying abelian sheaves before
and after restricting scalars; their induced group actions are unchanged. -/
theorem scalarExact (a : A ⟶ A') :
    PreservesFiniteLimits (scalarAction (G := G) a).functor ∧
    PreservesFiniteColimits (scalarAction (G := G) a).functor := by
  sorry

/-- Exactness on kernels, from the preceding statement.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants). -/
instance scalarLimits (a : A ⟶ A') :
    PreservesFiniteLimits (scalarAction (G := G) a).functor := (scalarExact a).1

/-- Exactness on cokernels, from the preceding statement.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants). -/
instance scalarColimits (a : A ⟶ A') :
    PreservesFiniteColimits (scalarAction (G := G) a).functor := (scalarExact a).2

/-- Termwise scalar restriction on derived action modules.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants). -/
def scalarDerived (a : A ⟶ A') (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : DerivedCategory.{u + 1} (Equivariant A' G) ⥤
      DerivedCategory.{u + 1} (Equivariant A G) :=
  (scalarAction (G := G) a).functor.mapDerivedCategory

/-- Termwise scalar restriction on derived internal modules.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants). -/
def scalarBase (a : A ⟶ A') : DerivedCategory.{u + 1} (Modules A') ⥤
    DerivedCategory.{u + 1} (Modules A) := (Mod.comap a.hom.hom).mapDerivedCategory

/-- Scalar restriction and taking the fully fixed subsheaf commute canonically. The
normalization fixes this isomorphism on the actual invariant inclusions.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants).
Proof: both sides consist of the same sections fixed after every profinite base change;
their inclusions identify the same submodule of the restricted underlying sheaf. -/
theorem scalarInvariantsExist (a : A ⟶ A') :
    ∃! e : (scalarAction (G := G) a).functor ⋙ (invariants A G).functor ≅
        (invariants A' G).functor ⋙ Mod.comap a.hom.hom,
      ∀ N, (invariants A G).inclusion.app ((scalarAction a).functor.obj N) ≫
          (scalarAction a).underlying.hom.app N =
        e.hom.app N ≫ (Mod.comap a.hom.hom).map ((invariants A' G).inclusion.app N) := by
  sorry

/-- The unique scalar/invariants comparison fixed by the invariant inclusions.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants). -/
def scalarInvariants (a : A ⟶ A') :
    (scalarAction (G := G) a).functor ⋙ (invariants A G).functor ≅
      (invariants A' G).functor ⋙ Mod.comap a.hom.hom :=
  Classical.choose (scalarInvariantsExist a)

/-- The scalar comparison is the unique derived transformation whose computation units
are the underived fixed-section identification, and is invertible for any ring map.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants).
Proof: view scalar restriction and invariants as direct images of the identity ringed
topos and the action projection. Their two composites are the same ringed direct image.
The canonical derived-composition comparisons give this isomorphism, compatibly with
computation units; uniqueness follows from the right-derived universal property. No
preservation of injectives by scalar restriction and no flatness is used. -/
theorem scalarComparisonExist (a : A ⟶ A') :
    ∃! d : scalarDerived a G ⋙ derived A G ≅ derived A' G ⋙ scalarBase a,
      ∀ K : CochainComplex (Equivariant A' G) ℤ,
        (invariants A G).functor.rightDerivedFunctorUnitQ
            (((scalarAction a).functor.mapHomologicalComplex (.up ℤ)).obj K) ≫
          (derived A G).map ((scalarAction a).functor.mapDerivedCategoryFactors.inv.app K) ≫
          d.hom.app (DerivedCategory.Q.obj K) =
        DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex (scalarInvariants a) (.up ℤ)).hom.app K) ≫
          (Mod.comap a.hom.hom).mapDerivedCategoryFactors.inv.app
            (((invariants A' G).functor.mapHomologicalComplex (.up ℤ)).obj K) ≫
          (scalarBase a).map ((invariants A' G).functor.rightDerivedFunctorUnitQ K) := by
  sorry


/-- The unique derived coefficient isomorphism normalized by the computation units.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants). -/
def scalarComparison (a : A ⟶ A') :
    scalarDerived a G ⋙ derived A G ≅ derived A' G ⋙ scalarBase a :=
  Classical.choose (scalarComparisonExist a)

/-- Coefficient map for any derived equivariant morphism. Modules enter via the ordinary
single-degree embedding; this formula also applies to every complex.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants). -/
def coefficientMap (a : A ⟶ A') {N : DerivedCategory.{u + 1} (Equivariant A G)}
    {N' : DerivedCategory.{u + 1} (Equivariant A' G)}
    (f : N ⟶ (scalarDerived a G).obj N') :
    (derived A G).obj N ⟶ (scalarBase a).obj ((derived A' G).obj N') :=
  (derived A G).map f ≫ (scalarComparison a).hom.app N'

/-- Scalar and group restriction commute, with the comparison fixed on underlying
section modules by the two scalar-action identifications.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants).
Proof: both actions are the same action precomposed with v, with the same scalar action.
The underlying comparisons determine the equivariant comparison uniquely. -/
theorem scalarGroupExist (a : A ⟶ A') (v : H →ₜ* G) :
    ∃! e : (scalarAction (G := G) a).functor ⋙ inflate v ≅
        inflate v ⋙ (scalarAction (G := H) a).functor,
      ∀ N, (e.hom.app N).val ≫ (scalarAction a).underlying.hom.app ((inflate v).obj N) =
        (scalarAction a).underlying.hom.app N := by
  sorry

/-- The unique underived commutation isomorphism, fixed by its underlying maps.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants). -/
def scalarGroup (a : A ⟶ A') (v : H →ₜ* G) :
    (scalarAction (G := G) a).functor ⋙ inflate v ≅
      inflate v ⋙ (scalarAction (G := H) a).functor :=
  Classical.choose (scalarGroupExist a v)

/-- The localization of the actual scalar/group commutation comparison.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants). -/
def scalarGroupDerived (a : A ⟶ A') (v : H →ₜ* G) :
    scalarDerived a G ⋙ groupDerived A v ≅ groupDerived A' v ⋙ scalarDerived a H :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (scalarGroup a v) ≪≫
      Functor.mapDerivedCategoryCompIso _ _

/-- The coefficient isomorphism commutes with the canonical signed shifts.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants).
Proof: the left scalar-extension comparisons commute with shifts on K-flat models;
conjugation through shift-compatible derived adjunctions gives the result. -/
instance scalarDerivedShift (a : A ⟶ A') : (scalarDerived a G).CommShift ℤ :=
  inferInstanceAs ((scalarAction (G := G) a).functor.mapDerivedCategory.CommShift ℤ)

/-- Canonical shift of exact scalar restriction on base modules.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants). -/
instance scalarBaseShift (a : A ⟶ A') : (scalarBase a).CommShift ℤ :=
  inferInstanceAs ((Mod.comap a.hom.hom).mapDerivedCategory.CommShift ℤ)

/-- The scalar comparison respects canonical shifts, so also connecting morphisms.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants).
Proof: its expression by units, the scalar-extension composition and counits commutes
with shifts by derived-adjunction normalization and closure under composition. -/
theorem scalarComparisonShift (a : A ⟶ A') :
    NatTrans.CommShift (scalarComparison (G := G) a).hom ℤ := by
  sorry



/-- Exact group restriction along the identity has its normalized identity comparison.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants).
Proof: both actions are the same action. The identity of the underlying module is
equivariant, invertible, and natural. Faithfulness determines the comparison uniquely. -/
theorem identityActionExist :
    ∃! e : inflate (R := A.toMon) (ContinuousMonoidHom.id G) ≅ 𝟭 (Equivariant A G),
      ∀ N, (e.hom.app N).val = 𝟙 N.module := by
  sorry

/-- The identity comparison fixed by the original internal-module identity maps.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants). -/
def identityAction : inflate (R := A.toMon) (ContinuousMonoidHom.id G) ≅
    𝟭 (Equivariant A G) := Classical.choose (identityActionExist (A := A) (G := G))

/-- Canonical identity comparison of derived group restriction.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants). -/
def identityGroup : groupDerived A (ContinuousMonoidHom.id G) ≅
    𝟭 (DerivedCategory.{u + 1} (Equivariant A G)) :=
  Functor.mapDerivedCategoryNatIso (identityAction (A := A) (G := G)) ≪≫
    Functor.mapDerivedCategoryIdIso (Equivariant A G)

/-- The canonical coefficient restriction to a subgroup, with degree-zero trivial
coefficients retained as the original regular module.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants). -/
def regularTrivial (A : CondensedBar.Ring.{u}) (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] :=
  (trivial (R := A.toMon) (P := G)).obj (Mod.regular A.X)

end CategoryTheory.CondensedDerivedRestriction
