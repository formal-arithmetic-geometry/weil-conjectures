/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q06
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import Sheaf.AlgebraicGeometry.GroupSpaceOverCartesian
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal

/-! # Quotients by free flat group algebraic spaces

Source: Stacks Project, bootstrap.tex, Tag 06PH, lemma-quotient-free-action
(blueprint: lem-sfb-free-flat-group-space-quotient).

Group objects and actions are Mathlib's internal objects in the category of fppf sheaves
over the base sheaf. The orbit presheaf is the presheaf coequalizer of action and projection.
Its sheafification and its quotient map are actual canonical constructions.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- The sectionwise orbit presheaf, expressed as the coequalizer of the action and
projection. Colimits of presheaves of sets are computed sectionwise, and for a group
action the generated equivalence relation is exactly the orbit relation.
Source: Stacks, spaces-groupoids.tex, definition-quotient-sheaf, used in Tag 06PH
(blueprint: lem-sfb-free-flat-group-space-quotient). -/
def groupSpaceOrbitPresheaf {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G Z : Over B.obj) [GrpObj G] [ModObj G Z] : (Over S)ᵒᵖ ⥤ Type u :=
  coequalizer (ModObj.smul (M := G) (X := Z)).left.hom
    (CartesianMonoidalCategory.snd G Z).left.hom

/-- The fppf sheafification of the sectionwise orbit presheaf.
Source: Stacks, Tag 06PH and spaces-groupoids.tex, definition-quotient-sheaf
(blueprint: lem-sfb-free-flat-group-space-quotient). -/
def groupSpaceQuotient {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G Z : Over B.obj) [GrpObj G] [ModObj G Z] :
    Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)) :=
  (presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).obj
    (groupSpaceOrbitPresheaf G Z ⋙ uliftFunctor.{u + 1, u})

/-- The canonical quotient map, the orbit projection followed by sheafification's unit.
Source: Stacks, Tag 06PH
(blueprint: lem-sfb-free-flat-group-space-quotient). -/
def groupSpaceQuotientMap {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G Z : Over B.obj) [GrpObj G] [ModObj G Z] :
    Z.left.obj ⋙ uliftFunctor.{u + 1, u} ⟶ (groupSpaceQuotient G Z).obj :=
  Functor.whiskerRight (coequalizer.π (ModObj.smul (M := G) (X := Z)).left.hom
      (CartesianMonoidalCategory.snd G Z).left.hom) uliftFunctor.{u + 1, u} ≫
    toSheafify (Scheme.fppfTopology.over S)
      (groupSpaceOrbitPresheaf G Z ⋙ uliftFunctor.{u + 1, u})

/-- A free flat locally finitely presented group-space action has an algebraic-space
quotient, with surjective flat locally finitely presented projection and the fppf torsor
property. The last cartesian square identifies `(g,z) ↦ (gz,z)` with the kernel pair.
Source: Stacks, bootstrap.tex, Tag 06PH, lemma-quotient-free-action
(blueprint: lem-sfb-free-flat-group-space-quotient).

Proof:
1. Regard spaces as discrete fppf stacks using def-trf-algebraic-space,
def-trf-scheme-algebraic-space, lem-sfb-fibred-groupoid-representable-smooth-calculus
and def-sfb-algebraic-moduli-stack. The chart tests agree with arbitrary scheme base
change by lem-sfb-space-local-properties-chart-test and
lem-sfb-representable-fppf-etale-open-descent. Use
lem-sfb-stack-chartwise-smooth-etale-calculus for base change and composition.
2. Form R = G times_B Z with source z and target gz. The action laws give the action
groupoid; freeness makes its arrow map a monomorphism. The orbit presheaf maps to B,
so def-weil-pbc-sheafification extends that map uniquely to the quotient sheaf.
3. By lem-weil-pbc-site-sheafification-sections-local, equal quotient sections are locally
in the same orbit. Freeness makes the relating group elements unique, so the sheaf G
glues them, proving the kernel-pair identity. The same lemma gives local lifts to Z.
4. On every scheme test T to the quotient, local lifts identify the pullback of Z with
T_i times_B G. These are algebraic spaces by lem-trf-space-fibre-products-etale-covers.
Their etale charts have a coproduct in the working universe by def-weil-size-convention
and lem-weil-pbc-scheme-coproduct-family. Apply lem-sfb-fppf-local-algebraic-space.
5. These local projections are flat and locally finitely presented by base change,
and surjective by their identity sections. Descend the two local properties using
lem-sfb-representable-fppf-etale-open-descent and the coproduct covering. Field-valued
points lift after a field extension, giving surjectivity on point classes.
6. Apply lem-sfb-fppf-space-atlas-bootstrap to the quotient sheaf and Z. Steps 4 and 5
verify every scheme-test hypothesis, hence the quotient is algebraic. The same tests
give the properties of its quotient map, and Step 3 gives both torsor clauses. -/
theorem free_flat_groupSpace_quotient {S : Scheme.{u}} (B : AlgebraicSpace S)
    (G Z : Over B.obj) [GrpObj G] [ModObj G Z]
    (hG : IsAlgebraicSpace G.left) (hZ : IsAlgebraicSpace Z.left)
    (hfree : ∀ T : Over S, Function.Injective
      ((prod.lift (ModObj.smul (M := G) (X := Z)).left.hom
        (CartesianMonoidalCategory.snd G Z).left.hom).app (op T)))
    (hflat : MapIsFlat (ObjectProperty.homMk G.hom :
      (⟨G.left, hG⟩ : AlgebraicSpace S) ⟶ B))
    (hlfp : MapIsLocallyOfFinitePresentation (ObjectProperty.homMk G.hom :
      (⟨G.left, hG⟩ : AlgebraicSpace S) ⟶ B)) :
    ∃ (F : AlgebraicSpace S) (q : Z.left ⟶ F.obj)
      (e : F.obj.obj ⋙ uliftFunctor.{u + 1, u} ≅ (groupSpaceQuotient G Z).obj),
      Functor.whiskerRight q.hom uliftFunctor.{u + 1, u} ≫ e.hom = groupSpaceQuotientMap G Z ∧
      MapIsFlat (ObjectProperty.homMk q : (⟨Z.left, hZ⟩ : AlgebraicSpace S) ⟶ F) ∧
      MapIsLocallyOfFinitePresentation
        (ObjectProperty.homMk q : (⟨Z.left, hZ⟩ : AlgebraicSpace S) ⟶ F) ∧
      IsJointlySurjective (fun _ : Unit ↦ q.hom) ∧
      (∀ (T : Over S) (x : F.obj.obj.obj (op T)),
        ∃ R : Sieve T, R ∈ (Scheme.fppfTopology.over S) T ∧
          ∀ (U : Over S) (f : U ⟶ T), R f →
            ∃ z : Z.left.obj.obj (op U), q.hom.app (op U) z = F.obj.obj.map f.op x) ∧
      IsPullback (ModObj.smul (M := G) (X := Z)).left
        (CartesianMonoidalCategory.snd G Z).left q q := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
