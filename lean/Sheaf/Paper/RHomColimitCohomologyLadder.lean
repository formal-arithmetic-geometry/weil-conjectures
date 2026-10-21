/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N8
-/
module

public import Sheaf.Paper.DerivedInternalHomFilteredColimitData
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import Sheaf.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
import WeilConjectures.Algebra.Homology.HomComplex
import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor

/-! # The filtered-target internal-Hom cohomology ladder

Source: Stacks Project, Tags 03DB, 08JC and 05RS
(blueprint: lem-sfb-rhom-colimit-cohomology-ladder).

The arrows below use the recorded internal Hom and its signed source shift.
The comparison is the actual image of the strict model's colimit cocone map.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v r w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

namespace WeilConjectures.SfbHomFilteredColimit

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max u v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}]
  (R : Sheaf J CommRingCat.{max u v r})

/-- The strict termwise-colimit Hom model, functorial contravariantly in its source.
Source: Stacks 03DB, 08J7 (blueprint: lem-sfb-rhom-colimit-cohomology-ladder). -/
def ladderModel {I : Type (max u v r)} [SmallCategory I]
    (N : I ⥤ CochainComplex (Modules.{u, v, r} J R) ℤ) :
    (CochainComplex (Modules.{u, v, r} J R) ℤ)ᵒᵖ ⥤
      CochainComplex (Modules.{u, v, r} J R) ℤ :=
  homComplexFunctor.{u, v, max u v r, max u v r} (R := R) ⋙
    (Functor.whiskeringLeft I _ _).obj (N ⋙ coefficientHomResolution.{r, u, v} J R) ⋙ colim

variable [HasDerivedCategory.{w} (Modules.{u, v, r} J R)]

/-- The fixed-target derived internal Hom, using the recorded bifunctor.
Source: Stacks 08J7 (blueprint: lem-sfb-rhom-colimit-cohomology-ladder). -/
abbrev ladderTarget (M : DerivedCategory (Modules.{u, v, r} J R)) :=
  (Functor.flip (Functor.curry.obj (derivedInternalHomOfUniverses.{u, v, r, w} J R))).obj M

/-- Precomposition, followed by degree-q cohomology, natural in the target.
Source: Stacks 08JC (blueprint: lem-sfb-rhom-colimit-cohomology-ladder). -/
def ladderPrecomp {A B : DerivedCategory (Modules.{u, v, r} J R)} (f : A ⟶ B) (q : ℤ) :
    RingedHomUniverses.hom.{u, v, r, w} J R B ⋙
        DerivedCategory.homologyFunctor (Modules.{u, v, r} J R) q ⟶
      RingedHomUniverses.hom.{u, v, r, w} J R A ⋙
        DerivedCategory.homologyFunctor (Modules.{u, v, r} J R) q :=
  Functor.whiskerRight ((Functor.curry.obj
    (derivedInternalHomOfUniverses.{u, v, r, w} J R)).map f.op) _

/-- The connecting arrow uses the signed source shift, not an arbitrary boundary.
In Hom degree n the inverse source reindexing has the factor (-1)^n.
Source: Stacks 0A8X, 08JC (blueprint: lem-sfb-rhom-colimit-cohomology-ladder). -/
def ladderBoundary (T : Triangle (DerivedCategory (Modules.{u, v, r} J R))) (q : ℤ) :
    RingedHomUniverses.hom.{u, v, r, w} J R T.obj₁ ⋙
        DerivedCategory.homologyFunctor (Modules.{u, v, r} J R) (q - 1) ⟶
      RingedHomUniverses.hom.{u, v, r, w} J R T.obj₃ ⋙
        DerivedCategory.homologyFunctor (Modules.{u, v, r} J R) q :=
  Functor.whiskerLeft (RingedHomUniverses.hom.{u, v, r, w} J R T.obj₁)
      ((DerivedCategory.homologyFunctor (Modules.{u, v, r} J R) 0).shiftIso
        (-1) q (q - 1) (by omega)).inv ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (RingedHomUniverses.sourceShift.{u, v, r, w} J R T.obj₁ 1).hom _ ≫
    ladderPrecomp.{u, v, r, w} J R T.mor₃ q

variable {I : Type (max u v r)} [SmallCategory I]
  (N : I ⥤ CochainComplex (Modules.{u, v, r} J R) ℤ)

/-- The diagram of degree-q derived internal-Hom cohomology sheaves.
Source: Stacks 08JC (blueprint: lem-sfb-rhom-colimit-cohomology-ladder). -/
abbrev ladderDiagram (A : DerivedCategory (Modules.{u, v, r} J R)) (q : ℤ) :=
  N ⋙ DerivedCategory.Q ⋙ RingedHomUniverses.hom.{u, v, r, w} J R A ⋙
    DerivedCategory.homologyFunctor (Modules.{u, v, r} J R) q

/-- The colimit-row precomposition arrow.
Source: Stacks 03DB, 08JC (blueprint: lem-sfb-rhom-colimit-cohomology-ladder). -/
def ladderColimPrecomp {A B : DerivedCategory (Modules.{u, v, r} J R)}
    (f : A ⟶ B) (q : ℤ) :
    colimit (ladderDiagram.{u, v, r, w} J R N B q) ⟶
      colimit (ladderDiagram.{u, v, r, w} J R N A q) :=
  colim.map (Functor.whiskerLeft (N ⋙ DerivedCategory.Q) (ladderPrecomp.{u, v, r, w} J R f q))

/-- The colimit of the signed connecting arrows.
Source: Stacks 03DB, 08JC (blueprint: lem-sfb-rhom-colimit-cohomology-ladder). -/
def ladderColimBoundary (T : Triangle (DerivedCategory (Modules.{u, v, r} J R)))
    (q : ℤ) : colimit (ladderDiagram.{u, v, r, w} J R N T.obj₁ (q - 1)) ⟶
      colimit (ladderDiagram.{u, v, r, w} J R N T.obj₃ q) :=
  colim.map (Functor.whiskerLeft (N ⋙ DerivedCategory.Q) (ladderBoundary.{u, v, r, w} J R T q))

/-- The vertical map induced by the actual target cocone, on cohomology sheaves.
Source: Stacks 03DB, 08JC (blueprint: lem-sfb-rhom-colimit-cohomology-ladder). -/
def ladderVertical (A : DerivedCategory (Modules.{u, v, r} J R)) (q : ℤ) :
    colimit (ladderDiagram.{u, v, r, w} J R N A q) ⟶
      ((RingedHomUniverses.hom.{u, v, r, w} J R A ⋙
        DerivedCategory.homologyFunctor (Modules.{u, v, r} J R) q).obj
          (DerivedCategory.Q.obj (colimit N))) :=
  colimit.desc _ ((RingedHomUniverses.hom.{u, v, r, w} J R A ⋙
    DerivedCategory.homologyFunctor (Modules.{u, v, r} J R) q).mapCocone
      (DerivedCategory.Q.mapCocone (colimit.cocone N)))

/-- The image of the canonical strict Hom-complex cocone map, with its fixed
localization comparison to the derived internal Hom at the target colimit.
Source: Stacks 03DB, 08J7 (blueprint: lem-sfb-rhom-colimit-cohomology-ladder). -/
def ladderStrictAlpha (P : CochainComplex (Modules.{u, v, r} J R) ℤ) :
    DerivedCategory.Q.obj ((ladderModel.{u, v, r} J R N).obj (op P)) ⟶
      (ladderTarget.{u, v, r, w} J R (DerivedCategory.Q.obj (colimit N))).obj
        (op (DerivedCategory.Q.obj P)) :=
  DerivedCategory.Q.map
      (colimit.desc (N ⋙ homFixed.{u, v, r} J R P)
        ((homFixed.{u, v, r} J R P).mapCocone (colimit.cocone N))) ≫
    (coefficientHomResolutionIso.{r, u, v, w} J R P (colimit N)).inv

/-- Cohomology commutes naturally with every filtered termwise complex colimit.
The preservation predicate specifies the canonical comparison isomorphism, including
its equation on every colimit leg.
Source: Stacks 03DB (blueprint: lem-sfb-rhom-colimit-cohomology-ladder).
Proof: filtered colimits are exact in module sheaves. Apply this first to the
kernel-image sequences of the differential, and then to boundaries inside cycles.
This identifies cycles, boundaries and their quotient after colimiting. Each map
is induced by a kernel inclusion or quotient, so the identification is natural
in complex diagrams and agrees with cohomology of every colimit injection. -/
theorem ladder_filtered_cohomology [IsFiltered I] (q : ℤ) :
    PreservesColimitsOfShape I
      (HomologicalComplex.homologyFunctor (Modules.{u, v, r} J R) (.up ℤ) q) := by
  sorry

/-- Filtered termwise colimits preserve quasi-isomorphisms and common lower bounds.
Source: Stacks 03DB (blueprint: lem-sfb-rhom-colimit-cohomology-ladder).
Proof: apply ladder_filtered_cohomology in each degree. A colimit of a natural
isomorphism is an isomorphism. A diagram of zero cohomology objects has zero
colimit, so a lower bound shared by all stages survives the colimit. -/
theorem ladder_filtered_consequences [IsFiltered I] :
    (∀ (K L : I ⥤ CochainComplex (Modules.{u, v, r} J R) ℤ) (f : K ⟶ L),
      (∀ i : I, QuasiIso (f.app i)) → QuasiIso (colim.map f)) ∧
    (∀ (K : I ⥤ CochainComplex (Modules.{u, v, r} J R) ℤ) (a : ℤ),
      (∀ (i : I) (q : ℤ), q < a → IsZero
        ((HomologicalComplex.homologyFunctor (Modules.{u, v, r} J R) (.up ℤ) q).obj
          (K.obj i))) →
      ∀ q : ℤ, q < a → IsZero
        ((HomologicalComplex.homologyFunctor (Modules.{u, v, r} J R) (.up ℤ) q).obj
          (colimit K))) := by
  sorry

/-- The canonical model cocone descends in the source, and its cohomology is the
vertical colimit map under the canonical cohomology-colimit identification.
The witnesses F and e present the localization of ladderModel; alpha is fixed by
its displayed equation on every complex, and beta is fixed on every colimit leg.
Thus this asserts a normalized canonical comparison, not a chosen unrelated map.
Source: Stacks 03DB, 0A95 and 08JC
(blueprint: lem-sfb-rhom-colimit-cohomology-ladder).
Proof:
1. The preceding filtered-colimit results identify cohomology of a termwise
   colimit with the colimit of cohomology, naturally on its injections.
2. Source quasi-isomorphisms induce quasi-isomorphisms into each K-injective
   target (lem-pur-rhom-well-defined-universes). The filtered colimit does too.
   Localize this contravariant functor to obtain F and its factorization e.
3. Precomposition commutes with target postcomposition on every Hom component.
   Therefore the canonical cocone map is a natural transformation of the
   unlocalized functors. Localize it to obtain alpha. Naturality for inverted
   source quasi-isomorphisms follows by composing with their inverse maps.
4. Apply cohomology to the strict colimit legs and the fixed resolution
   comparison. The resulting cocone gives beta, an isomorphism by step 1.
   Testing the equality with H(alpha) on each colimit injection proves it.
   No colimit of K-injectives is asserted to be K-injective. -/
theorem ladder_comparison [IsFiltered I] :
    ∃ (F : (DerivedCategory (Modules.{u, v, r} J R))ᵒᵖ ⥤
        DerivedCategory (Modules.{u, v, r} J R))
      (e : DerivedCategory.Q.op ⋙ F ≅ ladderModel.{u, v, r} J R N ⋙ DerivedCategory.Q)
      (alpha : F ⟶ ladderTarget.{u, v, r, w} J R (DerivedCategory.Q.obj (colimit N))),
      (∀ P : CochainComplex (Modules.{u, v, r} J R) ℤ,
        e.hom.app (op P) ≫ ladderStrictAlpha.{u, v, r, w} J R N P =
          alpha.app (op (DerivedCategory.Q.obj P))) ∧
      (∀ (P : CochainComplex (Modules.{u, v, r} J R) ℤ) (q : ℤ),
        ∃ beta : colimit (ladderDiagram.{u, v, r, w} J R N (DerivedCategory.Q.obj P) q) ≅
          (DerivedCategory.homologyFunctor (Modules.{u, v, r} J R) q).obj
            (DerivedCategory.Q.obj ((ladderModel.{u, v, r} J R N).obj (op P))),
          (∀ i : I,
            colimit.ι (ladderDiagram.{u, v, r, w} J R N (DerivedCategory.Q.obj P) q) i ≫
                beta.hom =
              (DerivedCategory.homologyFunctor (Modules.{u, v, r} J R) q).map
                ((coefficientHomResolutionIso.{r, u, v, w} J R P (N.obj i)).hom ≫
                  DerivedCategory.Q.map (colimit.ι (N ⋙ homFixed.{u, v, r} J R P) i))) ∧
          beta.hom ≫
              (DerivedCategory.homologyFunctor (Modules.{u, v, r} J R) q).map
                (e.inv.app (op P) ≫ alpha.app (op (DerivedCategory.Q.obj P))) =
            ladderVertical.{u, v, r, w} J R N (DerivedCategory.Q.obj P) q) := by
  sorry

/-- Both cohomology rows are exact and all squares commute, including the signed
connecting square. The three exact spots in every degree give the entire infinite
ladder, including the preceding arrow in degree q-1 and the following one in q+1.
Source: Stacks 03DB, 08JC and 05RS
(blueprint: lem-sfb-rhom-colimit-cohomology-ladder).
Proof:
1. Form termwise colimits of complexes degreewise. The cocone equations show
   that their differential squares to zero and give the complex colimit property.
2. Exact filtered colimits preserve cycles, boundaries and their quotient by
   applying exactness successively to the kernel-image short exact sequences.
3. Hence filtered colimits preserve quasi-isomorphisms and a common lower bound.
4. Use the fixed functorial K-injective targets. Precomposition and target
   postcomposition commute; quasi-isomorphism invariance lets the Hom functors
   and their cocone comparison descend to every derived source morphism.
5. The signed source shift reindexes components by p to p-1 and multiplies
   Hom degree n by (-1)^n. Substitution in the Hom differential verifies it is
   a chain isomorphism. This formula is independent of the target, so commutes
   with every target transition and the colimit cocone. No product is commuted
   with a colimit here.
6. Internal Hom sends the source triangle contravariantly to a distinguished
   triangle (lem-weil-pbc-ringed-internal-hom-exact-restriction). Derived
   cohomology gives its exact sequence (lem-sf-derived-homology-long-exact),
   with the boundary normalized by the signed source shift of step 5.
7. Naturality of precomposition gives the ordinary squares. Naturality of the
   signed shift gives the connecting square too, including for inverted source
   quasi-isomorphisms (lem-weil-pbc-derived-cohomology-ladder).
8. Exact filtered colimits give exactness at each spot of the first row.
   Each square commutes after composition with every colimit injection, hence
   commutes by the universal property. ladder_comparison identifies these
   vertical arrows with H^q(alpha). Vary q to obtain the complete ladder.
There is no boundedness, continuity or constructibility hypothesis. -/
theorem rhom_colimit_cohomology_ladder [IsFiltered I]
    (T : Triangle (DerivedCategory (Modules.{u, v, r} J R)))
    (hT : T ∈ distTriang (DerivedCategory (Modules.{u, v, r} J R))) (q : ℤ) :
    (∃ h :
      ladderColimBoundary.{u, v, r, w} J R N T q ≫
        ladderColimPrecomp.{u, v, r, w} J R N T.mor₂ q = 0,
      (ShortComplex.mk _ _ h).Exact) ∧
    (∃ h :
      ladderColimPrecomp.{u, v, r, w} J R N T.mor₂ q ≫
        ladderColimPrecomp.{u, v, r, w} J R N T.mor₁ q = 0,
      (ShortComplex.mk _ _ h).Exact) ∧
    (∃ h :
      ladderColimPrecomp.{u, v, r, w} J R N T.mor₁ (q - 1) ≫
        ladderColimBoundary.{u, v, r, w} J R N T q = 0,
      (ShortComplex.mk _ _ h).Exact) ∧
    (∃ h :
      (ladderBoundary.{u, v, r, w} J R T q).app (DerivedCategory.Q.obj (colimit N)) ≫
        (ladderPrecomp.{u, v, r, w} J R T.mor₂ q).app (DerivedCategory.Q.obj (colimit N)) = 0,
      (ShortComplex.mk _ _ h).Exact) ∧
    (∃ h :
      (ladderPrecomp.{u, v, r, w} J R T.mor₂ q).app (DerivedCategory.Q.obj (colimit N)) ≫
        (ladderPrecomp.{u, v, r, w} J R T.mor₁ q).app (DerivedCategory.Q.obj (colimit N)) = 0,
      (ShortComplex.mk _ _ h).Exact) ∧
    (∃ h :
      (ladderPrecomp.{u, v, r, w} J R T.mor₁ (q - 1)).app
      (DerivedCategory.Q.obj (colimit N)) ≫
        (ladderBoundary.{u, v, r, w} J R T q).app (DerivedCategory.Q.obj (colimit N)) = 0,
      (ShortComplex.mk _ _ h).Exact) ∧
    (ladderColimPrecomp.{u, v, r, w} J R N T.mor₂ q ≫
        ladderVertical.{u, v, r, w} J R N T.obj₂ q =
      ladderVertical.{u, v, r, w} J R N T.obj₃ q ≫
        (ladderPrecomp.{u, v, r, w} J R T.mor₂ q).app
          (DerivedCategory.Q.obj (colimit N))) ∧
    (ladderColimPrecomp.{u, v, r, w} J R N T.mor₁ q ≫
        ladderVertical.{u, v, r, w} J R N T.obj₁ q =
      ladderVertical.{u, v, r, w} J R N T.obj₂ q ≫
        (ladderPrecomp.{u, v, r, w} J R T.mor₁ q).app
          (DerivedCategory.Q.obj (colimit N))) ∧
    (ladderColimBoundary.{u, v, r, w} J R N T q ≫
        ladderVertical.{u, v, r, w} J R N T.obj₃ q =
      ladderVertical.{u, v, r, w} J R N T.obj₁ (q - 1) ≫
        (ladderBoundary.{u, v, r, w} J R T q).app
          (DerivedCategory.Q.obj (colimit N))) := by
  sorry

end WeilConjectures.SfbHomFilteredColimit
