/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q106
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import WeilConjectures.CategoryTheory.FinitePrecoverage
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.Sites.CohomologyRightDerivedSections
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.CategoryTheory.WithTerminal.Lemmas
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Sheaf.CategoryTheory.CohomologyColimitFiniteCoverSites
import WeilConjectures.CategoryTheory.ColimitSites
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import Sheaf.Algebra.Homology.FunctorialBoundedInjectiveResolution
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import WeilConjectures.AlgebraicGeometry.ObjectCohomologyPresheafResolution

/-! # Derived presheaf continuity on a finite-cover site

Source: Stacks Project, Cohomology on Sites, Tag 09YP and Section 01FT;
Derived Categories, Tags 0141 and 05TI.
(blueprint: lem-sfb-finite-cover-derived-presheaf-continuity).

The source is the extension by zero of the termwise colimit of nonnegative
presheaf resolution complexes, localized in the ordinary derived category.
The cohomology presheaf is modeled by the right derived functor of inclusion:
its value at W is R^q Gamma(W,-), as in Section 01FT. In particular the canonical
resolution identifications below are the actual isoRightDerivedObj maps.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe w u v a

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.FiniteCoverDerivedPresheaf

/-- A strictly compatible nonnegative resolution of a coefficient cocone, including its
vertex. All data are supplied, and all augmentation squares are imposed.
Source: Stacks 0141 and 09YP, compatible injective resolutions
(blueprint: lem-sfb-finite-cover-derived-presheaf-continuity). -/
structure ResolutionCocone {A : Type a} [Category.{v} A] [Abelian A]
    {I : Type u} [SmallCategory I] (F : I ⥤ A) (c : Cocone F) where
  /-- The diagram of resolution complexes. -/
  K : I ⥤ CochainComplex A ℕ
  /-- The natural augmentations. -/
  s : F ⋙ CochainComplex.single₀ A ⟶ K
  /-- Every term is injective. -/
  injective : ∀ (i : I) (n : ℕ), Injective ((K.obj i).X n)
  /-- Every augmentation is a quasi-isomorphism. -/
  quasiIso : ∀ i : I, QuasiIso (s.app i)
  /-- The resolution of the coefficient colimit. -/
  vertex : InjectiveResolution c.pt
  /-- The lifted coefficient coprojections. -/
  legs : K ⟶ (Functor.const I).obj vertex.cocomplex
  /-- The lifted legs lie over the original coprojections. -/
  comm : ∀ i : I, s.app i ≫ legs.app i =
    (CochainComplex.single₀ A).map (c.ι.app i) ≫ vertex.ι

/-- The resolution of an individual coefficient, with its original augmentation.
Source: Stacks 01FT (blueprint: lem-sfb-finite-cover-derived-presheaf-continuity). -/
def ResolutionCocone.at {A : Type a} [Category.{v} A] [Abelian A]
    {I : Type u} [SmallCategory I] {F : I ⥤ A} {c : Cocone F}
    (R : ResolutionCocone F c) (i : I) : InjectiveResolution (F.obj i) where
  cocomplex := R.K.obj i
  injective := R.injective i
  ι := R.s.app i
  quasiIso := R.quasiIso i

/-- The actual chain cocone of the compatible resolutions.
Source: Stacks 0141 (blueprint: lem-sfb-finite-cover-derived-presheaf-continuity). -/
def ResolutionCocone.cocone {A : Type a} [Category.{v} A] [Abelian A]
    {I : Type u} [SmallCategory I] {F : I ⥤ A} {c : Cocone F}
    (R : ResolutionCocone F c) : Cocone R.K :=
  ⟨R.vertex.cocomplex, R.legs⟩

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

/-- Inclusion of sheaves applied termwise to nonnegative complexes.
Source: Stacks 01FT (blueprint: lem-sfb-finite-cover-derived-presheaf-continuity). -/
def onComplexes :
    CochainComplex (Sheaf J AddCommGrpCat.{u}) ℕ ⥤
      CochainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ℕ :=
  (sheafToPresheaf J AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ)

/-- The comparison induced by the original cocone's lifted coprojections. Extension
by zero makes the nonnegative termwise colimit an integer-indexed complex.
Source: Stacks 09YP and 01FT, the coprojection-induced comparison
(blueprint: lem-sfb-finite-cover-derived-presheaf-continuity). -/
def comparison [HasDerivedCategory.{w} (Cᵒᵖ ⥤ AddCommGrpCat.{u})]
    {I : Type u} [SmallCategory I]
    {K : I ⥤ CochainComplex (Sheaf J AddCommGrpCat.{u}) ℕ} (c : Cocone K) :
    DerivedCategory.Q.obj
        ((colimit (K ⋙ onComplexes J)).extend ComplexShape.embeddingUpNat) ⟶
      DerivedCategory.Q.obj
        (((onComplexes J).obj c.pt).extend ComplexShape.embeddingUpNat) :=
  DerivedCategory.Q.map
    ((ComplexShape.embeddingUpNat.extendFunctor (Cᵒᵖ ⥤ AddCommGrpCat.{u})).map
      (colimit.desc (K ⋙ onComplexes J) ((onComplexes J).mapCocone c)))

/-- Extension of a diagram by zero at a newly adjoined strict initial object.
Source: Stacks 09YP, constant-site specialization
(blueprint: lem-sfb-finite-cover-derived-presheaf-continuity). -/
def zeroExtension {A : Type a} [Category.{v} A] [Abelian A]
    {I : Type u} [SmallCategory I] (F : I ⥤ A) : WithInitial I ⥤ A :=
  WithInitial.lift (Z := ⊥_ A) F (fun _ ↦ 0) (by intros; simp)

/-- Extend the original cocone with its unique leg from zero. The old legs are
literally the original coprojections, with no choice of a colimit isomorphism.
Source: Stacks 09YP (blueprint: lem-sfb-finite-cover-derived-presheaf-continuity). -/
def zeroExtensionCocone {A : Type a} [Category.{v} A] [Abelian A]
    {I : Type u} [SmallCategory I] {F : I ⥤ A} (c : Cocone F) :
    Cocone (zeroExtension F) where
  pt := c.pt
  ι :=
    { app := fun i ↦ match i with
        | .of i => c.ι.app i
        | .star => 0
      naturality := by
        intro i j f
        cases i <;> cases j
        · simp [zeroExtension, WithInitial.down]
        · exact f.elim
        · simp [zeroExtension]
        · simp [zeroExtension] }

/-- The identity cocone on the constant system of underlying site categories. The
covering precoverage at every stage and at this vertex is the very same J.
Source: Stacks 09YP, Sites 09YL and 0A35
(blueprint: lem-sfb-finite-cover-derived-presheaf-continuity). -/
def constantSiteCocone (I : Type u) [SmallCategory I] :
    Cocone ((Functor.const (WithInitial I)).obj (Cat.of C)) :=
  ⟨Cat.of C, 𝟙 _⟩

/-- Canonical resolution evaluation after a supplied natural identification of Ext
cohomology with derived sections. The identification exists by the recorded theorem
nonempty_cohomologyPresheafFunctor_eval_iso_rightDerived; no arbitrary choice is made.
Source: Stacks 01FT (blueprint: lem-sfb-finite-cover-derived-presheaf-continuity). -/
def resolutionSectionsIso [HasSheafify J AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf J AddCommGrpCat.{u})] (W : C) (q : ℕ)
    (e : Sheaf.cohomologyPresheafFunctor J q ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op W) ≅
      (sheafToPresheaf J AddCommGrpCat.{u} ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op W)).rightDerived q)
    {A : Sheaf J AddCommGrpCat.{u}} (R : InjectiveResolution A) :
    Sheaf.H' A q W ≅
      ((((onComplexes J).obj R.cocomplex).homology q).obj (op W)) :=
  e.app A ≪≫ R.isoRightDerivedObj
      (sheafToPresheaf J AddCommGrpCat.{u} ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op W)) q ≪≫
    ((((onComplexes J).obj R.cocomplex).sc q).mapHomologyIso
      ((evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op W)))

variable (P : Precoverage C)
  [HasSheafify P.toGrothendieck AddCommGrpCat.{u}]

/-- Strict compatible resolutions of the whole diagram and its colimit exist.
Source: Stacks 0141 and 09YP
(blueprint: lem-sfb-finite-cover-derived-presheaf-continuity).

Proof (node step 3): abelian sheaves on a small site are Grothendieck abelian by
lem-weil-pbc-sheaf-tensor-closed and def-weil-pbc-sheafification. Use functorial
injective embeddings and the lower-bound-preserving injective resolution functor
of lem-weil-pbc-functorial-bounded-injective-resolution on the degree-zero diagram
and its actual cocone. Naturality gives all augmentation squares. -/
theorem resolutions_exist
    (I : Type u) [SmallCategory I]
    (F : I ⥤ Sheaf P.toGrothendieck AddCommGrpCat.{u}) (c : Cocone F) :
    Nonempty (ResolutionCocone F c) := by
  sorry

/-- Derived presheaf inclusion commutes with filtered colimits on a finite-cover site,
for every compatible choice of resolutions and every actual colimit cocone.
Source: Stacks 09YP, Section 01FT, and Derived Categories 05TI
(blueprint: lem-sfb-finite-cover-derived-presheaf-continuity).

Proof, following all six steps of the node:
1. Adjoin a strict initial zero coefficient. Finite diagrams still have cocones, and
   cocones on the zero extension are exactly cocones on the original diagram.
2. The constant identity system of sites has colimit the original site. The arrow
   category at the new initial object is equivalent to the augmented index itself.
   Its coefficient transition maps are precisely those of the original diagram.
   Thus lem-weil-pbc-cohomology-colimit-of-sites gives object cohomology continuity,
   with every leg equal to cohomology of the original coefficient coprojection.
3. The functorial resolutions used by resolutions_exist compute R inclusion by
   lem-weil-pbc-right-derived-plus-injective, also on the actual coprojections.
4. Presheaf colimits, kernels, and cokernels are pointwise. Filtered abelian-group
   colimits are exact (lem-weil-pbc-filtered-colimit-abelian-groups-exact), so
   lem-weil-pbc-exact-functor-complex-cohomology identifies the homology of a
   termwise colimit with the colimit of the homologies, with their original legs.
5. The resolution formula of def-weil-pbc-sites-and-cohomology, also in
   lem-weil-pbc-object-cohomology-presheaf-resolution, and
   lem-weil-pbc-derived-functor-map-via-lift identify the map on each object with
   the map in step 2. Negative homology vanishes. Thus the comparison is a
   quasi-isomorphism, which localization inverts.
6. For any other strict compatible resolution, compare it by the natural zigzag
   J(F[0]) -> J(K) <- K, including the vertex and every leg. These are presheaf
   quasi-isomorphisms because they compare bounded-below injective complexes.
   Exact filtered colimits preserve the zigzag. This proves the assertion for all
   supplied resolutions. Functoriality gives coefficient naturality; all maps are
   presheaf maps, hence commute with restriction in W. No dimension bound is used. -/
theorem comparison_isIso
    (hP : P.IsSiteForCoverings)
    [P.IsStableUnderFiniteComposition] [P.IsStableUnderFiniteBaseChange]
    (hfinite : ∀ (W : C) (S : Presieve W), S ∈ P W → Finite S.uncurry)
    [HasDerivedCategory.{w} (Cᵒᵖ ⥤ AddCommGrpCat.{u})]
    (I : Type u) [SmallCategory I] [IsFiltered I]
    (F : I ⥤ Sheaf P.toGrothendieck AddCommGrpCat.{u})
    (c : Cocone F) (hc : IsColimit c) (R : ResolutionCocone F c) :
    IsIso (comparison P.toGrothendieck R.cocone) := by
  sorry

/-- Canonical resolution identifications, their precise colimit-leg normalization, and
cohomological continuity as a presheaf (therefore simultaneously at every W).
The isomorphism e is pinned to isoRightDerivedObj at every coefficient.
Source: Stacks 01FT and 09YP
(blueprint: lem-sfb-finite-cover-derived-presheaf-continuity).

Proof (node steps 2, 4, 5): rightDerived_map_eq applied to the lifts R.legs and the
augmentation equation identifies their homology maps with R^q inclusion of c.ι.
The same formula on every transition makes the displayed component isomorphisms
natural, defining e. Pointwise exactness of filtered colimits makes colimit.post
for homology invertible. Compare the two composites after each colimit leg:
isoRightDerivedObj_hom_naturality and the defining equation of colimit.desc give
the equality. Step 2 proves that the coefficient-cohomology cocone is colimiting.
Exact evaluation and extension by zero, together with homologyFunctorFactors for
Q, identify this equality with H^q(delta) evaluated at W. Restriction naturality
is already included because the equality and e are in the presheaf category. -/
theorem comparison_cohomology
    (hP : P.IsSiteForCoverings)
    [P.IsStableUnderFiniteComposition] [P.IsStableUnderFiniteBaseChange]
    (hfinite : ∀ (W : C) (S : Presieve W), S ∈ P W → Finite S.uncurry)
    (I : Type u) [SmallCategory I] [IsFiltered I]
    (F : I ⥤ Sheaf P.toGrothendieck AddCommGrpCat.{u})
    (c : Cocone F) (hc : IsColimit c) (R : ResolutionCocone F c) (q : ℕ) :
    ∃ e : F ⋙ (sheafToPresheaf P.toGrothendieck AddCommGrpCat.{u}).rightDerived q ≅
        (R.K ⋙ onComplexes P.toGrothendieck) ⋙
          HomologicalComplex.homologyFunctor (Cᵒᵖ ⥤ AddCommGrpCat.{u}) (.up ℕ) q,
      (∀ i : I, e.hom.app i =
        ((R.at i).isoRightDerivedObj
          (sheafToPresheaf P.toGrothendieck AddCommGrpCat.{u}) q).hom) ∧
      IsIso (colimit.post (R.K ⋙ onComplexes P.toGrothendieck)
        (HomologicalComplex.homologyFunctor (Cᵒᵖ ⥤ AddCommGrpCat.{u}) (.up ℕ) q)) ∧
      Nonempty (IsColimit
        ((sheafToPresheaf P.toGrothendieck AddCommGrpCat.{u}).rightDerived q
          |>.mapCocone c)) ∧
      colimit.post (R.K ⋙ onComplexes P.toGrothendieck)
          (HomologicalComplex.homologyFunctor (Cᵒᵖ ⥤ AddCommGrpCat.{u}) (.up ℕ) q) ≫
        (HomologicalComplex.homologyFunctor (Cᵒᵖ ⥤ AddCommGrpCat.{u}) (.up ℕ) q).map
          (colimit.desc (R.K ⋙ onComplexes P.toGrothendieck)
            ((onComplexes P.toGrothendieck).mapCocone R.cocone)) =
        colimMap e.inv ≫
          colimit.desc
            (F ⋙ (sheafToPresheaf P.toGrothendieck AddCommGrpCat.{u}).rightDerived q)
            ((sheafToPresheaf P.toGrothendieck AddCommGrpCat.{u}).rightDerived q
              |>.mapCocone c) ≫
          (R.vertex.isoRightDerivedObj
            (sheafToPresheaf P.toGrothendieck AddCommGrpCat.{u}) q).hom := by
  sorry

/-- The canonical resolution identifications assemble before evaluation in the object
of the site, naturally in coefficients as well. Thus restrictions in W are included.
Source: Stacks 01FT; the free-representable resolution computation in
lem-weil-pbc-object-cohomology-presheaf-resolution
(blueprint: lem-sfb-finite-cover-derived-presheaf-continuity).

Proof (node steps 3, 5, 6): compute the right derived inclusion by an injective
resolution. The free-representable sheaf adjunction identifies its Hom complex
with sections of that resolution, hence Ext with its section homology. The
presheaf resolution theorem gives naturality in W, and the morphism-via-lift
formula gives coefficient naturality. Comparison maps are unique up to homotopy,
so the identifications are independent of resolutions and assemble to this
natural isomorphism. No claim of exactness of the underived inclusion is made. -/
theorem cohomology_presheaf_identification
    [HasExt.{u} (Sheaf P.toGrothendieck AddCommGrpCat.{u})] (q : ℕ) :
    Nonempty ((sheafToPresheaf P.toGrothendieck AddCommGrpCat.{u}).rightDerived q ≅
      Sheaf.cohomologyPresheafFunctor P.toGrothendieck q) := by
  sorry

/-- Evaluation of the cohomology comparison is precisely the map on H^q(W,-)
induced by the coefficient coprojections, under the resolution identifications. This
holds for every natural identification with derived sections, including the canonical
one, so no arbitrary comparison map or choice of an isomorphism is used.
Source: Stacks 01FT and 09YP
(blueprint: lem-sfb-finite-cover-derived-presheaf-continuity).

Proof (node steps 2, 4, 5): apply comparison_cohomology and exact evaluation at W.
The existing nonempty_cohomologyPresheafFunctor_eval_iso_rightDerived supplies
identifications; isoRightDerivedObj_hom_naturality and the naturality of e identify
every transition and cocone leg. The comparison on homology is therefore the
unique map out of the colimit with these legs. This proves the equation below.
The 09YP comparison proves IsIso of precisely that colimit.desc. Exact extension
by zero and homologyFunctorFactors identify the chain homology with H^q(delta).
The construction before evaluation is natural in W, and all coefficient maps
commute by naturality of e and isoRightDerivedObj. -/
theorem comparison_object_cohomology
    (hP : P.IsSiteForCoverings)
    [P.IsStableUnderFiniteComposition] [P.IsStableUnderFiniteBaseChange]
    (hfinite : ∀ (W : C) (S : Presieve W), S ∈ P W → Finite S.uncurry)
    [HasExt.{u} (Sheaf P.toGrothendieck AddCommGrpCat.{u})]
    (I : Type u) [SmallCategory I] [IsFiltered I]
    (F : I ⥤ Sheaf P.toGrothendieck AddCommGrpCat.{u})
    (c : Cocone F) (hc : IsColimit c) (R : ResolutionCocone F c) (W : C) (q : ℕ)
    (b : Sheaf.cohomologyPresheafFunctor P.toGrothendieck q ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op W) ≅
      (sheafToPresheaf P.toGrothendieck AddCommGrpCat.{u} ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op W)).rightDerived q) :
    ∃ e : F ⋙ (Sheaf.cohomologyPresheafFunctor P.toGrothendieck q ⋙
          (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op W)) ≅
        (R.K ⋙ onComplexes P.toGrothendieck) ⋙
          (HomologicalComplex.homologyFunctor (Cᵒᵖ ⥤ AddCommGrpCat.{u}) (.up ℕ) q ⋙
            (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op W)),
      (∀ i : I, e.hom.app i =
        (resolutionSectionsIso P.toGrothendieck W q b (R.at i)).hom) ∧
      IsIso (colimit.desc (F ⋙ (Sheaf.cohomologyPresheafFunctor P.toGrothendieck q ⋙
          (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op W)))
        ((Sheaf.cohomologyPresheafFunctor P.toGrothendieck q ⋙
          (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op W)).mapCocone c)) ∧
      colimit.post (R.K ⋙ onComplexes P.toGrothendieck)
          (HomologicalComplex.homologyFunctor (Cᵒᵖ ⥤ AddCommGrpCat.{u}) (.up ℕ) q ⋙
            (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op W)) ≫
        (HomologicalComplex.homologyFunctor (Cᵒᵖ ⥤ AddCommGrpCat.{u}) (.up ℕ) q ⋙
          (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op W)).map
        (colimit.desc (R.K ⋙ onComplexes P.toGrothendieck)
          ((onComplexes P.toGrothendieck).mapCocone R.cocone)) =
        colimMap e.inv ≫
        colimit.desc (F ⋙ (Sheaf.cohomologyPresheafFunctor P.toGrothendieck q ⋙
          (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op W)))
          ((Sheaf.cohomologyPresheafFunctor P.toGrothendieck q ⋙
            (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op W)).mapCocone c) ≫
        (resolutionSectionsIso P.toGrothendieck W q b R.vertex).hom := by
  sorry

/-- Both representatives have zero cohomology in all negative degrees.
Source: Stacks 01FT and 0141
(blueprint: lem-sfb-finite-cover-derived-presheaf-continuity).
Proof (node steps 4-6): the representatives are extensions by zero of nonnegative
complexes; their negative terms and hence their negative homologies are zero.
The localization homology comparison transfers this to their derived objects. -/
theorem negative_homology
    (I : Type u) [SmallCategory I]
    (K : I ⥤ CochainComplex (Sheaf P.toGrothendieck AddCommGrpCat.{u}) ℕ)
    (c : Cocone K) (n : ℤ) (hn : n < 0) :
    IsZero (((colimit (K ⋙ onComplexes P.toGrothendieck)).extend
      ComplexShape.embeddingUpNat).homology n) ∧
    IsZero ((((onComplexes P.toGrothendieck).obj c.pt).extend
      ComplexShape.embeddingUpNat).homology n) := by
  sorry

/-- Naturality of the derived comparison for every compatible chain lift of a map of
coefficient diagrams and its colimit map. No functorial choice of resolutions is required.
Source: Stacks 0141 and 09YP
(blueprint: lem-sfb-finite-cover-derived-presheaf-continuity).
Proof (node step 6): after each colimit coprojection the equation is functoriality
of inclusion and the given square h. The colimit universal property gives the
chain equality. Extension by zero and Q preserve it. For coefficient maps, their
augmentation squares identify the same maps by derived-functor-map-via-lift. -/
theorem comparison_naturality
    [HasDerivedCategory.{w} (Cᵒᵖ ⥤ AddCommGrpCat.{u})]
    {I : Type u} [SmallCategory I]
    {K L : I ⥤ CochainComplex (Sheaf P.toGrothendieck AddCommGrpCat.{u}) ℕ}
    (c : Cocone K) (d : Cocone L) (f : K ⟶ L) (g : c.pt ⟶ d.pt)
    (h : ∀ i : I, f.app i ≫ d.ι.app i = c.ι.app i ≫ g) :
    DerivedCategory.Q.map
        ((ComplexShape.embeddingUpNat.extendFunctor (Cᵒᵖ ⥤ AddCommGrpCat.{u})).map
          (colimMap (Functor.whiskerRight f (onComplexes P.toGrothendieck)))) ≫
        comparison P.toGrothendieck d =
      comparison P.toGrothendieck c ≫ DerivedCategory.Q.map
        ((ComplexShape.embeddingUpNat.extendFunctor (Cᵒᵖ ⥤ AddCommGrpCat.{u})).map
          ((onComplexes P.toGrothendieck).map g)) := by
  sorry

/-- The augmented constant-site specialization of 09YP, including the arrow index at
its new initial object. Its cohomology cocone is the original one extended by zero;
reindexing it along Under.forget gives exactly the 09YP arrow-indexed cocone.
Source: Stacks 09YP, Sites 09YL and 0A35
(blueprint: lem-sfb-finite-cover-derived-presheaf-continuity).

Proof (node steps 1-2): WithInitial is small and filtered. Every cocone on the zero
extension restricts to the original cocone, and its missing leg is uniquely zero,
so its colimit remains c.pt. A filtered category is connected: a cocone on the
constant identity site system is precisely one functor out of C, proving its
colimit is C; the covering precoverage is unchanged. Uniqueness of arrows out of
the adjoined initial object makes Under.forget an equivalence. Under this functor,
all coefficient transitions are F.map, and identity site pullback gives the
identity on cohomology. The cohomology cocone on the zero extension is therefore
colimiting by 09YP, with its actual coefficient coprojections. Reindexing along
the equivalence preserves that property and gives the exact arrow-index cocone. -/
theorem augmented_constant_site
    (hP : P.IsSiteForCoverings)
    [P.IsStableUnderFiniteComposition] [P.IsStableUnderFiniteBaseChange]
    (hfinite : ∀ (W : C) (S : Presieve W), S ∈ P W → Finite S.uncurry)
    [HasExt.{u} (Sheaf P.toGrothendieck AddCommGrpCat.{u})]
    (I : Type u) [SmallCategory I] [IsFiltered I]
    (F : I ⥤ Sheaf P.toGrothendieck AddCommGrpCat.{u})
    (c : Cocone F) (hc : IsColimit c) (q : ℕ) :
    IsFiltered (WithInitial I) ∧
    Nonempty (IsColimit (zeroExtensionCocone c)) ∧
    Nonempty (IsColimit (constantSiteCocone (C := C) I)) ∧
    (Under.forget (WithInitial.star : WithInitial I)).IsEquivalence ∧
    Nonempty (IsColimit ((Sheaf.cohomologyPresheafFunctor P.toGrothendieck q).mapCocone
      (zeroExtensionCocone c))) ∧
    Nonempty (IsColimit (((Sheaf.cohomologyPresheafFunctor P.toGrothendieck q).mapCocone
      (zeroExtensionCocone c)).whisker
        (Under.forget (WithInitial.star : WithInitial I)))) := by
  sorry

end CategoryTheory.FiniteCoverDerivedPresheaf
