/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Sheaf.AlgebraicGeometry.CoverCech
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.RingTheory.IndEtaleUniverseTransport
import Sheaf.AlgebraicGeometry.ProEtaleComparisonSections
import Sheaf.RingTheory.IndEtaleStability
import WeilConjectures.AlgebraicGeometry.LimitAffineTransition
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.AlgebraicGeometry.Sites.MorphismProperty
import Mathlib.CategoryTheory.Limits.MorphismProperty
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-! # Second-limit comparison for finite affine étale Čech covers

Source: Stacks Project, Tags 099U (second Čech-colimit calculation) and 099S
(blueprint: lem-weil-pbc-finite-etale-cover-cech-stage-comparison).

The stage and limit families below are actual fibre products in the recorded sites.
The theorem specifies every transition and comparison map on tuple coordinates.
Its colimit universal properties express the canonical isomorphisms, both for complexes
and for every cohomology group. Fixed-ring left-module sheaves use the module-valued
comparison of `proEtaleSiteComparisonModules`; forgetting scalars gives exactly the
underlying abelian-presheaf Čech construction of `CoverCech`.
-/

@[expose] public section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Base change of an initial covering object to a later stage, in the small étale site.
Source: Stacks Project, Tag 099U, second limit paragraph
(blueprint: lem-weil-pbc-finite-etale-cover-cech-stage-comparison). -/
noncomputable abbrev finiteEtaleCoverStageObject {X : Scheme.{u}}
    {L : Type u} [Preorder L] (D : Lᵒᵖ ⥤ X.Etale) (i₀ : L)
    {m : ℕ} (W : Fin m → X.Etale) (f : ∀ a, W a ⟶ D.obj (op i₀))
    (i : {i : L // i₀ ≤ i}) (a : Fin m) : X.Etale :=
  pullback (f a) (D.map (homOfLE i.property).op)

/-- The covering arrow at a later stage is the second fibre-product projection.
Source: Stacks Project, Tag 099U, second limit paragraph
(blueprint: lem-weil-pbc-finite-etale-cover-cech-stage-comparison). -/
noncomputable abbrev finiteEtaleCoverStageArrow {X : Scheme.{u}}
    {L : Type u} [Preorder L] (D : Lᵒᵖ ⥤ X.Etale) (i₀ : L)
    {m : ℕ} (W : Fin m → X.Etale) (f : ∀ a, W a ⟶ D.obj (op i₀))
    (i : {i : L // i₀ ≤ i}) (a : Fin m) :
    finiteEtaleCoverStageObject D i₀ W f i a ⟶ D.obj (op i.val) :=
  pullback.snd (f a) (D.map (homOfLE i.property).op)

/-- Base change of an initial covering object to the given pro-étale limit.
Source: Stacks Project, Tags 099U and 099S
(blueprint: lem-weil-pbc-finite-etale-cover-cech-stage-comparison). -/
noncomputable abbrev finiteEtaleCoverLimitObject {X : Scheme.{u}}
    {L : Type u} [Preorder L] (D : Lᵒᵖ ⥤ X.Etale) (i₀ : L)
    {m : ℕ} (W : Fin m → X.Etale) (f : ∀ a, W a ⟶ D.obj (op i₀))
    (U : X.ProEt) (π : (Functor.const Lᵒᵖ).obj U ⟶ D ⋙ Scheme.toProEt X)
    (a : Fin m) : X.ProEt :=
  pullback ((Scheme.toProEt X).map (f a)) (π.app (op i₀))

/-- The limiting covering arrow is the second fibre-product projection.
Source: Stacks Project, Tags 099U and 099S
(blueprint: lem-weil-pbc-finite-etale-cover-cech-stage-comparison). -/
noncomputable abbrev finiteEtaleCoverLimitArrow {X : Scheme.{u}}
    {L : Type u} [Preorder L] (D : Lᵒᵖ ⥤ X.Etale) (i₀ : L)
    {m : ℕ} (W : Fin m → X.Etale) (f : ∀ a, W a ⟶ D.obj (op i₀))
    (U : X.ProEt) (π : (Functor.const Lᵒᵖ).obj U ⟶ D ⋙ Scheme.toProEt X)
    (a : Fin m) : finiteEtaleCoverLimitObject D i₀ W f U π a ⟶ U :=
  pullback.snd ((Scheme.toProEt X).map (f a)) (π.app (op i₀))

/-- The canonical restriction cocone of finite affine étale covering complexes is
colimiting, and remains colimiting on every Čech cohomology group. The two projection
identities for `r` and `s` uniquely characterize the canonical maps of tuple products;
the next two identities prescribe all cochain maps using those restrictions. Thus the
existentials assert existence of these specified canonical constructions, not a choice
of unrelated isomorphisms. The nonnegative complexes extend by zero to the integer
complexes of `CoverCech`; the second colimit assertion records that extension explicitly.

Source: Stacks Project, Tags 099U (second Čech-colimit calculation) and 099S
(blueprint: lem-weil-pbc-finite-etale-cover-cech-stage-comparison).

Proof: (1) The tail above `i₀` is nonempty and directed and retains the same limit:
extend a cone by choosing a common upper bound with `i₀`, with independence checked at
another common upper bound. For an empty cover every term is the zero abelian group.
(2) The affine-limit theorem makes the limit affine. Étale base change preserves the
finite covering and all tuple fibre products. Their sources are affine; their maps to
`X` are étale of finite presentation, since affine morphisms are quasi-compact and
separated and étale morphisms are locally of finite presentation.
(3) Each limit tuple product is the limit of its stage tuple products: a map to it is
exactly compatible maps to the base and each original covering factor. This also proves
the projection identities, including repeated indices.
(4) Coordinate rings are the filtered colimits of their stage rings, so these are
ind-étale basis objects. Apply comparison-sections to each tuple, with legs the comparison
unit followed by restriction. Ind-étale stability gives the required pro-étale objects;
base change gives the limiting cover.
(5) Filtered colimits commute with the finite products indexed by the ordered tuples.
Thus the prescribed cocone is colimiting in every nonnegative degree.
(6) The projection identities and naturality of the unit commute with deletion of any
factor, hence with the alternating sums defining the differentials. The maps therefore
form the stated diagram and cocone. Its degreewise colimit universal property gives the
colimit in complexes, also after extension by zero to negative degrees.
(7) Filtered colimits commute with kernels and are exact in abelian groups. Applying this
to cycles and boundaries identifies the colimit of the stage cohomology with the limit
complex's cohomology, with the same induced restriction legs. In degree zero the incoming
term is zero. No injectivity, augmentation exactness, or positive-degree vanishing is used. -/
theorem finite_etale_cover_cech_stage_comparison
    {X : Scheme.{u}} [IsAffine X]
    (Λ : Type (u + 1)) [Ring Λ] [Finite Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    {L : Type u} [Preorder L] [IsDirected L (· ≤ ·)] [Nonempty L]
    (D : Lᵒᵖ ⥤ X.Etale) [∀ i, IsAffine (D.obj i).left]
    (U : X.ProEt) (π : (Functor.const Lᵒᵖ).obj U ⟶ D ⋙ Scheme.toProEt X)
    (_hlim : IsLimit (Cone.mk U.left
      (Functor.whiskerRight π (Scheme.ProEt.forget X ⋙ Over.forget X))))
    (i₀ : L) {m : ℕ} (W : Fin m → X.Etale) [∀ a, IsAffine (W a).left]
    (f : ∀ a, W a ⟶ D.obj (op i₀))
    (_hcover : Sieve.ofArrows W f ∈ X.smallEtaleTopology (D.obj (op i₀)))
    (S : ∀ i : {i : L // i₀ ≤ i},
      SiteCechComplex (finiteEtaleCoverStageObject D i₀ W f i)
        (finiteEtaleCoverStageArrow D i₀ W f i))
    (T : SiteCechComplex (finiteEtaleCoverLimitObject D i₀ W f U π)
      (finiteEtaleCoverLimitArrow D i₀ W f U π)) :
    ∃ (r : ∀ {i j : {i : L // i₀ ≤ i}}, (i ⟶ j) →
        ∀ (p : ℕ) (t : Fin (p + 1) → Fin m), (S j).W p t ⟶ (S i).W p t)
      (s : ∀ (i : {i : L // i₀ ≤ i}) (p : ℕ) (t : Fin (p + 1) → Fin m),
        T.W p t ⟶ (Scheme.toProEt X).obj ((S i).W p t))
      (A : {i : L // i₀ ≤ i} ⥤ CochainComplex AddCommGrpCat.{u + 1} ℕ)
      (eA : ∀ i, A.obj i ≅ (S i).complex (F.obj ⋙ forget₂ (ModuleCat Λ) AddCommGrpCat))
      (K : Cocone A)
      (eK : K.pt ≅ T.complex
        (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) X).obj F).obj ⋙
          forget₂ (ModuleCat Λ) AddCommGrpCat)),
      (∀ (i j : {i : L // i₀ ≤ i}) (h : i ⟶ j) (p : ℕ)
          (t : Fin (p + 1) → Fin m) (k : Fin (p + 1)),
        (r h p t ≫ (S i).pr p t k ≫
          pullback.fst (f (t k)) (D.map (homOfLE i.property).op) =
            (S j).pr p t k ≫
              pullback.fst (f (t k)) (D.map (homOfLE j.property).op)) ∧
        (r h p t ≫ (S i).pr p t k ≫ finiteEtaleCoverStageArrow D i₀ W f i (t k) =
          (S j).pr p t k ≫ finiteEtaleCoverStageArrow D i₀ W f j (t k) ≫
            D.map (homOfLE (leOfHom h)).op)) ∧
      (∀ (i : {i : L // i₀ ≤ i}) (p : ℕ) (t : Fin (p + 1) → Fin m)
          (k : Fin (p + 1)),
        (s i p t ≫ (Scheme.toProEt X).map ((S i).pr p t k ≫
          pullback.fst (f (t k)) (D.map (homOfLE i.property).op)) =
            T.pr p t k ≫
              pullback.fst ((Scheme.toProEt X).map (f (t k))) (π.app (op i₀))) ∧
        (s i p t ≫ (Scheme.toProEt X).map
          ((S i).pr p t k ≫ finiteEtaleCoverStageArrow D i₀ W f i (t k)) =
            T.pr p t k ≫ finiteEtaleCoverLimitArrow D i₀ W f U π (t k) ≫
              π.app (op i.val))) ∧
      (∀ (i j : {i : L // i₀ ≤ i}) (h : i ⟶ j) (p : ℕ)
          (z : (S i).cochains (F.obj ⋙ forget₂ (ModuleCat Λ) AddCommGrpCat) p)
          (t : Fin (p + 1) → Fin m),
        (((eA i).inv ≫ A.map h ≫ (eA j).hom).f p) z t =
          (F.obj.map (r h p t).op) (z t)) ∧
      (∀ (i : {i : L // i₀ ≤ i}) (p : ℕ)
          (z : (S i).cochains (F.obj ⋙ forget₂ (ModuleCat Λ) AddCommGrpCat) p)
          (t : Fin (p + 1) → Fin m),
        (((eA i).inv ≫ K.ι.app i ≫ eK.hom).f p) z t =
          (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) X).obj F).obj.map
            (s i p t).op)
            ((((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} Λ) X).unit.app F).hom.app
              (op ((S i).W p t))) (z t))) ∧
      Nonempty (IsColimit K) ∧
      Nonempty (IsColimit ((ComplexShape.embeddingUpNat.extendFunctor
        AddCommGrpCat.{u + 1}).mapCocone K)) ∧
      ∀ q : ℕ, Nonempty (IsColimit
        ((HomologicalComplex.homologyFunctor AddCommGrpCat
          (ComplexShape.up ℕ) q).mapCocone K)) := by
  sorry

end AlgebraicGeometry
