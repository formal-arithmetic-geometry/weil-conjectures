/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q83
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.CategoryTheory.ComposableArrows.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Sheaf.CategoryTheory.DerivedColimitBar
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.Algebra.Homology.Functor
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-! # The augmented presheaf bar resolution

Source: Stacks Project, Tag 08PG, Example `example-left-derived-colimits`, with the
explicit presheaf resolution and evaluation contraction expanded in the DAG
(blueprint: def-trf-presheaf-bar-resolution-data).

The direct sums and every generator formula below are actual constructions.
`Resolution` specifies their functorial realization as cochain complexes, together
with the contraction, exactness and normalized colimit comparison. No resolution
or comparison is chosen from its existence theorem.
-/

@[expose] public section

set_option autoImplicit false

universe u v r

open CategoryTheory CategoryTheory.Limits Opposite
open scoped DirectSum

namespace CategoryTheory.PresheafBar

variable {E : Type u} [SmallCategory E] {R : Type r} [CommRing R]

/-- The coefficient presheaves on the identity-cover site. They are precisely module
sheaves for the constant ring on the bottom Grothendieck topology.
Source: Stacks 08PF--08PG (blueprint: def-trf-presheaf-bar-resolution-data). -/
abbrev Presheaves (E : Type u) [SmallCategory E] (R : Type r) [CommRing R] :=
  Eᵒᵖ ⥤ ModuleCat.{max u v} R

/-- The evaluated term of L_U(M), with its actual direct-sum module structure.
Source: Stacks 08PG, presheaf expansion
(blueprint: def-trf-presheaf-bar-resolution-data). -/
def freeTerm (U V : E) (M : ModuleCat.{max u v} R) : ModuleCat.{max u v} R :=
  ModuleCat.of R (⨁ _ : V ⟶ U, M)

/-- Inclusion of the a-summand in L_U(M)(V).
Source: Stacks 08PG (blueprint: def-trf-presheaf-bar-resolution-data). -/
noncomputable def freeι (U V : E) (M : ModuleCat.{max u v} R) (a : V ⟶ U) :
    M ⟶ freeTerm U V M := by
  classical
  exact ModuleCat.ofHom (DirectSum.lof R _ (fun _ ↦ M) a)

/-- Restriction in L_U: (a,x) maps to (b ≫ a,x).
Source: Stacks 08PG (blueprint: def-trf-presheaf-bar-resolution-data). -/
noncomputable def freeRestriction (U : E) (M : ModuleCat.{max u v} R)
    {V W : E} (b : W ⟶ V) : freeTerm U V M ⟶ freeTerm U W M := by
  classical
  exact ModuleCat.ofHom (DirectSum.toModule R _ _
    (fun a ↦ (freeι U W M (b ≫ a)).hom))

/-- Actual direct sum of all evaluated bar generators in degree -n. A chain c
is U_n → ... → U_0, so c.left = U_n and c.right = U_0.
Source: Stacks 08PG (blueprint: def-trf-presheaf-bar-resolution-data). -/
def term (F : Presheaves.{u, v} E R) (n : ℕ) (V : E) : ModuleCat.{max u v} R :=
  ModuleCat.of R (⨁ t : Σ c : ComposableArrows E n, V ⟶ c.left,
    F.obj (op t.1.right))

/-- Actual direct sum K^(-n), without the incoming evaluation arrow.
Source: Stacks 08PG (blueprint: def-trf-presheaf-bar-resolution-data). -/
def colimitTerm (F : Presheaves.{u, v} E R) (n : ℕ) : ModuleCat.{max u v} R :=
  ModuleCat.of R (⨁ c : ComposableArrows E n, F.obj (op c.right))

/-- The evaluated bar generator (a,c,x), linear in x.
Source: Stacks 08PG (blueprint: def-trf-presheaf-bar-resolution-data). -/
noncomputable def ι (F : Presheaves.{u, v} E R) (n : ℕ) (V : E)
    (c : ComposableArrows E n) (a : V ⟶ c.left) : F.obj (op c.right) ⟶ term F n V := by
  classical
  exact ModuleCat.ofHom (DirectSum.lof R _
    (fun (t : Σ c : ComposableArrows E n, V ⟶ c.left) ↦ F.obj (op t.1.right)) ⟨c, a⟩)

/-- The coefficient generator (c,x) of K.
Source: Stacks 08PG (blueprint: def-trf-presheaf-bar-resolution-data). -/
noncomputable def colimitι (F : Presheaves.{u, v} E R) (n : ℕ)
    (c : ComposableArrows E n) : F.obj (op c.right) ⟶ colimitTerm F n := by
  classical
  exact ModuleCat.ofHom (DirectSum.lof R _ (fun c ↦ F.obj (op c.right)) c)

/-- The actual restriction map, changing only the incoming arrow.
Source: Stacks 08PG (blueprint: def-trf-presheaf-bar-resolution-data). -/
noncomputable def restriction (F : Presheaves.{u, v} E R) (n : ℕ)
    {V W : E} (b : W ⟶ V) : term F n V ⟶ term F n W := by
  classical
  exact ModuleCat.ofHom (DirectSum.toModule R _ _
    (fun (t : Σ c : ComposableArrows E n, V ⟶ c.left) ↦ (ι F n W t.1 (b ≫ t.2)).hom))

/-- The map on coefficients induced by a morphism of presheaves.
Source: Stacks 08PG (blueprint: def-trf-presheaf-bar-resolution-data). -/
noncomputable def termMap {F G : Presheaves.{u, v} E R} (t : F ⟶ G) (n : ℕ) (V : E) :
    term F n V ⟶ term G n V := by
  classical
  exact ModuleCat.ofHom (DirectSum.toModule R _ _
    (fun (a : Σ c : ComposableArrows E n, V ⟶ c.left) ↦
      ((t.app (op a.1.right)) ≫ ι G n V a.1 a.2).hom))

/-- The coefficient map for K.
Source: Stacks 08PG (blueprint: def-trf-presheaf-bar-resolution-data). -/
noncomputable def colimitTermMap {F G : Presheaves.{u, v} E R} (t : F ⟶ G) (n : ℕ) :
    colimitTerm F n ⟶ colimitTerm G n := by
  classical
  exact ModuleCat.ofHom (DirectSum.toModule R _ _
    (fun (c : ComposableArrows E n) ↦ (t.app (op c.right) ≫ colimitι G n c).hom))

/-- The initial connecting arrow; nontrivial exactly when the first vertex is deleted.
Source: Stacks 08PG (blueprint: def-trf-presheaf-bar-resolution-data). -/
def deleteLeft {n : ℕ} (c : ComposableArrows E (n + 1)) (j : Fin (n + 2)) :
    c.left ⟶ (categoryBarDelete c j).left :=
  c.map (homOfLE (Fin.zero_le _))

/-- The terminal connecting arrow; only the last face restricts the coefficient.
Source: Stacks 08PG (blueprint: def-trf-presheaf-bar-resolution-data). -/
def deleteRight {n : ℕ} (c : ComposableArrows E (n + 1)) (j : Fin (n + 2)) :
    (categoryBarDelete c j).right ⟶ c.right :=
  c.map (homOfLE (Fin.le_last _))

/-- The actual face map on evaluated bar terms, including both end faces.
Source: Stacks 08PG (blueprint: def-trf-presheaf-bar-resolution-data). -/
noncomputable def face (F : Presheaves.{u, v} E R) (n : ℕ) (V : E) (j : Fin (n + 2)) :
    term F (n + 1) V ⟶ term F n V := by
  classical
  exact ModuleCat.ofHom (DirectSum.toModule R _ _
    (fun (t : Σ c : ComposableArrows E (n + 1), V ⟶ c.left) ↦
    (F.map (deleteRight t.1 j).op ≫ ι F n V (categoryBarDelete t.1 j)
      (t.2 ≫ deleteLeft t.1 j)).hom))

/-- The same face with the incoming arrow omitted.
Source: Stacks 08PG (blueprint: def-trf-presheaf-bar-resolution-data). -/
noncomputable def colimitFace (F : Presheaves.{u, v} E R) (n : ℕ) (j : Fin (n + 2)) :
    colimitTerm F (n + 1) ⟶ colimitTerm F n := by
  classical
  exact ModuleCat.ofHom (DirectSum.toModule R _ _ (fun (c : ComposableArrows E (n + 1)) ↦
    (F.map (deleteRight c j).op ≫ colimitι F n (categoryBarDelete c j)).hom))

/-- The signed bar differential in degree -(n+1).
Source: Stacks 08PG (blueprint: def-trf-presheaf-bar-resolution-data). -/
noncomputable def differential (F : Presheaves.{u, v} E R) (n : ℕ) (V : E) :
    term F (n + 1) V ⟶ term F n V :=
  ∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val • face F n V j

/-- The signed differential of K.
Source: Stacks 08PG (blueprint: def-trf-presheaf-bar-resolution-data). -/
noncomputable def colimitDifferential (F : Presheaves.{u, v} E R) (n : ℕ) :
    colimitTerm F (n + 1) ⟶ colimitTerm F n :=
  ∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val • colimitFace F n j

/-- The degree-zero augmentation (a,x) ↦ F(a)x.
Source: Stacks 08PG (blueprint: def-trf-presheaf-bar-resolution-data). -/
noncomputable def augmentation (F : Presheaves.{u, v} E R) (V : E) :
    term F 0 V ⟶ F.obj (op V) := by
  classical
  exact ModuleCat.ofHom (DirectSum.toModule R _ _
    (fun (t : Σ c : ComposableArrows E 0, V ⟶ c.left) ↦ (F.map t.2.op).hom))

/-- Insert the evaluation object and its identity at the beginning of a generator.
This map is specified only at a fixed V, with no naturality in V.
Source: Stacks 08PG (blueprint: def-trf-presheaf-bar-resolution-data). -/
noncomputable def contraction (F : Presheaves.{u, v} E R) (n : ℕ) (V : E) :
    term F n V ⟶ term F (n + 1) V := by
  classical
  exact ModuleCat.ofHom (DirectSum.toModule R _ _
    (fun (t : Σ c : ComposableArrows E n, V ⟶ c.left) ↦
      (ι F (n + 1) V (t.1.precomp t.2) (𝟙 V)).hom))

/-- The contraction in augmented degree -1 is the identity summand.
Source: Stacks 08PG (blueprint: def-trf-presheaf-bar-resolution-data). -/
noncomputable def augmentedContraction (F : Presheaves.{u, v} E R) (V : E) :
    F.obj (op V) ⟶ term F 0 V :=
  ι F 0 V (ComposableArrows.mk₀ V) (𝟙 V)

/-- Forget the incoming arrow, retaining the coefficient exactly.
Source: Stacks 08PG (blueprint: def-trf-presheaf-bar-resolution-data). -/
noncomputable def comparison (F : Presheaves.{u, v} E R) (n : ℕ) (V : E) :
    term F n V ⟶ colimitTerm F n := by
  classical
  exact ModuleCat.ofHom (DirectSum.toModule R _ _
    (fun (t : Σ c : ComposableArrows E n, V ⟶ c.left) ↦ (colimitι F n t.1).hom))

/-- The normalized augmentation of K^0 into the chosen colimit of F.
Source: Stacks 08PG (blueprint: def-trf-presheaf-bar-resolution-data). -/
noncomputable def colimitAugmentation (F : Presheaves.{u, v} E R) :
    colimitTerm F 0 ⟶ colimit F := by
  classical
  exact ModuleCat.ofHom (DirectSum.toModule R _ _
    (fun (c : ComposableArrows E 0) ↦ (colimit.ι F (op c.right)).hom))

/-- The map of L_U terms induced by a coefficient-module map.
Source: Stacks 08PG (blueprint: def-trf-presheaf-bar-resolution-data). -/
noncomputable def freeMap (U V : E) {M N : ModuleCat.{max u v} R} (f : M ⟶ N) :
    freeTerm U V M ⟶ freeTerm U V N := by
  classical
  exact ModuleCat.ofHom (DirectSum.toModule R _ _
    (fun (a : V ⟶ U) ↦ (f ≫ freeι U V N a).hom))

/-- The chosen categorical colimit, applied degreewise in the comparison below.
Source: Stacks 08PF--08PG; the category-colimit dependency
(blueprint: def-trf-presheaf-bar-resolution-data). -/
noncomputable abbrev C : Presheaves.{u, v} E R ⥤ ModuleCat.{max u v} R := colim

/-- Include all incoming-arrow summands belonging to one fixed chain. This is the
summand L_(U_n)(F(U_0)) of the presheaf bar term.
Source: Stacks 08PG (blueprint: def-trf-presheaf-bar-resolution-data). -/
noncomputable def summandMap (F : Presheaves.{u, v} E R) (n : ℕ) (V : E)
    (c : ComposableArrows E n) : freeTerm c.left V (F.obj (op c.right)) ⟶ term F n V := by
  classical
  exact ModuleCat.ofHom (DirectSum.toModule R _ _ (fun (a : V ⟶ c.left) ↦
    (ι F n V c a).hom))

/-- A fully normalized realization of the explicit bar formulas. The term isomorphisms
identify actual direct sums, and all restrictions, coefficient maps, faces, differentials,
augmentations and comparison maps are fixed by those identifications. This is a specification
of the construction, not a choice of a complex or an arbitrary comparison.
Source: Stacks 08PG, explicit presheaf-resolution expansion, all clauses
(blueprint: def-trf-presheaf-bar-resolution-data). -/
structure Resolution (E : Type u) [SmallCategory E] (R : Type r) [CommRing R] where
  /-- L_U as an additive functor in the coefficient module. -/
  L : E → ModuleCat.{max u v} R ⥤ Presheaves.{u, v} E R
  /-- L_U(M)(V) is the prescribed direct sum over arrows V → U. -/
  freeIso : ∀ (U V : E) (M : ModuleCat.{max u v} R),
    freeTerm U V M ≅ ((L U).obj M).obj (op V)
  /-- Restriction sends (a,x) to (b ≫ a,x). -/
  free_restriction : ∀ (U V W : E) (M : ModuleCat.{max u v} R) (b : W ⟶ V),
    (freeIso U V M).hom ≫ ((L U).obj M).map b.op =
      freeRestriction U M b ≫ (freeIso U W M).hom
  /-- Functoriality in M acts identically on the arrow index. -/
  free_map : ∀ (U V : E) (M N : ModuleCat.{max u v} R) (f : M ⟶ N),
    (freeIso U V M).hom ≫ ((L U).map f).app (op V) =
      freeMap U V f ≫ (freeIso U V N).hom
  /-- Additivity in the coefficient module. -/
  L_additive : ∀ U : E, (L U).Additive
  /-- The presheaf bar cochain complex, functorial in F. -/
  B : Presheaves.{u, v} E R ⥤ CochainComplex (Presheaves.{u, v} E R) ℤ
  /-- The category bar cochain complex, functorial in F. -/
  K : Presheaves.{u, v} E R ⥤ CochainComplex (ModuleCat.{max u v} R) ℤ
  /-- The functor B is additive. -/
  [B_additive : B.Additive]
  /-- The functor K is additive. -/
  [K_additive : K.Additive]
  /-- B^(-n)(V) is the actual sum over (a,c). This is the evaluated sum of L terms. -/
  termIso : ∀ (F : Presheaves.{u, v} E R) (n : ℕ) (V : E),
    term F n V ≅ ((B.obj F).X (-(n : ℤ))).obj (op V)
  /-- The natural inclusion of each L_(U_n)(F(U_0)) summand. -/
  summand : ∀ (F : Presheaves.{u, v} E R) (n : ℕ) (c : ComposableArrows E n),
    (L c.left).obj (F.obj (op c.right)) ⟶ (B.obj F).X (-(n : ℤ))
  /-- These inclusions are the actual incoming-arrow generator inclusions. -/
  summand_eq : ∀ (F : Presheaves.{u, v} E R) (n : ℕ) (V : E)
      (c : ComposableArrows E n),
    (freeIso c.left V (F.obj (op c.right))).hom ≫ (summand F n c).app (op V) =
      summandMap F n V c ≫ (termIso F n V).hom
  /-- B^(-n) is the coproduct of the specified L terms in the presheaf category. -/
  summands_isColimit : ∀ (F : Presheaves.{u, v} E R) (n : ℕ),
    IsColimit (Cofan.mk ((B.obj F).X (-(n : ℤ))) (summand F n))
  /-- K^(-n) is the actual sum of coefficients over chains c. -/
  colimitTermIso : ∀ (F : Presheaves.{u, v} E R) (n : ℕ),
    colimitTerm F n ≅ (K.obj F).X (-(n : ℤ))
  /-- Both complexes have zero positive terms. -/
  positive_zero : ∀ (F : Presheaves.{u, v} E R) (i : ℤ), 0 < i →
    IsZero ((B.obj F).X i) ∧ IsZero ((K.obj F).X i)
  /-- The B-term identifications intertwine all presheaf restrictions. -/
  restriction_eq : ∀ (F : Presheaves.{u, v} E R) (n : ℕ) (V W : E) (b : W ⟶ V),
    (termIso F n V).hom ≫ ((B.obj F).X (-(n : ℤ))).map b.op =
      restriction F n b ≫ (termIso F n W).hom
  /-- A natural map F → G sends every coefficient x to its image at U_0. -/
  map_eq : ∀ (F G : Presheaves.{u, v} E R) (t : F ⟶ G) (n : ℕ) (V : E),
    (termIso F n V).hom ≫ ((B.map t).f (-(n : ℤ))).app (op V) =
      termMap t n V ≫ (termIso G n V).hom
  /-- The same coefficient rule determines K on morphisms. -/
  colimit_map_eq : ∀ (F G : Presheaves.{u, v} E R) (t : F ⟶ G) (n : ℕ),
    (colimitTermIso F n).hom ≫ (K.map t).f (-(n : ℤ)) =
      colimitTermMap t n ≫ (colimitTermIso G n).hom
  /-- Each B face is a presheaf map natural in F. -/
  faces : ∀ (n : ℕ) (_j : Fin (n + 2)),
    B ⋙ HomologicalComplex.eval _ _ (-((n + 1 : ℕ) : ℤ)) ⟶
      B ⋙ HomologicalComplex.eval _ _ (-(n : ℤ))
  /-- Each K face is natural in F. -/
  colimitFaces : ∀ (n : ℕ) (_j : Fin (n + 2)),
    K ⋙ HomologicalComplex.eval _ _ (-((n + 1 : ℕ) : ℤ)) ⟶
      K ⋙ HomologicalComplex.eval _ _ (-(n : ℤ))
  /-- The faces are precisely the specified vertex deletions, including the end faces. -/
  face_eq : ∀ (F : Presheaves.{u, v} E R) (n : ℕ) (V : E) (j : Fin (n + 2)),
    (termIso F (n + 1) V).hom ≫ ((faces n j).app F).app (op V) =
      face F n V j ≫ (termIso F n V).hom
  /-- The K faces have the same coefficient-end restriction. -/
  colimit_face_eq : ∀ (F : Presheaves.{u, v} E R) (n : ℕ) (j : Fin (n + 2)),
    (colimitTermIso F (n + 1)).hom ≫ (colimitFaces n j).app F =
      colimitFace F n j ≫ (colimitTermIso F n).hom
  /-- The face relation d_i d_(j+1) = d_j d_i, for i ≤ j. -/
  face_identity : ∀ (F : Presheaves.{u, v} E R) (n : ℕ) (V : E)
      (i j : Fin (n + 2)), i ≤ j →
    face F (n + 1) V j.succ ≫ face F n V i =
      face F (n + 1) V i.castSucc ≫ face F n V j
  /-- The same face relation for K. -/
  colimit_face_identity : ∀ (F : Presheaves.{u, v} E R) (n : ℕ)
      (i j : Fin (n + 2)), i ≤ j →
    colimitFace F (n + 1) j.succ ≫ colimitFace F n i =
      colimitFace F (n + 1) i.castSucc ≫ colimitFace F n j
  /-- The differential is the alternating sum of faces, with the source convention. -/
  differential_eq : ∀ (F : Presheaves.{u, v} E R) (n : ℕ) (V : E),
    (termIso F (n + 1) V).hom ≫
        ((B.obj F).d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ))).app (op V) =
      differential F n V ≫ (termIso F n V).hom
  /-- K uses the same signed differential. -/
  colimit_differential_eq : ∀ (F : Presheaves.{u, v} E R) (n : ℕ),
    (colimitTermIso F (n + 1)).hom ≫
        (K.obj F).d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) =
      colimitDifferential F n ≫ (colimitTermIso F n).hom
  /-- The augmentation is a natural morphism of cochain complexes to F[0]. -/
  a : B ⟶ HomologicalComplex.single (Presheaves.{u, v} E R) (ComplexShape.up ℤ) 0
  /-- Its degree-zero map is exactly (a,x) ↦ F(a)x. -/
  augmentation_eq : ∀ (F : Presheaves.{u, v} E R) (V : E),
    (termIso F 0 V).hom ≫ ((a.app F).f 0).app (op V) ≫
        ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).hom).app (op V) =
      augmentation F V
  /-- The augmented contraction satisfies a_F s_(-1) = 1. -/
  contraction_augmented : ∀ (F : Presheaves.{u, v} E R) (V : E),
    augmentedContraction F V ≫ augmentation F V = 𝟙 _
  /-- The degree-zero contraction identity, with the augmentation term included. -/
  contraction_zero : ∀ (F : Presheaves.{u, v} E R) (V : E),
    contraction F 0 V ≫ differential F 0 V +
      augmentation F V ≫ augmentedContraction F V = 𝟙 _
  /-- The remaining identities d s_n + s_(n-1) d = 1, at each fixed V. -/
  contraction_succ : ∀ (F : Presheaves.{u, v} E R) (n : ℕ) (V : E),
    contraction F (n + 1) V ≫ differential F (n + 1) V +
      differential F n V ≫ contraction F n V = 𝟙 _
  /-- The augmentation is a quasi-isomorphism of presheaf cochain complexes. -/
  quasiIso : ∀ F : Presheaves.{u, v} E R, QuasiIso (a.app F)
  /-- B takes every objectwise short exact sequence to a short exact sequence of complexes. -/
  B_shortExact : ∀ S : ShortComplex (Presheaves.{u, v} E R),
    (∀ V : E, (S.map ((evaluation Eᵒᵖ (ModuleCat.{max u v} R)).obj (op V))).ShortExact) →
      (S.map B).ShortExact
  /-- K likewise preserves every objectwise short exact sequence. -/
  K_shortExact : ∀ S : ShortComplex (Presheaves.{u, v} E R),
    (∀ V : E, (S.map ((evaluation Eᵒᵖ (ModuleCat.{max u v} R)).obj (op V))).ShortExact) →
      (S.map K).ShortExact
  /-- The natural isomorphism C B ≅ K, in the category of cochain complexes. -/
  b : B ⋙ (C (E := E) (R := R)).mapHomologicalComplex (ComplexShape.up ℤ) ≅ K
  /-- On every evaluated generator the comparison retains the coefficient exactly. -/
  comparison_eq : ∀ (F : Presheaves.{u, v} E R) (n : ℕ) (V : E),
    (termIso F n V).hom ≫ colimit.ι ((B.obj F).X (-(n : ℤ))) (op V) ≫
        ((b.hom.app F).f (-(n : ℤ))) =
      comparison F n V ≫ (colimitTermIso F n).hom
  /-- Under b^0, C(a_F^0) is the normalized augmentation (U,x) ↦ ι_U(x). -/
  colimit_augmentation_eq : ∀ F : Presheaves.{u, v} E R,
    (b.hom.app F).f 0 ≫ (colimitTermIso F 0).inv ≫ colimitAugmentation F =
      C.map ((a.app F).f 0 ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).hom)

end CategoryTheory.PresheafBar
