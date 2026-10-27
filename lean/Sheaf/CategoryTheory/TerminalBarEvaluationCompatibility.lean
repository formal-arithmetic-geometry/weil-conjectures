/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q65
-/
module

public import Sheaf.CategoryTheory.DerivedColimitBar
public import Sheaf.CategoryTheory.SimplicialDerivedColimitComputation
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Terminal evaluation and the two category bar conventions

Source: Stacks Project, Tags 08PG, 08PH, 08Q9 and 08QV
(blueprint: lem-trf-terminal-bar-evaluation-compatibility).

Write `E = Jᵒᵖ`. Thus `F : Eᵒᵖ ⥤ ModuleCat R` is the covariant diagram in the
statement, and a terminal object of `J` is an initial object of `E`.
The recorded first-vertex model uses `SimplicialDerivedColimit.forwardGenerator`
on the same underlying complex. Consequently the convention isomorphism has underlying
map the identity: in the two coordinate systems its matrix is the prescribed sign.
No bar system or augmentation is chosen from a postponed existence theorem.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- The convention comparison in the existing signed-coordinate realization of the
first-vertex model. Its scalar matrix is asserted below, using the recorded first-vertex
generators. Source: Stacks 08PG, 08Q9
(blueprint: lem-trf-terminal-bar-evaluation-compatibility). -/
def terminalBarSignIso (B : CategoryColimitBarSystem.{u}) {E : Type u} [SmallCategory E]
    {R : Type u} [CommRing R] (F : Eᵒᵖ ⥤ ModuleCat.{u} R) :
    (B.models E R).bar.obj F ≅ (B.models E R).bar.obj F :=
  Iso.refl _

/-- A degree-zero cocone augmentation, specified on every summand, with zero components
elsewhere. Source: Stacks 08PG, 08PH
(blueprint: lem-trf-terminal-bar-evaluation-compatibility). -/
def IsBarCoconeAugmentation (B : CategoryColimitBarSystem.{u}) {E : Type u}
    [SmallCategory E] {R : Type u} [CommRing R] (F : Eᵒᵖ ⥤ ModuleCat.{u} R)
    (c : Cocone F)
    (e : (B.models E R).bar.obj F ⟶ (CochainComplex.singleFunctor _ 0).obj c.pt) : Prop :=
  (∀ a : ComposableArrows E 0,
    (B.models E R).generator F 0 a ≫ e.f 0 ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 c.pt).hom = c.ι.app (op a.right)) ∧
  (∀ r : ℤ, r ≠ 0 → e.f r = 0)

/-- The terminal augmentation formula, expressed on the opposite indexing category.
The unique arrow `t ⟶ a.right` of `E` is the arrow `a.right ⟶ t` of `J`.
Source: Stacks 08PG, 08PH and the evaluation in 08QV
(blueprint: lem-trf-terminal-bar-evaluation-compatibility). -/
def IsTerminalBarAugmentation (B : CategoryColimitBarSystem.{u}) {E : Type u}
    [SmallCategory E] {R : Type u} [CommRing R] (F : Eᵒᵖ ⥤ ModuleCat.{u} R)
    (t : E) (ht : IsInitial t)
    (e : (B.models E R).bar.obj F ⟶
      (CochainComplex.singleFunctor _ 0).obj (F.obj (op t))) : Prop :=
  (∀ a : ComposableArrows E 0,
    (B.models E R).generator F 0 a ≫ e.f 0 ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (F.obj (op t))).hom =
        F.map (ht.to a.right).op) ∧
  (∀ r : ℤ, r ≠ 0 → e.f r = 0)

/-- The functor selecting the terminal object, written on opposite categories.
Its pulled-back coefficient is canonically constant, by `F.map_id`.
Source: Stacks 08PH and 08QV
(blueprint: lem-trf-terminal-bar-evaluation-compatibility). -/
def terminalBarPoint {E : Type u} [SmallCategory E] (t : E) :
    Discrete PUnit.{u + 1} ⥤ E :=
  (Functor.const (Discrete PUnit.{u + 1})).obj t

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- The full sign and terminal-evaluation compatibility assertion. The first-vertex
complex and its maps are realized in the signed coordinates of the recorded dependency.
All equalities here are equalities of chain maps or their actual components, before
localization. Source: Stacks 08PG, 08PH, 08Q9 and 08QV
(blueprint: lem-trf-terminal-bar-evaluation-compatibility). -/
structure TerminalBarCompatibility (B : CategoryColimitBarSystem.{u}) : Prop where
  sign : ∀ {E : Type u} [SmallCategory E] {R : Type u} [CommRing R]
    (F : Eᵒᵖ ⥤ ModuleCat.{u} R) (n : ℕ) (a : ComposableArrows E n),
    (B.models E R).generator F n a ≫ (terminalBarSignIso B F).hom.f (-↑n) =
      (-1 : ℤ) ^ (n * (n + 1) / 2) •
        SimplicialDerivedColimit.forwardGenerator B F n a
  degreeZero : ∀ {E : Type u} [SmallCategory E] {R : Type u} [CommRing R]
    (F : Eᵒᵖ ⥤ ModuleCat.{u} R), (terminalBarSignIso B F).hom.f 0 = 𝟙 _
  coefficientNaturality : ∀ {E : Type u} [SmallCategory E] {R : Type u} [CommRing R]
    {F G : Eᵒᵖ ⥤ ModuleCat.{u} R} (s : F ⟶ G),
    (B.models E R).bar.map s ≫ (terminalBarSignIso B G).hom =
      (terminalBarSignIso B F).hom ≫ (B.models E R).bar.map s
  reindexNaturality : ∀ {E D : Type u} [SmallCategory E] [SmallCategory D]
    {R : Type u} [CommRing R] (v : E ⥤ D) {F : Eᵒᵖ ⥤ ModuleCat.{u} R}
    {G : Dᵒᵖ ⥤ ModuleCat.{u} R} (s : F ⟶ v.op ⋙ G),
    B.map v (RingHom.id R) s ≫ (terminalBarSignIso B G).hom =
      (terminalBarSignIso B F).hom ≫ B.map v (RingHom.id R) s
  coconeCompatibility : ∀ {E : Type u} [SmallCategory E] {R : Type u} [CommRing R]
    (F : Eᵒᵖ ⥤ ModuleCat.{u} R) (c : Cocone F)
    (e : (B.models E R).bar.obj F ⟶ (CochainComplex.singleFunctor _ 0).obj c.pt),
    IsBarCoconeAugmentation B F c e → (terminalBarSignIso B F).hom ≫ e = e
  terminal : ∀ {E : Type u} [SmallCategory E] {R : Type u} [CommRing R]
    (F : Eᵒᵖ ⥤ ModuleCat.{u} R) (t : E) (ht : IsInitial t),
    ∃ e : (B.models E R).bar.obj F ⟶
        (CochainComplex.singleFunctor _ 0).obj (F.obj (op t)),
      IsTerminalBarAugmentation B F t ht e ∧
      (∀ e' : (B.models E R).bar.obj F ⟶
          (CochainComplex.singleFunctor _ 0).obj (F.obj (op t)),
        IsTerminalBarAugmentation B F t ht e' → e' = e) ∧
      QuasiIso e ∧ IsIso (DerivedCategory.Q.map e) ∧
      (∀ {D : Type u} [SmallCategory D] (v : D ⥤ E),
        (∀ a : ComposableArrows D 0,
          (B.models D R).generator (v.op ⋙ F) 0 a ≫
              (B.map v (RingHom.id R) (𝟙 (v.op ⋙ F)) ≫ e).f 0 ≫
                (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (F.obj (op t))).hom =
            F.map (ht.to (v.obj a.right)).op) ∧
        (∀ r : ℤ, r ≠ 0 →
          (B.map v (RingHom.id R) (𝟙 (v.op ⋙ F)) ≫ e).f r = 0) ∧
        ((terminalBarSignIso B (v.op ⋙ F)).hom ≫
          B.map v (RingHom.id R) (𝟙 (v.op ⋙ F)) ≫ e =
            B.map v (RingHom.id R) (𝟙 (v.op ⋙ F)) ≫ e)) ∧
      (∃ ePoint : (B.models (Discrete PUnit.{u + 1}) R).bar.obj
          ((terminalBarPoint t).op ⋙ F) ⟶
            (CochainComplex.singleFunctor _ 0).obj (F.obj (op t)),
        (∀ a : ComposableArrows (Discrete PUnit.{u + 1}) 0,
          (B.models (Discrete PUnit.{u + 1}) R).generator
              ((terminalBarPoint t).op ⋙ F) 0 a ≫ ePoint.f 0 ≫
                (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (F.obj (op t))).hom = 𝟙 _) ∧
        (∀ r : ℤ, r ≠ 0 → ePoint.f r = 0) ∧
        B.map (terminalBarPoint t) (RingHom.id R)
          (𝟙 ((terminalBarPoint t).op ⋙ F)) ≫ e = ePoint ∧
        (terminalBarSignIso B ((terminalBarPoint t).op ⋙ F)).hom ≫
          B.map (terminalBarPoint t) (RingHom.id R)
            (𝟙 ((terminalBarPoint t).op ⋙ F)) ≫ e =
              (terminalBarSignIso B ((terminalBarPoint t).op ⋙ F)).hom ≫ ePoint)

/-- Terminal evaluation of the category bar, with strict bar-convention compatibility.
Source: Stacks 08PG, 08PH, 08Q9 and 08QV
(blueprint: lem-trf-terminal-bar-evaluation-compatibility).

Proof:
1. The reversed and first-vertex differentials differ in degree `-n` by `(-1)^n`.
   Set `lambda_n = (-1)^(n(n+1)/2)`. Then `lambda_n = (-1)^n lambda_(n-1)` and
   `lambda_n^2 = 1`. This identifies the two complexes, using precisely the signed
   generators of lem-trf-simplicial-derived-colimit-computation. In this realization
   the underlying isomorphism is identity. Reindexing and coefficient maps preserve
   the degree and commute with its scalar matrix. Since `lambda_0 = 1`, all cocone
   augmentations commute with it.
2. Define `e` on each degree-zero summand by the unique arrow to the terminal object;
   set its other components to zero. For `f : j_0 ⟶ j_1` the degree-one boundary maps
   to `F(!_(j_0))x - F(!_(j_1))F(f)x = 0` by terminality. Thus it is a chain map.
   The coproduct property gives uniqueness. Inclusion of the terminal summand gives
   a section, and the composite with the augmentation is identity.
3. Append the terminal vertex to each string. For the reversed faces its first face
   is identity and all remaining faces are the old faces followed by this insertion.
   Therefore `d s + s d = 1` in negative degrees and `d s = 1 - inclusion e` in
   degree zero. This is the explicit contraction from lem-trf-derived-colimit-bar.
4. Every negative-degree cycle is consequently a boundary. In degree zero, the
   augmentation and terminal inclusion induce inverse maps on cohomology; all
   positive terms are zero. Hence `e` is a quasi-isomorphism and becomes an
   isomorphism under the localization of def-weil-abstract-derived-category.
5. The reindexing formula of lem-trf-derived-colimit-bar gives the asserted composite
   on every generator, and its other components vanish. For the point selecting `t`,
   the unique endomorphism of `t` is identity: this gives the identity degree-zero
   augmentation of the constant alternating complex. Every face on the point is
   identity; its differential is zero in odd positive chain degrees and identity in
   even ones. Both equalities are strict chain-map equalities. Finally the sign
   comparison has degree-zero component identity, so the same equalities hold in
   first-vertex coordinates. -/
theorem terminalBarCompatibility (B : CategoryColimitBarSystem.{u}) :
    TerminalBarCompatibility B := by
  sorry

end CategoryTheory
