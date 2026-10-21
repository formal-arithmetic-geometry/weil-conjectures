/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NV
-/
module

public import Sheaf.CategoryTheory.StageSystemFunctorDescent
public import Mathlib.CategoryTheory.Idempotents.Biproducts

/-! # A raw local inverse through common stages and two Karoubi envelopes

Source: blueprint sketch 32, lines 1291--1359 and 1412--1455, ancestor proof steps 4--6
(blueprint: lem-sbc-common-stage-inverse-through-karoubi).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe w u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents

namespace CategoryTheory.CommonStage

variable {I : Type w} [PartialOrder I]

private theorem extension_left {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ C) (G : C ⥤ D) (h : F = 𝟭 C)
    (h' : (functorExtension₂ _ _).obj F = 𝟭 (Karoubi C)) :
    (functorExtension₂ _ _).mapIso
        (Functor.isoWhiskerRight (eqToIso h) G ≪≫ G.leftUnitor) =
      Functor.isoWhiskerRight (eqToIso h') ((functorExtension₂ _ _).obj G) ≪≫
        ((functorExtension₂ _ _).obj G).leftUnitor := by
  subst F
  ext P
  simp

private theorem extension_right {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (G : D ⥤ D) (h : G = 𝟭 D)
    (h' : (functorExtension₂ _ _).obj G = 𝟭 (Karoubi D)) :
    (functorExtension₂ _ _).mapIso
        (Functor.isoWhiskerLeft F (eqToIso h) ≪≫ F.rightUnitor) =
      Functor.isoWhiskerLeft ((functorExtension₂ _ _).obj F) (eqToIso h') ≪≫
        ((functorExtension₂ _ _).obj F).rightUnitor := by
  subst G
  ext P
  simp

private theorem extension_sandwich {C D : Type u} [Category.{v} C] [Category.{v} D]
    {F G : C ⥤ D} (η : F ⟶ G) (P : Karoubi C) :
    (((functorExtension₂ _ _).map η).app P).f =
      F.map P.p ≫ η.app P.X ≫ G.map P.p := by
  change F.map P.p ≫ η.app P.X = _
  rw [← η.naturality, ← Category.assoc, ← F.map_comp, P.idem]

private theorem extension_unit {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (U : C ⥤ C) (V : D ⥤ D) (hU : U = 𝟭 C) (hV : V = 𝟭 D)
    (hU' : (functorExtension₂ _ _).obj U = 𝟭 (Karoubi C))
    (hV' : (functorExtension₂ _ _).obj V = 𝟭 (Karoubi D)) :
    (functorExtension₂ _ _).mapIso
        (Functor.isoWhiskerLeft F (eqToIso hV) ≪≫ F.rightUnitor ≪≫ F.leftUnitor.symm ≪≫
          Functor.isoWhiskerRight (eqToIso hU).symm F) =
      Functor.isoWhiskerLeft ((functorExtension₂ _ _).obj F) (eqToIso hV') ≪≫
        ((functorExtension₂ _ _).obj F).rightUnitor ≪≫
        ((functorExtension₂ _ _).obj F).leftUnitor.symm ≪≫
        Functor.isoWhiskerRight (eqToIso hU').symm ((functorExtension₂ _ _).obj F) := by
  subst U
  subst V
  ext P
  simp

private theorem transport_self {A : Diagram.{w, u, v} I} {X Y : Pair A}
    (r : Rep A X Y) : transport r (le_refl r.stage) = r.arrow := by
  simp [transport, A.a_right, Functor.congr_hom (A.unit r.stage) r.arrow]

private abbrev stageObject {A : Diagram.{w, u, v} I} (R : PairStructure A)
    (E : I) (X : A.C E) : R.Obj := ⟨E, X⟩

private def stageClass {A : Diagram.{w, u, v} I} (R : PairStructure A) (E : I)
    {X Y : A.C E} (f : X ⟶ Y) : stageObject R E X ⟶ stageObject R E Y :=
  R.repr ⟨E, le_refl E, le_refl E, (A.U (le_refl E)).map f⟩

private theorem stageClass_id {A : Diagram.{w, u, v} I} (R : PairStructure A)
    (hR : R.IsCanonical) (E : I) (X : A.C E) :
    stageClass R E (𝟙 X) = 𝟙 (stageObject R E X) := by
  simpa only [stageClass, stageObject, Functor.map_id] using (hR.identity ⟨E, X⟩).symm

private theorem stageClass_comp {A : Diagram.{w, u, v} I} (R : PairStructure A)
    (hR : R.IsCanonical) (E : I) {X Y Z : A.C E} (f : X ⟶ Y) (g : Y ⟶ Z) :
    stageClass R E f ≫ stageClass R E g = stageClass R E (f ≫ g) := by
  let r : Rep A (stageObject R E X) (stageObject R E Y) :=
    ⟨E, le_refl E, le_refl E, (A.U (le_refl E)).map f⟩
  let t : Rep A (stageObject R E Y) (stageObject R E Z) :=
    ⟨E, le_refl E, le_refl E, (A.U (le_refl E)).map g⟩
  simpa only [stageClass, r, t, transport_self, Functor.map_comp] using
    hR.composition r t E (le_refl E) (le_refl E)

private theorem stageClass_eq {A : Diagram.{w, u, v} I} (R : PairStructure A)
    (hR : R.IsCanonical) (E M : I) (h : E ≤ M) {X Y : A.C E} (f : X ⟶ Y) :
    stageClass R E f = R.repr ⟨M, h, h, (A.U h).map f⟩ := by
  apply (hR.equality _ _).2
  refine ⟨M, h, le_refl M, ?_⟩
  rw [transport_self]
  simp [transport, A.a_left, ← Functor.map_comp,
    Functor.congr_hom (A.unit E) f]

private abbrev stageFunctor {A : Diagram.{w, u, v} I} (R : PairStructure A)
    (hR : R.IsCanonical) (E : I) : A.C E ⥤ R.Obj where
  obj := stageObject R E
  map := stageClass R E
  map_id := stageClass_id R hR E
  map_comp f g := (stageClass_comp R hR E f g).symm

/-- Additivity of the specified Karoubi extension (sketch 32, projector restriction).
(blueprint: lem-sbc-common-stage-inverse-through-karoubi).
Proof: the underlying arrow map is F.map, so its additivity is inherited from F;
the Karoubi Hom addition is the underlying addition. This is node proof step 2. -/
theorem localInverse_extension_additive {C D : Type u} [Category.{v} C] [Category.{v} D]
    [Preadditive C] [Preadditive D] (F : C ⥤ D) [F.Additive] :
    ((functorExtension₂ C D).obj F).Additive := by
  constructor
  intro P Q f g
  apply Karoubi.hom_ext
  exact F.map_add

/-- The extended transition, using Mathlib's canonical construction (sketch 32).
(blueprint: lem-sbc-common-stage-inverse-through-karoubi). -/
def Diagram.innerU (A : Diagram.{w, u, v} I) {i j : I} (h : i ≤ j) :
    Karoubi (A.C i) ⥤ Karoubi (A.C j) := (functorExtension₂ _ _).obj (A.U h)

/-- The extended associator, with its specified restricted inverse (sketch 32).
(blueprint: lem-sbc-common-stage-inverse-through-karoubi). -/
def Diagram.innerAssoc (A : Diagram.{w, u, v} I) {i j k : I}
    (h : i ≤ j) (h' : j ≤ k) : A.innerU h ⋙ A.innerU h' ≅ A.innerU (h.trans h') :=
  (functorExtension₂ _ _).mapIso (A.a h h')

/-- Identity transitions stay identities (sketch 32).
(blueprint: lem-sbc-common-stage-inverse-through-karoubi).
Proof: on an object the identity functor preserves its projector, and on an arrow
it is the identity map; functor extensionality gives equality. Node steps 1--2. -/
theorem Diagram.innerUnit (A : Diagram.{w, u, v} I) (i : I) :
    A.innerU (le_refl i) = 𝟭 (Karoubi (A.C i)) := by
  unfold Diagram.innerU
  rw [A.unit]
  rfl

/-- The left unit case for the extended associator (sketch 32).
(blueprint: lem-sbc-common-stage-inverse-through-karoubi).
Proof: restrict the original left unit equation to each projector. Its restricted
identity is the projector, the actual Karoubi identity. Node steps 1--2. -/
theorem Diagram.innerLeft (A : Diagram.{w, u, v} I) {i j : I} (h : i ≤ j) :
    A.innerAssoc (le_refl i) h =
      Functor.isoWhiskerRight (eqToIso (A.innerUnit i)) (A.innerU h) ≪≫
        (A.innerU h).leftUnitor := by
  unfold Diagram.innerAssoc
  rw [A.a_left]
  exact extension_left _ _ (A.unit i) (A.innerUnit i)

/-- The right unit case for the extended associator (sketch 32).
(blueprint: lem-sbc-common-stage-inverse-through-karoubi).
Proof: restrict the original right unit equation; naturality and idempotence remove
internal projectors, leaving the Karoubi identity. Node steps 1--2. -/
theorem Diagram.innerRight (A : Diagram.{w, u, v} I) {i j : I} (h : i ≤ j) :
    A.innerAssoc h (le_refl j) =
      Functor.isoWhiskerLeft (A.innerU h) (eqToIso (A.innerUnit j)) ≪≫
        (A.innerU h).rightUnitor := by
  unfold Diagram.innerAssoc
  rw [A.a_right]
  exact extension_right _ _ (A.unit j) (A.innerUnit j)

/-- The extended pentagon (sketch 32).
(blueprint: lem-sbc-common-stage-inverse-through-karoubi).
Proof: restrict both sides of the original pentagon. Restriction commutes with
whiskering and composition by naturality and idempotence. Node steps 1--2. -/
theorem Diagram.innerPentagon (A : Diagram.{w, u, v} I) {i j k n : I}
    (h : i ≤ j) (h' : j ≤ k) (h'' : k ≤ n) (X : Karoubi (A.C i)) :
    (A.innerU h'').map ((A.innerAssoc h h').hom.app X) ≫
        (A.innerAssoc (h.trans h') h'').hom.app X =
      (A.innerAssoc h' h'').hom.app ((A.innerU h).obj X) ≫
        (A.innerAssoc h (h'.trans h'')).hom.app X := by
  apply Karoubi.hom_ext
  dsimp [Diagram.innerU, Diagram.innerAssoc, functorExtension₂, functorExtension₁,
    FunctorExtension₁.obj, FunctorExtension₁.map]
  simp only [Functor.map_comp, Category.assoc]
  have ha := congrArg (A.U h'').map ((A.a h h').hom.naturality X.p)
  simp only [Functor.map_comp, Functor.comp_map] at ha
  slice_lhs 2 3 => rw [← ha]
  slice_lhs 1 2 => rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, X.idem]
  have hb := (A.a h' h'').hom.naturality ((A.U h).map X.p)
  simp only [Functor.comp_map] at hb
  slice_rhs 2 3 => rw [← hb]
  slice_rhs 1 2 => rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, X.idem]
  simpa only [Category.assoc] using congrArg ((A.U h'').map ((A.U h').map ((A.U h).map X.p)) ≫ ·)
    (A.pentagon h h' h'' X.X)

/-- The inner Karoubi diagram has real object, transition and associator data.
Source: sketch 32, finite-stage projector restriction
(blueprint: lem-sbc-common-stage-inverse-through-karoubi). -/
def Diagram.innerKaroubi (A : Diagram.{w, u, v} I) : Diagram.{w, max u v, v} I where
  C i := Karoubi (A.C i)
  U := A.innerU
  additive h := localInverse_extension_additive (A.U h)
  unit := A.innerUnit
  a := A.innerAssoc
  a_left := A.innerLeft
  a_right := A.innerRight
  pentagon := A.innerPentagon

/-- The extended family, including the restricted comparisons and inverse comparisons.
Source: sketch 32, comparison restriction
(blueprint: lem-sbc-common-stage-inverse-through-karoubi). -/
def Family.innerKaroubi {A B : Diagram.{w, u, v} I} (Φ : Family A B) :
    Family A.innerKaroubi B.innerKaroubi where
  φ i := (functorExtension₂ _ _).obj (Φ.φ i)
  additive i := localInverse_extension_additive (Φ.φ i)
  b h := (functorExtension₂ _ _).mapIso (Φ.b h)

/-- The restricted family satisfies the same unit and tower equations (sketch 32).
(blueprint: lem-sbc-common-stage-inverse-through-karoubi).
Proof: extend the original unit and tower equations using functorExtension₂;
composition of transformations restricts by cancelling internal projectors, and
whiskering restricts by functoriality. This is node steps 1--2. -/
theorem Family.innerCoherent {A B : Diagram.{w, u, v} I} (Φ : Family A B)
    (hΦ : Φ.Coherent) : Φ.innerKaroubi.Coherent := by
  constructor
  · intro i
    change (functorExtension₂ _ _).mapIso (Φ.b (le_refl i)) = _
    rw [hΦ.unit]
    exact extension_unit _ _ _ (A.unit i) (B.unit i) (A.innerUnit i) (B.innerUnit i)
  · intro i j k h h' P
    apply Karoubi.hom_ext
    dsimp [Diagram.innerKaroubi, Diagram.innerU, Diagram.innerAssoc, Family.innerKaroubi,
      functorExtension₂, functorExtension₁, FunctorExtension₁.obj, FunctorExtension₁.map]
    simp only [Functor.map_comp, Category.assoc]
    have ha := (B.a h h').hom.naturality ((Φ.φ i).map P.p)
    simp only [Functor.comp_map] at ha
    slice_lhs 2 3 => rw [← ha]
    slice_lhs 1 2 =>
      rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, P.idem]
    have hb := congrArg (B.U h').map ((Φ.b h).hom.naturality P.p)
    simp only [Functor.map_comp, Functor.comp_map] at hb
    slice_rhs 2 3 => rw [← hb]
    slice_rhs 1 2 =>
      rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, P.idem]
    have hc := (Φ.b h').hom.naturality ((A.U h).map P.p)
    simp only [Functor.comp_map] at hc
    slice_rhs 3 4 => rw [← hc]
    slice_rhs 2 3 => rw [← hb]
    slice_rhs 1 2 =>
      rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, P.idem]
    simpa only [Category.assoc] using congrArg ((B.U h').map ((B.U h).map ((Φ.φ i).map P.p)) ≫ ·)
      (hΦ.tower h h' P.X)

/-- The inner restricted transformation is Mathlib's extension of the raw one.
Source: sketch 32, projector restriction
(blueprint: lem-sbc-common-stage-inverse-through-karoubi). -/
def innerTransformation {A B : Diagram.{w, u, v} I} {Φ Ψ : Family A B}
    (η : ∀ i, Φ.φ i ⟶ Ψ.φ i) (i : I) :
    Φ.innerKaroubi.φ i ⟶ Ψ.innerKaroubi.φ i := (functorExtension₂ _ _).map (η i)

/-- Compatibility survives inner restriction (sketch 32).
(blueprint: lem-sbc-common-stage-inverse-through-karoubi).
Proof: apply extension to the compatibility square. Naturality at the projector
and idempotence identify each side with its restricted square. Node steps 1--2. -/
theorem innerCompatible {A B : Diagram.{w, u, v} I} {Φ Ψ : Family A B}
    (η : ∀ i, Φ.φ i ⟶ Ψ.φ i) (hη : Compatible η) :
    Compatible (innerTransformation η) := by
  intro i j h P
  apply Karoubi.hom_ext
  dsimp [innerTransformation, Family.innerKaroubi, Diagram.innerKaroubi, Diagram.innerU,
    functorExtension₂, functorExtension₁, FunctorExtension₁.obj, FunctorExtension₁.map]
  simp only [Functor.map_comp, Category.assoc]
  have ha := (Φ.b h).hom.naturality P.p
  simp only [Functor.comp_map] at ha
  slice_lhs 2 3 => rw [← ha]
  slice_lhs 1 2 => rw [← Functor.map_comp, ← Functor.map_comp, P.idem]
  have hb := congrArg (B.U h).map ((η i).naturality P.p)
  simp only [Functor.map_comp] at hb
  slice_rhs 2 3 => rw [← hb]
  slice_rhs 1 2 => rw [← Functor.map_comp, ← Functor.map_comp, P.idem]
  simpa only [Category.assoc] using congrArg ((B.U h).map ((Φ.φ i).map P.p) ≫ ·) (hη h P.X)


/-- The exact sandwiched formulas for the inner transformation and both directions of
its comparison isomorphisms.
Source: sketch 32, projector and scalar comparison formulas
(blueprint: lem-sbc-common-stage-inverse-through-karoubi).
Proof: functorExtension₂ maps a transformation to F(p)≫η. Naturality at p and
idempotence insert the target projector without changing the arrow. Apply the
same calculation to b.hom and b.inv. This is node proof steps 1--2. -/
theorem innerRestriction_formulas {A B : Diagram.{w, u, v} I} {Φ Ψ : Family A B}
    (η : ∀ i, Φ.φ i ⟶ Ψ.φ i) :
    (∀ (E : I) (P : Karoubi (A.C E)),
      ((innerTransformation η E).app P).f =
        (Φ.φ E).map P.p ≫ (η E).app P.X ≫ (Ψ.φ E).map P.p) ∧
    (∀ (E M : I) (h : E ≤ M) (P : Karoubi (A.C E)),
      ((Φ.innerKaroubi.b h).hom.app P).f =
        (B.U h).map ((Φ.φ E).map P.p) ≫ (Φ.b h).hom.app P.X ≫
          (Φ.φ M).map ((A.U h).map P.p) ∧
      ((Φ.innerKaroubi.b h).inv.app P).f =
        (Φ.φ M).map ((A.U h).map P.p) ≫ (Φ.b h).inv.app P.X ≫
          (B.U h).map ((Φ.φ E).map P.p)) := by
  refine ⟨fun E P ↦ extension_sandwich (η E) P, ?_⟩
  intro E M h P
  exact ⟨extension_sandwich (Φ.b h).hom P, extension_sandwich (Φ.b h).inv P⟩

/-- Restriction of a raw arrow to two specified projectors, via the standard retract maps.
Source: sketch 32, inner and outer projector formulas
(blueprint: lem-sbc-common-stage-inverse-through-karoubi). -/
def localInverseRestriction {C : Type u} [Category.{v} C] (P Q : Karoubi C)
    (f : P.X ⟶ Q.X) : P ⟶ Q :=
  Karoubi.decompId_i P ≫ (toKaroubi C).map f ≫ Karoubi.decompId_p Q

private def restrictedIso {C D : Type u} [Category.{v} C] [Category.{v} D]
    {F G : C ⥤ D} (η : F ⟶ G) (P : Karoubi C)
    (v : G.obj P.X ⟶ F.obj P.X)
    (hav : η.app P.X ≫ v = 𝟙 _) (hva : v ≫ η.app P.X = 𝟙 _) :
    ((functorExtension₂ _ _).obj F).obj P ≅ ((functorExtension₂ _ _).obj G).obj P where
  hom := ((functorExtension₂ _ _).map η).app P
  inv := localInverseRestriction _ _ v
  hom_inv_id := by
    apply Karoubi.hom_ext
    dsimp [localInverseRestriction, functorExtension₂, functorExtension₁,
      FunctorExtension₁.obj, FunctorExtension₁.map, Karoubi.decompId_i, Karoubi.decompId_p]
    simp only [Category.assoc]
    rw [← η.naturality_assoc, ← F.map_comp_assoc, P.idem]
    slice_lhs 2 3 => rw [hav]
    simp only [Category.id_comp, ← F.map_comp, P.idem]
  inv_hom_id := by
    apply Karoubi.hom_ext
    dsimp [localInverseRestriction, functorExtension₂, functorExtension₁,
      FunctorExtension₁.obj, FunctorExtension₁.map, Karoubi.decompId_i, Karoubi.decompId_p]
    simp only [Category.assoc]
    rw [← F.map_comp_assoc, P.idem, η.naturality, ← Category.assoc v, hva]
    simp only [Category.id_comp, ← G.map_comp, P.idem]

/-- The inner pair object, retaining its coefficient stage.
Source: sketch 32, finite-stage pair categories
(blueprint: lem-sbc-common-stage-inverse-through-karoubi). -/
def localInversePair (D : DescentSystem.{w, max u v, v} I) (A : Diagram.{w, u, v} I)
    (E : I) (P : Karoubi (A.C E)) : (D.pair A.innerKaroubi).Obj := ⟨E, P⟩

/-- The descended inner-extended family, using the dependency's canonical descent.
Source: sketch 32, finite-stage pair descent
(blueprint: lem-sbc-common-stage-inverse-through-karoubi). -/
def localInverseFunctor (D : DescentSystem.{w, max u v, v} I)
    {A B : Diagram.{w, u, v} I} (Φ : Family A B) (hΦ : Φ.Coherent) :
    (D.pair A.innerKaroubi).Obj ⥤ (D.pair B.innerKaroubi).Obj :=
  D.descend Φ.innerKaroubi (Φ.innerCoherent hΦ)

/-- The descended inner-extended transformation.
Source: sketch 32, finite-stage pair descent
(blueprint: lem-sbc-common-stage-inverse-through-karoubi). -/
def localInverseTransformation (D : DescentSystem.{w, max u v, v} I)
    {A B : Diagram.{w, u, v} I} {Φ Ψ : Family A B}
    (hΦ : Φ.Coherent) (hΨ : Ψ.Coherent) (η : ∀ i, Φ.φ i ⟶ Ψ.φ i)
    (hη : Compatible η) : localInverseFunctor D Φ hΦ ⟶ localInverseFunctor D Ψ hΨ :=
  D.transformation (Φ.innerCoherent hΦ) (Ψ.innerCoherent hΨ)
    (innerTransformation η) (innerCompatible η hη)

/-- A raw common-stage map included between the extended inner projectors.
Source: sketch 32, raw maps and identity-projector inclusions
(blueprint: lem-sbc-common-stage-inverse-through-karoubi). -/
def localInverseStageRep {A B : Diagram.{w, u, v} I} (Φ Ψ : Family A B)
    (E M : I) (h : E ≤ M) (P : Karoubi (A.C E))
    (f : (B.U h).obj ((Φ.φ E).obj P.X) ⟶ (B.U h).obj ((Ψ.φ E).obj P.X)) :
    Rep B.innerKaroubi (Φ.innerKaroubi.obj ⟨E, P⟩) (Ψ.innerKaroubi.obj ⟨E, P⟩) :=
  ⟨M, h, h, localInverseRestriction
    ((B.innerU h).obj (((functorExtension₂ _ _).obj (Φ.φ E)).obj P))
    ((B.innerU h).obj (((functorExtension₂ _ _).obj (Ψ.φ E)).obj P)) f⟩

/-- The class of a raw arrow at its original stage with the correct descended endpoints.
Source: sketch 32, local inverse in the pair quotient
(blueprint: lem-sbc-common-stage-inverse-through-karoubi). -/
def localInverseClass (D : DescentSystem.{w, max u v, v} I)
    {A B : Diagram.{w, u, v} I} (Φ Ψ : Family A B)
    (hΦ : Φ.Coherent) (hΨ : Ψ.Coherent) (E : I) (P : Karoubi (A.C E))
    (f : (Φ.φ E).obj P.X ⟶ (Ψ.φ E).obj P.X) :
    (localInverseFunctor D Φ hΦ).obj (localInversePair D A E P) ⟶
      (localInverseFunctor D Ψ hΨ).obj (localInversePair D A E P) :=
  eqToHom ((D.formula Φ.innerKaroubi (Φ.innerCoherent hΦ)).obj _) ≫
    (D.pair B.innerKaroubi).repr
      (localInverseStageRep Φ Ψ E E (le_refl E) P ((B.U (le_refl E)).map f)) ≫
    eqToHom ((D.formula Ψ.innerKaroubi (Ψ.innerCoherent hΨ)).obj _).symm

set_option backward.isDefEq.respectTransparency.types false in
private theorem stageRep_restriction {A B : Diagram.{w, u, v} I}
    (Φ Ψ : Family A B) (E M : I) (h : E ≤ M) (P : Karoubi (A.C E))
    (f : ((Φ.innerKaroubi.φ E).obj P) ⟶ ((Ψ.innerKaroubi.φ E).obj P)) :
    localInverseStageRep Φ Ψ E M h P ((B.U h).map f.f) =
      ⟨M, h, h, (B.innerU h).map f⟩ := by
  unfold localInverseStageRep
  simp only [Rep.mk.injEq, heq_eq_eq, true_and]
  apply Karoubi.hom_ext
  dsimp [localInverseStageRep, localInverseRestriction, Diagram.innerU,
    functorExtension₂, functorExtension₁, FunctorExtension₁.obj,
    Karoubi.decompId_i, Karoubi.decompId_p]
  have hf := f.comm
  dsimp [Family.innerKaroubi, functorExtension₂, functorExtension₁,
    FunctorExtension₁.obj] at hf
  simpa only [← Functor.map_comp] using congrArg (B.U h).map hf

set_option backward.isDefEq.respectTransparency.types false in
private def descendedStageIso (D : DescentSystem.{w, max u v, v} I)
    {A B : Diagram.{w, u, v} I} (Φ Ψ : Family A B)
    (hΦ : Φ.Coherent) (hΨ : Ψ.Coherent) (E : I) (P : Karoubi (A.C E))
    (e : (Φ.innerKaroubi.φ E).obj P ≅ (Ψ.innerKaroubi.φ E).obj P) :
    (localInverseFunctor D Φ hΦ).obj (localInversePair D A E P) ≅
      (localInverseFunctor D Ψ hΨ).obj (localInversePair D A E P) :=
  eqToIso ((D.formula Φ.innerKaroubi (Φ.innerCoherent hΦ)).obj _) ≪≫
    (stageFunctor (D.pair B.innerKaroubi) (D.canonical _) E).mapIso e ≪≫
      (eqToIso ((D.formula Ψ.innerKaroubi (Ψ.innerCoherent hΨ)).obj
        (localInversePair D A E P))).symm

private theorem localInverseClass_restriction (D : DescentSystem.{w, max u v, v} I)
    {A B : Diagram.{w, u, v} I} (Φ Ψ : Family A B)
    (hΦ : Φ.Coherent) (hΨ : Ψ.Coherent) (E : I) (P : Karoubi (A.C E))
    (f : (Φ.innerKaroubi.φ E).obj P ⟶ (Ψ.innerKaroubi.φ E).obj P) :
    localInverseClass D Φ Ψ hΦ hΨ E P f.f =
      eqToHom ((D.formula Φ.innerKaroubi (Φ.innerCoherent hΦ)).obj _) ≫
        stageClass (D.pair B.innerKaroubi) E f ≫
        eqToHom ((D.formula Ψ.innerKaroubi (Ψ.innerCoherent hΨ)).obj _).symm := by
  unfold localInverseClass
  rw [stageRep_restriction]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
private theorem transformation_class (D : DescentSystem.{w, max u v, v} I)
    {A B : Diagram.{w, u, v} I} {Φ Ψ : Family A B}
    (hΦ : Φ.Coherent) (hΨ : Ψ.Coherent) (η : ∀ i, Φ.φ i ⟶ Ψ.φ i)
    (hη : Compatible η) (E : I) (P : Karoubi (A.C E)) :
    (localInverseTransformation D hΦ hΨ η hη).app (localInversePair D A E P) =
      localInverseClass D Φ Ψ hΦ hΨ E P ((η E).app P.X) := by
  have hf := D.transformation_formula (Φ.innerCoherent hΦ) (Ψ.innerCoherent hΨ)
    (innerTransformation η) (innerCompatible η hη) (localInversePair D A E P)
  rw [← conj_eqToHom_iff_heq _ _
    ((D.formula Φ.innerKaroubi (Φ.innerCoherent hΦ)).obj _)
    ((D.formula Ψ.innerKaroubi (Ψ.innerCoherent hΨ)).obj _)] at hf
  change (D.transformation _ _ _ _).app _ = _
  rw [hf]
  unfold localInverseClass
  congr 2
  dsimp only [transformationRep, localInverseStageRep, localInversePair]
  apply congrArg (D.pair B.innerKaroubi).repr
  apply congrArg (fun f ↦
    (⟨E, le_refl E, le_refl E, f⟩ : Rep B.innerKaroubi
      (Φ.innerKaroubi.obj (localInversePair D A E P))
      (Ψ.innerKaroubi.obj (localInversePair D A E P))))
  apply Karoubi.hom_ext
  dsimp [Diagram.innerKaroubi, Family.innerKaroubi, PairStructure.Obj, localInversePair,
    transformationRep, innerTransformation, localInverseStageRep,
    localInverseRestriction, Diagram.innerU, functorExtension₂, functorExtension₁,
    FunctorExtension₁.obj, FunctorExtension₁.map, Karoubi.decompId_i, Karoubi.decompId_p]
  simp only [Functor.map_comp]
  have hn := congrArg (B.U (le_refl E)).map ((η E).naturality P.p)
  simp only [Functor.map_comp] at hn
  rw [← hn, ← (B.U (le_refl E)).map_comp_assoc, ← (Φ.φ E).map_comp, P.idem]

private theorem transformation_stage (D : DescentSystem.{w, max u v, v} I)
    {A B : Diagram.{w, u, v} I} {Φ Ψ : Family A B}
    (hΦ : Φ.Coherent) (hΨ : Ψ.Coherent) (η : ∀ i, Φ.φ i ⟶ Ψ.φ i)
    (hη : Compatible η) (E : I) (P : Karoubi (A.C E)) :
    (localInverseTransformation D hΦ hΨ η hη).app (localInversePair D A E P) =
      eqToHom ((D.formula Φ.innerKaroubi (Φ.innerCoherent hΦ)).obj _) ≫
        stageClass (D.pair B.innerKaroubi) E ((innerTransformation η E).app P) ≫
        eqToHom ((D.formula Ψ.innerKaroubi (Ψ.innerCoherent hΨ)).obj _).symm := by
  exact (conj_eqToHom_iff_heq _ _
    ((D.formula Φ.innerKaroubi (Φ.innerCoherent hΦ)).obj _)
    ((D.formula Ψ.innerKaroubi (Ψ.innerCoherent hΨ)).obj _)).2
    (D.transformation_formula (Φ.innerCoherent hΦ) (Ψ.innerCoherent hΨ)
      (innerTransformation η) (innerCompatible η hη) (localInversePair D A E P))

set_option backward.isDefEq.respectTransparency.types false in
private theorem localInverseClass_sandwich (D : DescentSystem.{w, max u v, v} I)
    {A B : Diagram.{w, u, v} I} (Φ Ψ : Family A B)
    (hΦ : Φ.Coherent) (hΨ : Ψ.Coherent) (E : I) (P : Karoubi (A.C E))
    (f : (Φ.φ E).obj P.X ⟶ (Ψ.φ E).obj P.X) :
    localInverseClass D Φ Ψ hΦ hΨ E P
        (localInverseRestriction ((Φ.innerKaroubi.φ E).obj P)
          ((Ψ.innerKaroubi.φ E).obj P) f).f =
      localInverseClass D Φ Ψ hΦ hΨ E P f := by
  unfold localInverseClass
  congr 2
  unfold localInverseStageRep
  apply congrArg (D.pair B.innerKaroubi).repr
  apply congrArg (fun f ↦
    (⟨E, le_refl E, le_refl E, f⟩ : Rep B.innerKaroubi
      (Φ.innerKaroubi.obj (localInversePair D A E P))
      (Ψ.innerKaroubi.obj (localInversePair D A E P))))
  apply Karoubi.hom_ext
  dsimp [Diagram.innerKaroubi, Family.innerKaroubi, PairStructure.Obj, localInversePair,
    localInverseStageRep, localInverseRestriction, Diagram.innerU,
    functorExtension₂, functorExtension₁, FunctorExtension₁.obj,
    Karoubi.decompId_i, Karoubi.decompId_p]
  simp only [← Functor.map_comp, Category.assoc, P.idem]
  simp only [← (Φ.φ E).map_comp_assoc, P.idem]

/-- The transported raw inverse, with the prescribed comparison conjugation.
Source: sketch 32, scalar conjugations
(blueprint: lem-sbc-common-stage-inverse-through-karoubi). -/
def localInverseTransport {A B : Diagram.{w, u, v} I} (Φ Ψ : Family A B)
    {E M : I} (h : E ≤ M) (X : A.C E)
    (v : (Ψ.φ E).obj X ⟶ (Φ.φ E).obj X) :
    (Ψ.φ M).obj ((A.U h).obj X) ⟶ (Φ.φ M).obj ((A.U h).obj X) :=
  (Ψ.b h).inv.app X ≫ (B.U h).map v ≫ (Φ.b h).hom.app X

private theorem rawTransport_component {A B : Diagram.{w, u, v} I} {Φ Ψ : Family A B}
    (η : ∀ i, Φ.φ i ⟶ Ψ.φ i) (hη : Compatible η) {E M : I} (h : E ≤ M)
    (X : A.C E) :
    (η M).app ((A.U h).obj X) =
      (Φ.b h).inv.app X ≫ (B.U h).map ((η E).app X) ≫ (Ψ.b h).hom.app X := by
  rw [← cancel_epi ((Φ.b h).hom.app X)]
  simpa only [Iso.hom_inv_id_app_assoc] using hη h X

private theorem rawTransport_inverse {A B : Diagram.{w, u, v} I} {Φ Ψ : Family A B}
    (η : ∀ i, Φ.φ i ⟶ Ψ.φ i) (hη : Compatible η) {E M : I} (h : E ≤ M)
    (X : A.C E) (v : (Ψ.φ E).obj X ⟶ (Φ.φ E).obj X)
    (hav : (η E).app X ≫ v = 𝟙 _) (hva : v ≫ (η E).app X = 𝟙 _) :
    (η M).app ((A.U h).obj X) ≫ localInverseTransport Φ Ψ h X v = 𝟙 _ ∧
      localInverseTransport Φ Ψ h X v ≫ (η M).app ((A.U h).obj X) = 𝟙 _ := by
  rw [rawTransport_component η hη h X]
  constructor
  · simp only [localInverseTransport, Category.assoc, Iso.hom_inv_id_app_assoc]
    slice_lhs 2 3 => rw [← Functor.map_comp, hav, Functor.map_id]
    simp
  · simp only [localInverseTransport, Category.assoc, Iso.hom_inv_id_app_assoc]
    slice_lhs 2 3 => rw [← Functor.map_comp, hva, Functor.map_id]
    simp

private theorem identityClass_stage (D : DescentSystem.{w, max u v, v} I)
    {A B : Diagram.{w, u, v} I} (Φ Ψ : Family A B)
    (hΦ : Φ.Coherent) (hΨ : Ψ.Coherent) (E M : I) (h : E ≤ M) (X : A.C E)
    (f : (Φ.φ E).obj X ⟶ (Ψ.φ E).obj X) :
    HEq (localInverseClass D Φ Ψ hΦ hΨ E ((toKaroubi _).obj X) f)
      ((D.pair B.innerKaroubi).repr
        (localInverseStageRep Φ Ψ E M h ((toKaroubi _).obj X) ((B.U h).map f))) := by
  let P := (toKaroubi (A.C E)).obj X
  let f' : (Φ.innerKaroubi.φ E).obj P ⟶ (Ψ.innerKaroubi.φ E).obj P :=
    localInverseRestriction _ _ f
  have hf : f'.f = f := by
    dsimp [f', localInverseRestriction, P, Family.innerKaroubi, functorExtension₂,
      functorExtension₁, FunctorExtension₁.obj, Karoubi.decompId_i, Karoubi.decompId_p]
    simp
  have hc := localInverseClass_restriction D Φ Ψ hΦ hΨ E P f'
  rw [hf] at hc
  apply HEq.trans (heq_of_eq hc)
  apply HEq.trans (eqToHom_comp_heq _ _ )
  apply HEq.trans (comp_eqToHom_heq _ _)
  apply heq_of_eq
  rw [stageClass_eq _ (D.canonical _) E M h f']
  have hr := stageRep_restriction Φ Ψ E M h P f'
  rw [hf] at hr
  exact congrArg (D.pair B.innerKaroubi).repr hr.symm

/-- A raw local inverse survives inner projectors, the common-stage quotient, and arbitrary
outer projectors, with the stated transport and presentation formulas.

Source: sketch 32, lines 1291--1359 and 1412--1455, ancestor proof steps 4--6
(blueprint: lem-sbc-common-stage-inverse-through-karoubi).

Proof plan, following all ten node steps:
1. Karoubi arrow relations are equivalent to the two one-sided projector relations.
   Functor extension and restricted transformations preserve compositions and identities.
2. Restrict transitions, associators and comparisons. Naturality removes internal
   projectors in the unit, pentagon, tower and compatibility equations. The extensions
   are additive; Mathlib's Karoubi biproducts give additive stage categories.
3. Apply lem-sbc-coherent-pair-functor-descent to these extended data; its component
   formula is the class of the restricted stage transformation, also after outer extension.
4. Write e=F(p), d=G(p), a=η.app X. Naturality gives a≫d=e≫a. From the raw inverse
   identities derive d≫v=v≫e. Then (d≫v≫e) and (e≫a≫d) compose to d and e.
5. Compute these composites at E in the canonical quotient. Its inner identities are
   exactly the projector classes, so this one component has the displayed inverse.
6. Naturality at the outer projector gives the corresponding commutation for its inverse.
   Sandwiching both arrows by the outer projectors gives composites F(q) and G(q),
   which are the actual outer Karoubi identities. Identity projectors are included.
7. Compatibility gives η_M=bF.inv≫V(a)≫bG.hom. Multiply by the displayed conjugate
   inverse in either order, cancelling comparisons and using the two raw inverse laws.
8. Conjugating back gives V(a) and V(v). The unit associators identify their classes
   with those at E. This includes M=E and compares arbitrary M,N through the E class.
9. Two raw inverses coincide by v'=v'≫a≫v=v; therefore every displayed formula is
   independent of the raw inverse. Categorical inverses are unique by the same argument.
10. Outer naturality along t gives the displayed conjugation. Its proposed inverse
    cancels t and uses step 6 in both orders. Each presentation gives the same component.
-/
theorem commonStage_inverse_through_karoubi (l : ℕ) [Fact l.Prime]
    (K : Type w) [Field K] [Algebra ℚ_[l] K] [IsAlgClosure ℚ_[l] K]
    (D : DescentSystem.{w, max u v, v} (Padic.FiniteCoefficientFields l K))
    (A B : Diagram.{w, u, v} (Padic.FiniteCoefficientFields l K))
    (Φ Ψ : Family A B) (hΦ : Φ.Coherent) (hΨ : Ψ.Coherent)
    (η : ∀ E, Φ.φ E ⟶ Ψ.φ E) (hη : Compatible η)
    (E : Padic.FiniteCoefficientFields l K) (X : A.C E)
    (v : (Ψ.φ E).obj X ⟶ (Φ.φ E).obj X)
    (hav : (η E).app X ≫ v = 𝟙 _) (hva : v ≫ (η E).app X = 𝟙 _) :
    (∀ (P : Karoubi (A.C E)) (hP : P.X = X)
      (Q : Karoubi (D.pair A.innerKaroubi).Obj)
      (hQ : Q.X = localInversePair D A E P),
      ∃ e : ((functorExtension₂ _ _).obj (localInverseFunctor D Φ hΦ)).obj Q ≅
          ((functorExtension₂ _ _).obj (localInverseFunctor D Ψ hΨ)).obj Q,
        e.hom = ((functorExtension₂ _ _).map
          (localInverseTransformation D hΦ hΨ η hη)).app Q ∧
        HEq e.inv.f
          ((localInverseFunctor D Ψ hΨ).map Q.p ≫
            eqToHom (congrArg (localInverseFunctor D Ψ hΨ).obj hQ) ≫
            localInverseClass D Ψ Φ hΨ hΦ E P
              ((Ψ.φ E).map (eqToHom hP) ≫ v ≫ (Φ.φ E).map (eqToHom hP.symm)) ≫
            eqToHom (congrArg (localInverseFunctor D Φ hΦ).obj hQ.symm) ≫
            (localInverseFunctor D Φ hΦ).map Q.p) ∧
        HEq e.hom.f
          ((localInverseFunctor D Φ hΦ).map Q.p ≫
            (localInverseTransformation D hΦ hΨ η hη).app Q.X ≫
            (localInverseFunctor D Ψ hΨ).map Q.p) ∧
        HEq e.hom.f
          ((localInverseFunctor D Φ hΦ).map Q.p ≫
            eqToHom (congrArg (localInverseFunctor D Φ hΦ).obj hQ) ≫
            localInverseClass D Φ Ψ hΦ hΨ E P ((η E).app P.X) ≫
            eqToHom (congrArg (localInverseFunctor D Ψ hΨ).obj hQ.symm) ≫
            (localInverseFunctor D Ψ hΨ).map Q.p) ∧
        e.hom.f ≫ e.inv.f = (localInverseFunctor D Φ hΦ).map Q.p ∧
        e.inv.f ≫ e.hom.f = (localInverseFunctor D Ψ hΨ).map Q.p ∧
        (∀ (R : Karoubi (D.pair A.innerKaroubi).Obj) (t : Q ≅ R),
          ∃ r : ((functorExtension₂ _ _).obj (localInverseFunctor D Φ hΦ)).obj R ≅
              ((functorExtension₂ _ _).obj (localInverseFunctor D Ψ hΨ)).obj R,
            r.hom = ((functorExtension₂ _ _).map
              (localInverseTransformation D hΦ hΨ η hη)).app R ∧
            r.hom = ((functorExtension₂ _ _).obj (localInverseFunctor D Φ hΦ)).map
                t.inv ≫ e.hom ≫
              ((functorExtension₂ _ _).obj (localInverseFunctor D Ψ hΨ)).map t.hom ∧
            r.inv = ((functorExtension₂ _ _).obj (localInverseFunctor D Ψ hΨ)).map
                t.inv ≫ e.inv ≫
              ((functorExtension₂ _ _).obj (localInverseFunctor D Φ hΦ)).map t.hom)) ∧
    (∀ (M : Padic.FiniteCoefficientFields l K) (h : E ≤ M),
      (η M).app ((A.U h).obj X) ≫ localInverseTransport Φ Ψ h X v = 𝟙 _ ∧
      localInverseTransport Φ Ψ h X v ≫ (η M).app ((A.U h).obj X) = 𝟙 _ ∧
      HEq ((localInverseTransformation D hΦ hΨ η hη).app
          (localInversePair D A E ((toKaroubi _).obj X)))
        ((D.pair B.innerKaroubi).repr
          (localInverseStageRep Φ Ψ E M h ((toKaroubi _).obj X)
            ((Φ.b h).hom.app X ≫ (η M).app ((A.U h).obj X) ≫ (Ψ.b h).inv.app X))) ∧
      HEq (localInverseClass D Ψ Φ hΨ hΦ E ((toKaroubi _).obj X) v)
        ((D.pair B.innerKaroubi).repr
          (localInverseStageRep Ψ Φ E M h ((toKaroubi _).obj X)
            ((Ψ.b h).hom.app X ≫ localInverseTransport Φ Ψ h X v ≫
              (Φ.b h).inv.app X)))) ∧
    (∀ v' : (Ψ.φ E).obj X ⟶ (Φ.φ E).obj X,
      (η E).app X ≫ v' = 𝟙 _ → v' ≫ (η E).app X = 𝟙 _ → v' = v) := by
  let F := localInverseFunctor D Φ hΦ
  let G := localInverseFunctor D Ψ hΨ
  let θ := localInverseTransformation D hΦ hΨ η hη
  refine ⟨?_, ?_, ?_⟩
  · intro P hP Q hQ
    let vP := (Ψ.φ E).map (eqToHom hP) ≫ v ≫ (Φ.φ E).map (eqToHom hP.symm)
    have hvP : (η E).app P.X ≫ vP = 𝟙 _ ∧ vP ≫ (η E).app P.X = 𝟙 _ := by
      cases hP
      simpa [vP] using And.intro hav hva
    let ei := restrictedIso (η E) P vP hvP.1 hvP.2
    let e0 := descendedStageIso D Φ Ψ hΦ hΨ E P ei
    have e0hom : e0.hom = θ.app (localInversePair D A E P) := by
      rw [transformation_stage]
      rfl
    have e0inv : e0.inv = localInverseClass D Ψ Φ hΨ hΦ E P vP := by
      calc
        e0.inv = localInverseClass D Ψ Φ hΨ hΦ E P ei.inv.f :=
          by simpa only [e0, descendedStageIso, Iso.trans_inv, Functor.mapIso_inv,
            eqToIso.inv, eqToIso.hom, Iso.symm_inv, stageFunctor, Category.assoc] using
            (localInverseClass_restriction D Ψ Φ hΨ hΦ E P ei.inv).symm
        _ = localInverseClass D Ψ Φ hΨ hΦ E P vP :=
          localInverseClass_sandwich D Ψ Φ hΨ hΦ E P vP
    let eQ : F.obj Q.X ≅ G.obj Q.X :=
      eqToIso (congrArg F.obj hQ) ≪≫ e0 ≪≫ (eqToIso (congrArg G.obj hQ)).symm
    have eQhom : eQ.hom = θ.app Q.X := by
      dsimp [eQ]
      rw [e0hom]
      simpa only [eqToHom_map] using (θ.congr hQ).symm
    have eQinv : eQ.inv =
        eqToHom (congrArg G.obj hQ) ≫ localInverseClass D Ψ Φ hΨ hΦ E P vP ≫
          eqToHom (congrArg F.obj hQ.symm) := by
      dsimp [eQ]
      rw [e0inv]
      simp only [Category.assoc]
    let e := restrictedIso θ Q eQ.inv
      (by rw [← eQhom]; exact eQ.hom_inv_id)
      (by rw [← eQhom]; exact eQ.inv_hom_id)
    refine ⟨e, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · apply heq_of_eq
      change G.map Q.p ≫ eQ.inv ≫ F.map Q.p = _
      rw [eQinv]
      simp only [Category.assoc]
      rfl
    · exact heq_of_eq (extension_sandwich θ Q)
    · apply heq_of_eq
      change (((functorExtension₂ _ _).map θ).app Q).f = _
      rw [extension_sandwich, θ.congr hQ, transformation_class]
      simp only [eqToHom_map, Category.assoc]
    · exact congrArg Karoubi.Hom.f e.hom_inv_id
    · exact congrArg Karoubi.Hom.f e.inv_hom_id
    · intro R t
      let r := (((functorExtension₂ _ _).obj F).mapIso t).symm ≪≫ e ≪≫
        ((functorExtension₂ _ _).obj G).mapIso t
      refine ⟨r, ?_, rfl, ?_⟩
      rotate_left
      · simp only [r, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv,
          Functor.mapIso_hom, Category.assoc]
        rfl
      dsimp [r]
      change ((functorExtension₂ _ _).obj F).map t.inv ≫
          (((functorExtension₂ _ _).map θ).app Q) ≫
          ((functorExtension₂ _ _).obj G).map t.hom = _
      rw [← Category.assoc, ((functorExtension₂ _ _).map θ).naturality t.inv,
        Category.assoc, ← Functor.map_comp, t.inv_hom_id, Functor.map_id, Category.comp_id]
  · intro M h
    refine ⟨(rawTransport_inverse η hη h X v hav hva).1,
      (rawTransport_inverse η hη h X v hav hva).2, ?_, ?_⟩
    · rw [transformation_class]
      have hc : (Φ.b h).hom.app X ≫ (η M).app ((A.U h).obj X) ≫
          (Ψ.b h).inv.app X = (B.U h).map ((η E).app X) := by
        rw [← Category.assoc, hη h X]
        simp
      rw [hc]
      exact identityClass_stage D Φ Ψ hΦ hΨ E M h X ((η E).app X)
    · have hc : (Ψ.b h).hom.app X ≫ localInverseTransport Φ Ψ h X v ≫
          (Φ.b h).inv.app X = (B.U h).map v := by
        simp [localInverseTransport, Category.assoc]
      rw [hc]
      exact identityClass_stage D Ψ Φ hΨ hΦ E M h X v
  · intro v' hav' hva'
    calc
      v' = v' ≫ ((η E).app X ≫ v) := by rw [hav, Category.comp_id]
      _ = v := by rw [← Category.assoc, hva', Category.id_comp]


end CategoryTheory.CommonStage
