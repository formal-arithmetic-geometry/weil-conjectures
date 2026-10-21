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

/-- Additivity of the specified Karoubi extension (sketch 32, projector restriction).
(blueprint: lem-sbc-common-stage-inverse-through-karoubi).
Proof: the underlying arrow map is F.map, so its additivity is inherited from F;
the Karoubi Hom addition is the underlying addition. This is node proof step 2. -/
theorem localInverse_extension_additive {C D : Type u} [Category.{v} C] [Category.{v} D]
    [Preadditive C] [Preadditive D] (F : C ⥤ D) [F.Additive] :
    ((functorExtension₂ C D).obj F).Additive := by
  sorry

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
  sorry

/-- The left unit case for the extended associator (sketch 32).
(blueprint: lem-sbc-common-stage-inverse-through-karoubi).
Proof: restrict the original left unit equation to each projector. Its restricted
identity is the projector, the actual Karoubi identity. Node steps 1--2. -/
theorem Diagram.innerLeft (A : Diagram.{w, u, v} I) {i j : I} (h : i ≤ j) :
    A.innerAssoc (le_refl i) h =
      Functor.isoWhiskerRight (eqToIso (A.innerUnit i)) (A.innerU h) ≪≫
        (A.innerU h).leftUnitor := by
  sorry

/-- The right unit case for the extended associator (sketch 32).
(blueprint: lem-sbc-common-stage-inverse-through-karoubi).
Proof: restrict the original right unit equation; naturality and idempotence remove
internal projectors, leaving the Karoubi identity. Node steps 1--2. -/
theorem Diagram.innerRight (A : Diagram.{w, u, v} I) {i j : I} (h : i ≤ j) :
    A.innerAssoc h (le_refl j) =
      Functor.isoWhiskerLeft (A.innerU h) (eqToIso (A.innerUnit j)) ≪≫
        (A.innerU h).rightUnitor := by
  sorry

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
  sorry

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
  sorry

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
  sorry


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
  sorry

/-- Restriction of a raw arrow to two specified projectors, via the standard retract maps.
Source: sketch 32, inner and outer projector formulas
(blueprint: lem-sbc-common-stage-inverse-through-karoubi). -/
def localInverseRestriction {C : Type u} [Category.{v} C] (P Q : Karoubi C)
    (f : P.X ⟶ Q.X) : P ⟶ Q :=
  Karoubi.decompId_i P ≫ (toKaroubi C).map f ≫ Karoubi.decompId_p Q

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

/-- The transported raw inverse, with the prescribed comparison conjugation.
Source: sketch 32, scalar conjugations
(blueprint: lem-sbc-common-stage-inverse-through-karoubi). -/
def localInverseTransport {A B : Diagram.{w, u, v} I} (Φ Ψ : Family A B)
    {E M : I} (h : E ≤ M) (X : A.C E)
    (v : (Ψ.φ E).obj X ⟶ (Φ.φ E).obj X) :
    (Ψ.φ M).obj ((A.U h).obj X) ⟶ (Φ.φ M).obj ((A.U h).obj X) :=
  (Ψ.b h).inv.app X ≫ (B.U h).map v ≫ (Φ.b h).hom.app X

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
  sorry

end CategoryTheory.CommonStage
