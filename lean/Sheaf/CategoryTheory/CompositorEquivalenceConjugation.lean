module

public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.InducedCategory
public import Mathlib.CategoryTheory.Whiskering

/-! # Conjugation of arbitrary compositor and unit pastings

Source: blueprint main-20261015, sec-six-functors-basics,
sk-prop-sf-comp-coherence/det-sf-comp-coherence-cocycle.proof.md,
refinement isomorphisms; formal calculation extracted from the derived compositor proof
(blueprint: lem-sfb-compositor-equivalence-conjugation).

The helper definitions spell out the pastings in the statement, including equality
transports and functor associators and unitors. No coherence of the input data is assumed.
-/

@[expose] public section

universe uI vI uA vA uB vB

namespace CategoryTheory.CompositorEquivalenceConjugation

open CategoryTheory.Functor

variable {I : Type uI} [Category.{vI} I]
variable {A : I → Type uA} [∀ i, Category.{vA} (A i)]
variable {B : I → Type uB} [∀ i, Category.{vB} (B i)]

/-- The left triple pasting L, in diagrammatic composition order.
Source: blueprint compositor-coherence cocycle, formal refinement calculation.
(blueprint: lem-sfb-compositor-equivalence-conjugation). -/
def leftTriple (F : ∀ {i j : I}, (i ⟶ j) → (A i ⥤ A j))
    (κ : ∀ {i j k : I} (a : i ⟶ j) (b : j ⟶ k), F (a ≫ b) ≅ F a ⋙ F b)
    {i j k l : I} (a : i ⟶ j) (b : j ⟶ k) (c : k ⟶ l) :
    F ((a ≫ b) ≫ c) ≅ (F a ⋙ F b) ⋙ F c :=
  κ (a ≫ b) c ≪≫ isoWhiskerRight (κ a b) (F c)

/-- The right triple pasting P, transported to the same source and target as L.
Source: blueprint compositor-coherence cocycle, formal refinement calculation.
(blueprint: lem-sfb-compositor-equivalence-conjugation). -/
def rightTriple (F : ∀ {i j : I}, (i ⟶ j) → (A i ⥤ A j))
    (κ : ∀ {i j k : I} (a : i ⟶ j) (b : j ⟶ k), F (a ≫ b) ≅ F a ⋙ F b)
    {i j k l : I} (a : i ⟶ j) (b : j ⟶ k) (c : k ⟶ l) :
    F ((a ≫ b) ≫ c) ≅ (F a ⋙ F b) ⋙ F c :=
  eqToIso (congrArg F (Category.assoc a b c)) ≪≫ κ a (b ≫ c) ≪≫
    isoWhiskerLeft (F a) (κ b c) ≪≫ (associator (F a) (F b) (F c)).symm

/-- The left unit pasting U, using the transport a ≫ 1 = a.
Source: blueprint compositor-coherence cocycle, formal refinement calculation.
(blueprint: lem-sfb-compositor-equivalence-conjugation). -/
def leftUnit (F : ∀ {i j : I}, (i ⟶ j) → (A i ⥤ A j))
    (κ : ∀ {i j k : I} (a : i ⟶ j) (b : j ⟶ k), F (a ≫ b) ≅ F a ⋙ F b)
    (ε : ∀ i : I, F (𝟙 i) ≅ 𝟭 (A i)) {i j : I} (a : i ⟶ j) : F a ≅ F a :=
  eqToIso (congrArg F (Category.comp_id a).symm) ≪≫ κ a (𝟙 j) ≪≫
    isoWhiskerLeft (F a) (ε j) ≪≫ rightUnitor (F a)

/-- The right unit pasting V, using the transport 1 ≫ a = a.
Source: blueprint compositor-coherence cocycle, formal refinement calculation.
(blueprint: lem-sfb-compositor-equivalence-conjugation). -/
def rightUnit (F : ∀ {i j : I}, (i ⟶ j) → (A i ⥤ A j))
    (κ : ∀ {i j k : I} (a : i ⟶ j) (b : j ⟶ k), F (a ≫ b) ≅ F a ⋙ F b)
    (ε : ∀ i : I, F (𝟙 i) ≅ 𝟭 (A i)) {i j : I} (a : i ⟶ j) : F a ≅ F a :=
  eqToIso (congrArg F (Category.id_comp a).symm) ≪≫ κ (𝟙 i) a ≪≫
    isoWhiskerRight (ε i) (F a) ≪≫ leftUnitor (F a)

/-- The binary comparison b, with the three canonical associators inserted.
Source: blueprint compositor-coherence cocycle, formal refinement calculation.
(blueprint: lem-sfb-compositor-equivalence-conjugation). -/
def pairComparison (E : ∀ i : I, A i ≌ B i)
    (F : ∀ {i j : I}, (i ⟶ j) → (A i ⥤ A j))
    (G : ∀ {i j : I}, (i ⟶ j) → (B i ⥤ B j))
    (α : ∀ {i j : I} (a : i ⟶ j), F a ⋙ (E j).functor ≅ (E i).functor ⋙ G a)
    {i j k : I} (a : i ⟶ j) (b : j ⟶ k) :
    (F a ⋙ F b) ⋙ (E k).functor ≅ (E i).functor ⋙ (G a ⋙ G b) :=
  associator (F a) (F b) (E k).functor ≪≫ isoWhiskerLeft (F a) (α b) ≪≫
    (associator (F a) (E j).functor (G b)).symm ≪≫
    isoWhiskerRight (α a) (G b) ≪≫ associator (E i).functor (G a) (G b)

/-- The triple comparison B, first applying α_c, then α_b, then α_a.
Source: blueprint compositor-coherence cocycle, formal refinement calculation.
(blueprint: lem-sfb-compositor-equivalence-conjugation). -/
def tripleComparison (E : ∀ i : I, A i ≌ B i)
    (F : ∀ {i j : I}, (i ⟶ j) → (A i ⥤ A j))
    (G : ∀ {i j : I}, (i ⟶ j) → (B i ⥤ B j))
    (α : ∀ {i j : I} (a : i ⟶ j), F a ⋙ (E j).functor ≅ (E i).functor ⋙ G a)
    {i j k l : I} (a : i ⟶ j) (b : j ⟶ k) (c : k ⟶ l) :
    ((F a ⋙ F b) ⋙ F c) ⋙ (E l).functor ≅ (E i).functor ⋙ ((G a ⋙ G b) ⋙ G c) :=
  associator (F a ⋙ F b) (F c) (E l).functor ≪≫
    isoWhiskerLeft (F a ⋙ F b) (α c) ≪≫
    (associator (F a ⋙ F b) (E k).functor (G c)).symm ≪≫
    isoWhiskerRight (pairComparison E F G α a b) (G c) ≪≫
    associator (E i).functor (G a ⋙ G b) (G c)

/-- All four conjugation formulas and reflection of associativity and both unit laws.
Source: blueprint main-20261015, compositor-coherence cocycle, refinement isomorphisms;
formal calculation underlying the canonical derived identifications.

Proof: (1) Take components; the canonical associators and unitors have identity components.
Substitute equal arrows for the equality transports. (2) For L, naturality of α_c at
κ_{b,a}(x) moves E_l(F_c(κ_{b,a}(x))) past α_c. (3) Apply the pair square for (b,a),
then (c,ba); functoriality of G_c gives B E_l L = barred L α_cba.
(4) For P, apply the pair square for (c,b) at F_a x. (5) Naturality of barred κ_{c,b}
at α_a(x), followed by the pair square for (cb,a), gives B E_l P = barred P α_cba.
(6) Cancel the invertible B to obtain the two triple formulas.
(7) For U, substitute the identity square at F_a x, use naturality of barred ε_j at
α_a(x), and then use the pair square for (1_j,a). (8) For V, use naturality of α_a
at ε_i(x), substitute the identity square, and use the pair square for (a,1_i).
(9) Cancel α_a to obtain the two unit formulas. (10) If the barred paths agree, the
triple formulas give equal E_l-images. The Hom-set injectivity of equivalences
(def-sf-induced-category, Mathlib Functor.Faithful) reflects this equality.
For identity barred unit paths, cancel α_a and reflect identities in the same way.
Equality of components implies equality of natural transformations and hence of isomorphisms.
(blueprint: lem-sfb-compositor-equivalence-conjugation). -/
theorem pasting_conjugation
    (E : ∀ i : I, A i ≌ B i)
    (F : ∀ {i j : I}, (i ⟶ j) → (A i ⥤ A j))
    (G : ∀ {i j : I}, (i ⟶ j) → (B i ⥤ B j))
    (α : ∀ {i j : I} (a : i ⟶ j), F a ⋙ (E j).functor ≅ (E i).functor ⋙ G a)
    (κ : ∀ {i j k : I} (a : i ⟶ j) (b : j ⟶ k), F (a ≫ b) ≅ F a ⋙ F b)
    (κbar : ∀ {i j k : I} (a : i ⟶ j) (b : j ⟶ k), G (a ≫ b) ≅ G a ⋙ G b)
    (ε : ∀ i : I, F (𝟙 i) ≅ 𝟭 (A i))
    (εbar : ∀ i : I, G (𝟙 i) ≅ 𝟭 (B i))
    (hpair : ∀ {i j k : I} (a : i ⟶ j) (b : j ⟶ k),
      isoWhiskerRight (κ a b) (E k).functor ≪≫ pairComparison E F G α a b =
        α (a ≫ b) ≪≫ isoWhiskerLeft (E i).functor (κbar a b))
    (hid : ∀ i : I,
      isoWhiskerRight (ε i) (E i).functor ≪≫ leftUnitor (E i).functor =
        α (𝟙 i) ≪≫ isoWhiskerLeft (E i).functor (εbar i) ≪≫ rightUnitor (E i).functor) :
    (∀ {i j k l : I} (a : i ⟶ j) (b : j ⟶ k) (c : k ⟶ l),
      isoWhiskerRight (leftTriple F κ a b c) (E l).functor =
        α ((a ≫ b) ≫ c) ≪≫ isoWhiskerLeft (E i).functor (leftTriple G κbar a b c) ≪≫
          (tripleComparison E F G α a b c).symm ∧
      isoWhiskerRight (rightTriple F κ a b c) (E l).functor =
        α ((a ≫ b) ≫ c) ≪≫ isoWhiskerLeft (E i).functor (rightTriple G κbar a b c) ≪≫
          (tripleComparison E F G α a b c).symm ∧
      (leftTriple G κbar a b c = rightTriple G κbar a b c →
        leftTriple F κ a b c = rightTriple F κ a b c)) ∧
    (∀ {i j : I} (a : i ⟶ j),
      isoWhiskerRight (leftUnit F κ ε a) (E j).functor =
        α a ≪≫ isoWhiskerLeft (E i).functor (leftUnit G κbar εbar a) ≪≫ (α a).symm ∧
      isoWhiskerRight (rightUnit F κ ε a) (E j).functor =
        α a ≪≫ isoWhiskerLeft (E i).functor (rightUnit G κbar εbar a) ≪≫ (α a).symm ∧
      (leftUnit G κbar εbar a = Iso.refl (G a) →
        rightUnit G κbar εbar a = Iso.refl (G a) →
        leftUnit F κ ε a = Iso.refl (F a) ∧ rightUnit F κ ε a = Iso.refl (F a))) := by
  have hp {i j k : I} (a : i ⟶ j) (b : j ⟶ k) (x : A i) :=
    congrArg (fun e ↦ e.hom.app x) (hpair a b)
  dsimp [pairComparison] at hp
  simp only [Category.id_comp, Category.comp_id] at hp
  have hi (i : I) (x : A i) := congrArg (fun e ↦ e.hom.app x) (hid i)
  dsimp at hi
  simp only [Category.comp_id] at hi
  have ht {i j : I} (a b : i ⟶ j) (h : a = b) (x : A i) :
      (E j).functor.map ((eqToIso (congrArg F h)).hom.app x) ≫ (α b).hom.app x =
        (α a).hom.app x ≫ (eqToIso (congrArg G h)).hom.app ((E i).functor.obj x) := by
    subst b
    simp
  have hL {i j k l : I} (a : i ⟶ j) (b : j ⟶ k) (c : k ⟶ l) :
      isoWhiskerRight (leftTriple F κ a b c) (E l).functor ≪≫
          tripleComparison E F G α a b c =
        α ((a ≫ b) ≫ c) ≪≫ isoWhiskerLeft (E i).functor (leftTriple G κbar a b c) := by
    ext x
    simp only [leftTriple, tripleComparison, pairComparison, Iso.trans_hom,
      NatTrans.comp_app, isoWhiskerRight_hom, isoWhiskerLeft_hom,
      whiskerRight_app, whiskerLeft_app, associator_hom_app, associator_inv_app,
      Functor.comp_obj, Functor.map_comp, Iso.symm_hom,
      Category.id_comp, Category.comp_id, Category.assoc]
    have hn := (α c).hom.naturality ((κ a b).hom.app x)
    dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
    rw [reassoc_of% hn]
    simp only [← Functor.map_comp]
    rw [hp a b x]
    simp only [Functor.map_comp]
    simpa only [Category.assoc] using congrArg
      (fun f ↦ f ≫ (G c).map ((κbar a b).hom.app ((E i).functor.obj x)))
      (hp (a ≫ b) c x)
  have hR {i j k l : I} (a : i ⟶ j) (b : j ⟶ k) (c : k ⟶ l) :
      isoWhiskerRight (rightTriple F κ a b c) (E l).functor ≪≫
          tripleComparison E F G α a b c =
        α ((a ≫ b) ≫ c) ≪≫ isoWhiskerLeft (E i).functor (rightTriple G κbar a b c) := by
    ext x
    simp only [rightTriple, tripleComparison, pairComparison, Iso.trans_hom,
      NatTrans.comp_app, isoWhiskerRight_hom, isoWhiskerLeft_hom,
      whiskerRight_app, whiskerLeft_app, associator_hom_app, associator_inv_app,
      Functor.comp_obj, Functor.map_comp, Iso.symm_hom,
      Category.id_comp, Category.comp_id, Category.assoc]
    have hbc := congrArg
      (fun f ↦ f ≫ (G c).map ((G b).map ((α a).hom.app x))) (hp b c ((F a).obj x))
    simp only [Category.assoc] at hbc
    rw [hbc]
    have hn := (κbar b c).hom.naturality ((α a).hom.app x)
    dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
    rw [← hn]
    change (E l).functor.map ((eqToIso (congrArg F (Category.assoc a b c))).hom.app x) ≫
      (E l).functor.map ((κ a (b ≫ c)).hom.app x) ≫
      (α (b ≫ c)).hom.app ((F a).obj x) ≫ (G (b ≫ c)).map ((α a).hom.app x) ≫
      (κbar b c).hom.app ((G a).obj ((E i).functor.obj x)) = _
    calc
      _ = (E l).functor.map
            ((eqToIso (congrArg F (Category.assoc a b c))).hom.app x) ≫
          (α (a ≫ (b ≫ c))).hom.app x ≫
          (κbar a (b ≫ c)).hom.app ((E i).functor.obj x) ≫
          (κbar b c).hom.app ((G a).obj ((E i).functor.obj x)) := by
        simpa only [Category.assoc] using congrArg
          (fun f ↦ (E l).functor.map
            ((eqToIso (congrArg F (Category.assoc a b c))).hom.app x) ≫ f ≫
            (κbar b c).hom.app ((G a).obj ((E i).functor.obj x))) (hp a (b ≫ c) x)
      _ = _ := by
        simpa only [Category.assoc] using congrArg
          (fun f ↦ f ≫ (κbar a (b ≫ c)).hom.app ((E i).functor.obj x) ≫
            (κbar b c).hom.app ((G a).obj ((E i).functor.obj x)))
          (ht _ _ (Category.assoc a b c) x)
  have hU {i j : I} (a : i ⟶ j) :
      isoWhiskerRight (leftUnit F κ ε a) (E j).functor ≪≫ α a =
        α a ≪≫ isoWhiskerLeft (E i).functor (leftUnit G κbar εbar a) := by
    ext x
    simp only [leftUnit, Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom,
      isoWhiskerLeft_hom, whiskerRight_app, whiskerLeft_app, rightUnitor_hom_app,
      Functor.map_comp, Category.assoc]
    dsimp only [Functor.comp_obj, Functor.id_obj]
    simp only [Functor.map_id, Category.comp_id, Category.id_comp]
    rw [hi j ((F a).obj x)]
    simp only [Category.assoc]
    have hn := (εbar j).hom.naturality ((α a).hom.app x)
    dsimp only [Functor.id_map, Functor.comp_obj] at hn
    rw [← hn]
    change (E j).functor.map
        ((eqToIso (congrArg F (Category.comp_id a).symm)).hom.app x) ≫
      (E j).functor.map ((κ a (𝟙 j)).hom.app x) ≫
      (α (𝟙 j)).hom.app ((F a).obj x) ≫ (G (𝟙 j)).map ((α a).hom.app x) ≫
      (εbar j).hom.app ((G a).obj ((E i).functor.obj x)) = _
    calc
      _ = (E j).functor.map
            ((eqToIso (congrArg F (Category.comp_id a).symm)).hom.app x) ≫
          (α (a ≫ 𝟙 j)).hom.app x ≫ (κbar a (𝟙 j)).hom.app ((E i).functor.obj x) ≫
          (εbar j).hom.app ((G a).obj ((E i).functor.obj x)) := by
        simpa only [Category.assoc] using congrArg
          (fun f ↦ (E j).functor.map
            ((eqToIso (congrArg F (Category.comp_id a).symm)).hom.app x) ≫ f ≫
            (εbar j).hom.app ((G a).obj ((E i).functor.obj x))) (hp a (𝟙 j) x)
      _ = _ := by
        simpa only [Category.assoc] using congrArg
          (fun f ↦ f ≫ (κbar a (𝟙 j)).hom.app ((E i).functor.obj x) ≫
            (εbar j).hom.app ((G a).obj ((E i).functor.obj x)))
          (ht _ _ (Category.comp_id a).symm x)
  have hV {i j : I} (a : i ⟶ j) :
      isoWhiskerRight (rightUnit F κ ε a) (E j).functor ≪≫ α a =
        α a ≪≫ isoWhiskerLeft (E i).functor (rightUnit G κbar εbar a) := by
    ext x
    simp only [rightUnit, Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom,
      isoWhiskerLeft_hom, whiskerRight_app, whiskerLeft_app, leftUnitor_hom_app,
      Functor.map_comp, Category.assoc]
    dsimp only [Functor.comp_obj, Functor.id_obj]
    simp only [Functor.map_id, Category.comp_id, Category.id_comp]
    have hn := (α a).hom.naturality ((ε i).hom.app x)
    dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
    rw [hn]
    rw [hi i x, (G a).map_comp]
    change (E j).functor.map
        ((eqToIso (congrArg F (Category.id_comp a).symm)).hom.app x) ≫
      (E j).functor.map ((κ (𝟙 i) a).hom.app x) ≫
      (α a).hom.app ((F (𝟙 i)).obj x) ≫ (G a).map ((α (𝟙 i)).hom.app x) ≫
      (G a).map ((εbar i).hom.app ((E i).functor.obj x)) = _
    calc
      _ = (E j).functor.map
            ((eqToIso (congrArg F (Category.id_comp a).symm)).hom.app x) ≫
          (α (𝟙 i ≫ a)).hom.app x ≫ (κbar (𝟙 i) a).hom.app ((E i).functor.obj x) ≫
          (G a).map ((εbar i).hom.app ((E i).functor.obj x)) := by
        simpa only [Category.assoc] using congrArg
          (fun f ↦ (E j).functor.map
            ((eqToIso (congrArg F (Category.id_comp a).symm)).hom.app x) ≫ f ≫
            (G a).map ((εbar i).hom.app ((E i).functor.obj x))) (hp (𝟙 i) a x)
      _ = _ := by
        simpa only [Category.assoc] using congrArg
          (fun f ↦ f ≫ (κbar (𝟙 i) a).hom.app ((E i).functor.obj x) ≫
            (G a).map ((εbar i).hom.app ((E i).functor.obj x)))
          (ht _ _ (Category.id_comp a).symm x)
  have solve {i j : I} {P Q R : A i ⥤ B j}
      (a : P ≅ Q) (b : Q ≅ R) (c : P ≅ R) (h : a ≪≫ b = c) :
      a = c ≪≫ b.symm := by
    simpa only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl] using
      congrArg (fun e ↦ e ≪≫ b.symm) h
  have reflect {i j : I} {P Q : A i ⥤ A j} (e e' : P ≅ Q)
      (h : isoWhiskerRight e (E j).functor = isoWhiskerRight e' (E j).functor) :
      e = e' := by
    ext x
    apply (E j).functor.map_injective
    exact congrArg (fun t ↦ t.hom.app x) h
  constructor
  · intro i j k l a b c
    have hl := hL a b c
    have hr := hR a b c
    have hl' : isoWhiskerRight (leftTriple F κ a b c) (E l).functor =
        α ((a ≫ b) ≫ c) ≪≫ isoWhiskerLeft (E i).functor (leftTriple G κbar a b c) ≪≫
          (tripleComparison E F G α a b c).symm := by
      simpa only [Iso.trans_assoc] using solve _ _ _ hl
    have hr' : isoWhiskerRight (rightTriple F κ a b c) (E l).functor =
        α ((a ≫ b) ≫ c) ≪≫ isoWhiskerLeft (E i).functor (rightTriple G κbar a b c) ≪≫
          (tripleComparison E F G α a b c).symm := by
      simpa only [Iso.trans_assoc] using solve _ _ _ hr
    refine ⟨hl', hr', fun h ↦ reflect _ _ ?_⟩
    rw [hl', hr', h]
  · intro i j a
    have hu : isoWhiskerRight (leftUnit F κ ε a) (E j).functor =
        α a ≪≫ isoWhiskerLeft (E i).functor (leftUnit G κbar εbar a) ≪≫ (α a).symm := by
      simpa only [Iso.trans_assoc] using solve _ _ _ (hU a)
    have hv : isoWhiskerRight (rightUnit F κ ε a) (E j).functor =
        α a ≪≫ isoWhiskerLeft (E i).functor (rightUnit G κbar εbar a) ≪≫ (α a).symm := by
      simpa only [Iso.trans_assoc] using solve _ _ _ (hV a)
    refine ⟨hu, hv, fun h₁ h₂ ↦ ⟨reflect _ _ ?_, reflect _ _ ?_⟩⟩
    · rw [hu, h₁]
      simp
    · rw [hv, h₂]
      simp

end CategoryTheory.CompositorEquivalenceConjugation
