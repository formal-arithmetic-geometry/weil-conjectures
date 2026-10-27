module

public import Sheaf.CategoryTheory.StrictRoosModel
public import Sheaf.CategoryTheory.StrictRoosComparison
public import Sheaf.Paper.ExactProductFunctorStrictLimit
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryCocycle
public import Mathlib.CategoryTheory.Functor.OfSequence
import Sheaf.Paper.ExactProductFunctorRoosChainMaps
import all Sheaf.CategoryTheory.StrictRoosDerivation
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses

/-!
# Composition of normalized product, signed Roos and derived-limit comparisons

Source: Stacks Project, Tag 0941, lemma-derived-limit-is-ok and proof;
blueprint main-20261015, trace-transport, Step 1, Global powers
(blueprint: lem-trf-roos-cone-compositor-descent).

The helpers package the comparisons and the clauses of this single statement. All
products, strict cone maps, exact derived functors and localization identifications
are the recorded constructions. Index `n` denotes the paper's positive index `n+1`.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v uS vS wA wS uC vC r

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.RoosCompositor

variable {A : Type u} [Category.{v} A] [Abelian A] [HasCountableProducts A]
  {S : Type uS} [Category.{vS} S] [Abelian S]

/-- Termwise application of the given functor to unbounded complexes.
Source: Stacks 015F (blueprint: lem-trf-roos-cone-compositor-descent). -/
abbrev complex {B : Type uS} [Category.{vS} B] [Preadditive B]
    (F : B ⥤ A) [F.Additive] := F.mapHomologicalComplex (.up ℤ)

/-- The given functor applied levelwise to strict towers.
Source: Stacks 0941 (blueprint: lem-trf-roos-cone-compositor-descent). -/
abbrev tower (F : A ⥤ A) := (Functor.whiskeringRight ℕᵒᵖ A A).obj F

/-- Signed coordinates `(x,y)=(old z,-old y)` on the recorded Roos cone.
Source: Stacks 0941, signed-coordinate conversion in proof step 1
(blueprint: lem-trf-roos-cone-compositor-descent). -/
def coordinates (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ) :
    (roosF.obj X).X (p + 1) ⟶ (roosP X).X (p + 1) ⊞ (roosP X).X p :=
  (roosχ X p).hom ≫ (biprod.braiding _ _).hom ≫ biprod.map (𝟙 _) (-𝟙 _)

private def coordIso (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ) :
    (roosF.obj X).X (p + 1) ≅ (roosP X).X (p + 1) ⊞ (roosP X).X p :=
  roosχ X p ≪≫ biprod.braiding _ _ ≪≫
    ⟨biprod.map (𝟙 _) (-𝟙 _), biprod.map (𝟙 _) (-𝟙 _),
      by ext <;> simp, by ext <;> simp⟩

private lemma coordIso_hom (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ) :
    (coordIso X p).hom = coordinates X p := rfl

private lemma coord_map {X Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : X ⟶ Y) (p : ℤ) :
    (roosF.map f).f (p + 1) ≫ coordinates Y p =
      coordinates X p ≫ biprod.map ((roosPmap f).f (p + 1)) ((roosPmap f).f p) := by
  dsimp only [coordinates]
  rw [← Category.assoc, ← Category.assoc, roosF_map_χ]
  simp only [Category.assoc]
  congr 1
  apply biprod.hom_ext <;> simp [Category.assoc]

private lemma coord_inclusion [HasLimitsOfShape ℕᵒᵖ A]
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ) :
    (roosι X).f (p + 1) ≫ coordinates X p =
      biprod.lift ((Pi.lift (fun n : ℕ ↦ limit.π X.asFunctor (op n))).f (p + 1)) 0 := by
  dsimp only [coordinates]
  rw [← Category.assoc, ← Category.assoc, roosι_χ]
  apply biprod.hom_ext <;> simp [Category.assoc]

private lemma coord_canonical (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ) :
    coordinates X p =
      ((CochainComplex.mappingCone (roosU X)).shiftFunctorObjXIso
        (-1) (p + 1) p (add_neg_cancel_right p 1).symm).hom ≫
      (HomologicalComplex.homotopyCofiber.XIsoBiprod (roosU X) p (p + 1) rfl).hom ≫
      biprod.map (𝟙 _) (-𝟙 _) := by
  simp only [coordinates, roosχ, Iso.trans_hom, Category.assoc]
  rw [← Category.assoc (biprod.braiding _ _).hom]
  have hb {V W : A} : (biprod.braiding V W).hom ≫ (biprod.braiding W V).hom = 𝟙 _ := by
    apply biprod.hom_ext <;> simp
  rw [hb, Category.id_comp]

private lemma coord_d (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ) :
    (roosF.obj X).d (p + 1) (p + 1 + 1) ≫ coordinates X (p + 1) =
      coordinates X p ≫ biprod.desc
        (biprod.lift ((roosP X).d (p + 1) (p + 1 + 1)) ((roosU X).f (p + 1)))
        (biprod.lift 0 (-((roosP X).d p (p + 1)))) := by
  let eS (p : ℤ) := (CochainComplex.mappingCone (roosU X)).shiftFunctorObjXIso
    (-1) (p + 1) p (add_neg_cancel_right p 1).symm
  have hd : (roosF.obj X).d (p + 1) (p + 1 + 1) ≫ (eS (p + 1)).hom =
      -(eS p).hom ≫ (CochainComplex.mappingCone (roosU X)).d p (p + 1) := by
    dsimp only [roosF, Functor.comp_obj, roosConeFunctor, eS,
      CochainComplex.shiftFunctorObjXIso]
    simp only [CochainComplex.shiftFunctor_obj_d', Int.negOnePow_neg,
      Int.negOnePow_one, Units.neg_smul, one_smul, Preadditive.neg_comp,
      HomologicalComplex.d_comp_XIsoOfEq_hom,
      HomologicalComplex.XIsoOfEq_hom_comp_d]
  have hs (r q : ℤ) (hq : (ComplexShape.up ℤ).Rel r q) :
      HomologicalComplex.homotopyCofiber.sndX (roosU X) r =
        (HomologicalComplex.homotopyCofiber.XIsoBiprod (roosU X) r q hq).hom ≫
          biprod.snd := by
    obtain rfl := (ComplexShape.up ℤ).next_eq' hq
    simp only [HomologicalComplex.homotopyCofiber.sndX, dif_pos hq]
  simp only [coord_canonical]
  rw [← Category.assoc, hd]
  apply biprod.hom_ext
  · simp only [Category.assoc, biprod.map_fst, Category.comp_id,
      Preadditive.neg_comp, biprod.desc_eq, Preadditive.add_comp, biprod.lift_fst,
      comp_zero, add_zero, biprod.map_fst_assoc]
    have h := HomologicalComplex.homotopyCofiber.d_fstX (roosU X) p (p + 1)
      (p + 1 + 1) rfl rfl
    have h' := congrArg (fun f ↦ -(eS p).hom ≫ f) h
    simp only [HomologicalComplex.homotopyCofiber.fstX, Category.assoc,
      Preadditive.comp_neg, neg_neg] at h'
    convert h' using 1 <;> simp only [roosF, Functor.comp_obj, roosConeFunctor,
      CochainComplex.mappingCone, eS, Category.id_comp] <;> rfl
  · simp only [Category.assoc, biprod.map_snd, Preadditive.comp_neg,
      Category.comp_id, Preadditive.neg_comp, neg_neg, biprod.desc_eq,
      Preadditive.add_comp, biprod.lift_snd,
      Preadditive.comp_add, biprod.map_fst_assoc, biprod.map_snd_assoc]
    have h := HomologicalComplex.homotopyCofiber.d_sndX (roosU X) p (p + 1) rfl
    simp only [hs p (p + 1) rfl, hs (p + 1) (p + 1 + 1) rfl,
      HomologicalComplex.homotopyCofiber.fstX, Category.assoc] at h
    change (eS p).hom ≫ HomologicalComplex.homotopyCofiber.d (roosU X) p (p + 1) ≫
      (HomologicalComplex.homotopyCofiber.XIsoBiprod (roosU X)
        (p + 1) (p + 1 + 1) rfl).hom ≫ biprod.snd = _
    rw [h]
    simp only [Preadditive.comp_add, Category.id_comp]
    rfl

attribute [local irreducible] coordinates coordIso roosF roosConeFunctor

private def productFunctor :
    CochainComplex (ℕᵒᵖ ⥤ A) ℤ ⥤ CochainComplex A ℤ where
  obj := roosP
  map := roosPmap
  map_id := roosPmap_id
  map_comp := roosPmap_comp

private lemma product_ext {X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} {p : ℤ} {V : A}
    {f g : V ⟶ (roosP X).X p}
    (h : ∀ n : ℕ, f ≫ (Pi.π (fun n : ℕ ↦ X.asFunctor.obj (op n)) n).f p =
      g ≫ (Pi.π (fun n : ℕ ↦ X.asFunctor.obj (op n)) n).f p) : f = g := by
  let E := HomologicalComplex.eval A (.up ℤ) p
  exact (Fan.isLimitMapConeEquiv E _ _ (isLimitOfPreserves E (productIsProduct _))).hom_ext
    (fun n ↦ h n.as)

private abbrev complexB (U : S ⥤ ℕᵒᵖ ⥤ A) [U.Additive]
    (F : A ⥤ A) [F.Additive] (G : S ⥤ S) [G.Additive]
    (b : U ⋙ tower F ≅ G ⋙ U) :
    complex U ⋙ complex (tower F) ≅ complex G ⋙ complex U :=
  (Functor.mapHomologicalComplexCompIso b (.up ℤ))

@[irreducible] private def productIso (U : S ⥤ ℕᵒᵖ ⥤ A) [U.Additive]
    (F : A ⥤ A) [F.Additive] [PreservesLimitsOfShape (Discrete ℕ) F]
    (G : S ⥤ S) [G.Additive] (b : U ⋙ tower F ≅ G ⋙ U)
    (M : CochainComplex S ℤ) :
    (complex F).obj (roosP ((complex U).obj M)) ≅
      roosP ((complex U).obj ((complex G).obj M)) :=
  asIso (piComparison (complex F)
    (fun n : ℕ ↦ ((complex U).obj M).asFunctor.obj (op n))) ≪≫
    (productFunctor (A := A)).mapIso ((complexB U F G b).app M)

@[reassoc] private lemma productIso_π (U : S ⥤ ℕᵒᵖ ⥤ A) [U.Additive]
    (F : A ⥤ A) [F.Additive] [PreservesLimitsOfShape (Discrete ℕ) F]
    (G : S ⥤ S) [G.Additive] (b : U ⋙ tower F ≅ G ⋙ U)
    (M : CochainComplex S ℤ) (n : ℕ) :
    (productIso U F G b M).hom ≫ Pi.π
      (fun k : ℕ ↦ ((complex U).obj ((complex G).obj M)).asFunctor.obj (op k)) n =
      (complex F).map
        (Pi.π (fun k : ℕ ↦ ((complex U).obj M).asFunctor.obj (op k)) n) ≫
      (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
        ((NatIso.mapHomologicalComplex b (.up ℤ)).hom.app M)).app (op n) := by
  simp only [productIso, Iso.trans_hom, asIso_hom, Functor.mapIso_hom,
    productFunctor, roosPmap, Functor.comp_obj, Category.assoc, Pi.map_π]
  change piComparison (complex F)
      (fun n : ℕ ↦ ((complex U).obj M).asFunctor.obj (op n)) ≫ Pi.π _ n ≫ _ = _
  simp only [piComparison_comp_π_assoc]
  ext p
  rfl

private lemma productIso_natural (U : S ⥤ ℕᵒᵖ ⥤ A) [U.Additive]
    (F : A ⥤ A) [F.Additive] [PreservesLimitsOfShape (Discrete ℕ) F]
    (G : S ⥤ S) [G.Additive] (b : U ⋙ tower F ≅ G ⋙ U)
    {M M' : CochainComplex S ℤ} (f : M ⟶ M') :
    (complex F).map (roosPmap ((complex U).map f)) ≫ (productIso U F G b M').hom =
      (productIso U F G b M).hom ≫ roosPmap ((complex U).map ((complex G).map f)) := by
  apply Pi.hom_ext
  intro n
  simp only [Category.assoc, productIso_π, productIso_π_assoc, roosPmap, Pi.map_π]
  rw [← Category.assoc, ← Functor.map_comp, Pi.map_π, Functor.map_comp, Category.assoc]
  ext p
  have h := NatTrans.congr_app (b.hom.naturality (f.f p)) (op n)
  dsimp at h ⊢
  simpa only [Category.assoc] using congrArg (fun z ↦ F.map
    ((Pi.π (fun k : ℕ ↦ ((complex U).obj M).asFunctor.obj (op k)) n).f p) ≫ z) h

private lemma productIso_shift (U : S ⥤ ℕᵒᵖ ⥤ A) [U.Additive]
    (F : A ⥤ A) [F.Additive] [PreservesLimitsOfShape (Discrete ℕ) F]
    (G : S ⥤ S) [G.Additive] (b : U ⋙ tower F ≅ G ⋙ U)
    (M : CochainComplex S ℤ) :
    (complex F).map (towerProductShift
      (fun n : ℕ ↦ ((complex U).obj M).asFunctor.map (homOfLE (Nat.le_succ n)).op)) ≫
        (productIso U F G b M).hom =
      (productIso U F G b M).hom ≫ towerProductShift
        (fun n : ℕ ↦ ((complex U).obj ((complex G).obj M)).asFunctor.map
          (homOfLE (Nat.le_succ n)).op) := by
  apply Pi.hom_ext
  intro n
  simp only [Category.assoc, productIso_π, towerProductShift, Pi.lift_π]
  rw [← Category.assoc, ← Functor.map_comp, Pi.lift_π, Functor.map_comp, Category.assoc]
  rw [productIso_π_assoc]
  ext p
  have h := (b.hom.app (M.X p)).naturality (homOfLE (Nat.le_succ n)).op
  dsimp at h ⊢
  simpa only [Category.assoc] using congrArg (fun z ↦ F.map
    ((Pi.π (fun k : ℕ ↦ ((complex U).obj M).asFunctor.obj (op k)) (n + 1)).f p) ≫ z) h

private lemma productIso_compositor (U : S ⥤ ℕᵒᵖ ⥤ A) [U.Additive]
    (F : Fin 3 → A ⥤ A) [∀ i, (F i).Additive]
    [∀ i, PreservesLimitsOfShape (Discrete ℕ) (F i)]
    (G : Fin 3 → S ⥤ S) [∀ i, (G i).Additive]
    (b : ∀ i, U ⋙ tower (F i) ≅ G i ⋙ U)
    (d : F 0 ⋙ F 1 ≅ F 2) (t : G 0 ⋙ G 1 ≅ G 2)
    (hb : ∀ M : S,
      (Functor.whiskerLeft (U.obj M) d.hom) ≫ (b 2).hom.app M =
        (tower (F 1)).map ((b 0).hom.app M) ≫
          (b 1).hom.app ((G 0).obj M) ≫ U.map (t.hom.app M))
    (M : CochainComplex S ℤ) :
    (Functor.mapHomologicalComplexCompIso d (.up ℤ)).hom.app
        (roosP ((complex U).obj M)) ≫ (productIso U (F 2) (G 2) (b 2) M).hom =
      (complex (F 1)).map (productIso U (F 0) (G 0) (b 0) M).hom ≫
        (productIso U (F 1) (G 1) (b 1) ((complex (G 0)).obj M)).hom ≫
        roosPmap ((complex U).map
          ((Functor.mapHomologicalComplexCompIso t (.up ℤ)).hom.app M)) := by
  apply Pi.hom_ext
  intro n
  simp only [Category.assoc, productIso_π, roosPmap, Pi.map_π]
  rw [productIso_π_assoc]
  erw [← Functor.map_comp_assoc, productIso_π, Functor.map_comp, Category.assoc]
  ext p
  have h := NatTrans.congr_app (hb (M.X p)) (op n)
  have hn := d.hom.naturality
    ((Pi.π (fun k : ℕ ↦ ((complex U).obj M).asFunctor.obj (op k)) n).f p)
  dsimp at h hn ⊢
  erw [← Category.assoc, ← hn, Category.assoc, h]

variable [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ A)]
  [HasDerivedCategory.{wS} S]
  (U : S ⥤ ℕᵒᵖ ⥤ A) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  (F : Fin 3 → A ⥤ A) [∀ i, (F i).Additive]
  [∀ i, PreservesFiniteLimits (F i)] [∀ i, PreservesFiniteColimits (F i)]
  (G : Fin 3 → S ⥤ S) [∀ i, (G i).Additive]
  [∀ i, PreservesFiniteLimits (G i)] [∀ i, PreservesFiniteColimits (G i)]
  (RL : DerivedCategory.{wA} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{wA} A)

/-- The specified functor `L = Rlim ∘ U` on the ordinary unbounded derived category.
Source: Stacks 0941 (blueprint: lem-trf-roos-cone-compositor-descent). -/
abbrev total := U.mapDerivedCategory ⋙ RL

/-- The four simultaneous comparisons whose properties this node asserts.
The fields carry no arbitrary comparison assumptions: the theorem below supplies
these data with every projection, coordinate, normalization and compositor equation.
Source: Stacks 0941 and blueprint Global powers
(blueprint: lem-trf-roos-cone-compositor-descent). -/
structure Comparisons where
  /-- Normalized comparison from total derived limit to the actual strict Roos model. -/
  theta : DerivedCategory.Q.{wA} ⋙ RL ≅ roosF ⋙ DerivedCategory.Q.{wA}
  /-- Canonical product comparison, subsequently fixed by all its projections. -/
  psi : ∀ (i : Fin 3) (M : CochainComplex S ℤ),
    (complex (F i)).obj (roosP ((complex U).obj M)) ≅
      roosP ((complex U).obj ((complex (G i)).obj M))
  /-- Natural chain isomorphism with the same product map on both signed coordinates. -/
  kappa : ∀ i : Fin 3,
    complex U ⋙ roosF ⋙ complex (F i) ≅ complex (G i) ⋙ complex U ⋙ roosF
  /-- Natural comparison on all objects and morphisms of the unbounded derived category. -/
  a : ∀ i : Fin 3,
    total U RL ⋙ (F i).mapDerivedCategory ≅ (G i).mapDerivedCategory ⋙ total U RL

variable (N : Comparisons U F G RL)

/-- Localization transport from `L[M]` to the strict Roos complex of `UM`.
Source: Stacks 015F, 0941 (blueprint: lem-trf-roos-cone-compositor-descent). -/
def toRoos (M : CochainComplex S ℤ) :
    (total U RL).obj (DerivedCategory.Q.obj M) ⟶
      DerivedCategory.Q.obj (roosF.obj ((complex U).obj M)) :=
  RL.map (U.mapDerivedCategoryFactors.hom.app M) ≫ N.theta.hom.app ((complex U).obj M)

/-- The prescribed canonical product projections, strict naturality and shift square.
Source: Stacks 0941, proof steps 2-3
(blueprint: lem-trf-roos-cone-compositor-descent). -/
def HasProducts (b : ∀ i : Fin 3, U ⋙ tower (F i) ≅ G i ⋙ U) : Prop :=
  (∀ (i : Fin 3) (M : CochainComplex S ℤ) (n : ℕ),
    (N.psi i M).hom ≫ Pi.π
      (fun k : ℕ ↦ ((complex U).obj ((complex (G i)).obj M)).asFunctor.obj (op k)) n =
      (complex (F i)).map
        (Pi.π (fun k : ℕ ↦ ((complex U).obj M).asFunctor.obj (op k)) n) ≫
      (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
        ((NatIso.mapHomologicalComplex (b i) (.up ℤ)).hom.app M)).app (op n)) ∧
  (∀ (i : Fin 3) {M M' : CochainComplex S ℤ} (f : M ⟶ M'),
    (complex (F i)).map (roosPmap ((complex U).map f)) ≫ (N.psi i M').hom =
      (N.psi i M).hom ≫ roosPmap ((complex U).map ((complex (G i)).map f))) ∧
  (∀ (i : Fin 3) (M : CochainComplex S ℤ),
    (complex (F i)).map (towerProductShift
      (fun n : ℕ ↦ ((complex U).obj M).asFunctor.map (homOfLE (Nat.le_succ n)).op)) ≫
        (N.psi i M).hom =
      (N.psi i M).hom ≫ towerProductShift
        (fun n : ℕ ↦ ((complex U).obj ((complex (G i)).obj M)).asFunctor.map
          (homOfLE (Nat.le_succ n)).op))

/-- Both complete projection equations for the signed diagonal chain isomorphism.
Together these prescribe both diagonal entries and zero off-diagonal entries.
Source: Stacks 0941, proof step 3
(blueprint: lem-trf-roos-cone-compositor-descent). -/
def HasDiagonal : Prop :=
  ∀ (i : Fin 3) (M : CochainComplex S ℤ) (p : ℤ),
    (((N.kappa i).hom.app M).f (p + 1) ≫
      coordinates ((complex U).obj ((complex (G i)).obj M)) p ≫ biprod.fst =
      (F i).map (coordinates ((complex U).obj M) p ≫ biprod.fst) ≫
        (N.psi i M).hom.f (p + 1)) ∧
    (((N.kappa i).hom.app M).f (p + 1) ≫
      coordinates ((complex U).obj ((complex (G i)).obj M)) p ≫ biprod.snd =
      (F i).map (coordinates ((complex U).obj M) p ≫ biprod.snd) ≫
        (N.psi i M).hom.f p)

/-- The signed differential and the whole strict-map action in those coordinates.
This is a clause about the recorded cone, not a new complex construction.
Source: Stacks 0941, proof steps 1 and 3
(blueprint: lem-trf-roos-cone-compositor-descent). -/
def HasSignedCoordinates : Prop :=
  (∀ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ),
    (roosF.obj X).d (p + 1) (p + 1 + 1) ≫ coordinates X (p + 1) =
      coordinates X p ≫ biprod.desc
        (biprod.lift ((roosP X).d (p + 1) (p + 1 + 1)) ((roosU X).f (p + 1)))
        (biprod.lift 0 (-((roosP X).d p (p + 1))))) ∧
  (∀ {X Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : X ⟶ Y) (p : ℤ),
    (roosF.map f).f (p + 1) ≫ coordinates Y p =
      coordinates X p ≫ biprod.map ((roosPmap f).f (p + 1)) ((roosPmap f).f p))

/-- Normalization by the actual ordinary-limit inclusion on every K-injective tower.
Its signed coordinates are `(iota,0)` and its localization is the specified unit.
Source: Stacks 0941, proof steps 1 and 6
(blueprint: lem-trf-roos-cone-compositor-descent). -/
def HasNormalization [HasLimitsOfShape ℕᵒᵖ A]
    (eta : roosLimitFunctor ⋙ DerivedCategory.Q.{wA} ⟶ DerivedCategory.Q.{wA} ⋙ RL) : Prop :=
  ∀ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [I.IsKInjective],
    QuasiIso (roosι I) ∧
    (∀ p : ℤ, (roosι I).f (p + 1) ≫ coordinates I p =
      biprod.lift ((Pi.lift (fun n : ℕ ↦ limit.π I.asFunctor (op n))).f (p + 1)) 0) ∧
    eta.app I ≫ N.theta.hom.app I = DerivedCategory.Q.map (roosι I)

/-- The conjugation formula, with all exact-functor localization identifications.
Since `a` is a natural isomorphism, this also specifies descent on all derived maps.
Source: Stacks 0941, proof steps 6-7
(blueprint: lem-trf-roos-cone-compositor-descent). -/
def HasDerivedModel : Prop :=
  ∀ (i : Fin 3) (M : CochainComplex S ℤ),
    (N.a i).hom.app (DerivedCategory.Q.obj M) ≫
        (total U RL).map ((G i).mapDerivedCategoryFactors.hom.app M) ≫
        toRoos U F G RL N ((complex (G i)).obj M) =
      (F i).mapDerivedCategory.map (toRoos U F G RL N M) ≫
        (F i).mapDerivedCategoryFactors.hom.app (roosF.obj ((complex U).obj M)) ≫
        DerivedCategory.Q.map ((N.kappa i).hom.app M)

/-- The three compositor equations, as equalities of entire strict or derived maps.
The second equation retains both signed coordinates; it is not a cohomology-only claim.
Source: Stacks 0941 and blueprint Global powers, proof steps 4, 5 and 8
(blueprint: lem-trf-roos-cone-compositor-descent). -/
def HasCompositors (d : F 0 ⋙ F 1 ≅ F 2) (t : G 0 ⋙ G 1 ≅ G 2) : Prop :=
  (∀ M : CochainComplex S ℤ,
    (Functor.mapHomologicalComplexCompIso d (.up ℤ)).hom.app
        (roosP ((complex U).obj M)) ≫ (N.psi 2 M).hom =
      (complex (F 1)).map (N.psi 0 M).hom ≫
        (N.psi 1 ((complex (G 0)).obj M)).hom ≫
        roosPmap ((complex U).map
          ((Functor.mapHomologicalComplexCompIso t (.up ℤ)).hom.app M))) ∧
  (∀ M : CochainComplex S ℤ,
    (Functor.mapHomologicalComplexCompIso d (.up ℤ)).hom.app
        (roosF.obj ((complex U).obj M)) ≫ (N.kappa 2).hom.app M =
      (complex (F 1)).map ((N.kappa 0).hom.app M) ≫
        (N.kappa 1).hom.app ((complex (G 0)).obj M) ≫
        roosF.map ((complex U).map
          ((Functor.mapHomologicalComplexCompIso t (.up ℤ)).hom.app M))) ∧
  (∀ M : DerivedCategory.{wS} S,
    (Functor.mapDerivedCategoryCompNatIso d).hom.app ((total U RL).obj M) ≫
        (N.a 2).hom.app M =
      (F 1).mapDerivedCategory.map ((N.a 0).hom.app M) ≫
        (N.a 1).hom.app ((G 0).mapDerivedCategory.obj M) ≫
        (total U RL).map ((Functor.mapDerivedCategoryCompNatIso t).hom.app M))

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

@[irreducible] private def transportIso : DerivedCategory.Q.{wS} ⋙ total U RL ≅
    complex U ⋙ roosF ⋙ DerivedCategory.Q.{wA} :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight U.mapDerivedCategoryFactors RL ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft (complex U) N.theta

private lemma transportIso_hom (M : CochainComplex S ℤ) :
    (transportIso U F G RL N).hom.app M = toRoos U F G RL N M := by
  simp [transportIso, toRoos]

private lemma transport_natural {M M' : CochainComplex S ℤ} (f : M ⟶ M') :
    (total U RL).map (DerivedCategory.Q.map f) ≫ toRoos U F G RL N M' =
      toRoos U F G RL N M ≫ DerivedCategory.Q.map (roosF.map ((complex U).map f)) := by
  simpa only [transportIso_hom, Functor.comp_obj, Functor.comp_map] using
    (transportIso U F G RL N).hom.naturality f

private lemma derived_compositor
    (d : F 0 ⋙ F 1 ≅ F 2) (t : G 0 ⋙ G 1 ≅ G 2)
    (hm : HasDerivedModel U F G RL N)
    (hc : ∀ M : CochainComplex S ℤ,
      (Functor.mapHomologicalComplexCompIso d (.up ℤ)).hom.app
          (roosF.obj ((complex U).obj M)) ≫ (N.kappa 2).hom.app M =
        (complex (F 1)).map ((N.kappa 0).hom.app M) ≫
          (N.kappa 1).hom.app ((complex (G 0)).obj M) ≫
          roosF.map ((complex U).map
            ((Functor.mapHomologicalComplexCompIso t (.up ℤ)).hom.app M))) :
    ∀ M : DerivedCategory.{wS} S,
      (Functor.mapDerivedCategoryCompNatIso d).hom.app ((total U RL).obj M) ≫
          (N.a 2).hom.app M =
        (F 1).mapDerivedCategory.map ((N.a 0).hom.app M) ≫
          (N.a 1).hom.app ((G 0).mapDerivedCategory.obj M) ≫
          (total U RL).map ((Functor.mapDerivedCategoryCompNatIso t).hom.app M) := by
  let L := total U RL
  let DD := Functor.mapDerivedCategoryCompNatIso d
  let TT := Functor.mapDerivedCategoryCompNatIso t
  suffices h : Functor.whiskerLeft L DD.hom ≫ (N.a 2).hom =
      Functor.whiskerRight (N.a 0).hom (F 1).mapDerivedCategory ≫
        Functor.whiskerLeft (G 0).mapDerivedCategory (N.a 1).hom ≫
        Functor.whiskerRight TT.hom L from fun M ↦ congr_app h M
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso S (.up ℤ))
  intro M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  have : IsIso (toRoos U F G RL N ((complex (G 2)).obj M)) := by
    rw [← transportIso_hom]
    infer_instance
  apply (cancel_mono
    (L.map ((G 2).mapDerivedCategoryFactors.hom.app M) ≫
      toRoos U F G RL N ((complex (G 2)).obj M))).1
  simp only [Category.assoc]
  rw [hm 2 M]
  have ht := Functor.mapDerivedCategoryCompNatIso_hom_app_Q t M
  have heq : Functor.mapHomologicalComplexCompIsoHomOfIso t M =
      (Functor.mapHomologicalComplexCompIso t (.up ℤ)).hom.app M := by
    ext p
    simp [Functor.mapHomologicalComplexCompIsoHomOfIso]
  rw [heq] at ht
  have hd := Functor.mapDerivedCategoryCompNatIso_hom_app_Q d
    (roosF.obj ((complex U).obj M))
  have heqd : Functor.mapHomologicalComplexCompIsoHomOfIso d
      (roosF.obj ((complex U).obj M)) =
      (Functor.mapHomologicalComplexCompIso d (.up ℤ)).hom.app
        (roosF.obj ((complex U).obj M)) := by
    ext p
    simp [Functor.mapHomologicalComplexCompIsoHomOfIso]
  rw [heqd] at hd
  have hn := (N.a 1).hom.naturality ((G 0).mapDerivedCategoryFactors.hom.app M)
  change (F 1).mapDerivedCategory.map (L.map ((G 0).mapDerivedCategoryFactors.hom.app M)) ≫
      (N.a 1).hom.app (DerivedCategory.Q.obj ((complex (G 0)).obj M)) =
    (N.a 1).hom.app ((G 0).mapDerivedCategory.obj (DerivedCategory.Q.obj M)) ≫
      L.map ((G 1).mapDerivedCategory.map ((G 0).mapDerivedCategoryFactors.hom.app M)) at hn
  have hf := (F 1).mapDerivedCategoryFactors.hom.naturality ((N.kappa 0).hom.app M)
  dsimp only [Functor.comp_map] at hf
  rw [← L.map_comp_assoc, ht, L.map_comp, L.map_comp]
  simp only [Category.assoc]
  rw [transport_natural, ← reassoc_of% hn]
  erw [reassoc_of% (hm 1 ((complex (G 0)).obj M))]
  rw [← (F 1).mapDerivedCategory.map_comp_assoc,
    ← (F 1).mapDerivedCategory.map_comp_assoc]
  simp only [Category.assoc]
  erw [hm 0 M]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hf]
  rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp, ← hc M]
  rw [DerivedCategory.Q.map_comp]
  rw [← reassoc_of% hd]
  have hdτ := DD.hom.naturality (toRoos U F G RL N M)
  dsimp only [Functor.comp_map] at hdτ
  erw [← reassoc_of% hdτ]

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private lemma cone_compositor
    (b : ∀ i : Fin 3, U ⋙ tower (F i) ≅ G i ⋙ U)
    [∀ i, PreservesLimitsOfShape (Discrete ℕ) (F i)]
    (d : F 0 ⋙ F 1 ≅ F 2) (t : G 0 ⋙ G 1 ≅ G 2)
    (hb : ∀ M : S,
      (Functor.whiskerLeft (U.obj M) d.hom) ≫ (b 2).hom.app M =
        (tower (F 1)).map ((b 0).hom.app M) ≫
          (b 1).hom.app ((G 0).obj M) ≫ U.map (t.hom.app M))
    (hd : HasDiagonal U F G RL N)
    (hp : ∀ (i : Fin 3) (M : CochainComplex S ℤ),
      N.psi i M = productIso U (F i) (G i) (b i) M) (M : CochainComplex S ℤ) :
    (Functor.mapHomologicalComplexCompIso d (.up ℤ)).hom.app
        (roosF.obj ((complex U).obj M)) ≫ (N.kappa 2).hom.app M =
      (complex (F 1)).map ((N.kappa 0).hom.app M) ≫
        (N.kappa 1).hom.app ((complex (G 0)).obj M) ≫
        roosF.map ((complex U).map
          ((Functor.mapHomologicalComplexCompIso t (.up ℤ)).hom.app M)) := by
  have hc := productIso_compositor U F G b d t hb M
  simp only [← hp] at hc
  apply HomologicalComplex.Hom.ext
  funext q
  obtain ⟨p, hq⟩ := (Equiv.addRight (1 : ℤ)).surjective q
  change p + 1 = q at hq
  subst q
  apply (cancel_mono (coordIso (A := A) ((complex U).obj ((complex (G 2)).obj M)) p).hom).1
  simp only [coordIso_hom]
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    Functor.mapHomologicalComplexCompIso_hom_app_f, Category.assoc]
  apply biprod.hom_ext
  · simp only [Category.assoc]
    erw [(hd 2 M p).1, ← Category.assoc, ← (d.hom.naturality _)]
    dsimp only [Functor.comp_map]
    rw [Category.assoc]
    have hc' := congrArg (fun z ↦ z.f (p + 1)) hc
    simp only [HomologicalComplex.comp_f,
      Functor.mapHomologicalComplexCompIso_hom_app_f,
      Functor.mapHomologicalComplex_map_f] at hc'
    rw [hc']
    erw [reassoc_of% (coord_map _ p), biprod.map_fst]
    erw [reassoc_of% (hd 1 ((complex (G 0)).obj M) p).1]
    have h₀ := congrArg (fun z ↦ (F 1).map z) (hd 0 M p).1
    simp only [Functor.map_comp, Category.assoc] at h₀ ⊢
    simpa only [Category.assoc] using congrArg
      (fun z ↦ z ≫ (N.psi 1 ((complex (G 0)).obj M)).hom.f (p + 1) ≫
        (roosPmap ((complex U).map
          ((Functor.mapHomologicalComplexCompIso t (.up ℤ)).hom.app M))).f (p + 1)) h₀.symm
  · simp only [Category.assoc]
    erw [(hd 2 M p).2, ← Category.assoc, ← (d.hom.naturality _)]
    dsimp only [Functor.comp_map]
    rw [Category.assoc]
    have hc' := congrArg (fun z ↦ z.f p) hc
    simp only [HomologicalComplex.comp_f,
      Functor.mapHomologicalComplexCompIso_hom_app_f,
      Functor.mapHomologicalComplex_map_f] at hc'
    rw [hc']
    erw [reassoc_of% (coord_map _ p), biprod.map_snd]
    erw [reassoc_of% (hd 1 ((complex (G 0)).obj M) p).2]
    have h₀ := congrArg (fun z ↦ (F 1).map z) (hd 0 M p).2
    simp only [Functor.map_comp, Category.assoc] at h₀ ⊢
    simpa only [Category.assoc] using congrArg
      (fun z ↦ z ≫ (N.psi 1 ((complex (G 0)).obj M)).hom.f p ≫
        (roosPmap ((complex U).map
          ((Functor.mapHomologicalComplexCompIso t (.up ℤ)).hom.app M))).f p) h₀.symm

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private theorem descendComparison
    (θ : DerivedCategory.Q.{wA} ⋙ RL ≅ roosF ⋙ DerivedCategory.Q.{wA})
    (k : ∀ i : Fin 3,
      complex U ⋙ roosF ⋙ complex (F i) ≅ complex (G i) ⋙ complex U ⋙ roosF) :
    ∃ a : ∀ i : Fin 3,
      total U RL ⋙ (F i).mapDerivedCategory ≅ (G i).mapDerivedCategory ⋙ total U RL,
      ∀ (i : Fin 3) (M : CochainComplex S ℤ),
      (a i).hom.app (DerivedCategory.Q.obj M) ≫
          (total U RL).map ((G i).mapDerivedCategoryFactors.hom.app M) ≫
          (RL.map (U.mapDerivedCategoryFactors.hom.app ((complex (G i)).obj M)) ≫
            θ.hom.app ((complex U).obj ((complex (G i)).obj M))) =
        (F i).mapDerivedCategory.map
          (RL.map (U.mapDerivedCategoryFactors.hom.app M) ≫
            θ.hom.app ((complex U).obj M)) ≫
          (F i).mapDerivedCategoryFactors.hom.app (roosF.obj ((complex U).obj M)) ≫
          DerivedCategory.Q.map ((k i).hom.app M) := by
  let τ : DerivedCategory.Q.{wS} ⋙ total U RL ≅ complex U ⋙ roosF ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight U.mapDerivedCategoryFactors RL ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft (complex U) θ
  let e₁ (i : Fin 3) : DerivedCategory.Q ⋙ (total U RL ⋙ (F i).mapDerivedCategory) ≅
      (complex U ⋙ roosF ⋙ complex (F i)) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight τ (F i).mapDerivedCategory ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (complex U) (Functor.associator _ _ _) ≪≫
      Functor.isoWhiskerLeft (complex U ⋙ roosF) (F i).mapDerivedCategoryFactors
  let e₂ (i : Fin 3) : DerivedCategory.Q ⋙ ((G i).mapDerivedCategory ⋙ total U RL) ≅
      (complex (G i) ⋙ complex U ⋙ roosF) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (G i).mapDerivedCategoryFactors (total U RL) ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft (complex (G i)) τ
  let e (i : Fin 3) : DerivedCategory.Q ⋙ (total U RL ⋙ (F i).mapDerivedCategory) ≅
      DerivedCategory.Q ⋙ ((G i).mapDerivedCategory ⋙ total U RL) :=
    e₁ i ≪≫ Functor.isoWhiskerRight (k i) DerivedCategory.Q ≪≫ (e₂ i).symm
  let ff := Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso S (.up ℤ)) (DerivedCategory.{wA} A)
  let a (i : Fin 3) := ff.preimageIso (e i)
  refine ⟨a, ?_⟩
  intro i M
  have ha : (a i).hom.app (DerivedCategory.Q.obj M) = (e i).hom.app M :=
    congr_app (ff.map_preimage (e i).hom) M
  have hh : (e₁ i).hom.app M ≫ DerivedCategory.Q.map ((k i).hom.app M) =
      (a i).hom.app (DerivedCategory.Q.obj M) ≫ (e₂ i).hom.app M := by
    rw [ha]
    simp [e, Category.assoc]
  simpa [e₁, e₂, τ, Category.assoc, Functor.map_comp] using hh.symm

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

omit [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ A)]
  [HasDerivedCategory.{wS} S] in
private theorem extendConeComparison
    (U : S ⥤ ℕᵒᵖ ⥤ A) [U.Additive]
    (F : A ⥤ A) [F.Additive] [PreservesLimitsOfShape (Discrete ℕ) F]
    (G : S ⥤ S) [G.Additive] (b : U ⋙ tower F ≅ G ⋙ U)
    (ψ : ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
      (complex F).obj (roosP X) ≅ roosP ((complex (tower F)).obj X))
    (κ : ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
      (complex F).obj (roosF.obj X) ≅ roosF.obj ((complex (tower F)).obj X))
    (hp : ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
      (ψ X).hom = piComparison (complex F) (fun n : ℕ ↦ X.asFunctor.obj (op n)))
    (hd : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ),
      ((κ X).hom.f (p + 1) ≫ coordinates ((complex (tower F)).obj X) p ≫ biprod.fst =
        F.map (coordinates X p ≫ biprod.fst) ≫ (ψ X).hom.f (p + 1)) ∧
      ((κ X).hom.f (p + 1) ≫ coordinates ((complex (tower F)).obj X) p ≫ biprod.snd =
        F.map (coordinates X p ≫ biprod.snd) ≫ (ψ X).hom.f p))
    (hn : ∀ {X Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : X ⟶ Y),
      (complex F).map (roosF.map f) ≫ (κ Y).hom =
        (κ X).hom ≫ roosF.map ((complex (tower F)).map f)) :
    ∃ k : complex U ⋙ roosF ⋙ complex F ≅ complex G ⋙ complex U ⋙ roosF,
      ∀ (M : CochainComplex S ℤ) (p : ℤ),
      (k.hom.app M).f (p + 1) ≫
          coordinates ((complex U).obj ((complex G).obj M)) p ≫ biprod.fst =
        F.map (coordinates ((complex U).obj M) p ≫ biprod.fst) ≫
          (productIso U F G b M).hom.f (p + 1) ∧
      (k.hom.app M).f (p + 1) ≫
          coordinates ((complex U).obj ((complex G).obj M)) p ≫ biprod.snd =
        F.map (coordinates ((complex U).obj M) p ≫ biprod.snd) ≫
          (productIso U F G b M).hom.f p := by
  let k : complex U ⋙ roosF ⋙ complex F ≅ complex G ⋙ complex U ⋙ roosF :=
    NatIso.ofComponents
      (fun M ↦ κ ((complex U).obj M) ≪≫ roosF.mapIso ((complexB U F G b).app M))
      (by
        intro M M' f
        dsimp only [Iso.trans_hom, Functor.mapIso_hom, Functor.comp_map]
        rw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp]
        have h := (complexB U F G b).hom.naturality f
        dsimp only [Functor.comp_map] at h
        calc
          _ = (κ ((complex U).obj M)).hom ≫ roosF.map
              ((complexB U F G b).hom.app M ≫
                (complex U).map ((complex G).map f)) :=
            congrArg (fun z ↦ (κ ((complex U).obj M)).hom ≫ roosF.map z) h
          _ = _ := by rw [Functor.map_comp, Category.assoc]; rfl)
  refine ⟨k, ?_⟩
  intro M p
  have hmap := coord_map
    (X := (complex (tower F)).obj ((complex U).obj M))
    (Y := (complex U).obj ((complex G).obj M)) ((complexB U F G b).app M).hom p
  have hfst := congrArg (fun z ↦ (κ ((complex U).obj M)).hom.f (p + 1) ≫
    z ≫ biprod.fst) hmap
  have hsnd := congrArg (fun z ↦ (κ ((complex U).obj M)).hom.f (p + 1) ≫
    z ≫ biprod.snd) hmap
  simp only [Category.assoc, biprod.map_fst] at hfst
  simp only [Category.assoc, biprod.map_snd] at hsnd
  constructor
  · change ((κ _).hom.f _ ≫ (roosF.map _).f _) ≫ _ ≫ _ = _
    simp only [Category.assoc]
    calc
      _ = _ := hfst
      _ = F.map (coordinates ((complex U).obj M) p ≫ biprod.fst) ≫
          (ψ ((complex U).obj M)).hom.f (p + 1) ≫
          (roosPmap ((complexB U F G b).app M).hom).f (p + 1) := by
        simpa only [Category.assoc] using congrArg (fun z ↦ z ≫
            (roosPmap ((complexB U F G b).app M).hom).f (p + 1))
          (hd ((complex U).obj M) p).1
      _ = _ := by
        simp only [productIso, Iso.trans_hom, Functor.mapIso_hom, productFunctor,
          HomologicalComplex.comp_f, asIso_hom, hp]
  · change ((κ _).hom.f _ ≫ (roosF.map _).f _) ≫ _ ≫ _ = _
    simp only [Category.assoc]
    calc
      _ = _ := hsnd
      _ = F.map (coordinates ((complex U).obj M) p ≫ biprod.snd) ≫
          (ψ ((complex U).obj M)).hom.f p ≫
          (roosPmap ((complexB U F G b).app M).hom).f p := by
        simpa only [Category.assoc] using congrArg
          (fun z ↦ z ≫ (roosPmap ((complexB U F G b).app M).hom).f p)
          (hd ((complex U).obj M) p).2
      _ = _ := by
        simp only [productIso, Iso.trans_hom, Functor.mapIso_hom, productFunctor,
          HomologicalComplex.comp_f, asIso_hom, hp]


omit [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ A)] in
private lemma diagonal_of_projections
    (F : A ⥤ A) [F.Additive] (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (ψ : (complex F).obj (roosP X) ≅ roosP ((complex (tower F)).obj X))
    (κ : (complex F).obj (roosF.obj X) ≅ roosF.obj ((complex (tower F)).obj X))
    (hψ : ∀ n : ℕ, ψ.hom ≫ Pi.π (fun k : ℕ ↦ ((complex (tower F)).obj X).asFunctor.obj (op k)) n =
      (complex F).map (Pi.π (fun k : ℕ ↦ X.asFunctor.obj (op k)) n))
    (hκ : ∀ p : ℤ, ∀ n : ℕ,
      (κ.hom.f (p + 1) ≫ coordinates ((complex (tower F)).obj X) p ≫ biprod.fst ≫
          (Pi.π (fun k : ℕ ↦ ((complex (tower F)).obj X).asFunctor.obj (op k)) n).f (p + 1) =
        F.map (coordinates X p ≫ biprod.fst ≫
          (Pi.π (fun k : ℕ ↦ X.asFunctor.obj (op k)) n).f (p + 1))) ∧
      (κ.hom.f (p + 1) ≫ coordinates ((complex (tower F)).obj X) p ≫ biprod.snd ≫
          (Pi.π (fun k : ℕ ↦ ((complex (tower F)).obj X).asFunctor.obj (op k)) n).f p =
        F.map (coordinates X p ≫ biprod.snd ≫
          (Pi.π (fun k : ℕ ↦ X.asFunctor.obj (op k)) n).f p))) :
    ∀ p : ℤ,
      (κ.hom.f (p + 1) ≫ coordinates ((complex (tower F)).obj X) p ≫ biprod.fst =
        F.map (coordinates X p ≫ biprod.fst) ≫ ψ.hom.f (p + 1)) ∧
      (κ.hom.f (p + 1) ≫ coordinates ((complex (tower F)).obj X) p ≫ biprod.snd =
        F.map (coordinates X p ≫ biprod.snd) ≫ ψ.hom.f p) := by
  intro p
  constructor
  · apply product_ext
    intro n
    have h := congrArg (fun z ↦ z.f (p + 1)) (hψ n)
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f] at h
    simp only [Category.assoc, F.map_comp]
    rw [h]
    simpa only [F.map_comp] using (hκ p n).1
  · apply product_ext
    intro n
    have h := congrArg (fun z ↦ z.f p) (hψ n)
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f] at h
    simp only [Category.assoc, F.map_comp]
    rw [h]
    simpa only [F.map_comp] using (hκ p n).2

attribute [local semireducible] coordinates coordIso roosF roosConeFunctor

omit [HasDerivedCategory.{wS} S] in
private theorem coneData
    {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max uC vC r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC r}]
    (R : Sheaf J RingCat.{max uC vC r})
    (hcomm : ∀ (V : Cᵒᵖ) (x y : R.obj.obj V), x * y = y * x)
    [HasExactLimitsOfShape (Discrete ℕ) (ringedSiteModules.{max uC vC r} R)]
    [HasDerivedCategory.{wA} (ringedSiteModules.{max uC vC r} R)]
    [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R)]
    (U : S ⥤ ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) [U.Additive]
    (F : ringedSiteModules.{max uC vC r} R ⥤ ringedSiteModules.{max uC vC r} R)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesLimitsOfShape (Discrete ℕ) F]
    (G : S ⥤ S) [G.Additive] (b : U ⋙ tower F ≅ G ⋙ U) :
    ∃ k : complex U ⋙ roosF ⋙ complex F ≅ complex G ⋙ complex U ⋙ roosF,
      ∀ (M : CochainComplex S ℤ) (p : ℤ),
      (k.hom.app M).f (p + 1) ≫
          coordinates ((complex U).obj ((complex G).obj M)) p ≫ biprod.fst =
        F.map (coordinates ((complex U).obj M) p ≫ biprod.fst) ≫
          (productIso U F G b M).hom.f (p + 1) ∧
      (k.hom.app M).f (p + 1) ≫
          coordinates ((complex U).obj ((complex G).obj M)) p ≫ biprod.snd =
        F.map (coordinates ((complex U).obj M) p ≫ biprod.snd) ≫
          (productIso U F G b M).hom.f p := by
  classical
  obtain ⟨ψ, κ, hψ, hκ, hn⟩ := exactProductFunctorRoosChainMaps.{uC, vC, r, uC, vC, r, wA, wA}
    J R J R hcomm hcomm F (fun _ ↦ inferInstance)
    roosF roosF (fun _ ↦ rfl) (fun _ ↦ rfl) coordIso coordIso
    ⟨by intro X p; simpa only [coordIso_hom, eqToIso_refl, Iso.refl_hom, Category.id_comp] using
          coord_canonical X p,
      by intro X p; simpa only [coordIso_hom, eqToIso_refl, Iso.refl_hom, Category.id_comp] using
          coord_canonical X p⟩
      ⟨coord_map, coord_map⟩
  have hp (X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ) :
      (ψ X).hom = piComparison (complex F) (fun n : ℕ ↦ X.asFunctor.obj (op n)) := by
    apply Pi.hom_ext
    intro n
    exact (hψ X n).trans (piComparison_comp_π _ _ _).symm
  have hd (X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ) :=
    diagonal_of_projections F X (ψ X) (κ X) (hψ X)
      (by simpa only [coordIso_hom] using hκ X)
  exact extendConeComparison U F G b ψ κ hp hd hn

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] coordinates coordIso roosF roosConeFunctor

private theorem assemble [HasLimitsOfShape ℕᵒᵖ A]
    [∀ i, PreservesLimitsOfShape (Discrete ℕ) (F i)]
    (b : ∀ i : Fin 3, U ⋙ tower (F i) ≅ G i ⋙ U)
    (d : F 0 ⋙ F 1 ≅ F 2) (t : G 0 ⋙ G 1 ≅ G 2)
    (hb : ∀ M : S,
      (Functor.whiskerLeft (U.obj M) d.hom) ≫ (b 2).hom.app M =
        (tower (F 1)).map ((b 0).hom.app M) ≫
          (b 1).hom.app ((G 0).obj M) ≫ U.map (t.hom.app M))
    (eta : roosLimitFunctor ⋙ DerivedCategory.Q.{wA} ⟶ DerivedCategory.Q.{wA} ⋙ RL)
    (θ : DerivedCategory.Q.{wA} ⋙ RL ≅ roosF ⋙ DerivedCategory.Q.{wA})
    (hnorm : ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
      eta.app X ≫ θ.hom.app X = DerivedCategory.Q.map (roosι X))
    (hq : ∀ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [I.IsKInjective], QuasiIso (roosι I))
    (k : ∀ i : Fin 3,
      complex U ⋙ roosF ⋙ complex (F i) ≅ complex (G i) ⋙ complex U ⋙ roosF)
    (hk : ∀ (i : Fin 3) (M : CochainComplex S ℤ) (p : ℤ),
      ((k i).hom.app M).f (p + 1) ≫
          coordinates ((complex U).obj ((complex (G i)).obj M)) p ≫ biprod.fst =
        (F i).map (coordinates ((complex U).obj M) p ≫ biprod.fst) ≫
          (productIso U (F i) (G i) (b i) M).hom.f (p + 1) ∧
      ((k i).hom.app M).f (p + 1) ≫
          coordinates ((complex U).obj ((complex (G i)).obj M)) p ≫ biprod.snd =
        (F i).map (coordinates ((complex U).obj M) p ≫ biprod.snd) ≫
          (productIso U (F i) (G i) (b i) M).hom.f p) :
    ∃ N : Comparisons U F G RL,
      HasSignedCoordinates (A := A) ∧ HasNormalization U F G RL N eta ∧
      HasProducts U F G RL N b ∧ HasDiagonal U F G RL N ∧
      HasDerivedModel U F G RL N ∧ HasCompositors U F G RL N d t := by
  obtain ⟨a, ha⟩ := descendComparison U F G RL θ k
  let N : Comparisons U F G RL :=
    { theta := θ
      psi := fun i ↦ productIso U (F i) (G i) (b i)
      kappa := k
      a := a }
  refine ⟨N, ⟨coord_d, coord_map⟩, ?_,
    ⟨(fun i ↦ productIso_π U (F i) (G i) (b i)),
      (fun i _ _ f ↦ productIso_natural U (F i) (G i) (b i) f),
      (fun i ↦ productIso_shift U (F i) (G i) (b i))⟩, hk, ha, ?_⟩
  · intro I hI
    exact ⟨hq I, coord_inclusion I, hnorm I⟩
  · have hc := cone_compositor U F G RL N b d t hb hk (fun _ _ ↦ rfl)
    exact ⟨productIso_compositor U F G b d t hb, hc,
      derived_compositor U F G RL N d t ha hc⟩


end CategoryTheory.RoosCompositor

namespace CategoryTheory

/-- The normalized product, signed cone and total-derived-limit comparisons compose.

Source: Stacks Project, Tag 0941, lemma-derived-limit-is-ok and proof;
blueprint main-20261015, trace-transport Step 1, Global powers
(blueprint: lem-trf-roos-cone-compositor-descent).

Proof, following the eight DAG steps:
1. Use exact termwise derived factorization for U, F and G; tower exactness is
   levelwise. Change the recorded Roos coordinates (y,z) to (z,-y), obtaining
   D(x,y)=(dx,(1-s)x-dy) and inclusion (iota,0).
2. The product comparison is P(b) composed with the product-preservation comparison.
   Its inverse uses their inverses. Its projections prove strict chain naturality.
3. Strict tower compatibility proves the shift square on each projection. Additivity
   gives the 1-s square. The diagonal map commutes with the signed differential;
   its inverse and naturality hold on both coordinates.
4. Project the product compositor identity to each tower level. Naturality of d
   moves it past that projection; the assumed b/d/t equation identifies the results.
5. Naturality of d on the two biproduct inclusions makes it diagonal. Step 4 gives
   both diagonal equalities, and the off-diagonal entries vanish. Hence the whole
   strict cone maps agree.
6. Apply exactProductFunctorStrictLimit to each F. Compose its normalized comparison
   with Rlim(b). Naturality of strictRoosComparison turns its cone representative
   into kappa, giving exactly HasDerivedModel with the same normalized theta.
   For a general K-injective tower, refine to one with injective terms. The refinement
   is a homotopy equivalence; ordinary limit preserves its homotopies. Naturality of
   the inclusion transports its quasi-isomorphism and unit normalization back.
7. Exact termwise functors invert quasi-isomorphisms. Fully faithful precomposition
   with localization lifts the natural isomorphisms uniquely, retaining naturality
   for arbitrary derived morphisms and inverses of localized quasi-isomorphisms.
8. Expand the derived conjugation formulas. Cancel the adjacent theta and its
   inverse inside F1. Naturality of theta along U(t) leaves the strict cone identity
   from step 5. Naturality of derived d along theta gives the required left side.
   Localization detects equality of these natural transformations on all D(S).
Only strict products and biproducts were tested by projections, never derived maps. -/
theorem roosConeCompositorDescent
    {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max uC vC r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC r}]
    (R : Sheaf J RingCat.{max uC vC r})
    (_hcomm : ∀ (V : Cᵒᵖ) (x y : R.obj.obj V), x * y = y * x)
    [HasExactLimitsOfShape (Discrete ℕ) (ringedSiteModules.{max uC vC r} R)]
    [HasDerivedCategory.{wA} (ringedSiteModules.{max uC vC r} R)]
    [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R)]
    {S : Type uS} [Category.{vS} S] [Abelian S] [HasDerivedCategory.{wS} S]
    (U : S ⥤ ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R)
    [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (F : Fin 3 → ringedSiteModules.{max uC vC r} R ⥤ ringedSiteModules.{max uC vC r} R)
    [∀ i, (F i).Additive] [∀ i, PreservesFiniteLimits (F i)]
    [∀ i, PreservesFiniteColimits (F i)]
    [∀ i, PreservesLimitsOfShape (Discrete ℕ) (F i)]
    (G : Fin 3 → S ⥤ S) [∀ i, (G i).Additive]
    [∀ i, PreservesFiniteLimits (G i)] [∀ i, PreservesFiniteColimits (G i)]
    (b : ∀ i : Fin 3, U ⋙ RoosCompositor.tower (F i) ≅ G i ⋙ U)
    (d : F 0 ⋙ F 1 ≅ F 2) (t : G 0 ⋙ G 1 ≅ G 2)
    (_hb : ∀ M : S,
      (Functor.whiskerLeft (U.obj M) d.hom) ≫ (b 2).hom.app M =
        (RoosCompositor.tower (F 1)).map ((b 0).hom.app M) ≫
          (b 1).hom.app ((G 0).obj M) ≫ U.map (t.hom.app M))
    (RL : DerivedCategory.{wA} (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ⥤
      DerivedCategory.{wA} (ringedSiteModules.{max uC vC r} R))
    (eta : roosLimitFunctor ⋙ DerivedCategory.Q.{wA} ⟶ DerivedCategory.Q.{wA} ⋙ RL)
    (_hRL : RL.IsRightDerivedFunctor eta
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) (.up ℤ))) :
    ∃ N : RoosCompositor.Comparisons U F G RL,
      RoosCompositor.HasSignedCoordinates (A := ringedSiteModules.{max uC vC r} R) ∧
      RoosCompositor.HasNormalization U F G RL N eta ∧
      RoosCompositor.HasProducts U F G RL N b ∧
      RoosCompositor.HasDiagonal U F G RL N ∧
      RoosCompositor.HasDerivedModel U F G RL N ∧
      RoosCompositor.HasCompositors U F G RL N d t := by
  classical
  let A := ringedSiteModules.{max uC vC r} R
  let := _hRL
  obtain ⟨CF, κ, hCF, hι⟩ := strictRoosDerivation.{uC, vC, r, wA} J R _hcomm
  let := hCF
  let W := HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ)
  let ρ := CF.rightDerivedUnique RL (roosDerivedUnit κ) eta W
  let θ := (κ ≪≫ Functor.isoWhiskerLeft DerivedCategory.Q ρ).symm
  have hunit (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
      DerivedCategory.Q.map (roosι X) ≫ θ.inv.app X = eta.app X := by
    have h := CF.rightDerivedNatTrans_app RL (roosDerivedUnit κ) eta W (𝟙 _) X
    simpa [θ, ρ, Functor.rightDerivedUnique, Functor.rightDerivedNatIso,
      roosDerivedUnit, roosInclusion, roosLimitFunctor,
      Functor.rightDerivedNatTrans, Category.assoc] using h
  have hnorm (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
      eta.app X ≫ θ.hom.app X = DerivedCategory.Q.map (roosι X) := by
    rw [← hunit]
    simp
  choose k hk using fun i : Fin 3 ↦
    RoosCompositor.coneData.{uS, vS, wA, uC, vC, r} (S := S) J R _hcomm U (F i) (G i) (b i)
  have hqI (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [I.IsKInjective] :
      QuasiIso (roosι I) := by
    let : IsGrothendieckAbelian.{max uC vC r} A :=
      SheafOfModules.isGrothendieckAbelianOfUniverses.{uC, vC, max uC vC r, 0} J R
    exact CategoryTheory.roos_inclusion_quasiIso I
  exact RoosCompositor.assemble U F G RL b d t _hb eta θ hnorm hqI k hk

end CategoryTheory
