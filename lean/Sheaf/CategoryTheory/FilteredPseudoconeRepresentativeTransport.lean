module

public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import WeilConjectures.CategoryTheory.ArrowsFunctor

/-! # Transport between representatives of a filtered category colimit

Source: Stacks Project, Categories, Tag 04AX and Tag 002V, with the agent's coherent
comparison calculus (blueprint: lem-per-filtered-pseudocone-representative-transport).
-/

@[expose] public section

universe z u v u' v'

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {J : Type z} [SmallCategory J] [IsFiltered J] (D : J ⥤ Cat.{z, z})
variable {A : Type u} [Category.{v} A]

/-- The componentwise identity and composition coherence for the comparisons.
Source: Tag 04AX, agent comparison calculus
(blueprint: lem-per-filtered-pseudocone-representative-transport). -/
def FilteredPseudoconeCoherent (F : ∀ i, D.obj i ⥤ A)
    (θ : ∀ {i k} (a : i ⟶ k), (D.map a).toFunctor ⋙ F k ≅ F i) : Prop :=
  (∀ (i : J) (x : D.obj i),
    (θ (𝟙 i)).hom.app x = eqToHom (congrArg (F i).obj
      (congrArg (fun f : D.obj i ⟶ D.obj i ↦ f.toFunctor.obj x) (D.map_id i)))) ∧
  (∀ (i k l : J) (a : i ⟶ k) (b : k ⟶ l) (x : D.obj i),
    (θ (a ≫ b)).hom.app x =
      eqToHom (congrArg (F l).obj
        (congrArg (fun f : D.obj i ⟶ D.obj l ↦ f.toFunctor.obj x) (D.map_comp a b))) ≫
        (θ b).hom.app ((D.map a).toFunctor.obj x) ≫ (θ a).hom.app x)

/-- Transport computed at a specified common stage, including the middle object equality.
Source: Tag 04AX, agent comparison calculus
(blueprint: lem-per-filtered-pseudocone-representative-transport). -/
def filteredPseudoconeWitnessTransport (F : ∀ i, D.obj i ⥤ A)
    (θ : ∀ {i k} (a : i ⟶ k), (D.map a).toFunctor ⋙ F k ≅ F i)
    {i j k : J} (x : D.obj i) (y : D.obj j) (a : i ⟶ k) (b : j ⟶ k)
    (e : (D.map a).toFunctor.obj x = (D.map b).toFunctor.obj y) :
    (F i).obj x ≅ (F j).obj y :=
  ((θ a).app x).symm ≪≫ eqToIso (congrArg (F k).obj e) ≪≫ (θ b).app y

/-- Choose an eventual-equality witness using the proved set-colimit equality criterion,
then evaluate the displayed transport formula. No data is chosen from a postponed proof.
Source: Tag 04AX (blueprint: lem-per-filtered-pseudocone-representative-transport). -/
noncomputable def filteredPseudoconeTransport (F : ∀ i, D.obj i ⥤ A)
    (θ : ∀ {i k} (a : i ⟶ k), (D.map a).toFunctor ⋙ F k ≅ F i)
    {i j : J} (x : D.obj i) (y : D.obj j)
    (h : colimit.ι (D ⋙ Cat.objects) i x = colimit.ι (D ⋙ Cat.objects) j y) :
    (F i).obj x ≅ (F j).obj y :=
  let w := (Types.FilteredColimit.colimit_eq_iff (D ⋙ Cat.objects)).mp h
  filteredPseudoconeWitnessTransport D F θ x y w.choose_spec.choose
    w.choose_spec.choose_spec.choose w.choose_spec.choose_spec.choose_spec

omit [IsFiltered J] in
private theorem comparison_comp (F : ∀ i, D.obj i ⥤ A)
    (θ : ∀ {i k} (a : i ⟶ k), (D.map a).toFunctor ⋙ F k ≅ F i)
    (hθ : FilteredPseudoconeCoherent D F θ)
    {i k l : J} (a : i ⟶ k) (b : k ⟶ l) (x : D.obj i) :
    (θ (a ≫ b)).app x =
      eqToIso (congrArg (F l).obj
        (congrArg (fun f : D.obj i ⟶ D.obj l ↦ f.toFunctor.obj x) (D.map_comp a b))) ≪≫
        (θ b).app ((D.map a).toFunctor.obj x) ≪≫ (θ a).app x := by
  apply Iso.ext
  exact hθ.2 i k l a b x

omit [IsFiltered J] in
private theorem witness_refine (F : ∀ i, D.obj i ⥤ A)
    (θ : ∀ {i k} (a : i ⟶ k), (D.map a).toFunctor ⋙ F k ≅ F i)
    (hθ : FilteredPseudoconeCoherent D F θ)
    {i j k l : J} (x : D.obj i) (y : D.obj j)
    (a : i ⟶ k) (b : j ⟶ k) (c : k ⟶ l)
    (e : (D.map a).toFunctor.obj x = (D.map b).toFunctor.obj y)
    (e' : (D.map (a ≫ c)).toFunctor.obj x = (D.map (b ≫ c)).toFunctor.obj y) :
    filteredPseudoconeWitnessTransport D F θ x y (a ≫ c) (b ≫ c) e' =
      filteredPseudoconeWitnessTransport D F θ x y a b e := by
  unfold filteredPseudoconeWitnessTransport
  rw [comparison_comp D F θ hθ a c x, comparison_comp D F θ hθ b c y]
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, eqToIso.hom, eqToIso.inv,
    Category.assoc]
  simp only [eqToHom_trans_assoc]
  rw [eqToHom_iso_inv_naturality_assoc (fun z ↦ (θ c).app z) e]
  simp

private theorem witness_independent (F : ∀ i, D.obj i ⥤ A)
    (θ : ∀ {i k} (a : i ⟶ k), (D.map a).toFunctor ⋙ F k ≅ F i)
    (hθ : FilteredPseudoconeCoherent D F θ)
    {i j k l : J} (x : D.obj i) (y : D.obj j)
    (a : i ⟶ k) (b : j ⟶ k) (a' : i ⟶ l) (b' : j ⟶ l)
    (e : (D.map a).toFunctor.obj x = (D.map b).toFunctor.obj y)
    (e' : (D.map a').toFunctor.obj x = (D.map b').toFunctor.obj y) :
    filteredPseudoconeWitnessTransport D F θ x y a b e =
      filteredPseudoconeWitnessTransport D F θ x y a' b' e' := by
  obtain ⟨m, c, d, ha, hb⟩ := IsFiltered.bowtie a a' b b'
  have ec : (D.map (a ≫ c)).toFunctor.obj x = (D.map (b ≫ c)).toFunctor.obj y := by
    simpa only [D.map_comp, Cat.Hom.comp_toFunctor, Functor.comp_obj] using
      congrArg (D.map c).toFunctor.obj e
  have ed : (D.map (a' ≫ d)).toFunctor.obj x = (D.map (b' ≫ d)).toFunctor.obj y := by
    simpa only [D.map_comp, Cat.Hom.comp_toFunctor, Functor.comp_obj] using
      congrArg (D.map d).toFunctor.obj e'
  rw [← witness_refine D F θ hθ x y a b c e ec,
    ← witness_refine D F θ hθ x y a' b' d e' ed]
  congr 1

private theorem transport_eq_witness (F : ∀ i, D.obj i ⥤ A)
    (θ : ∀ {i k} (a : i ⟶ k), (D.map a).toFunctor ⋙ F k ≅ F i)
    (hθ : FilteredPseudoconeCoherent D F θ)
    {i j k : J} (x : D.obj i) (y : D.obj j)
    (h : colimit.ι (D ⋙ Cat.objects) i x = colimit.ι (D ⋙ Cat.objects) j y)
    (a : i ⟶ k) (b : j ⟶ k)
    (e : (D.map a).toFunctor.obj x = (D.map b).toFunctor.obj y) :
    filteredPseudoconeTransport D F θ x y h =
      filteredPseudoconeWitnessTransport D F θ x y a b e := by
  dsimp only [filteredPseudoconeTransport]
  apply witness_independent D F θ hθ

omit [IsFiltered J] in
private theorem witness_comp (F : ∀ i, D.obj i ⥤ A)
    (θ : ∀ {i k} (a : i ⟶ k), (D.map a).toFunctor ⋙ F k ≅ F i)
    {i j k l : J} (x : D.obj i) (y : D.obj j) (w : D.obj k)
    (a : i ⟶ l) (b : j ⟶ l) (c : k ⟶ l)
    (e : (D.map a).toFunctor.obj x = (D.map b).toFunctor.obj y)
    (e' : (D.map b).toFunctor.obj y = (D.map c).toFunctor.obj w) :
    filteredPseudoconeWitnessTransport D F θ x y a b e ≪≫
        filteredPseudoconeWitnessTransport D F θ y w b c e' =
      filteredPseudoconeWitnessTransport D F θ x w a c (e.trans e') := by
  apply Iso.ext
  simp [filteredPseudoconeWitnessTransport]

omit [IsFiltered J] in
private theorem witness_arrow_naturality (F : ∀ i, D.obj i ⥤ A)
    (θ : ∀ {i k} (a : i ⟶ k), (D.map a).toFunctor ⋙ F k ≅ F i)
    {i j k : J} (x y : D.obj i) (x' y' : D.obj j) (f : x ⟶ y) (g : x' ⟶ y')
    (a : i ⟶ k) (b : j ⟶ k)
    (ex : (D.map a).toFunctor.obj x = (D.map b).toFunctor.obj x')
    (ey : (D.map a).toFunctor.obj y = (D.map b).toFunctor.obj y')
    (ef : (D.map a).toFunctor.map f =
      eqToHom ex ≫ (D.map b).toFunctor.map g ≫ eqToHom ey.symm) :
    (F i).map f ≫ (filteredPseudoconeWitnessTransport D F θ y y' a b ey).hom =
      (filteredPseudoconeWitnessTransport D F θ x x' a b ex).hom ≫ (F j).map g := by
  have hs : (F k).map ((D.map a).toFunctor.map f) ≫ eqToHom (congrArg (F k).obj ey) =
      eqToHom (congrArg (F k).obj ex) ≫ (F k).map ((D.map b).toFunctor.map g) := by
    rw [ef]
    simp [Functor.map_comp, eqToHom_map, Category.assoc]
  change (F i).map f ≫ ((θ a).inv.app y ≫
      eqToHom (congrArg (F k).obj ey) ≫ (θ b).hom.app y') =
    ((θ a).inv.app x ≫ eqToHom (congrArg (F k).obj ex) ≫ (θ b).hom.app x') ≫
      (F j).map g
  rw [(θ a).inv.naturality_assoc f]
  simp only [Functor.comp_map]
  rw [← Category.assoc ((F k).map _) (eqToHom _) _, hs]
  simp only [Category.assoc]
  have hn := (θ b).hom.naturality g
  dsimp only [Functor.comp_map] at hn
  rw [hn]

omit [IsFiltered J] in
private theorem witness_modification (F G : ∀ i, D.obj i ⥤ A)
    (θ : ∀ {i k} (a : i ⟶ k), (D.map a).toFunctor ⋙ F k ≅ F i)
    (η : ∀ {i k} (a : i ⟶ k), (D.map a).toFunctor ⋙ G k ≅ G i)
    (ρ : ∀ i, F i ⟶ G i)
    (hρ : ∀ (i k : J) (a : i ⟶ k) (x : D.obj i),
      (θ a).hom.app x ≫ (ρ i).app x =
        (ρ k).app ((D.map a).toFunctor.obj x) ≫ (η a).hom.app x)
    {i j k : J} (x : D.obj i) (y : D.obj j) (a : i ⟶ k) (b : j ⟶ k)
    (e : (D.map a).toFunctor.obj x = (D.map b).toFunctor.obj y) :
    (filteredPseudoconeWitnessTransport D F θ x y a b e).hom ≫ (ρ j).app y =
      (ρ i).app x ≫ (filteredPseudoconeWitnessTransport D G η x y a b e).hom := by
  have hi : (θ a).inv.app x ≫ (ρ k).app ((D.map a).toFunctor.obj x) =
      (ρ i).app x ≫ (η a).inv.app x := by
    apply (cancel_mono ((η a).hom.app x)).1
    simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    rw [← hρ i k a x]
    simp
  change ((θ a).inv.app x ≫ eqToHom (congrArg (F k).obj e) ≫
      (θ b).hom.app y) ≫ (ρ j).app y =
    (ρ i).app x ≫ (η a).inv.app x ≫ eqToHom (congrArg (G k).obj e) ≫
      (η b).hom.app y
  simp only [Category.assoc]
  rw [hρ j k b y, ← eqToHom_naturality_assoc (fun z ↦ (ρ k).app z) e]
  rw [← Category.assoc ((θ a).inv.app x) ((ρ k).app _) _, hi]
  simp only [Category.assoc]

omit [IsFiltered J] in
private theorem coherent_postcompose (F : ∀ i, D.obj i ⥤ A)
    (θ : ∀ {i k} (a : i ⟶ k), (D.map a).toFunctor ⋙ F k ≅ F i)
    (hθ : FilteredPseudoconeCoherent D F θ)
    {B : Type u'} [Category.{v'} B] (H : A ⥤ B) :
    FilteredPseudoconeCoherent D (fun i ↦ F i ⋙ H)
      (fun {_ _} a ↦ Functor.isoWhiskerRight (θ a) H) := by
  constructor
  · intro i x
    change H.map ((θ (𝟙 i)).hom.app x) = _
    rw [hθ.1]
    simp only [eqToHom_map]
  · intro i k l a b x
    change H.map ((θ (a ≫ b)).hom.app x) = _
    rw [hθ.2]
    simp only [Functor.map_comp, eqToHom_map]
    rfl

omit [IsFiltered J] in
private theorem witness_postcompose (F : ∀ i, D.obj i ⥤ A)
    (θ : ∀ {i k} (a : i ⟶ k), (D.map a).toFunctor ⋙ F k ≅ F i)
    {B : Type u'} [Category.{v'} B] (H : A ⥤ B)
    {i j k : J} (x : D.obj i) (y : D.obj j) (a : i ⟶ k) (b : j ⟶ k)
    (e : (D.map a).toFunctor.obj x = (D.map b).toFunctor.obj y) :
    H.mapIso (filteredPseudoconeWitnessTransport D F θ x y a b e) =
      filteredPseudoconeWitnessTransport D (fun i ↦ F i ⋙ H)
        (fun {_ _} a ↦ Functor.isoWhiskerRight (θ a) H) x y a b e := by
  apply Iso.ext
  change H.map ((θ a).inv.app x ≫ eqToHom (congrArg (F k).obj e) ≫
      (θ b).hom.app y) = _
  simp only [Functor.map_comp, eqToHom_map]
  rfl

/-- Canonical representative transport: independence, unit, composition, transition,
complete-arrow naturality, modification naturality, and postcomposition.
Source: Stacks Project, Categories, Tags 04AX and 002V, agent comparison calculus
(blueprint: lem-per-filtered-pseudocone-representative-transport).

Proof:
1. The object equality criterion in lem-weil-pbc-filtered-colimit-categories gives
   a common-stage witness; the definition evaluates the two comparison components there.
2. Further transition preserves this expression by composition coherence and cancellation.
3. For two witnesses, filteredness (def-weil-pbc-category-colimit) first gives a common
   target and then equalizes the two parallel pairs of arrows. Step 2 proves independence;
   proof irrelevance removes the equality-witness choice.
4. Compute at the identity witness for the unit and at `(a, identity)` for a transition.
5. Refine two successive witnesses to one common target, equalizing their arrows out of
   the middle stage. Cancellation of its comparison gives the composition identity.
6. Apply the complete-arrow equality criterion of lem-weil-pbc-filtered-colimit-categories
   to obtain one witness for both endpoints and the morphisms. Naturality of both
   comparisons then gives the displayed conjugation identity.
7. Substitute the two modification compatibility equations at a common witness and
   cancel only comparison isomorphisms; no component of the modification is inverted.
8. Compute postcomposition at the same witness. A functor preserves composition,
   inverses and equality identifications. Independence removes the witness choice.
-/
theorem filteredPseudoconeTransport_spec (F : ∀ i, D.obj i ⥤ A)
    (θ : ∀ {i k} (a : i ⟶ k), (D.map a).toFunctor ⋙ F k ≅ F i)
    (hθ : FilteredPseudoconeCoherent D F θ) :
    (∀ (i j k : J) (x : D.obj i) (y : D.obj j)
      (h : colimit.ι (D ⋙ Cat.objects) i x = colimit.ι (D ⋙ Cat.objects) j y)
      (a : i ⟶ k) (b : j ⟶ k)
      (e : (D.map a).toFunctor.obj x = (D.map b).toFunctor.obj y),
      filteredPseudoconeTransport D F θ x y h =
        filteredPseudoconeWitnessTransport D F θ x y a b e) ∧
    (∀ (i : J) (x : D.obj i),
      filteredPseudoconeTransport D F θ x x rfl = Iso.refl ((F i).obj x)) ∧
    (∀ (i j k : J) (x : D.obj i) (y : D.obj j) (w : D.obj k)
      (h : colimit.ι (D ⋙ Cat.objects) i x = colimit.ι (D ⋙ Cat.objects) j y)
      (h' : colimit.ι (D ⋙ Cat.objects) j y = colimit.ι (D ⋙ Cat.objects) k w),
      filteredPseudoconeTransport D F θ x y h ≪≫
        filteredPseudoconeTransport D F θ y w h' =
          filteredPseudoconeTransport D F θ x w (h.trans h')) ∧
    (∀ (i k : J) (a : i ⟶ k) (x : D.obj i),
      ∃ h : colimit.ι (D ⋙ Cat.objects) i x =
          colimit.ι (D ⋙ Cat.objects) k ((D.map a).toFunctor.obj x),
        filteredPseudoconeTransport D F θ x ((D.map a).toFunctor.obj x) h =
          ((θ a).app x).symm) ∧
    (∀ (i j : J) (x y : D.obj i) (x' y' : D.obj j) (f : x ⟶ y) (g : x' ⟶ y'),
      colimit.ι (D ⋙ Cat.arrows) i (Arrow.mk f) =
        colimit.ι (D ⋙ Cat.arrows) j (Arrow.mk g) →
      ∃ (hx : colimit.ι (D ⋙ Cat.objects) i x = colimit.ι (D ⋙ Cat.objects) j x')
        (hy : colimit.ι (D ⋙ Cat.objects) i y = colimit.ι (D ⋙ Cat.objects) j y'),
        (F i).map f ≫ (filteredPseudoconeTransport D F θ y y' hy).hom =
          (filteredPseudoconeTransport D F θ x x' hx).hom ≫ (F j).map g) ∧
    (∀ (G : ∀ i, D.obj i ⥤ A)
      (η : ∀ {i k} (a : i ⟶ k), (D.map a).toFunctor ⋙ G k ≅ G i),
      FilteredPseudoconeCoherent D G η →
      ∀ (ρ : ∀ i, F i ⟶ G i),
      (∀ (i k : J) (a : i ⟶ k) (x : D.obj i),
        (θ a).hom.app x ≫ (ρ i).app x =
          (ρ k).app ((D.map a).toFunctor.obj x) ≫ (η a).hom.app x) →
      ∀ (i j : J) (x : D.obj i) (y : D.obj j)
        (h : colimit.ι (D ⋙ Cat.objects) i x = colimit.ι (D ⋙ Cat.objects) j y),
        (filteredPseudoconeTransport D F θ x y h).hom ≫ (ρ j).app y =
          (ρ i).app x ≫ (filteredPseudoconeTransport D G η x y h).hom) ∧
    (∀ (B : Type u') [Category.{v'} B] (H : A ⥤ B),
      FilteredPseudoconeCoherent D (fun i ↦ F i ⋙ H)
        (fun {_ _} a ↦ Functor.isoWhiskerRight (θ a) H) ∧
      ∀ (i j : J) (x : D.obj i) (y : D.obj j)
        (h : colimit.ι (D ⋙ Cat.objects) i x = colimit.ι (D ⋙ Cat.objects) j y),
        H.mapIso (filteredPseudoconeTransport D F θ x y h) =
          filteredPseudoconeTransport D (fun i ↦ F i ⋙ H)
            (fun {_ _} a ↦ Functor.isoWhiskerRight (θ a) H) x y h) := by
  refine ⟨fun _ _ _ x y h a b e ↦ transport_eq_witness D F θ hθ x y h a b e,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i x
    rw [transport_eq_witness D F θ hθ x x rfl (𝟙 i) (𝟙 i) rfl]
    simp [filteredPseudoconeWitnessTransport]
  · intro i j k x y w h h'
    obtain ⟨l, a, b, e⟩ := (Types.FilteredColimit.colimit_eq_iff (D ⋙ Cat.objects)).mp h
    obtain ⟨m, c, d, e'⟩ := (Types.FilteredColimit.colimit_eq_iff (D ⋙ Cat.objects)).mp h'
    change (D.map a).toFunctor.obj x = (D.map b).toFunctor.obj y at e
    change (D.map c).toFunctor.obj y = (D.map d).toFunctor.obj w at e'
    obtain ⟨n, s, t, hb⟩ := IsFiltered.span b c
    have ex : (D.map (a ≫ s)).toFunctor.obj x = (D.map (b ≫ s)).toFunctor.obj y := by
      simpa only [D.map_comp, Cat.Hom.comp_toFunctor, Functor.comp_obj] using
        congrArg (D.map s).toFunctor.obj e
    have ey : (D.map (b ≫ s)).toFunctor.obj y = (D.map (d ≫ t)).toFunctor.obj w := by
      rw [hb]
      simpa only [D.map_comp, Cat.Hom.comp_toFunctor, Functor.comp_obj] using
        congrArg (D.map t).toFunctor.obj e'
    rw [transport_eq_witness D F θ hθ x y h (a ≫ s) (b ≫ s) ex,
      transport_eq_witness D F θ hθ y w h' (b ≫ s) (d ≫ t) ey,
      transport_eq_witness D F θ hθ x w (h.trans h') (a ≫ s) (d ≫ t) (ex.trans ey)]
    exact witness_comp D F θ x y w (a ≫ s) (b ≫ s) (d ≫ t) ex ey
  · intro i k a x
    have h : colimit.ι (D ⋙ Cat.objects) i x =
        colimit.ι (D ⋙ Cat.objects) k ((D.map a).toFunctor.obj x) :=
      (colimit.w_apply (D ⋙ Cat.objects) a x).symm
    refine ⟨h, ?_⟩
    have e := congrArg (fun f : D.obj k ⟶ D.obj k ↦
      f.toFunctor.obj ((D.map a).toFunctor.obj x)) (D.map_id k)
    rw [transport_eq_witness D F θ hθ x _ h a (𝟙 k) e.symm]
    apply Iso.ext
    simp only [filteredPseudoconeWitnessTransport, Iso.trans_hom, Iso.symm_hom,
      eqToIso.hom, Iso.app_hom, hθ.1, eqToHom_trans,
      eqToHom_refl, Category.comp_id]
  · intro i j x y x' y' f g h
    obtain ⟨k, a, b, e⟩ := (Types.FilteredColimit.colimit_eq_iff (D ⋙ Cat.arrows)).mp h
    change Arrow.mk ((D.map a).toFunctor.map f) =
      Arrow.mk ((D.map b).toFunctor.map g) at e
    obtain ⟨ex, ey, ef⟩ := (Arrow.mk_eq_mk_iff _ _).mp e
    have hx := (Types.FilteredColimit.colimit_eq_iff (D ⋙ Cat.objects)).mpr
      ⟨k, a, b, ex⟩
    have hy := (Types.FilteredColimit.colimit_eq_iff (D ⋙ Cat.objects)).mpr
      ⟨k, a, b, ey⟩
    refine ⟨hx, hy, ?_⟩
    rw [transport_eq_witness D F θ hθ y y' hy a b ey,
      transport_eq_witness D F θ hθ x x' hx a b ex]
    exact witness_arrow_naturality D F θ x y x' y' f g a b ex ey ef
  · intro G η hη ρ hρ i j x y h
    obtain ⟨k, a, b, e⟩ := (Types.FilteredColimit.colimit_eq_iff (D ⋙ Cat.objects)).mp h
    rw [transport_eq_witness D F θ hθ x y h a b e,
      transport_eq_witness D G η hη x y h a b e]
    exact witness_modification D F G θ η ρ hρ x y a b e
  · intro B _ H
    have hH := coherent_postcompose D F θ hθ H
    refine ⟨hH, ?_⟩
    intro i j x y h
    obtain ⟨k, a, b, e⟩ := (Types.FilteredColimit.colimit_eq_iff (D ⋙ Cat.objects)).mp h
    rw [transport_eq_witness D F θ hθ x y h a b e,
      transport_eq_witness D (fun i ↦ F i ⋙ H)
        (fun {_ _} a ↦ Functor.isoWhiskerRight (θ a) H) hH x y h a b e]
    exact witness_postcompose D F θ H x y a b e

end CategoryTheory
