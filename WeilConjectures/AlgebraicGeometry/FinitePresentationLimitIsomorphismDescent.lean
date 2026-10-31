/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FinitePresentationAffineLimitDescent
import WeilConjectures.AlgebraicGeometry.TensorPullbackCompositionAssociativity
import WeilConjectures.AlgebraicGeometry.TensorPullbackFinitePresentation

/-!
# Specified isomorphisms of finitely presented modules descend

Source: Stacks Project, Limits, Tag 01ZR, clauses (2), (3), and Tag 0B8W,
proof of clause (2) (blueprint: lem-trf-fp-module-limit-isomorphism-descent).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

attribute [local irreducible] tensorPullback

-- Identify the normalized comparison with the existing adjunction-induced comparison.
private theorem adjointComparison
    {C E : Type*} [Category C] [Category E]
    {L L' : C ⥤ E} {R R' : E ⥤ C}
    (a : L ⊣ R) (b : L' ⊣ R') (e : R ≅ R') :
    b.leftAdjointUniq (a.ofNatIsoRight e) = (conjugateIsoEquiv a b).symm e := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply (b.homEquiv _ _).injective
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
  simpa only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Adjunction.homEquiv_unit,
    conjugateIsoEquiv_symm_apply_hom] using
    (unit_conjugateEquiv_symm a b e.hom M)

private theorem sectionAdjunction_eq {X Y : Scheme.{u}} (g : X ⟶ Y) :
    tensorPullbackSectionAdjunction g =
      Classical.choose (exists_tensorPullbackAdjunction g) := by
  apply ((Classical.choose_spec (existsUnique_tensorPullbackSectionAdjunction g)).2
    (Classical.choose (exists_tensorPullbackAdjunction g)) ?_).symm
  intro M U m
  exact Classical.choose_spec (exists_tensorPullbackAdjunction g) M (op U) m

private theorem sectionComparison_eq
    {X Y Z : Scheme.{u}} (g : Z ⟶ Y) (h : Y ⟶ X)
    (k : Z ⟶ X) (w : g ≫ h = k) (M : X.Modules) :
    ((tensorPullbackSectionComp g h).symm.app M) ≪≫
      eqToIso (congrArg (fun f : Z ⟶ X ↦ (tensorPullback f).obj M) w) =
        (tensorPullbackCompositionIso g h k w).symm.app M := by
  subst k
  simp only [eqToIso_refl, Iso.trans_refl]
  have hp : pushforwardCongr (rfl : g ≫ h = g ≫ h) = Iso.refl _ := by
    apply Iso.ext
    apply NatTrans.ext
    funext N
    apply hom_ext
    intro U
    simp [pushforwardCongr_hom_app_app]
  unfold tensorPullbackSectionComp tensorPullbackCompositionIso
  rw [adjointComparison]
  simp only [sectionAdjunction_eq, hp, Iso.trans_refl]

private theorem limitComparison_eq
    {I : Type u} [Preorder I] (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D)
    {i j : I} (hij : i ≤ j) (M : (D.obj (op i)).Modules) :
    affineLimitTensorPullbackComparison D c hij M =
      (tensorPullbackCompositionIso (c.π.app (op j))
        (D.map (homOfLE hij).op) (c.π.app (op i)) (c.w _)).symm.app M :=
  sectionComparison_eq _ _ _ _ _

-- Keep the endpoint inequality explicit so both maps use identical object expressions.
private noncomputable def stageComparison
    {I : Type u} [Preorder I] (D : Iᵒᵖ ⥤ Scheme.{u})
    {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) (hik : i ≤ k) (M : (D.obj (op i)).Modules) :
    (tensorPullback (D.map (homOfLE hjk).op)).obj
      ((tensorPullback (D.map (homOfLE hij).op)).obj M) ≅
        (tensorPullback (D.map (homOfLE hik).op)).obj M :=
  (tensorPullbackCompositionIso (D.map (homOfLE hjk).op)
    (D.map (homOfLE hij).op) (D.map (homOfLE hik).op)
    (by rw [← D.map_comp]; congr 1)).symm.app M

@[reassoc] private theorem comparison_naturality
    {I : Type u} [Preorder I] (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D)
    {i j : I} (hij : i ≤ j) {M N : (D.obj (op i)).Modules} (f : M ⟶ N) :
    (affineLimitTensorPullbackComparison D c hij M).inv ≫
        (tensorPullback (c.π.app (op j))).map
          ((tensorPullback (D.map (homOfLE hij).op)).map f) ≫
        (affineLimitTensorPullbackComparison D c hij N).hom =
      (tensorPullback (c.π.app (op i))).map f := by
  simp only [limitComparison_eq, Iso.app_inv, Iso.app_hom,
    Iso.symm_inv, Iso.symm_hom]
  exact NatIso.naturality_2 _ f

private theorem comparison_associativity
    {I : Type u} [Preorder I] (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D)
    {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) (hik : i ≤ k) (M : (D.obj (op i)).Modules) :
    (affineLimitTensorPullbackComparison D c hik M).inv ≫
        (tensorPullback (c.π.app (op k))).map (stageComparison D hij hjk hik M).inv =
      (affineLimitTensorPullbackComparison D c hij M).inv ≫
        (affineLimitTensorPullbackComparison D c hjk
          ((tensorPullback (D.map (homOfLE hij).op)).obj M)).inv := by
  simp only [limitComparison_eq, stageComparison, Iso.app_inv, Iso.symm_inv]
  exact tensorPullbackCompositionIso_associativity _ _ _ _ _ _ _ _ _ _ M

private theorem comparison_associativity_hom
    {I : Type u} [Preorder I] (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D)
    {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) (hik : i ≤ k) (M : (D.obj (op i)).Modules) :
    (tensorPullback (c.π.app (op k))).map (stageComparison D hij hjk hik M).hom ≫
        (affineLimitTensorPullbackComparison D c hik M).hom =
      (affineLimitTensorPullbackComparison D c hjk
        ((tensorPullback (D.map (homOfLE hij).op)).obj M)).hom ≫
        (affineLimitTensorPullbackComparison D c hij M).hom := by
  have he :
      (affineLimitTensorPullbackComparison D c hik M).symm ≪≫
        ((tensorPullback (c.π.app (op k))).mapIso
          (stageComparison D hij hjk hik M)).symm =
      (affineLimitTensorPullbackComparison D c hij M).symm ≪≫
        (affineLimitTensorPullbackComparison D c hjk
          ((tensorPullback (D.map (homOfLE hij).op)).obj M)).symm :=
    Iso.ext (comparison_associativity D c hij hjk hik M)
  exact congrArg Iso.inv he

private noncomputable def refineMap
    {I : Type u} [Preorder I] (D : Iᵒᵖ ⥤ Scheme.{u})
    {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) (hik : i ≤ k)
    {M N : (D.obj (op i)).Modules}
    (f : (tensorPullback (D.map (homOfLE hij).op)).obj M ⟶
      (tensorPullback (D.map (homOfLE hij).op)).obj N) :
    (tensorPullback (D.map (homOfLE hik).op)).obj M ⟶
      (tensorPullback (D.map (homOfLE hik).op)).obj N :=
  (stageComparison D hij hjk hik M).inv ≫
    (tensorPullback (D.map (homOfLE hjk).op)).map f ≫
    (stageComparison D hij hjk hik N).hom

private theorem refineMap_limit
    {I : Type u} [Preorder I] (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D)
    {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) (hik : i ≤ k)
    {M N : (D.obj (op i)).Modules}
    (f : (tensorPullback (D.map (homOfLE hij).op)).obj M ⟶
      (tensorPullback (D.map (homOfLE hij).op)).obj N) :
    (affineLimitTensorPullbackComparison D c hik M).inv ≫
        (tensorPullback (c.π.app (op k))).map (refineMap D hij hjk hik f) ≫
        (affineLimitTensorPullbackComparison D c hik N).hom =
      (affineLimitTensorPullbackComparison D c hij M).inv ≫
        (tensorPullback (c.π.app (op j))).map f ≫
        (affineLimitTensorPullbackComparison D c hij N).hom := by
  simp only [refineMap, Functor.map_comp, Category.assoc]
  rw [comparison_associativity_hom]
  rw [← Category.assoc, comparison_associativity]
  simp only [Category.assoc]
  rw [comparison_naturality_assoc D c hjk f]

private theorem stage_naturality
    {I : Type u} [Preorder I] (D : Iᵒᵖ ⥤ Scheme.{u})
    {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) (hik : i ≤ k)
    {M N : (D.obj (op i)).Modules} (f : M ⟶ N) :
    (stageComparison D hij hjk hik M).inv ≫
        (tensorPullback (D.map (homOfLE hjk).op)).map
          ((tensorPullback (D.map (homOfLE hij).op)).map f) ≫
        (stageComparison D hij hjk hik N).hom =
      (tensorPullback (D.map (homOfLE hik).op)).map f := by
  simp only [stageComparison, Iso.app_inv, Iso.app_hom, Iso.symm_inv, Iso.symm_hom]
  exact NatIso.naturality_2 _ f

private theorem map_eq_later
    {I : Type u} [Preorder I] (D : Iᵒᵖ ⥤ Scheme.{u})
    {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) (hik : i ≤ k)
    {M N : (D.obj (op i)).Modules} (f g : M ⟶ N)
    (he : (tensorPullback (D.map (homOfLE hij).op)).map f =
      (tensorPullback (D.map (homOfLE hij).op)).map g) :
    (tensorPullback (D.map (homOfLE hik).op)).map f =
      (tensorPullback (D.map (homOfLE hik).op)).map g := by
  rw [← stage_naturality D hij hjk hik f, ← stage_naturality D hij hjk hik g, he]

private theorem map_inverse_identity
    {C E : Type*} [Category C] [Category E] (P : C ⥤ E)
    {M N : C} {A B : E} (eM : P.obj M ≅ A) (eN : P.obj N ≅ B)
    (f : M ⟶ N) (g : N ⟶ M) (φ : A ≅ B)
    (hf : eM.inv ≫ P.map f ≫ eN.hom = φ.hom)
    (hg : eN.inv ≫ P.map g ≫ eM.hom = φ.inv) :
    P.map (f ≫ g) = P.map (𝟙 M) := by
  apply (cancel_epi eM.inv).1
  apply (cancel_mono eM.hom).1
  simpa [Functor.map_comp, Category.assoc] using calc
    (eM.inv ≫ P.map f ≫ eN.hom) ≫ (eN.inv ≫ P.map g ≫ eM.hom) =
        φ.hom ≫ φ.inv := by rw [hf, hg]
    _ = 𝟙 A := φ.hom_inv_id

private theorem refineMap_inverse_identity
    {I : Type u} [Preorder I] (D : Iᵒᵖ ⥤ Scheme.{u})
    {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) (hik : i ≤ k)
    {M N : (D.obj (op i)).Modules}
    (f : (tensorPullback (D.map (homOfLE hij).op)).obj M ⟶
      (tensorPullback (D.map (homOfLE hij).op)).obj N)
    (g : (tensorPullback (D.map (homOfLE hij).op)).obj N ⟶
      (tensorPullback (D.map (homOfLE hij).op)).obj M)
    (he : (tensorPullback (D.map (homOfLE hjk).op)).map (f ≫ g) =
      (tensorPullback (D.map (homOfLE hjk).op)).map (𝟙 _)) :
    refineMap D hij hjk hik f ≫ refineMap D hij hjk hik g = 𝟙 _ := by
  simpa [refineMap, Functor.map_comp, Category.assoc] using
    congrArg (fun t ↦ (stageComparison D hij hjk hik M).inv ≫ t ≫
      (stageComparison D hij hjk hik M).hom) he

attribute [local irreducible] stageComparison refineMap affineLimitTensorPullbackComparison

private theorem common_limit_map_lifts
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ j : Iᵒᵖ, CompactSpace (D.obj j)]
    [∀ j : Iᵒᵖ, QuasiSeparatedSpace (D.obj j)]
    [∀ {j k : Iᵒᵖ} (f : j ⟶ k), IsAffineHom (D.map f)]
    (c : Cone D) (hc : IsLimit c)
    (i : I) (F_i G_i : (D.obj (op i)).Modules)
    (hF : F_i.IsFinitePresentation) (hG : G_i.IsFinitePresentation)
    (f : (tensorPullback (c.π.app (op i))).obj F_i ⟶
      (tensorPullback (c.π.app (op i))).obj G_i)
    (g : (tensorPullback (c.π.app (op i))).obj G_i ⟶
      (tensorPullback (c.π.app (op i))).obj F_i) :
    ∃ (j : I) (hij : i ≤ j)
      (f' : (tensorPullback (D.map (homOfLE hij).op)).obj F_i ⟶
        (tensorPullback (D.map (homOfLE hij).op)).obj G_i)
      (g' : (tensorPullback (D.map (homOfLE hij).op)).obj G_i ⟶
        (tensorPullback (D.map (homOfLE hij).op)).obj F_i),
      (affineLimitTensorPullbackComparison D c hij F_i).inv ≫
        (tensorPullback (c.π.app (op j))).map f' ≫
        (affineLimitTensorPullbackComparison D c hij G_i).hom = f ∧
      (affineLimitTensorPullbackComparison D c hij G_i).inv ≫
        (tensorPullback (c.π.app (op j))).map g' ≫
        (affineLimitTensorPullbackComparison D c hij F_i).hom = g := by
  have hmap := (finitePresentation_descent_affineLimit D c hc).2.1
  obtain ⟨a, hia, f', hf⟩ := hmap i F_i G_i hF hG f
  obtain ⟨b, hib, g', hg⟩ := hmap i G_i F_i hG hF g
  obtain ⟨j, haj, hbj⟩ := exists_ge_ge a b
  let hij : i ≤ j := hia.trans haj
  exact ⟨j, hij, refineMap D hia haj hij f', refineMap D hib hbj hij g',
    (refineMap_limit D c hia haj hij f').trans hf,
    (refineMap_limit D c hib hbj hij g').trans hg⟩

private theorem inverse_identities_eventually
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ j : Iᵒᵖ, CompactSpace (D.obj j)]
    [∀ j : Iᵒᵖ, QuasiSeparatedSpace (D.obj j)]
    [∀ {j k : Iᵒᵖ} (f : j ⟶ k), IsAffineHom (D.map f)]
    (c : Cone D) (hc : IsLimit c)
    (j : I) (F G : (D.obj (op j)).Modules)
    (hF : F.IsFinitePresentation) (hG : G.IsFinitePresentation)
    (f : F ⟶ G) (g : G ⟶ F)
    (hfg : (tensorPullback (c.π.app (op j))).map (f ≫ g) =
      (tensorPullback (c.π.app (op j))).map (𝟙 F))
    (hgf : (tensorPullback (c.π.app (op j))).map (g ≫ f) =
      (tensorPullback (c.π.app (op j))).map (𝟙 G)) :
    ∃ (k : I) (hjk : j ≤ k),
      (tensorPullback (D.map (homOfLE hjk).op)).map (f ≫ g) =
        (tensorPullback (D.map (homOfLE hjk).op)).map (𝟙 F) ∧
      (tensorPullback (D.map (homOfLE hjk).op)).map (g ≫ f) =
        (tensorPullback (D.map (homOfLE hjk).op)).map (𝟙 G) := by
  have heq := (finitePresentation_descent_affineLimit D c hc).2.2
  obtain ⟨a, hja, hea⟩ := heq j F F hF hF (f ≫ g) (𝟙 F) hfg
  obtain ⟨b, hjb, heb⟩ := heq j G G hG hG (g ≫ f) (𝟙 G) hgf
  obtain ⟨k, hak, hbk⟩ := exists_ge_ge a b
  let hjk : j ≤ k := hja.trans hak
  exact ⟨k, hjk, map_eq_later D hja hak hjk _ _ hea,
    map_eq_later D hjb hbk hjk _ _ heb⟩

/-- A specified isomorphism between limit pullbacks of fixed finitely presented
modules descends together with its inverse and both inverse identities.
The comparison is the existing canonical, section-normalized tensor-pullback comparison.

Source: Stacks Project, Limits, Tag 01ZR, clauses (2), (3), and Tag 0B8W,
proof of clause (2) (blueprint: lem-trf-fp-module-limit-isomorphism-descent).

Proof:
1. Tensor pullback preserves finite presentation. Locally pull back a finite free
   presentation: the adjunction of `def-pc-module-pullback` preserves its cokernel,
   and the tensor formula identifies the pullbacks of the finite free modules with
   finite free modules of the same ranks. Flatness is unnecessary.
2. Apply clause (2) of `lem-trf-fp-modules-affine-limit-descent` to the given
   isomorphism's forward map and separately to its inverse. Obtain stages a and b
   and maps whose canonical limit pullbacks are exactly these specified maps.
3. Choose a common upper stage j and pull both maps there, conjugating by the
   canonical composition comparisons. Naturality and the associativity identity
   `lem-pc-tensor-pullback-composition-associativity` identify successive and direct
   pullbacks. The limit pullbacks of the two composites are therefore identities.
4. The modules at j remain finitely presented by step 1. Apply clause (3) of
   `lem-trf-fp-modules-affine-limit-descent` to each composite and its identity.
   Choose a common upper stage k for the two resulting equalities. Pull both maps
   to k and conjugate to the direct pullbacks of the fixed models at i.
   Functoriality preserves both inverse identities; naturality and associativity
   preserve the two specified-lift equations. These are the four conclusions below.
-/
theorem finitePresentation_iso_descent_affineLimit
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ j : Iᵒᵖ, CompactSpace (D.obj j)]
    [∀ j : Iᵒᵖ, QuasiSeparatedSpace (D.obj j)]
    [∀ {j k : Iᵒᵖ} (f : j ⟶ k), IsAffineHom (D.map f)]
    (c : Cone D) (hc : IsLimit c)
    (i : I) (F_i G_i : (D.obj (op i)).Modules)
    (hF : F_i.IsFinitePresentation) (hG : G_i.IsFinitePresentation)
    (φ : (tensorPullback (c.π.app (op i))).obj F_i ≅
      (tensorPullback (c.π.app (op i))).obj G_i) :
    ∃ (k : I) (hik : i ≤ k)
      (u_k : (tensorPullback (D.map (homOfLE hik).op)).obj F_i ⟶
        (tensorPullback (D.map (homOfLE hik).op)).obj G_i)
      (v_k : (tensorPullback (D.map (homOfLE hik).op)).obj G_i ⟶
        (tensorPullback (D.map (homOfLE hik).op)).obj F_i),
      u_k ≫ v_k = 𝟙 ((tensorPullback (D.map (homOfLE hik).op)).obj F_i) ∧
      v_k ≫ u_k = 𝟙 ((tensorPullback (D.map (homOfLE hik).op)).obj G_i) ∧
      (affineLimitTensorPullbackComparison D c hik F_i).inv ≫
        (tensorPullback (c.π.app (op k))).map u_k ≫
        (affineLimitTensorPullbackComparison D c hik G_i).hom = φ.hom ∧
      (affineLimitTensorPullbackComparison D c hik G_i).inv ≫
        (tensorPullback (c.π.app (op k))).map v_k ≫
        (affineLimitTensorPullbackComparison D c hik F_i).hom = φ.inv := by
  obtain ⟨j, hij, f, g, hf, hg⟩ :=
    common_limit_map_lifts D c hc i F_i G_i hF hG φ.hom φ.inv
  have hFj := isFinitePresentation_tensorPullback (D.map (homOfLE hij).op) F_i
  have hGj := isFinitePresentation_tensorPullback (D.map (homOfLE hij).op) G_i
  have hfg := map_inverse_identity (tensorPullback (c.π.app (op j)))
    (affineLimitTensorPullbackComparison D c hij F_i)
    (affineLimitTensorPullbackComparison D c hij G_i) f g φ hf hg
  have hgf := map_inverse_identity (tensorPullback (c.π.app (op j)))
    (affineLimitTensorPullbackComparison D c hij G_i)
    (affineLimitTensorPullbackComparison D c hij F_i) g f φ.symm hg hf
  obtain ⟨k, hjk, hefg, hegf⟩ :=
    inverse_identities_eventually D c hc j _ _ hFj hGj f g hfg hgf
  let hik : i ≤ k := hij.trans hjk
  exact ⟨k, hik, refineMap D hij hjk hik f, refineMap D hij hjk hik g,
    refineMap_inverse_identity D hij hjk hik f g hefg,
    refineMap_inverse_identity D hij hjk hik g f hegf,
    (refineMap_limit D c hij hjk hik f).trans hf,
    (refineMap_limit D c hij hjk hik g).trans hg⟩

end AlgebraicGeometry.Scheme.Modules
