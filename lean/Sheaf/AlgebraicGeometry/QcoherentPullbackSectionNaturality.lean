/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups E9 and Q2
-/
module

public import Sheaf.AlgebraicGeometry.QcoherentPullbackSections
import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsMapNaturality
import Mathlib.CategoryTheory.Adjunction.CompositionIso

/-! # Restrictions of structural tensor pullback sections
Source: Stacks Project, Descent, Tag 03DR and Cohomology, Tag 01FD.

The private adjunction calculations adapt the proved arguments of
`WeilConjectures.AlgebraicGeometry.EtaleTensorSections` and
`WeilConjectures.AlgebraicGeometry.EtaleOpenQuasiCoherentIdentificationNaturality`.
They apply to arbitrary scheme triangles, since the first projection of a base
change need not be etale.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option autoImplicit false
attribute [local irreducible] tensorPullback tensorPullbackObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The global-section unit for an arbitrary left adjoint of scheme pushforward.
Source: Stacks, Tag 03DR (blueprint: lem-pbc-qcoherent-pullback-section-naturality). -/
private def sectionsUnitOfAdjunction {A B : Scheme.{u}} (f : A ⟶ B)
    (L : B.Modules ⥤ A.Modules) (adj : L ⊣ pushforward f) (G : B.Modules) :
    Γ(G, ⊤) ⟶ Γ(L.obj G, ⊤) :=
  (adj.unit.app G).app ⊤ ≫ (L.obj G).presheaf.map (homOfLE f.preimage_top.ge).op

/-- The normalized composition map for a family of left adjoints.
Source: Stacks, Tag 03DR (blueprint: lem-pbc-qcoherent-pullback-section-naturality). -/
private def compOfAdjunction
    (L : ∀ {A B : Scheme.{u}}, (A ⟶ B) → B.Modules ⥤ A.Modules)
    (adj : ∀ {A B : Scheme.{u}} (f : A ⟶ B), L f ⊣ pushforward f)
    {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) :
    L b ⋙ L a ≅ L (a ≫ b) :=
  (conjugateIsoEquiv (adj (a ≫ b)) ((adj b).comp (adj a))).symm
    (pushforwardComp a b).symm

/-- Naturality of the unit on global sections.
Source: Stacks, Tag 03DR (blueprint: lem-pbc-qcoherent-pullback-section-naturality). -/
private theorem sectionsUnit_naturality {A B : Scheme.{u}} (f : A ⟶ B)
    (L : B.Modules ⥤ A.Modules) (adj : L ⊣ pushforward f)
    {M N : B.Modules} (φ : M ⟶ N) :
    φ.app ⊤ ≫ sectionsUnitOfAdjunction f L adj N =
      sectionsUnitOfAdjunction f L adj M ≫ (L.map φ).app ⊤ := by
  have hu := congrArg (fun t ↦ t.app ⊤) (adj.unit_naturality φ).symm
  change φ.app ⊤ ≫ (adj.unit.app N).app ⊤ =
    (adj.unit.app M).app ⊤ ≫ (L.map φ).app (f ⁻¹ᵁ ⊤) at hu
  have hn := (L.map φ).val.naturality (homOfLE f.preimage_top.ge).op
  have ht := congrArg (fun t ↦ (forget₂ _ AddCommGrpCat).map t) hn
  change (L.obj M).presheaf.map (homOfLE f.preimage_top.ge).op ≫ (L.map φ).app ⊤ =
    (L.map φ).app (f ⁻¹ᵁ ⊤) ≫
      (L.obj N).presheaf.map (homOfLE f.preimage_top.ge).op at ht
  unfold sectionsUnitOfAdjunction
  rw [← Category.assoc, hu, Category.assoc, ← ht, ← Category.assoc]

/-- The unit equation before taking global sections.
Source: Stacks, Tag 03DR (blueprint: lem-pbc-qcoherent-pullback-section-naturality). -/
private theorem comp_unit
    (L : ∀ {A B : Scheme.{u}}, (A ⟶ B) → B.Modules ⥤ A.Modules)
    (adj : ∀ {A B : Scheme.{u}} (f : A ⟶ B), L f ⊣ pushforward f)
    {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) (G : C.Modules) :
    (adj (a ≫ b)).unit.app G ≫ (pushforwardComp a b).inv.app _ =
      (adj b).unit.app G ≫ (pushforward b).map ((adj a).unit.app ((L b).obj G)) ≫
        (pushforward a ⋙ pushforward b).map ((compOfAdjunction L adj a b).hom.app G) := by
  exact unit_conjugateEquiv_symm (adj (a ≫ b)) ((adj b).comp (adj a))
    (pushforwardComp a b).inv G

/-- The inverse image of the whole scheme contributes an identity restriction.
Source: Stacks, Tag 03DR (blueprint: lem-pbc-qcoherent-pullback-section-naturality). -/
private theorem sectionsUnit_eq {A B : Scheme.{u}} (f : A ⟶ B)
    (L : B.Modules ⥤ A.Modules) (adj : L ⊣ pushforward f) (G : B.Modules) :
    sectionsUnitOfAdjunction f L adj G =
      (show Γ(G, ⊤) ⟶ Γ(L.obj G, ⊤) from (adj.unit.app G).app ⊤) := by
  have hi : homOfLE f.preimage_top.ge = 𝟙 (⊤ : Opens A) := rfl
  unfold sectionsUnitOfAdjunction
  erw [hi, op_id, (L.obj G).presheaf.map_id, Category.comp_id]

/-- Successive global-section units agree with the composite unit.
Source: Stacks, Tag 03DR (blueprint: lem-pbc-qcoherent-pullback-section-naturality). -/
private theorem sectionsUnit_comp
    (L : ∀ {A B : Scheme.{u}}, (A ⟶ B) → B.Modules ⥤ A.Modules)
    (adj : ∀ {A B : Scheme.{u}} (f : A ⟶ B), L f ⊣ pushforward f)
    {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) (G : C.Modules) :
    sectionsUnitOfAdjunction b (L b) (adj b) G ≫
      sectionsUnitOfAdjunction a (L a) (adj a) ((L b).obj G) ≫
      ((compOfAdjunction L adj a b).hom.app G).app ⊤ =
    sectionsUnitOfAdjunction (a ≫ b) (L (a ≫ b)) (adj (a ≫ b)) G := by
  have hu := congrArg (fun t ↦ t.app ⊤) (comp_unit L adj a b G)
  erw [sectionsUnit_eq, sectionsUnit_eq, sectionsUnit_eq]
  simp only [Hom.comp_app, pushforward_map_app, Functor.comp_map,
    pushforwardComp_inv_app_app] at hu
  change ((adj (a ≫ b)).unit.app G).app ⊤ ≫ 𝟙 _ =
    ((adj b).unit.app G).app ⊤ ≫
      ((adj a).unit.app ((L b).obj G)).app ⊤ ≫
      ((compOfAdjunction L adj a b).hom.app G).app ⊤ at hu
  erw [Category.comp_id] at hu
  exact hu.symm

/-- Associativity of the normalized comparison maps.
Source: Stacks, Tag 03DR; Mathlib `Adjunction.leftAdjointCompIso_assoc`
(blueprint: lem-pbc-qcoherent-pullback-section-naturality). -/
private theorem compOfAdjunction_assoc
    (L : ∀ {A B : Scheme.{u}}, (A ⟶ B) → B.Modules ⥤ A.Modules)
    (adj : ∀ {A B : Scheme.{u}} (f : A ⟶ B), L f ⊣ pushforward f)
    {A B C D : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D) (F : D.Modules) :
    ((compOfAdjunction L adj a b).hom.app ((L c).obj F)) ≫
      (compOfAdjunction L adj (a ≫ b) c).hom.app F ≫
      eqToHom (congrArg (fun f ↦ (L f).obj F) (Category.assoc a b c)) =
    (L a).map ((compOfAdjunction L adj b c).hom.app F) ≫
      (compOfAdjunction L adj a (b ≫ c)).hom.app F := by
  have he : Functor.isoWhiskerLeft (pushforward a) (pushforwardComp b c) ≪≫
      pushforwardComp a (b ≫ c) =
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (pushforwardComp a b) (pushforward c) ≪≫
        pushforwardComp (a ≫ b) c := by
    ext M V x
    rfl
  have h := Adjunction.leftAdjointCompIso_assoc (adj c) (adj b) (adj a)
    (adj (b ≫ c)) (adj (a ≫ b)) (adj (a ≫ (b ≫ c)))
    (pushforwardComp b c) (pushforwardComp a b)
    (pushforwardComp (a ≫ b) c) (pushforwardComp a (b ≫ c)) he
  have hc := congrArg (fun e ↦ e.hom.app F) h
  dsimp only [Adjunction.leftAdjointCompIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.associator_inv_app] at hc
  erw [Category.id_comp] at hc
  erw [eqToHom_refl, Category.comp_id]
  exact hc

/-- The two section maps for three composable scheme morphisms agree.
Source: Stacks, Tag 03DR (blueprint: lem-pbc-qcoherent-pullback-section-naturality). -/
private theorem tripleSections
    (L : ∀ {A B : Scheme.{u}}, (A ⟶ B) → B.Modules ⥤ A.Modules)
    (adj : ∀ {A B : Scheme.{u}} (f : A ⟶ B), L f ⊣ pushforward f)
    {A B C D : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D) (F : D.Modules) :
    sectionsUnitOfAdjunction (a ≫ b) (L (a ≫ b)) (adj (a ≫ b)) ((L c).obj F) ≫
      ((compOfAdjunction L adj (a ≫ b) c).hom.app F).app ⊤ ≫
      (eqToHom (congrArg (fun f ↦ (L f).obj F) (Category.assoc a b c))).app ⊤ =
    (sectionsUnitOfAdjunction b (L b) (adj b) ((L c).obj F) ≫
      ((compOfAdjunction L adj b c).hom.app F).app ⊤) ≫
    (sectionsUnitOfAdjunction a (L a) (adj a) ((L (b ≫ c)).obj F) ≫
      ((compOfAdjunction L adj a (b ≫ c)).hom.app F).app ⊤) := by
  have ha := congrArg (fun φ ↦ φ.app ⊤) (compOfAdjunction_assoc L adj a b c F)
  simp only [Hom.comp_app] at ha
  rw [← sectionsUnit_comp L adj a b ((L c).obj F)]
  simp only [Category.assoc]
  rw [ha]
  have hn := sectionsUnit_naturality a (L a) (adj a)
    ((compOfAdjunction L adj b c).hom.app F)
  dsimp only [Functor.comp_obj] at hn
  exact (by simpa only [Category.assoc] using
    congrArg (fun t ↦ sectionsUnitOfAdjunction b (L b) (adj b) ((L c).obj F) ≫
      t ≫ ((compOfAdjunction L adj a (b ≫ c)).hom.app F).app ⊤) hn.symm)

/-- Normalized sections restriction along a commutative triangle.
Source: Stacks, Tag 03DR (blueprint: lem-pbc-qcoherent-pullback-section-naturality). -/
private def restrictionOfAdjunction
    (L : ∀ {A B : Scheme.{u}}, (A ⟶ B) → B.Modules ⥤ A.Modules)
    (adj : ∀ {A B : Scheme.{u}} (f : A ⟶ B), L f ⊣ pushforward f)
    {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) (d : A ⟶ C)
    (p : a ≫ b = d) (F : C.Modules) : Γ((L b).obj F, ⊤) ⟶ Γ((L d).obj F, ⊤) :=
  sectionsUnitOfAdjunction a (L a) (adj a) ((L b).obj F) ≫
    ((compOfAdjunction L adj a b).hom.app F).app ⊤ ≫
    (eqToHom (congrArg (fun f ↦ (L f).obj F) p)).app ⊤

/-- Composition of normalized sections restrictions along commutative triangles.
Source: Stacks, Tag 03DR (blueprint: lem-pbc-qcoherent-pullback-section-naturality). -/
private theorem restrictionOfAdjunction_comp
    (L : ∀ {A B : Scheme.{u}}, (A ⟶ B) → B.Modules ⥤ A.Modules)
    (adj : ∀ {A B : Scheme.{u}} (f : A ⟶ B), L f ⊣ pushforward f)
    {A B C D : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D)
    (d : B ⟶ D) (e : A ⟶ D) (p : b ≫ c = d) (q : a ≫ d = e)
    (r : (a ≫ b) ≫ c = e) (F : D.Modules) :
    restrictionOfAdjunction L adj (a ≫ b) c e r F =
      restrictionOfAdjunction L adj b c d p F ≫
        restrictionOfAdjunction L adj a d e q F := by
  subst d
  subst e
  unfold restrictionOfAdjunction
  have h := tripleSections L adj a b c F
  simpa only [eqToHom_refl, Hom.id_app, Category.comp_id] using h

/-- Restriction along equal triangle arrows is unchanged; proof terms are irrelevant.
Source: Stacks, Tag 03DR, equation-quasi-coherent-presheaf. -/
private theorem restrictionOfAdjunction_congr
    (L : ∀ {A B : Scheme.{u}}, (A ⟶ B) → B.Modules ⥤ A.Modules)
    (adj : ∀ {A B : Scheme.{u}} (f : A ⟶ B), L f ⊣ pushforward f)
    {A B C : Scheme.{u}} (a a' : A ⟶ B) (b : B ⟶ C) (d : A ⟶ C)
    (e : a = a') (p : a ≫ b = d) (q : a' ≫ b = d) (F : C.Modules) :
    restrictionOfAdjunction L adj a b d p F =
      restrictionOfAdjunction L adj a' b d q F := by
  subst a'
  rfl

/-- Move an inverse composition comparison across the other composition comparison.
Source: Stacks 03DR, equation-quasi-coherent-presheaf. This follows by cancelling
isomorphisms in the forward associativity equation. -/
private theorem composition_inverse
    (L : ∀ {A B : Scheme.{u}}, (A ⟶ B) → B.Modules ⥤ A.Modules)
    (adj : ∀ {A B : Scheme.{u}} (f : A ⟶ B), L f ⊣ pushforward f)
    {A B C D : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D)
    (F : D.Modules) :
    (compOfAdjunction L adj a (b ≫ c)).hom.app F ≫
      (compOfAdjunction L adj (a ≫ b) c).inv.app F =
    (L a).map ((compOfAdjunction L adj b c).inv.app F) ≫
      (compOfAdjunction L adj a b).hom.app ((L c).obj F) := by
  have h := compOfAdjunction_assoc L adj a b c F
  simp only [eqToHom_refl, Category.comp_id] at h
  apply (cancel_epi ((L a).map ((compOfAdjunction L adj b c).hom.app F))).mp
  rw [← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id_app]
  erw [Category.comp_id]
  rw [← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id]
  erw [Category.id_comp]

/-- Inverse composition comparisons intertwine restrictions along scheme triangles.
Source: Stacks, Tag 03DR, equation-quasi-coherent-presheaf. -/
private theorem composition_restriction
    (L : ∀ {A B : Scheme.{u}}, (A ⟶ B) → B.Modules ⥤ A.Modules)
    (adj : ∀ {A B : Scheme.{u}} (f : A ⟶ B), L f ⊣ pushforward f)
    {A B C D : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) (c : A ⟶ C)
    (j : C ⟶ D) (h : a ≫ b = c) (F : D.Modules) :
    restrictionOfAdjunction L adj a (b ≫ j) (c ≫ j)
        (by rw [← Category.assoc, h]) F ≫
      ((compOfAdjunction L adj c j).inv.app F).app ⊤ =
    ((compOfAdjunction L adj b j).inv.app F).app ⊤ ≫
      restrictionOfAdjunction L adj a b c h ((L j).obj F) := by
  subst c
  unfold restrictionOfAdjunction
  simp only [eqToHom_refl, Hom.id_app, Category.comp_id]
  have hc := congrArg (fun φ ↦ φ.app ⊤) (composition_inverse L adj a b j F)
  simp only [Hom.comp_app] at hc
  rw [Category.assoc, hc, ← Category.assoc, ← sectionsUnit_naturality, Category.assoc]
  rfl

/-- Combine the three commuting diagram pieces by associativity.
Source: the diagram composition in Stacks, Tag 03DR. -/
private theorem combine_triangles {C : Type*} [Category C]
    {S A B D E H I J : C}
    {a : S ⟶ A} {b : A ⟶ D} {c : S ⟶ B} {d : B ⟶ D}
    {i : D ⟶ E} {j : B ⟶ H} {e : H ⟶ E}
    {m : E ⟶ J} {n : H ⟶ I} {r : I ⟶ J}
    (ht : a ≫ b = c ≫ d) (hc : d ≫ i = j ≫ e) (hn : e ≫ m = n ≫ r) :
    a ≫ (b ≫ i ≫ m) = (c ≫ j ≫ n) ≫ r := by
  calc
    _ = (a ≫ b) ≫ i ≫ m := by simp only [Category.assoc]
    _ = (c ≫ d) ≫ i ≫ m := by rw [ht]
    _ = c ≫ (d ≫ i) ≫ m := by simp only [Category.assoc]
    _ = c ≫ (j ≫ e) ≫ m := by rw [hc]
    _ = _ := by
      simpa only [Category.assoc] using congrArg (fun z ↦ c ≫ j ≫ z) hn

/-- Naturality for arbitrary adjoints of scheme pushforward and a commutative square.
Source: Stacks, Tag 03DR, equation-quasi-coherent-presheaf. Compose the two pairs
of triangle restrictions, identify their projection composites, move the inverse
comparison through the remaining triangle, and use coefficient naturality `hn`.
All the diagram algebra is performed before specializing the left adjoints. -/
private theorem square_sections
    (L : ∀ {A B : Scheme.{u}}, (A ⟶ B) → B.Modules ⥤ A.Modules)
    (adj : ∀ {A B : Scheme.{u}} (f : A ⟶ B), L f ⊣ pushforward f)
    {X Y A B A' B' : Scheme.{u}} (g : Y ⟶ X)
    (a : A ⟶ X) (b : B ⟶ X) (a' : A' ⟶ Y) (b' : B' ⟶ Y)
    (h : B ⟶ A) (k : B' ⟶ A') (p : A' ⟶ A) (q : B' ⟶ B)
    (hh : h ≫ a = b) (hk : k ≫ a' = b')
    (hp : p ≫ a = a' ≫ g) (hq : q ≫ b = b' ≫ g) (he : k ≫ p = q ≫ h)
    (F : X.Modules) (G : Y.Modules) (ψ : (L g).obj F ⟶ G)
    (hn : restrictionOfAdjunction L adj k a' b' hk ((L g).obj F) ≫
        ((L b').map ψ).app ⊤ =
      ((L a').map ψ).app ⊤ ≫ restrictionOfAdjunction L adj k a' b' hk G) :
    restrictionOfAdjunction L adj h a b hh F ≫
        (restrictionOfAdjunction L adj q b (b' ≫ g) hq F ≫
          ((compOfAdjunction L adj b' g).inv.app F).app ⊤ ≫
          ((L b').map ψ).app ⊤) =
      (restrictionOfAdjunction L adj p a (a' ≫ g) hp F ≫
        ((compOfAdjunction L adj a' g).inv.app F).app ⊤ ≫
        ((L a').map ψ).app ⊤) ≫ restrictionOfAdjunction L adj k a' b' hk G := by
  have hk' : k ≫ (a' ≫ g) = b' ≫ g :=
    (Category.assoc k a' g).symm.trans (congrArg (fun f ↦ f ≫ g) hk)
  have rV : (q ≫ h) ≫ a = b' ≫ g :=
    (Category.assoc q h a).trans ((congrArg (fun f ↦ q ≫ f) hh).trans hq)
  have rU : (k ≫ p) ≫ a = b' ≫ g :=
    (Category.assoc k p a).trans ((congrArg (fun f ↦ k ≫ f) hp).trans hk')
  have ht : restrictionOfAdjunction L adj h a b hh F ≫
      restrictionOfAdjunction L adj q b (b' ≫ g) hq F =
    restrictionOfAdjunction L adj p a (a' ≫ g) hp F ≫
      restrictionOfAdjunction L adj k (a' ≫ g) (b' ≫ g) hk' F :=
    (restrictionOfAdjunction_comp L adj q h a b (b' ≫ g) hh hq rV F).symm.trans
      ((restrictionOfAdjunction_congr L adj (q ≫ h) (k ≫ p) a (b' ≫ g)
        he.symm rV rU F).trans
          (restrictionOfAdjunction_comp L adj k p a (a' ≫ g) (b' ≫ g) hp hk' rU F))
  have hc := composition_restriction L adj k a' b' g hk F
  exact combine_triangles ht hc hn

/-- Identify the generic normalized comparison without unfolding tensor pullbacks.
Source: the definition of normalized composition in Stacks, Tag 03DR. -/
private theorem compOfAdjunction_tensor {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) :
    compOfAdjunction (@tensorPullback)
      (fun {_A _B} f ↦ Classical.choose (exists_tensorPullbackAdjunction f)) a b =
      tensorSectionsComp a b := rfl

/-- Identify a generic triangle restriction using the named tensor-section operations.
Source: Stacks, Tag 03DR, equation-quasi-coherent-presheaf. -/
private theorem restrictionOfAdjunction_tensor {A B C : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ C) (c : A ⟶ C) (h : a ≫ b = c) (F : C.Modules) :
    restrictionOfAdjunction (@tensorPullback)
        (fun {_A _B} f ↦ Classical.choose (exists_tensorPullbackAdjunction f)) a b c h F =
      tensorSectionsUnit a ((tensorPullback b).obj F) ≫
        ((tensorSectionsComp a b).hom.app F).app ⊤ ≫
        (eqToHom (congrArg (fun f ↦ (tensorPullback f).obj F) h)).app ⊤ := rfl

/-- Structural pullback across base-change squares commutes with restrictions.
This only concerns additive section maps, without any cohomology comparison.

Source: Stacks Project, Descent, Tag 03DR, equation (35.8.1);
Cohomology, Tag 01FD.
(blueprint: lem-pbc-qcoherent-pullback-section-naturality).

Proof: Expand both restrictions and qcoherentPullbackSection. Naturality of the
adjunction unit moves the coefficient morphism through section pullback.
The normalized left-adjoint composition isomorphisms satisfy associativity,
since their right adjoints are the sectionwise pushforward compositions.
Apply that associativity to the two triangles in the square of pullbacks.
The universal property of pullback identifies the composites of the projection
maps. Equality transport respects composition. Cancel the two inverse
composition comparisons, and use coefficient naturality of tensor restrictions.
Evaluation on global sections gives the equality. No flatness, affineness,
compactness, separatedness or quasi-coherence is used, so the empty and zero
cases are included. -/
theorem qcoherentPullbackSection_naturality {X Y : Scheme.{u}} (g : Y ⟶ X)
    (F : X.Modules) (G : Y.Modules) (ψ : (tensorPullback g).obj F ⟶ G)
    {U V : X.Etale} (h : V ⟶ U) :
    etaleTensorSectionsRestriction F h ≫
        qcoherentPullbackSection g F G ψ V
          ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ g).obj V)
          (pullback.fst V.hom g) pullback.condition =
      qcoherentPullbackSection g F G ψ U
          ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ g).obj U)
          (pullback.fst U.hom g) pullback.condition ≫
        etaleTensorSectionsRestriction G
          ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ g).map h) := by
  let P := MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ g
  let U' := P.obj U
  let V' := P.obj V
  let k : V' ⟶ U' := P.map h
  change etaleTensorSectionsRestriction F h ≫
      qcoherentPullbackSection g F G ψ V V' (pullback.fst V.hom g) pullback.condition =
    qcoherentPullbackSection g F G ψ U U' (pullback.fst U.hom g) pullback.condition ≫
      etaleTensorSectionsRestriction G k
  have hp : k.left ≫ pullback.fst U.hom g = pullback.fst V.hom g ≫ h.left := by
    simp [k, P]
  have hn := etaleTensorSectionsMap_naturality ψ k
  have hn' : restrictionOfAdjunction (@tensorPullback)
        (fun {_A _B} f ↦ Classical.choose (exists_tensorPullbackAdjunction f))
        k.left U'.hom V'.hom k.w ((tensorPullback g).obj F) ≫
        ((tensorPullback V'.hom).map ψ).app ⊤ =
      ((tensorPullback U'.hom).map ψ).app ⊤ ≫
        restrictionOfAdjunction (@tensorPullback)
          (fun {_A _B} f ↦ Classical.choose (exists_tensorPullbackAdjunction f))
          k.left U'.hom V'.hom k.w G := by
    simpa only [restrictionOfAdjunction_tensor, etaleTensorSectionsRestriction] using hn
  have hs := square_sections (@tensorPullback)
    (fun {_A _B} f ↦ Classical.choose (exists_tensorPullbackAdjunction f))
    g U.hom V.hom U'.hom V'.hom h.left k.left
    (pullback.fst U.hom g) (pullback.fst V.hom g)
    h.w k.w pullback.condition pullback.condition hp F G ψ hn'
  simpa only [restrictionOfAdjunction_tensor, compOfAdjunction_tensor,
    qcoherentPullbackSection, etaleTensorSectionsRestriction, Category.assoc] using hs


end
end AlgebraicGeometry.Scheme.Modules
