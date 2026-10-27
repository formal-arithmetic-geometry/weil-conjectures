module

public import Sheaf.CategoryTheory.StrictDiagramPseudococone
public import WeilConjectures.CategoryTheory.FilteredColimitCategories
public import Mathlib.CategoryTheory.Limits.Final
import WeilConjectures.CategoryTheory.FilteredColimitFunctorDescent
import Sheaf.CategoryTheory.FilteredPseudococoneEffectivity

/-! # Filtered category colimits and pseudococones

Source: Stacks Project, Categories, Tags 04AX and 04E7; Tag 004A is contextual.
The category-valued finite-representative extension is not asserted verbatim by those tags.
(blueprint: lem-per-filtered-category-pseudococones).

The object- and arrow-colimit hypotheses specify the presentation supplied by
`CategoryTheory.exists_filteredColimit_category`. They allow any choice of those set colimits.
-/

@[expose] public section

universe z u v u' v'

open CategoryTheory.Limits CategoryTheory.Functor

namespace CategoryTheory

private theorem comparison_component_eq
    {C : Type z} [SmallCategory C] {B : Type z} [SmallCategory B]
    {A : Type u} [Category.{v} A] {l r : C ⥤ B} (h : r = l)
    {F G : B ⥤ A} (α : l ⋙ F ⟶ l ⋙ G) (β : r ⋙ F ⟶ r ⋙ G) (x : C)
    (hc : (isoWhiskerRight (eqToIso h) F).hom.app x ≫ α.app x =
      β.app x ≫ (isoWhiskerRight (eqToIso h) G).hom.app x) :
    Arrow.mk (α.app x) = Arrow.mk (β.app x) := by
  subst r
  have he : α.app x = β.app x := by simpa using hc
  exact congrArg Arrow.mk he

private theorem restriction_fullyFaithful
    {J : Type z} [SmallCategory J] (D : J ⥤ Cat.{z, z})
    (c : Cocone D) (ho : IsColimit (Cat.objects.mapCocone c))
    (ha : IsColimit (Cat.arrows.mapCocone c))
    (A : Type u) [Category.{v} A] :
    (StrictDiagramPseudococone.restriction c A).Faithful ∧
      (StrictDiagramPseudococone.restriction c A).Full := by
  constructor
  · constructor
    intro F G α β he
    ext X
    obtain ⟨j, x, hx⟩ := Types.jointly_surjective_of_isColimit ho X
    change (c.ι.app j).toFunctor.obj x = X at hx
    subst X
    exact congrArg (fun t ↦ (t.app j).app x) he
  · constructor
    intro F G ρ
    let t : (D ⋙ Cat.objects).CoconeTypes :=
      { pt := Arrow A
        ι j x := Arrow.mk ((ρ.app j).app x)
        ι_naturality := by
          intro j k a
          funext x
          exact (comparison_component_eq
            (congrArg Cat.Hom.toFunctor (c.w a)) (ρ.app j)
            (whiskerLeft (D.map a).toFunctor (ρ.app k)) x
            (ρ.compatibility a x)).symm }
    obtain ⟨m, hm⟩ :=
      ((Types.isColimit_iff_coconeTypesIsColimit (Cat.objects.mapCocone c)).mp
        ⟨ho⟩).exists_desc t
    have hrep (j : J) (x : D.obj j) :
        m ((c.ι.app j).toFunctor.obj x) = Arrow.mk ((ρ.app j).app x) :=
      congrFun (hm j) x
    have hl (X : c.pt) : (m X).left = F.obj X := by
      obtain ⟨j, x, hx⟩ := Types.jointly_surjective_of_isColimit ho X
      change (c.ι.app j).toFunctor.obj x = X at hx
      subst X
      exact congrArg Arrow.left (hrep j x)
    have hr (X : c.pt) : (m X).right = G.obj X := by
      obtain ⟨j, x, hx⟩ := Types.jointly_surjective_of_isColimit ho X
      change (c.ι.app j).toFunctor.obj x = X at hx
      subst X
      exact congrArg Arrow.right (hrep j x)
    let app (X : c.pt) : F.obj X ⟶ G.obj X :=
      eqToHom (hl X).symm ≫ (m X).hom ≫ eqToHom (hr X)
    have happ (X : c.pt) : Arrow.mk (app X) = m X := by simp [app]
    have happ_rep (j : J) (x : D.obj j) :
        app ((c.ι.app j).toFunctor.obj x) = (ρ.app j).app x := by
      apply Arrow.mk_injective
      exact (happ _).trans (hrep j x)
    have hn (a : Arrow c.pt) :
        F.map a.hom ≫ app a.right = app a.left ≫ G.map a.hom := by
      obtain ⟨j, f, hf⟩ := Types.jointly_surjective_of_isColimit ha a
      change Arrow.mk ((c.ι.app j).toFunctor.map f.hom) = a at hf
      subst a
      simp only [Arrow.mk_left, Arrow.mk_right, Arrow.mk_hom, happ_rep]
      exact (ρ.app j).naturality f.hom
    let α : F ⟶ G := { app := app, naturality := fun X Y f ↦ hn (Arrow.mk f) }
    refine ⟨α, ?_⟩
    apply StrictDiagramPseudococone.hom_ext
    intro j
    ext x
    exact happ_rep j x

/-- Restriction is an equivalence from functors on the set-presented filtered colimit to
coherent pseudococones.

Source: finite-representative extension of Stacks Tag 04AX
(blueprint: lem-per-filtered-category-pseudococones).

Proof (node Steps 1--3): use the canonical transports of
lem-per-filtered-pseudocone-representative-transport. Choose a representative r_z for each
object z. Send z to the value of its representative. For an arrow represented by f:x→y,
send it to T_(y,r_target) A_i(f) T_(r_source,x). The transport square for equal arrow
representatives proves independence. Lift a composable pair and its endpoint equalities to
one stage by lem-weil-pbc-filtered-colimit-categories: the middle transports cancel, giving
composition, and the identity calculation gives preservation of identities. The transports
from chosen representatives to stage representatives give a coherent natural isomorphism
from the restriction of this functor to the original pseudococone. This proves essential
surjectivity. A modification between restrictions has a component at each object independent
of its representative, by eventual equality of object representatives. Naturality holds on
stage arrows and hence on every arrow. Every object is a stage image, proving uniqueness.
Restriction is fully faithful and essentially surjective, so apply
lem-trf-fully-faithful-ess-surj-equivalence. -/
theorem filteredColimit_restriction_isEquivalence
    {J : Type z} [SmallCategory J] [IsFiltered J] (D : J ⥤ Cat.{z, z})
    (c : Cocone D) (hobjects : IsColimit (Cat.objects.mapCocone c))
    (harrows : IsColimit (Cat.arrows.mapCocone c))
    (A : Type u) [Category.{v} A] :
    (StrictDiagramPseudococone.restriction c A).IsEquivalence := by
  obtain ⟨hfaithful, hfull⟩ := restriction_fullyFaithful D c hobjects harrows A
  exact ⟨hfaithful, hfull, filteredPseudococone_effective D c hobjects harrows A⟩

/-- Restriction commutes with postcomposition, including transformations of the vertex functor.

Source: finite-representative extension of Stacks Tag 04AX
(blueprint: lem-per-filtered-category-pseudococones).

Proof (node Step 3, last sentences): both composite functors send F to the family v_j F H,
with comparisons obtained by applying H to the equality comparisons of v_j F. Their maps
are the same whiskered transformations. Equality follows componentwise, with proof
irrelevance for the coherence fields. For t:H→H', both transformations have component
at (F,j,x) equal to t at F(v_j x). Thus the transformation equality holds after identifying
the equal source and target functors; HEq records exactly this identification. -/
theorem pseudococone_restriction_naturality
    {J : Type z} [SmallCategory J] (D : J ⥤ Cat.{z, z}) (c : Cocone D)
    {A : Type u} [Category.{v} A] {B : Type u'} [Category.{v'} B] :
    (∀ H : A ⥤ B,
      StrictDiagramPseudococone.restriction c A ⋙
          StrictDiagramPseudococone.postcompose H =
        (whiskeringRight c.pt A B).obj H ⋙
          StrictDiagramPseudococone.restriction c B) ∧
    (∀ (H H' : A ⥤ B) (t : H ⟶ H'),
      HEq (whiskerLeft (StrictDiagramPseudococone.restriction c A)
        (StrictDiagramPseudococone.postcomposeMap (D := D) t))
        (whiskerRight ((whiskeringRight c.pt A B).map t)
          (StrictDiagramPseudococone.restriction c B))) := by
  constructor
  · intro H
    rfl
  · intro H H' t
    rfl

private theorem arrowHomHEq {C : Type u} [Category.{v} C] {a b : Arrow C}
    (h : a = b) : HEq a.hom b.hom := by
  cases h
  rfl

private theorem stageFunctor_ext
    {J : Type z} [SmallCategory J] {D : J ⥤ Cat.{z, z}}
    (c : Cocone D) (ho : IsColimit (Cat.objects.mapCocone c))
    (ha : IsColimit (Cat.arrows.mapCocone c))
    {A : Type u} [Category.{v} A] {F G : c.pt ⥤ A}
    (h : ∀ j, (c.ι.app j).toFunctor ⋙ F = (c.ι.app j).toFunctor ⋙ G) : F = G := by
  apply Functor.hext
  · intro X
    obtain ⟨j, x, hx⟩ := Types.jointly_surjective_of_isColimit ho X
    change (c.ι.app j).toFunctor.obj x = X at hx
    subst X
    exact congrArg (fun H : D.obj j ⥤ A ↦ H.obj x) (h j)
  · intro X Y f
    have he : Arrow.mk (F.map f) = Arrow.mk (G.map f) := by
      obtain ⟨j, a, he⟩ := Types.jointly_surjective_of_isColimit ha (Arrow.mk f)
      change Arrow.mk ((c.ι.app j).toFunctor.map a.hom) = Arrow.mk f at he
      have he' := congrArg (fun H : D.obj j ⥤ A ↦ Arrow.mk (H.map a.hom)) (h j)
      exact (congrArg F.mapArrow.obj he).symm.trans
        (he'.trans (congrArg G.mapArrow.obj he))
    exact arrowHomHEq he

private noncomputable def setPresentedIsColimit
    {J : Type z} [SmallCategory J] [IsFiltered J] (D : J ⥤ Cat.{z, z})
    (c : Cocone D) (ho : IsColimit (Cat.objects.mapCocone c))
    (ha : IsColimit (Cat.arrows.mapCocone c)) : IsColimit c :=
  IsColimit.ofExistsUnique fun s ↦ by
    obtain ⟨F, hF⟩ := @exists_filteredColimit_functor_descent J _ _ D c
      ⟨ho⟩ ⟨ha⟩ s.pt (Cat.str s.pt)
      (fun j ↦ (s.ι.app j).toFunctor)
      (fun j k a ↦ congrArg Cat.Hom.toFunctor (s.w a))
    refine ⟨F.toCatHom, fun j ↦ Cat.ext (hF j), ?_⟩
    intro m hm
    apply Cat.ext
    apply stageFunctor_ext c ho ha
    intro j
    exact (congrArg Cat.Hom.toFunctor (hm j)).trans (hF j).symm

private theorem pseudococone_hext
    {J : Type z} [SmallCategory J] {D : J ⥤ Cat.{z, z}}
    {A : Type u} [Category.{v} A] (P Q : StrictDiagramPseudococone D A)
    (h : P.functor = Q.functor)
    (hc : ∀ {j k : J} (a : j ⟶ k), HEq (P.comparison a) (Q.comparison a)) : P = Q := by
  cases P
  cases Q
  cases h
  congr
  funext j k a
  exact eq_of_heq (hc a)

private theorem pseudococoneHom_hext
    {J : Type z} [SmallCategory J] {D : J ⥤ Cat.{z, z}}
    {A : Type u} [Category.{v} A] {P Q P' Q' : StrictDiagramPseudococone D A}
    (hP : P = P') (hQ : Q = Q') (f : P ⟶ Q) (g : P' ⟶ Q')
    (h : ∀ j x, HEq ((f.app j).app x) ((g.app j).app x)) : HEq f g := by
  cases hP
  cases hQ
  apply heq_of_eq
  apply StrictDiagramPseudococone.hom_ext
  intro j
  ext x
  exact eq_of_heq (h j x)

private theorem isoWhiskerRight_eqToIso
    {C : Type z} [Category.{z} C] {A : Type u} [Category.{v} A]
    {B : Type u'} [Category.{v'} B] {F G : C ⥤ A} (h : F = G) (H : A ⥤ B) :
    isoWhiskerRight (eqToIso h) H = eqToIso (congrArg (fun K ↦ K ⋙ H) h) := by
  subst G
  ext x
  simp

private theorem eqToIsoHEq {C : Type u} [Category.{v} C] {X Y X' Y' : C}
    (hX : X = X') (hY : Y = Y') (h : X = Y) (h' : X' = Y') :
    HEq (eqToIso h) (eqToIso h') := by
  cases hX
  cases hY
  rfl

private theorem restriction_reindex_obj
    {J K : Type z} [SmallCategory J] [SmallCategory K]
    (D : J ⥤ Cat.{z, z}) (w : K ⥤ J) (c : Cocone D) (cK : Cocone (w ⋙ D))
    (q : cK.pt ⥤ c.pt)
    (hq : ∀ k, (cK.ι.app k).toFunctor ⋙ q = (c.ι.app (w.obj k)).toFunctor)
    {A : Type u} [Category.{v} A] (F : c.pt ⥤ A) :
    StrictDiagramPseudococone.restrictObj cK (q ⋙ F) =
      StrictDiagramPseudococone.reindexObj w (StrictDiagramPseudococone.restrictObj c F) := by
  apply pseudococone_hext
  · funext k
    exact congrArg (fun H ↦ H ⋙ F) (hq k)
  · intro j k a
    dsimp [StrictDiagramPseudococone.restrictObj, StrictDiagramPseudococone.reindexObj]
    rw [isoWhiskerRight_eqToIso, isoWhiskerRight_eqToIso]
    apply eqToIsoHEq
    · exact congrArg (fun H ↦ (D.map (w.map a)).toFunctor ⋙ H ⋙ F) (hq k)
    · exact congrArg (fun H ↦ H ⋙ F) (hq j)

/-- Final reindexing induces an equivalence, with strict structure-functor and restriction
compatibility. The leg equations determine the induced functor on all objects and arrows.

Source: Stacks Tags 04E7 and 04AX
(blueprint: lem-per-filtered-category-pseudococones).

Proof (node Steps 4--5): the opposites of the nonempty connected comma categories are the
comma categories for an initial opposite functor. Apply
lem-weil-pbc-initial-functor-limit to the opposite object- and arrow-set diagrams in Setsᵒᵖ
and dualize. The induced object and arrow maps are bijections. They respect source, target
and identities on representatives; a composable pair lifts to one stage, proving
compatibility with composition. Hence these maps form the canonical isomorphism of
categories, in particular an equivalence q. Its stage-leg equations hold on objects and
arrows. Restricting Fq to a stage is exactly restricting the pseudococone of F along w,
including comparison maps and transformations. This is the asserted equality of functors;
it is compatible with postcomposition by the preceding naturality statement. -/
theorem filteredColimit_final_reindexing
    {J K : Type z} [SmallCategory J] [SmallCategory K] [IsFiltered J] [IsFiltered K]
    (D : J ⥤ Cat.{z, z}) (w : K ⥤ J) [w.Final]
    (c : Cocone D) (hobjects : IsColimit (Cat.objects.mapCocone c))
    (harrows : IsColimit (Cat.arrows.mapCocone c))
    (cK : Cocone (w ⋙ D)) (hKobjects : IsColimit (Cat.objects.mapCocone cK))
    (hKarrows : IsColimit (Cat.arrows.mapCocone cK)) :
    ∃ q : cK.pt ⥤ c.pt, q.IsEquivalence ∧
      (∀ k : K, (cK.ι.app k).toFunctor ⋙ q = (c.ι.app (w.obj k)).toFunctor) ∧
      (∀ (A : Type u) [Category.{v} A],
        (whiskeringLeft cK.pt c.pt A).obj q ⋙
            StrictDiagramPseudococone.restriction cK A =
          StrictDiagramPseudococone.restriction c A ⋙
            StrictDiagramPseudococone.reindex w) := by
  let hc := setPresentedIsColimit D c hobjects harrows
  let hcK := setPresentedIsColimit (w ⋙ D) cK hKobjects hKarrows
  let hcW := (Functor.Final.isColimitWhiskerEquiv w c).symm hc
  let e := hcK.coconePointUniqueUpToIso hcW
  let q := (Cat.equivOfIso e).functor
  have hq (k : K) : (cK.ι.app k).toFunctor ⋙ q = (c.ι.app (w.obj k)).toFunctor :=
    congrArg Cat.Hom.toFunctor (hcK.comp_coconePointUniqueUpToIso_hom hcW k)
  refine ⟨q, inferInstance, hq, ?_⟩
  intro A instA
  apply Functor.hext
  · intro F
    exact restriction_reindex_obj D w c cK q hq F
  · intro F G t
    apply pseudococoneHom_hext
      (restriction_reindex_obj D w c cK q hq F)
      (restriction_reindex_obj D w c cK q hq G)
    intro k x
    change HEq (t.app (q.obj ((cK.ι.app k).toFunctor.obj x)))
      (t.app ((c.ι.app (w.obj k)).toFunctor.obj x))
    have hx := congrArg (fun H : D.obj (w.obj k) ⥤ c.pt ↦ H.obj x) (hq k)
    have ht (X Y : c.pt) (h : X = Y) : HEq (t.app X) (t.app Y) := by
      cases h
      rfl
    exact ht _ _ hx

/-- Coherent objectwise equivalences induce an equivalence on filtered category colimits.
The last equation is the compatibility of the stage isomorphisms with the supplied comparisons.

Source: finite-representative extension of Stacks Tag 04AX; Tag 004A is contextual
(blueprint: lem-per-filtered-category-pseudococones).

Proof (node Step 6): compose each objectwise equivalence e_j with its target colimit leg.
The inverses of the supplied comparisons, followed by the target cocone equalities, make
this a pseudococone. The restriction equivalence gives Q and coherent stage isomorphisms.
Every target object is represented at a stage and is isomorphic to e_j(x), so Q is
essentially surjective. To lift a morphism, move its endpoint representatives to a common
stage. Represent the conjugated target morphism at a later stage using the Hom-colimit
assertion of lem-weil-pbc-filtered-colimit-categories. Conjugate by the supplied comparisons
so its endpoints lie in the image of e_k; fullness of e_k lifts it. The coherent stage
isomorphisms identify the image of the lift with the required arrow. For faithfulness,
put two arrows at one stage. Equality of their images becomes equality at a later stage
by the same Hom equality criterion. Conjugate by the comparisons and use faithfulness
of e_k, giving equality of source representatives. Thus Q is fully faithful and essentially
surjective; apply lem-trf-fully-faithful-ess-surj-equivalence. Its stage isomorphisms obey
precisely the displayed coherence equation. -/
theorem filteredColimit_objectwise_equivalences
    {J : Type z} [SmallCategory J] [IsFiltered J] (D E : J ⥤ Cat.{z, z})
    (c : Cocone D) (hobjects : IsColimit (Cat.objects.mapCocone c))
    (harrows : IsColimit (Cat.arrows.mapCocone c))
    (cE : Cocone E) (hEobjects : IsColimit (Cat.objects.mapCocone cE))
    (hEarrows : IsColimit (Cat.arrows.mapCocone cE))
    (e : ∀ j : J, D.obj j ≌ E.obj j)
    (s : ∀ {j k : J} (a : j ⟶ k),
      (e j).functor ⋙ (E.map a).toFunctor ≅ (D.map a).toFunctor ⋙ (e k).functor)
    (hidentity : ∀ (j : J) (x : D.obj j), (s (𝟙 j)).hom.app x =
      eqToHom (congrArg (fun f ↦ f.toFunctor.obj ((e j).functor.obj x)) (E.map_id j)) ≫
        (e j).functor.map
          (eqToHom (congrArg (fun f ↦ f.toFunctor.obj x) (D.map_id j)).symm))
    (hcomposition : ∀ {j k l : J} (a : j ⟶ k) (b : k ⟶ l) (x : D.obj j),
      (s (a ≫ b)).hom.app x ≫ (e l).functor.map
          (eqToHom (congrArg (fun f ↦ f.toFunctor.obj x) (D.map_comp a b))) =
        eqToHom (congrArg (fun f ↦ f.toFunctor.obj ((e j).functor.obj x))
          (E.map_comp a b)) ≫
        (E.map b).toFunctor.map ((s a).hom.app x) ≫
        (s b).hom.app ((D.map a).toFunctor.obj x)) :
    ∃ (Q : c.pt ≌ cE.pt)
      (t : ∀ j : J, (c.ι.app j).toFunctor ⋙ Q.functor ≅
        (e j).functor ⋙ (cE.ι.app j).toFunctor),
      ∀ {j k : J} (a : j ⟶ k) (x : D.obj j),
        Q.functor.map (eqToHom (congrArg (fun F ↦ F.obj x)
          (congrArg Cat.Hom.toFunctor (c.w a)))) ≫ (t j).hom.app x =
        (t k).hom.app ((D.map a).toFunctor.obj x) ≫
          (cE.ι.app k).toFunctor.map ((s a).inv.app x) ≫
          eqToHom (congrArg (fun F ↦ F.obj ((e j).functor.obj x))
            (congrArg Cat.Hom.toFunctor (cE.w a))) := by
  sorry

end CategoryTheory
