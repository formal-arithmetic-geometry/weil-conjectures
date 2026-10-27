/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q76
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Sheaf.AlgebraicGeometry.OrdinaryEtaleIdentification
import Mathlib.CategoryTheory.Sites.SheafHom
import Mathlib.CategoryTheory.Sites.CoversTop.Basic
import Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests
import Sheaf.AlgebraicGeometry.OrdinaryAtlasTupleRealization
import Sheaf.AlgebraicGeometry.OrdinaryEtaleIdentificationLocalFrames

/-!
# Descent of invertible modules on an algebraic space

Source: Stacks Project, Spaces, Tags 04W8 and 060X; Descent, Tag 05VG;
Sites, Tags 04TR and 04TQ (blueprint: lem-trf-algebraic-space-invertible-descent).

Ordinary invertible modules are identified with restrictions of the descended module by
linear equivalences on every object of the localized étale site. The ordinary module's
value there is the global sections of its tensor pullback. This spells out the
Zariski/small-étale interpretation without choosing an inverse equivalence of categories.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.AlgebraicSpace

/-- The ordinary overlap isomorphisms, their identity along each diagonal, and their
cocycle after pullback to every test scheme of a triple overlap. The test-scheme
formulation is the Yoneda formulation of equality on the represented triple product;
it does not identify different iterated tensor pullbacks definitionally.
Source: Stacks, Spaces, Tag 04W8; Descent, descent data for quasi-coherent modules
(blueprint: lem-trf-algebraic-space-invertible-descent). -/
structure InvertibleAtlasDescentDatum {S : Scheme.{u}} {I : Type u}
    (V : I → Over S) (R : I → I → Over S)
    (p₁ : ∀ i j : I, R i j ⟶ V i) (p₂ : ∀ i j : I, R i j ⟶ V j)
    (M : ∀ i : I, (V i).left.Modules) where
  /-- The specified ordinary module isomorphisms on the represented double overlaps. -/
  transition : ∀ i j : I,
    (tensorPullback (p₂ i j).left).obj (M j) ≅ (tensorPullback (p₁ i j).left).obj (M i)
  /-- Identity only after restriction along the diagonal, including for self-overlaps. -/
  diagonal : ∀ (i : I) (d : V i ⟶ R i i)
    (h₁ : d ≫ p₁ i i = 𝟙 (V i)) (h₂ : d ≫ p₂ i i = 𝟙 (V i)),
    atlasTransitionOver (M i) (M i) (p₁ i i) (p₂ i i) (transition i i)
      d (𝟙 (V i)) (𝟙 (V i)) h₁ h₂ =
      Iso.refl ((tensorPullback (𝟙 (V i).left)).obj (M i))
  /-- The cocycle on all scheme tests of the triple fibre product. -/
  cocycle : ∀ (i j k : I) (T : Over S)
    (a : T ⟶ V i) (b : T ⟶ V j) (c : T ⟶ V k)
    (rᵢⱼ : T ⟶ R i j) (rⱼₖ : T ⟶ R j k) (rᵢₖ : T ⟶ R i k)
    (hᵢⱼ₁ : rᵢⱼ ≫ p₁ i j = a) (hᵢⱼ₂ : rᵢⱼ ≫ p₂ i j = b)
    (hⱼₖ₁ : rⱼₖ ≫ p₁ j k = b) (hⱼₖ₂ : rⱼₖ ≫ p₂ j k = c)
    (hᵢₖ₁ : rᵢₖ ≫ p₁ i k = a) (hᵢₖ₂ : rᵢₖ ≫ p₂ i k = c),
    atlasTransitionOver (M i) (M k) (p₁ i k) (p₂ i k) (transition i k)
      rᵢₖ a c hᵢₖ₁ hᵢₖ₂ =
    atlasTransitionOver (M j) (M k) (p₁ j k) (p₂ j k) (transition j k)
      rⱼₖ b c hⱼₖ₁ hⱼₖ₂ ≪≫
    atlasTransitionOver (M i) (M j) (p₁ i j) (p₂ i j) (transition i j)
      rᵢⱼ a b hᵢⱼ₁ hᵢⱼ₂

private theorem atlas_coversTop
    {S : Scheme.{u}} (F : AlgebraicSpace S) {I : Type u} (V : I → F.EtaleSite)
    (hjoint : ∀ (T : Over S) (a : yoneda.obj T ⟶ F.obj.obj) (x : T.left),
      ∃ (i : I) (U : Over S) (p : U ⟶ T)
        (r : yoneda.obj U ⟶ yoneda.obj (V i).obj.left),
        IsPullback r (yoneda.map p) (V i).obj.hom a ∧
          ∃ y : U.left, p.left.base y = x) : F.etaleTopology.CoversTop V := by
  have tests := representable_etale_scheme_tests (S := S)
  have comparison := tests.2.2.2.2.2.2.2.2.2
  have baseChange : ∀ {A B C D : (Over S)ᵒᵖ ⥤ Type u}
      {q : D ⟶ A} {p : D ⟶ B} {f : A ⟶ C} {g : B ⟶ C},
      IsPullback q p f g → IsEtale f → IsEtale p := by
    intro A B C D q p f g sq hf T a
    obtain ⟨U, r, b, hb, hr⟩ := hf T (a ≫ g)
    let l := sq.lift b (yoneda.map r ≫ a) (by simpa only [Category.assoc] using hb.w)
    refine ⟨U, r, l, ?_, hr⟩
    apply IsPullback.of_right (h₁₂ := q) (h₂₂ := g) _ (sq.lift_snd _ _ _) sq
    simpa only [l, IsPullback.lift_fst] using hb
  intro T
  rw [← Sieve.generate_sieve (Sieve.ofObjects V T)]
  apply Precoverage.generate_mem_toGrothendieck
  constructor
  · intro U f _
    exact comparison F U.obj.left T.obj.left U.obj.hom T.obj.hom f.hom.left
      U.property T.property (CostructuredArrow.w f.hom)
  · intro x
    obtain ⟨i, U, p, r, sq, y, hy⟩ := hjoint T.obj.left T.obj.hom x
    have hp : IsEtale (yoneda.map p) := baseChange sq (V i).property
    let W : F.EtaleSite := ⟨CostructuredArrow.mk (yoneda.map p ≫ T.obj.hom),
      isEtale_comp _ _ hp T.property⟩
    let f : W ⟶ T := ObjectProperty.homMk (CostructuredArrow.homMk p (by rfl))
    let a : W ⟶ V i := ObjectProperty.homMk
      (CostructuredArrow.homMk (yoneda.preimage r) (by
        change yoneda.map (yoneda.preimage r) ≫ (V i).obj.hom = yoneda.map p ≫ T.obj.hom
        rw [yoneda.map_preimage]
        exact sq.w))
    exact ⟨W, f, ⟨i, ⟨a⟩⟩, y, hy⟩

private theorem atlas_hom_descent
    {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) {I : Type u} (V : I → C)
    (hcover : J.CoversTop V) (P Q : SheafOfModules.{u} R)
    (g : ∀ i : I, (SheafOfModules.overFunctor R (V i)).obj P ⟶
      (SheafOfModules.overFunctor R (V i)).obj Q)
    (hg : ∀ (i j : I) (T : C) (a : T ⟶ V i) (b : T ⟶ V j),
      (g i).val.app (op (Over.mk a)) = (g j).val.app (op (Over.mk b))) :
    ∃! f : P ⟶ Q, ∀ i : I, (SheafOfModules.overFunctor R (V i)).map f = g i := by
  classical
  let A := P.val.presheaf
  let B := Q.val.presheaf
  let x : Presheaf.FamilyOfElementsOnObjects (presheafHom A B) V :=
    fun i ↦ (PresheafOfModules.toPresheaf _).map (g i).val
  have hx : x.IsCompatible := by
    intro T i j a b
    change Functor.whiskerLeft (Over.map a).op (x i) =
      Functor.whiskerLeft (Over.map b).op (x j)
    ext ⟨W : Over T⟩ z
    exact congrArg (fun f ↦ f z) (hg i j W.left (W.hom ≫ a) (W.hom ≫ b))
  obtain ⟨s, hs, _⟩ := hx.existsUnique_section hcover (Q.isSheaf.hom A)
  let f₀ : A ⟶ B := presheafHomSectionsEquiv A B s
  have local_eq (i : I) (T : C) (a : T ⟶ V i) :
      f₀.app (op T) =
        ((PresheafOfModules.toPresheaf _).map (g i).val).app (op (Over.mk a)) := by
    change (s.val (op T)).app (op (Over.mk (𝟙 T))) = _
    rw [← s.property a.op, hs i]
    exact presheafHom_map_app_op_mk_id a (x i)
  have hQ : Presheaf.IsSheaf J (B ⋙ forget AddCommGrpCat) :=
    GrothendieckTopology.HasSheafCompose.isSheaf B Q.isSheaf
  have natural (T U : C) (a : U ⟶ T) (z : P.val.obj (op T)) :
      f₀.app (op U) (P.val.map a.op z) = Q.val.map a.op (f₀.app (op T) z) :=
    ConcreteCategory.congr_hom (f₀.naturality a.op) z
  have linear (T : C) (r : R.obj.obj (op T))
      (z : P.val.obj (op T)) : f₀.app (op T) (r • z) = r • f₀.app (op T) z := by
    apply ((isSheaf_iff_isSheaf_of_type _ _).mp hQ).isSeparated
      _ (hcover T) |>.ext
    rintro W a ⟨i, ⟨b⟩⟩
    change Q.val.map a.op (f₀.app (op T) (r • z)) =
      Q.val.map a.op (r • f₀.app (op T) z)
    rw [← natural T W a (r • z)]
    change f₀.app (op W) (P.val.map a.op (r • z)) = _
    rw [P.val.map_smul, Q.val.map_smul, local_eq i W b]
    change (g i).val.app (op (Over.mk b))
        (R.obj.map a.op r • P.val.map a.op z) = _
    refine (((g i).val.app (op (Over.mk b))).hom.map_smul
      (R.obj.map a.op r) (P.val.map a.op z)).trans ?_
    congr 1
    change (((PresheafOfModules.toPresheaf _).map (g i).val).app
      (op (Over.mk b))) (P.val.map a.op z) = Q.val.map a.op (f₀.app (op T) z)
    rw [← local_eq i W b]
    exact natural T W a z
  let f : P ⟶ Q := ⟨{
    app := fun T ↦ ModuleCat.ofHom {
      toFun := f₀.app T
      map_add' := map_add (f₀.app T).hom
      map_smul' := linear T.unop }
    naturality := by
      intro T U a
      ext z
      change f₀.app U (P.val.map a z) = Q.val.map a (f₀.app T z)
      exact ConcreteCategory.congr_hom (f₀.naturality a) z }⟩
  have hf (i : I) : (SheafOfModules.overFunctor R (V i)).map f = g i := by
    ext ⟨T : Over (V i)⟩ z
    exact ConcreteCategory.congr_hom (local_eq i T.left T.hom) z
  refine ⟨f, hf, ?_⟩
  intro k hk
  ext ⟨T⟩ z
  apply ((isSheaf_iff_isSheaf_of_type _ _).mp hQ).isSeparated
    _ (hcover T) |>.ext
  rintro W a ⟨i, ⟨b⟩⟩
  change Q.val.map a.op (k.val.app (op T) z) = Q.val.map a.op (f.val.app (op T) z)
  rw [← PresheafOfModules.naturality_apply k.val,
    ← PresheafOfModules.naturality_apply f.val]
  have hi := congrArg (fun l ↦ l.val.app (op (Over.mk b))) ((hk i).trans (hf i).symm)
  exact congrArg (fun l ↦ l (P.val.map a.op z)) hi

/-- Invertible modules and their morphisms descend along any jointly surjective family
of étale scheme maps to an algebraic space. The ordinary invertible modules `M i`
and the specified overlap isomorphisms are retained; the conclusion gives a line
module with natural linear identifications inducing exactly those isomorphisms.
The second conjunct is the bijection on morphisms, expressed as existence and
uniqueness of a global map with each prescribed local restriction.
Source: Stacks, Spaces, Tags 04W8 and 060X; Descent, Tag 05VG; Sites, Tags 04TR and 04TQ
(blueprint: lem-trf-algebraic-space-invertible-descent).

Proof:
1. Interpret each ordinary invertible module on the localized small étale site by
   its tensor-pullback sections, using lem-trf-scheme-etale-invertible-comparison.
   The unit-normalized composition comparisons transport the transitions and cocycle.
2. For every test scheme W over F, form W_i and W_ij by the representable diagonal.
   Sending W to the sections of the local module on W_i, or on W_ij, gives sheaves:
   their covering equalizers are those on the corresponding base-changed scheme.
3. Take the equalizer of the two maps from the product of the first family to the
   product of the second. By lem-weil-pbc-site-sheaf-sets-limits-sectionwise its values
   are exactly the tuples s_i with s_i restricted equal to α_ij(s_j restricted).
4. Define addition and scalar multiplication coordinatewise. Linearity of α_ij
   preserves the equations, and semilinearity of restriction gives a module sheaf.
5. Over V_a, evaluation of the a-coordinate along the graph defines the local
   identification; its inverse sends y to the tuple α_ia(y restricted). The cocycle
   makes this a compatible tuple and proves that these formulas are natural.
6. The diagonal identity and tuple compatibility prove that these maps are inverse.
   Pulling the tuple equation back along the two graphs proves that the resulting
   identifications induce precisely the specified transitions, also on self-overlaps.
7. Pull back Zariski trivializing covers of the M_i to the W_i. Covering composition
   then trivializes the descended module on every W, so it is a line module.
8. For any two line modules, apply compatible local maps to the local restrictions
   of a section. The sheaf axiom glues the results uniquely. Uniqueness proves
   naturality, additivity, scalar linearity and agreement with the local maps, and
   proves uniqueness of the resulting global map. -/
theorem exists_lineModule_of_etale_descent
    {S : Scheme.{u}} (F : AlgebraicSpace S) {I : Type u} (V : I → F.EtaleSite)
    (hjoint : ∀ (T : Over S) (a : yoneda.obj T ⟶ F.obj.obj) (x : T.left),
      ∃ (i : I) (U : Over S) (p : U ⟶ T)
        (r : yoneda.obj U ⟶ yoneda.obj (V i).obj.left),
        IsPullback r (yoneda.map p) (V i).obj.hom a ∧
          ∃ y : U.left, p.left.base y = x)
    (R : I → I → Over S)
    (p₁ : ∀ i j : I, R i j ⟶ (V i).obj.left)
    (p₂ : ∀ i j : I, R i j ⟶ (V j).obj.left)
    (hR : ∀ i j : I, IsPullback (yoneda.map (p₁ i j)) (yoneda.map (p₂ i j))
      (V i).obj.hom (V j).obj.hom)
    (M : ∀ i : I, (F.etaleForget.obj (V i)).Modules)
    (hM : ∀ i : I, Scheme.Modules.IsInvertible (M i))
    (D : InvertibleAtlasDescentDatum (fun i ↦ (V i).obj.left) R p₁ p₂ M) :
    (∃ (N : F.Modules), F.IsLineModule N ∧
      ∃ (e : ∀ i : I, OrdinaryEtaleIdentification F (V i) N (M i)),
        ∀ (i j : I) (T : F.EtaleSite) (a : T ⟶ V i) (b : T ⟶ V j)
          (r : T.obj.left ⟶ R i j)
          (h₁ : r ≫ p₁ i j = a.hom.left) (h₂ : r ≫ p₂ i j = b.hom.left)
          (s : ((tensorPullback (F.etaleForget.map b)).obj (M j)).val.obj (op ⊤)),
          (e i).app T a
            (((atlasTransitionOver (M i) (M j) (p₁ i j) (p₂ i j) (D.transition i j)
              r a.hom.left b.hom.left h₁ h₂).hom.app ⊤) s) = (e j).app T b s) ∧
    (∀ (P Q : F.Modules), F.IsLineModule P → F.IsLineModule Q →
      ∀ (g : ∀ i : I, (F.etalePullback (V i)).obj P ⟶ (F.etalePullback (V i)).obj Q),
        (∀ (i j : I) (T : F.EtaleSite) (a : T ⟶ V i) (b : T ⟶ V j),
          (g i).val.app (op (Over.mk a)) = (g j).val.app (op (Over.mk b))) →
        ∃! f : P ⟶ Q, ∀ i : I, (F.etalePullback (V i)).map f = g i) := by
  classical
  have hcover := atlas_coversTop F V hjoint
  constructor
  · obtain ⟨N, e, he⟩ := exists_ordinary_atlas_tuple_realization F V R p₁ p₂ hR M hM
      D.transition D.diagonal D.cocycle
    refine ⟨N, ?_, e, he⟩
    intro T
    have local_frames (U : F.EtaleSite) (f : U ⟶ T) (hf : Sieve.ofObjects V T f) :
        ∃ R : Sieve U, R ∈ F.etaleTopology U ∧
          ∀ (W : F.EtaleSite) (g : W ⟶ U), R g →
            Nonempty ((F.etalePullback W).obj N ≅
              SheafOfModules.unit (F.structureSheaf.over W)) := by
      obtain ⟨i, ⟨a⟩⟩ := hf
      exact ordinary_etale_identification_local_frames F (V i) N (M i) (hM i) (e i) U a
    choose C hC htriv using local_frames
    refine ⟨Sieve.bind (Sieve.ofObjects V T).arrows (fun {U} {f} hf ↦ C U f hf),
      F.etaleTopology.bind_covering (hcover T) (fun {_} {_} hf ↦ hC _ _ hf), ?_⟩
    rintro U f ⟨W, a, b, hb, ha, _⟩
    exact htriv W b hb U a ha
  · intro P Q _ _ g hg
    exact atlas_hom_descent F.structureSheaf V hcover P Q g hg

end AlgebraicGeometry.AlgebraicSpace
