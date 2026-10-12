module

public import Sheaf.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import Sheaf.AlgebraicGeometry.ArtinSchreierDataConstruction

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

set_option autoImplicit false

private theorem transport_section_identifications (X : Scheme.{u})
    (G H : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (e : G ≅ H)
    (b : ∀ U : X.Etaleᵒᵖ, G.obj.obj U ≃+ Γ(U.unop.left, ⊤))
    (hb : ∀ (U V : X.Etaleᵒᵖ) (g : U ⟶ V) (x : G.obj.obj U),
      b V (G.obj.map g x) = g.unop.left.appTop (b U x)) :
    ∃ (a : ∀ U : X.Etaleᵒᵖ, H.obj.obj U ≃+ Γ(U.unop.left, ⊤)),
      ∀ (U V : X.Etaleᵒᵖ) (g : U ⟶ V) (x : H.obj.obj U),
        a V (H.obj.map g x) = g.unop.left.appTop (a U x) := by
  let d (U : X.Etaleᵒᵖ) : H.obj.obj U ≃+ G.obj.obj U :=
    AddMonoidHom.toAddEquiv (e.inv.hom.app U).hom (e.hom.hom.app U).hom
      (by
        ext x
        exact ConcreteCategory.congr_hom
          (congrArg (fun f ↦ f.hom.app U) e.inv_hom_id) x)
      (by
        ext x
        exact ConcreteCategory.congr_hom
          (congrArg (fun f ↦ f.hom.app U) e.hom_inv_id) x)
  refine ⟨fun U ↦ (d U).trans (b U), ?_⟩
  intro U V g x
  change b V (e.inv.hom.app V (H.obj.map g x)) =
    g.unop.left.appTop (b U (e.inv.hom.app U x))
  rw [← hb U V g (e.inv.hom.app U x)]
  exact congrArg (b V) (ConcreteCategory.congr_hom (e.inv.hom.naturality g) x)

private theorem construct_section_maps (X : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hp : (p : Γ(X, ⊤)) = 0)
    (H : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (a : ∀ U : X.Etaleᵒᵖ, H.obj.obj U ≃+ Γ(U.unop.left, ⊤))
    (hrestr : ∀ (U V : X.Etaleᵒᵖ) (g : U ⟶ V) (x : H.obj.obj U),
      a V (H.obj.map g x) = g.unop.left.appTop (a U x)) :
    ∃ (wp : H ⟶ H) (iota : X.constantZMod p ⟶ H) (_hzero : iota ≫ wp = 0),
      (∀ (U : X.Etaleᵒᵖ) (x : H.obj.obj U),
        a U (wp.hom.app U x) = (a U x) ^ p - a U x) ∧
      (∀ (U : X.Etaleᵒᵖ) (c : ZMod p),
        a U (iota.hom.app U
          ((toSheafify X.smallEtaleTopology
            ((Functor.const X.Etaleᵒᵖ).obj
              (AddCommGrpCat.of (ULift.{u + 1} (ZMod p))))).app U (ULift.up c))) =
          (c.val : Γ(U.unop.left, ⊤))) := by
  classical
  let : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hpU (U : X.Etaleᵒᵖ) : (p : Γ(U.unop.left, ⊤)) = 0 := by
    simpa only [map_natCast, map_zero] using congrArg U.unop.hom.appTop hp
  have hadd (U : X.Etaleᵒᵖ) (x y : Γ(U.unop.left, ⊤)) :
      (x + y) ^ p = x ^ p + y ^ p := by
    by_cases h : Subsingleton Γ(U.unop.left, ⊤)
    · exact @Subsingleton.elim _ h _ _
    have : Nontrivial Γ(U.unop.left, ⊤) := not_subsingleton_iff_nontrivial.mp h
    have : CharP Γ(U.unop.left, ⊤) p :=
      (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr (hpU U)
    exact add_pow_char x y p
  let w (U : X.Etaleᵒᵖ) : H.obj.obj U →+ H.obj.obj U :=
    { toFun := fun x ↦ (a U).symm ((a U x) ^ p - a U x)
      map_zero' := by simp [(Fact.out : p.Prime).ne_zero]
      map_add' := by
        intro x y
        apply (a U).injective
        simp only [map_add, AddEquiv.apply_symm_apply]
        rw [hadd]
        abel }
  let wp : H ⟶ H := ⟨{
    app := fun U ↦ AddCommGrpCat.ofHom (w U)
    naturality := by
      intro U V g
      ext x
      apply (a V).injective
      simp only [AddCommGrpCat.comp_apply]
      change a V (w V (H.obj.map g x)) = a V (H.obj.map g (w U x))
      simp only [w, hrestr, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
        AddEquiv.apply_symm_apply, map_sub, map_pow] }⟩
  have hwp (U : X.Etaleᵒᵖ) (x : H.obj.obj U) :
      a U (wp.hom.app U x) = (a U x) ^ p - a U x := by
    exact (a U).apply_symm_apply _
  let z (U : X.Etaleᵒᵖ) : ZMod p →+* Γ(U.unop.left, ⊤) :=
    ZMod.castHom ((CharP.cast_eq_zero_iff Γ(U.unop.left, ⊤)
      (ringChar Γ(U.unop.left, ⊤)) p).mp (hpU U)) _
  have hz (U : X.Etaleᵒᵖ) (c : ZMod p) : z U c = (c.val : Γ(U.unop.left, ⊤)) := by
    exact ZMod.cast_eq_val c
  let t : (Functor.const X.Etaleᵒᵖ).obj
      (AddCommGrpCat.of (ULift.{u + 1} (ZMod p))) ⟶ H.obj := {
    app := fun U ↦ AddCommGrpCat.ofHom
      ((a U).symm.toAddMonoidHom.comp
        ((z U).toAddMonoidHom.comp AddEquiv.ulift.toAddMonoidHom))
    naturality := by
      intro U V g
      ext x
      apply (a V).injective
      change a V ((a V).symm (z V x.down)) =
        a V (H.obj.map g ((a U).symm (z U x.down)))
      simp only [hrestr, AddEquiv.apply_symm_apply, hz, map_natCast] }
  let iota : X.constantZMod p ⟶ H :=
    ⟨sheafifyLift X.smallEtaleTopology t H.property⟩
  have ht : toSheafify X.smallEtaleTopology _ ≫ iota.hom = t :=
    toSheafify_sheafifyLift _ _ _
  have hiota (U : X.Etaleᵒᵖ) (c : ZMod p) :
      a U (iota.hom.app U ((toSheafify X.smallEtaleTopology
        ((Functor.const X.Etaleᵒᵖ).obj
          (AddCommGrpCat.of (ULift.{u + 1} (ZMod p))))).app U (ULift.up c))) =
        (c.val : Γ(U.unop.left, ⊤)) := by
    have he := congrArg (fun q ↦ q.app U (ULift.up c)) ht
    change iota.hom.app U ((toSheafify X.smallEtaleTopology
        ((Functor.const X.Etaleᵒᵖ).obj
          (AddCommGrpCat.of (ULift.{u + 1} (ZMod p))))).app U (ULift.up c)) =
      (a U).symm (z U c) at he
    rw [he, AddEquiv.apply_symm_apply, hz]
  refine ⟨wp, iota, ?_, hwp, hiota⟩
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ H.property
  rw [InducedCategory.comp_hom, ← Category.assoc, ht]
  ext U c
  change wp.hom.app U (t.app U c) = 0
  apply (a U).injective
  rw [hwp, map_zero]
  change (a U ((a U).symm (z U c.down))) ^ p -
    a U ((a U).symm (z U c.down)) = 0
  rw [AddEquiv.apply_symm_apply, ← map_pow, ZMod.pow_card, sub_self]

set_option linter.unusedVariables false in
/-- Construction and section formulas for the Artin--Schreier maps, without exactness.
Source: Stacks Project, Tag 0A3J, opening sequence.
(blueprint: lem-sc-artin-schreier-scheme-section-data).

Proof: The pullback of the structure module along each étale U → X is canonically
its structure module. The tensor-pullback units and composition isomorphisms identify
restrictions with pullback of functions. Taking global sections and removing ULift
therefore gives natural additive equivalences a. The image of hp under U → X makes
p vanish in each section ring. The characteristic-p binomial identity makes
x ↦ x^p - x additive, and ring maps commute with it. Conjugating by a defines a
natural presheaf endomorphism, hence a sheaf morphism wp. The maps c ↦ c.val • 1
from ZMod p are additive (p = 0), commute with restrictions, and extend uniquely
from the constant presheaf through sheafification to iota. Their values satisfy
c^p = c, so the composite is zero on the sheafification unit. The universal
property of sheafification implies iota ≫ wp = 0. These constructions give all
three displayed formulas. No assertion about kernels or local preimages is used.
-/
theorem exists_artinSchreier_section_data (X : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hp : (p : Γ(X, ⊤)) = 0) :
    let G := (sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
      (Modules.etaleTensorSectionsSheaf (Modules.unit X))
    ∃ (a : ∀ U : X.Etaleᵒᵖ, G.obj.obj U ≃+ Γ(U.unop.left, ⊤))
      (wp : G ⟶ G) (iota : X.constantZMod p ⟶ G) (hzero : iota ≫ wp = 0),
      (∀ (U V : X.Etaleᵒᵖ) (g : U ⟶ V) (x : G.obj.obj U),
        a V (G.obj.map g x) = g.unop.left.appTop (a U x)) ∧
      (∀ (U : X.Etaleᵒᵖ) (x : G.obj.obj U),
        a U (wp.hom.app U x) = (a U x) ^ p - a U x) ∧
      (∀ (U : X.Etaleᵒᵖ) (c : ZMod p),
        a U (iota.hom.app U
          ((toSheafify X.smallEtaleTopology
            ((Functor.const X.Etaleᵒᵖ).obj
              (AddCommGrpCat.of (ULift.{u + 1} (ZMod p))))).app U (ULift.up c))) =
          (c.val : Γ(U.unop.left, ⊤))) := by
  dsimp
  classical
  obtain ⟨G, e, b, hb⟩ := AlgebraicGeometry.artinSchreier_construction X
  let H := (sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
    (Modules.etaleTensorSectionsSheaf (Modules.unit X))
  obtain ⟨a, hrestr⟩ := transport_section_identifications X G H e b hb
  obtain ⟨wp, iota, hzero, hwp, hiota⟩ := construct_section_maps X p hp H a hrestr
  exact ⟨a, wp, iota, hzero, hrestr, hwp, hiota⟩



end AlgebraicGeometry.Scheme
