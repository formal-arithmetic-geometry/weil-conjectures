module

public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.AlgebraicGeometry.Curve

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
namespace AlgebraicGeometry
set_option autoImplicit false

/-- Artin--Schreier maps exist for any sheaf naturally identified with regular functions.
Source: blueprint `lem-sc-as-sequence`, proof, the maps paragraph; Stacks, Tag 0A3J.
(blueprint: lem-sc-as-sequence-formulas-helper)

Proof: Since k is a field of positive characteristic p, p is prime. Each étale U
is a k-scheme through U → C → Spec k. Pullback of functions therefore sends p to
zero in Gamma(U, O_U), including when U is empty. The binomial theorem makes
x ↦ x^p - x an additive homomorphism on every such ring. Conjugate it by a U to
obtain wp_U. The restriction identity for a and preservation of powers and
subtraction by g-sharp prove naturality, giving a sheaf map wp.
The composite ZMod p → k → Gamma(U, O_U) sends c to (c.val : Gamma(U, O_U)),
including when the section ring is trivial.
Compose its additive homomorphism with ULift.down and (a U).symm. Naturality of a
and of integer casts gives a map from the constant presheaf into G. The universal
property of sheafification extends it uniquely to iota : C.constantZMod p → G.
The equation on the sheafification unit gives the displayed constant formula;
conjugation gives the displayed formula for wp. Fermat's identity c^p = c in
ZMod p makes the composite zero on the constant presheaf. Uniqueness in the
sheafification universal property then gives iota ≫ wp = 0. No compatibility
is claimed for arbitrary maps: the maps are constructed from the natural a. -/
theorem artinSchreier_formulas
    {k : Type u} [Field k] [IsAlgClosed k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve f]
    (p : ℕ) [CharP k p] (hp : 0 < p)
    (G : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1})
    (a : ∀ U : C.Etaleᵒᵖ, G.obj.obj U ≃+ Γ(U.unop.left, ⊤))
    (hrestr : ∀ (U V : C.Etaleᵒᵖ) (g : U ⟶ V) (x : G.obj.obj U),
      a V (G.obj.map g x) = g.unop.left.appTop (a U x)) :
    ∃ (wp : G ⟶ G) (iota : C.constantZMod p ⟶ G) (_hzero : iota ≫ wp = 0),
      (∀ (U : C.Etaleᵒᵖ) (x : G.obj.obj U),
        a U (wp.hom.app U x) = (a U x) ^ p - a U x) ∧
      (∀ (U : C.Etaleᵒᵖ) (c : ZMod p),
        a U (iota.hom.app U
          ((toSheafify C.smallEtaleTopology
            ((Functor.const C.Etaleᵒᵖ).obj
              (AddCommGrpCat.of (ULift.{u + 1} (ZMod p))))).app U (ULift.up c))) =
          (c.val : Γ(U.unop.left, ⊤))) := by
  classical
  have hprime : p.Prime := (CharP.char_is_prime_or_zero k p).resolve_right hp.ne'
  let : Fact p.Prime := ⟨hprime⟩
  let : NeZero p := ⟨hp.ne'⟩
  let ρ (U : C.Etaleᵒᵖ) : k →+* Γ(U.unop.left, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ U.unop.hom.appTop).hom
  have hpU (U : C.Etaleᵒᵖ) : (p : Γ(U.unop.left, ⊤)) = 0 := by
    rw [← map_natCast (ρ U), CharP.cast_eq_zero k p, map_zero]
  have hadd (U : C.Etaleᵒᵖ) (x y : Γ(U.unop.left, ⊤)) :
      (x + y) ^ p = x ^ p + y ^ p := by
    by_cases h : Subsingleton Γ(U.unop.left, ⊤)
    · exact @Subsingleton.elim _ h _ _
    have : Nontrivial Γ(U.unop.left, ⊤) := not_subsingleton_iff_nontrivial.mp h
    have : CharP Γ(U.unop.left, ⊤) p :=
      (CharP.charP_iff_prime_eq_zero hprime).mpr (hpU U)
    exact add_pow_char x y p
  let w (U : C.Etaleᵒᵖ) : G.obj.obj U →+ G.obj.obj U :=
    { toFun := fun x ↦ (a U).symm ((a U x) ^ p - a U x)
      map_zero' := by simp [hp.ne']
      map_add' := by
        intro x y
        apply (a U).injective
        simp only [map_add, AddEquiv.apply_symm_apply]
        rw [hadd]
        abel }
  let wp : G ⟶ G := ⟨{
    app := fun U ↦ AddCommGrpCat.ofHom (w U)
    naturality := by
      intro U V g
      ext x
      apply (a V).injective
      simp only [AddCommGrpCat.comp_apply]
      change a V (w V (G.obj.map g x)) = a V (G.obj.map g (w U x))
      simp only [w, hrestr, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
        AddEquiv.apply_symm_apply, map_sub, map_pow] }⟩
  have hwp (U : C.Etaleᵒᵖ) (x : G.obj.obj U) :
      a U (wp.hom.app U x) = (a U x) ^ p - a U x := by
    exact (a U).apply_symm_apply _
  let z (U : C.Etaleᵒᵖ) : ZMod p →+* Γ(U.unop.left, ⊤) :=
    (ρ U).comp (ZMod.castHom (dvd_refl p) k)
  have hz (U : C.Etaleᵒᵖ) (c : ZMod p) : z U c = (c.val : Γ(U.unop.left, ⊤)) := by
    change ρ U (ZMod.cast c) = _
    rw [ZMod.cast_eq_val, map_natCast]
  let t : (Functor.const C.Etaleᵒᵖ).obj
      (AddCommGrpCat.of (ULift.{u + 1} (ZMod p))) ⟶ G.obj := {
    app := fun U ↦ AddCommGrpCat.ofHom
      ((a U).symm.toAddMonoidHom.comp
        ((z U).toAddMonoidHom.comp AddEquiv.ulift.toAddMonoidHom))
    naturality := by
      intro U V g
      ext x
      apply (a V).injective
      change a V ((a V).symm (z V x.down)) =
        a V (G.obj.map g ((a U).symm (z U x.down)))
      simp only [hrestr, AddEquiv.apply_symm_apply, hz, map_natCast] }
  let iota : C.constantZMod p ⟶ G :=
    ⟨sheafifyLift C.smallEtaleTopology t G.property⟩
  have ht : toSheafify C.smallEtaleTopology _ ≫ iota.hom = t :=
    toSheafify_sheafifyLift _ _ _
  have hiota (U : C.Etaleᵒᵖ) (c : ZMod p) :
      a U (iota.hom.app U ((toSheafify C.smallEtaleTopology
        ((Functor.const C.Etaleᵒᵖ).obj
          (AddCommGrpCat.of (ULift.{u + 1} (ZMod p))))).app U (ULift.up c))) =
        (c.val : Γ(U.unop.left, ⊤)) := by
    have he := congrArg (fun q ↦ q.app U (ULift.up c)) ht
    change iota.hom.app U ((toSheafify C.smallEtaleTopology
        ((Functor.const C.Etaleᵒᵖ).obj
          (AddCommGrpCat.of (ULift.{u + 1} (ZMod p))))).app U (ULift.up c)) =
      (a U).symm (z U c) at he
    rw [he, AddEquiv.apply_symm_apply, hz]
  refine ⟨wp, iota, ?_, hwp, hiota⟩
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ G.property
  rw [InducedCategory.comp_hom, ← Category.assoc, ht]
  ext U c
  change wp.hom.app U (t.app U c) = 0
  apply (a U).injective
  rw [hwp, map_zero]
  change (a U ((a U).symm (z U c.down))) ^ p -
    a U ((a U).symm (z U c.down)) = 0
  rw [AddEquiv.apply_symm_apply, ← map_pow, ZMod.pow_card, sub_self]

end AlgebraicGeometry
