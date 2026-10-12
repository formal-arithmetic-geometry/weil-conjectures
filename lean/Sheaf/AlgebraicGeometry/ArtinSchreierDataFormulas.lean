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
The canonical ring homomorphism ZMod p → Gamma(U, O_U) is c ↦ (c.val : Gamma(U, O_U)).
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
  sorry

end AlgebraicGeometry
