module

public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Data.PNat.Basic

/-! # Exchange followed by point transport

Source: blueprint sec-trace-formula/sk-d-weil,
lem-trf-frobenius-operator-compact-description.proof.md, final naturality calculation
and change of compact-support representative
(blueprint: lem-trf-exchange-transport-composition-conjugation).

The positive index type excludes degree zero, for which no data are supplied.
Functor composition `P m ⋙ P 1` means the paper's rightmost-first `P₁ Pₘ`.
-/

@[expose] public section

set_option autoImplicit false

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
  {B : Type u₂} [Category.{v₂} B] {D : Type u₃} [Category.{v₃} D]

/-- Point transport followed by exchange, as a natural transformation.
Source: blueprint sec-trace-formula/sk-d-weil,
lem-trf-frobenius-operator-compact-description.proof.md, final naturality calculation
(blueprint: lem-trf-exchange-transport-composition-conjugation). -/
def exchangePointTransport (F : C ⥤ B) (V : B ⥤ D)
    {P : C ⥤ C} {Q : B ⥤ B} (ι : V ⟶ Q ⋙ V) (e : F ⋙ Q ⟶ P ⋙ F) :
    F ⋙ V ⟶ P ⋙ F ⋙ V :=
  Functor.whiskerLeft F ι ≫ Functor.whiskerRight e V

/-- Exchange on the specified representative, using its comparison with the original functor.
Source: blueprint sec-trace-formula/sk-d-weil,
lem-trf-frobenius-operator-compact-description.proof.md, change of representative
(blueprint: lem-trf-exchange-transport-composition-conjugation). -/
def conjugatedExchange {F Fd : C ⥤ B} (a : Fd ≅ F)
    {P : C ⥤ C} {Q : B ⥤ B} (e : F ⋙ Q ⟶ P ⋙ F) : Fd ⋙ Q ⟶ P ⋙ Fd :=
  Functor.whiskerRight a.hom Q ≫ e ≫ Functor.whiskerLeft P a.inv

/-- Exchange and point coherence imply transport coherence and representative conjugacy.
Source: blueprint sec-trace-formula/sk-d-weil,
lem-trf-frobenius-operator-compact-description.proof.md, final naturality calculation
and change of representative
(blueprint: lem-trf-exchange-transport-composition-conjugation).

Proof: Naturality follows by composing the naturality squares of exchange at a
morphism and of point transport at its image under F. For the first recurrence,
substitute the point law and combine the adjacent V-images; substitute the exchange
law and use naturality of ι 1 at e m evaluated at M. Reassociate to obtain the two
transport factors and the image of c m. For conjugacy, expand conjugatedExchange,
distribute V over composition, and use naturality of ι r at a.hom.app M. For the
last recurrence, substitute this conjugacy twice, cancel a.hom followed by a.inv
at P m evaluated at M, and use naturality of a at (c m).hom.app M. The first
recurrence now gives the desired identity. Associativity and identities are those
of def-nagata-category. Only components of a are cancelled; neither exchange nor
point transport is assumed invertible.
-/
theorem exchange_transport_composition_conjugation
    (F : C ⥤ B) (V : B ⥤ D) (P : ℕ+ → C ⥤ C) (Q : ℕ+ → B ⥤ B)
    (c : ∀ m : ℕ+, P m ⋙ P 1 ≅ P (m + 1))
    (t : ∀ m : ℕ+, Q m ⋙ Q 1 ≅ Q (m + 1))
    (ι : ∀ r : ℕ+, V ⟶ Q r ⋙ V)
    (e : ∀ r : ℕ+, F ⋙ Q r ⟶ P r ⋙ F)
    (hι : ∀ (m : ℕ+) (N : B),
      (ι (m + 1)).app N =
        (ι m).app N ≫ (ι 1).app ((Q m).obj N) ≫ V.map ((t m).hom.app N))
    (he : ∀ (m : ℕ+) (M : C),
      (t m).hom.app (F.obj M) ≫ (e (m + 1)).app M =
        (Q 1).map ((e m).app M) ≫ (e 1).app ((P m).obj M) ≫
          F.map ((c m).hom.app M)) :
    (∀ (m : ℕ+) (M : C),
      (exchangePointTransport F V (ι (m + 1)) (e (m + 1))).app M =
        (exchangePointTransport F V (ι m) (e m)).app M ≫
          (exchangePointTransport F V (ι 1) (e 1)).app ((P m).obj M) ≫
            (F ⋙ V).map ((c m).hom.app M)) ∧
    (∀ (Fd : C ⥤ B) (a : Fd ≅ F),
      (∀ (r : ℕ+) (M : C),
        (exchangePointTransport Fd V (ι r) (conjugatedExchange a (e r))).app M =
          V.map (a.hom.app M) ≫ (exchangePointTransport F V (ι r) (e r)).app M ≫
            V.map (a.inv.app ((P r).obj M))) ∧
      (∀ (m : ℕ+) (M : C),
        (exchangePointTransport Fd V (ι (m + 1))
          (conjugatedExchange a (e (m + 1)))).app M =
            (exchangePointTransport Fd V (ι m) (conjugatedExchange a (e m))).app M ≫
              (exchangePointTransport Fd V (ι 1)
                (conjugatedExchange a (e 1))).app ((P m).obj M) ≫
                  (Fd ⋙ V).map ((c m).hom.app M))) := by
  have hcomp : ∀ (m : ℕ+) (M : C),
      (exchangePointTransport F V (ι (m + 1)) (e (m + 1))).app M =
        (exchangePointTransport F V (ι m) (e m)).app M ≫
          (exchangePointTransport F V (ι 1) (e 1)).app ((P m).obj M) ≫
            (F ⋙ V).map ((c m).hom.app M) := by
    intro m M
    change (ι (m + 1)).app (F.obj M) ≫ V.map ((e (m + 1)).app M) =
      ((ι m).app (F.obj M) ≫ V.map ((e m).app M)) ≫
        ((ι 1).app (F.obj ((P m).obj M)) ≫ V.map ((e 1).app ((P m).obj M))) ≫
          V.map (F.map ((c m).hom.app M))
    rw [hι]
    simp only [Category.assoc]
    rw [← V.map_comp, he]
    simp only [V.map_comp]
    have hn := (ι 1).naturality ((e m).app M)
    dsimp at hn
    rw [← Category.assoc ((ι 1).app _) (V.map ((Q 1).map _)), ← hn]
    simp only [Category.assoc]
  refine ⟨hcomp, ?_⟩
  intro Fd a
  have hconj : ∀ (r : ℕ+) (M : C),
      (exchangePointTransport Fd V (ι r) (conjugatedExchange a (e r))).app M =
        V.map (a.hom.app M) ≫ (exchangePointTransport F V (ι r) (e r)).app M ≫
          V.map (a.inv.app ((P r).obj M)) := by
    intro r M
    change (ι r).app (Fd.obj M) ≫
        V.map ((Q r).map (a.hom.app M) ≫ (e r).app M ≫
          a.inv.app ((P r).obj M)) = _
    simp only [V.map_comp]
    have hn := (ι r).naturality (a.hom.app M)
    dsimp at hn
    rw [← Category.assoc ((ι r).app _) (V.map ((Q r).map _)), ← hn]
    simp only [exchangePointTransport, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Category.assoc]
  refine ⟨hconj, ?_⟩
  intro m M
  rw [hconj, hconj, hconj, hcomp]
  simp only [Functor.comp_map, Category.assoc]
  simp only [← V.map_comp_assoc, Iso.inv_hom_id_app, V.map_id, Category.id_comp]
  rw [← V.map_comp, a.inv.naturality, V.map_comp]

end CategoryTheory
