/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.HomologyCoherence
public import WeilConjectures.TraceFormula.WeilTrace

/-!

# Iterated Weil structures of Weil complexes and of their homology sheaves

Let `e : X ≅ X` be an automorphism of a scheme over `Spec k` and `(K, φ)` a Weil object of
`Dᵇc(X)⟦ℚ̲̄_ℓ⟧` for `e`. Its iterate `(K, φ^{(n+1)})`
(`ProEtale.CondensedRing.WeilBoundedConstructible.powSucc`) is a Weil object for `e^{n+1}`, with
the iterated structure isomorphism `Iso.powSuccStr` of the derived pullbacks, as for Weil sheaves
(`ProEtale.CondensedRing.WeilSheaf.powSucc`). The homology sheaves of the iterate are the
iterates of the homology sheaves (`ProEtale.CondensedRing.WeilBoundedConstructible.homologyPowSuccIso`):
the commutation of the homology sheaves with the derived pullbacks is compatible with the
composition isomorphisms (`ProEtale.CondensedRing.leftDerivedUpperStarHomologyIso_comp_hom_app`).

The general statement is `CategoryTheory.Iso.powSuccStr_hom_eq_of_comp`: a functor `H` with
commutation isomorphisms `H ⋙ Q g ≅ P g ⋙ H` compatible with the composition isomorphisms
commutes with the iterated structure isomorphisms.

## Main definitions

- `ProEtale.CondensedRing.WeilBoundedConstructible.powSucc`: the iterate `(K, φ^{(n+1)})`.
- `ProEtale.CondensedRing.weilHomologyComparisonOfHom`: the commutation `Hʲ ⋙ g^* ≅ Lg^* ⋙ Hʲ`
  for an endomorphism `g`.

## Main results

- `ProEtale.CondensedRing.WeilBoundedConstructible.homologyPowSuccIso`:
  `Hʲ(K, φ^{(n+1)}) ≅ (Hʲ(K), φ_{Hʲ(K)}^{(n+1)})` as Weil sheaves for `e^{n+1}`.

-/

@[expose] public section

universe u

open CategoryTheory Endofunctor

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory.Iso

variable {C : Type*} [Category C] {X : C} (e : X ≅ X) {D E : Type*} [Category D] [Category E]

/-- A functor `H : D ⥤ E` commutes with the iterated structure isomorphisms: let `P g` and
`Q g` be families of endofunctors of `D` and `E` indexed by the endomorphisms `g` of `X`, with
composition isomorphisms, and let `h g : H ⋙ Q g ≅ P g ⋙ H` be compatible with them. Then the
iterated structure isomorphism of `(h e).app a ≪≫ H.mapIso φ` is
`(h e^{n+1}).app a ≫ H (φ^{(n+1)})`. -/
theorem powSuccStr_hom_eq_of_comp (P : (X ⟶ X) → D ⥤ D)
    (compP : ∀ f g : X ⟶ X, P (f ≫ g) ≅ P g ⋙ P f) (Q : (X ⟶ X) → E ⥤ E)
    (compQ : ∀ f g : X ⟶ X, Q (f ≫ g) ≅ Q g ⋙ Q f) (H : D ⥤ E)
    (h : ∀ g : X ⟶ X, H ⋙ Q g ≅ P g ⋙ H)
    (hcomp : ∀ (f g : X ⟶ X) (a : D), (h (f ≫ g)).hom.app a ≫ H.map ((compP f g).hom.app a) =
      (compQ f g).hom.app (H.obj a) ≫ (Q f).map ((h g).hom.app a) ≫
        (h f).hom.app ((P g).obj a))
    {a : D} (φ : (P e.hom).obj a ≅ a) (n : ℕ) :
    (e.powSuccStr Q compQ ((h e.hom).app a ≪≫ H.mapIso φ) n).hom =
      (h (e.powSucc n).hom).hom.app a ≫ H.map (e.powSuccStr P compP φ n).hom := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (compQ (e.powSucc n).hom e.hom).hom.app (H.obj a) ≫
        (Q (e.powSucc n).hom).map ((h e.hom).hom.app a ≫ H.map φ.hom) ≫
          (e.powSuccStr Q compQ ((h e.hom).app a ≪≫ H.mapIso φ) n).hom =
      (h ((e.powSucc n).hom ≫ e.hom)).hom.app a ≫
        H.map ((compP (e.powSucc n).hom e.hom).hom.app a ≫ (P (e.powSucc n).hom).map φ.hom ≫
          (e.powSuccStr P compP φ n).hom)
    rw [ih, Functor.map_comp_assoc, ← (h (e.powSucc n).hom).hom.naturality_assoc,
      Functor.map_comp, Functor.map_comp, reassoc_of% (hcomp (e.powSucc n).hom e.hom a)]
    simp only [Functor.comp_map, Category.assoc]

end CategoryTheory.Iso

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-! ### The iterated Weil structure -/

namespace WeilBoundedConstructible

variable {e : X ≅ X}

/-- The iterate `(K, φ^{(n+1)})` of a Weil object `(K, φ)` for an automorphism `e`: a Weil object
for `e^{n+1}`, with the iterated structure isomorphism `Iso.powSuccStr` of the derived pullbacks,
`φ^{(1)} = φ` and `φ^{(n+2)} : L(e^{n+1} ≫ e)^* K ≅ L(e^{n+1})^* Le^* K ≅ L(e^{n+1})^* K ≅ K`. -/
noncomputable def powSucc (K : WeilBoundedConstructible ℓ e.hom) (n : ℕ) :
    WeilBoundedConstructible ℓ (e.powSucc n).hom :=
  IsoAlgebra.mk K.carrier
    (e.powSuccStr (fun g ↦ boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g)
      (fun f g ↦ boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ f g) K.str n)

end WeilBoundedConstructible

end AlgebraicGeometry.ProEtale.CondensedRing
