/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantEtale
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantSets

/-!
# Finite locally constant sheaves of sets and finite étale schemes

For a scheme `T`, the sheaf of sections of a finite étale `T`-scheme is a finite locally
constant sheaf of sets on the small étale site, and every finite locally constant sheaf of sets
is of this form (`AlgebraicGeometry.Scheme.isFiniteLocallyConstant_yoneda_and_exists_iso`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- **Finite locally constant sheaves of sets are finite étale schemes.** For a scheme `T`:

* for every finite étale `π : P ⟶ T`, the presheaf of sections `U ↦ Hom_T(U, P)` on the small
  étale site (the Yoneda presheaf of `P`, viewed as an étale `T`-scheme) is a sheaf, and it
  is finite locally constant;
* every finite locally constant sheaf of sets `E` is isomorphic to the sheaf of sections of
  a finite étale `T`-scheme.

These are the two object-level halves of the blueprint node. Together with the Yoneda lemma
(morphisms of the sheaves of sections are `T`-morphisms) they give the equivalence between
finite étale `T`-schemes and finite locally constant sheaves of sets, and with it the
statement about finite group actions; neither is stated here.
(blueprint: `lemma-weil-pbc-finite-locally-constant-etale-equivalence`) 
(blueprint: lem-galois-flc-representable)
(blueprint: lemma-weil-pbc-finite-locally-constant-etale-equivalence)
-/
theorem Scheme.isFiniteLocallyConstant_yoneda_and_exists_iso (T : Scheme.{u}) :
    (∀ (P : Scheme.{u}) (π : P ⟶ T) [IsFinite π] [Etale π],
      ∃ h : Presheaf.IsSheaf T.smallEtaleTopology (uliftYoneda.{u + 1}.obj (Scheme.Etale.mk π)),
        IsFiniteLocallyConstantSheafOfTypes ⟨_, h⟩) ∧
    ∀ E : Sheaf T.smallEtaleTopology (Type (u + 1)), IsFiniteLocallyConstantSheafOfTypes E →
      ∃ (P : Scheme.{u}) (π : P ⟶ T) (_ : IsFinite π) (_ : Etale π),
        Nonempty (E.obj ≅ uliftYoneda.{u + 1}.obj (Scheme.Etale.mk π)) :=
  isFiniteLocallyConstant_yoneda_and_exists_iso' T

end AlgebraicGeometry
