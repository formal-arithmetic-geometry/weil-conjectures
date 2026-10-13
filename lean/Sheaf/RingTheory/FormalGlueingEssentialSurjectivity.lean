/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J3
-/
module

public import Sheaf.RingTheory.FormalGlueingData
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Sheaf.Paper.FormalGlueingCanonicalMaps
import Sheaf.RingTheory.FormalGlueingH0Localization
import Sheaf.Algebra.Module.TorsionSubmoduleFlatBaseChangeIso
import Sheaf.Paper.TorsionModuleFlatBaseChangeIso
import Sheaf.RingTheory.TorsionExtensionFlatDescent

/-!
# Algebraizing formal glueing data

Source: Stacks Project, More on Algebra, Proposition 05ER.
(blueprint: lem-weil-pbc-formal-glueing-essential-surjectivity).
-/

@[expose] public section

universe u v w

open CategoryTheory

namespace FormalGlueing

/-- Every formal glueing datum is isomorphic to a canonical one.
Source: Stacks, More on Algebra, Proposition 05ER, second and third paragraphs;
steps 7–11 of its formal-glueing equivalence node.
(blueprint: lem-weil-pbc-formal-glueing-essential-surjectivity).
Proof: let H be the submodule of compatible families in X. Chart projection extends
uniquely to a bijection H localized at f i to X.M i by the H0 localization lemma.
Tensor the prime projection with S and use the fraction formulas to obtain a morphism
Psi from Can(H) to X. Its prime map is bijective after each localization, because the
chart maps and the comparisons are bijective. Exactness of localization makes its
kernel and cokernel vanish locally; finitely many annihilating powers of the generators
make both I-power torsion. Torsion-submodule base change writes an element of the
kernel as 1 tensor h for a torsion h in H. All chart projections of h vanish, and
its prime projection vanishes by membership in the kernel, so h = 0. Thus Psi.prime
is injective. Its cokernel Q identifies with its scalar extension by torsion-module
base change. Descend the extension of Q extended to S by H extended to S, obtaining
H -> E -> Q and an isomorphism E extended to S to X.M'. The injection H -> E
becomes bijective on each localization since Q vanishes there. Combine its localized
inverses with Psi's chart maps and the prime isomorphism to obtain Can(E) -> X.
Precomposing the compatibility equations with these local bijections verifies that
this is a morphism; the componentwise inverse maps satisfy the same equations and
form its inverse. Bundle E in the stated universe: the construction uses submodules,
quotients and finite products of modules already in that universe. For t = 0 the
quotient hypothesis identifies R with S and there are no chart equations; for I = R
all ideal-power torsion kernel/cokernel terms are zero. -/
theorem canonical_essentially_surjective {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (φ : R →+* S) (t : ℕ) (f : Fin t → R)
    (Can : ModuleCat.{max u v w} R ⥤ Data.{u, v, max u v w} φ f)
    (hobj : (∀ M : ModuleCat.{max u v w} R,
        (Can.obj M).M' = extend φ M ∧
        (∀ i : Fin t, (Can.obj M).M i =
          ModuleCat.of (Localization.Away (f i)) (LocalizedModule.Away (f i) M)) ∧
        (∀ i : Fin t, HEq ((Can.obj M).alpha i).toLinearMap (compare φ (f i) M)) ∧
        (∀ i j : Fin t,
          HEq ((Can.obj M).alpha_overlap i j).toLinearMap (swap (f i) (f j) M))))
    (hflat : φ.Flat)
    (hquot : Function.Bijective
      (Ideal.quotientMap ((Ideal.span (Set.range f)).map φ) φ Ideal.le_comap_map))
    (X : Data.{u, v, max u v w} φ f) :
    ∃ M : ModuleCat.{max u v w} R, Nonempty (Can.obj M ≅ X) := by
  sorry

end FormalGlueing
