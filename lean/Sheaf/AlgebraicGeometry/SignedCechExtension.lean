/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.CategoryTheory.SiteCechComplex
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.GroupTheory.Perm.Sign

/-!
# Signed extension of ordered Čech cochains

Source: Stacks Project, Cohomology of Sheaves, Tags 01FI, 01FJ and 01FK.
(blueprint: lem-pc-signed-cech-extension-differential)
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) {I : Type v} [LinearOrder I]
    (U : I → X.Opens) (F : X.Opensᵒᵖ ⥤ AddCommGrpCat.{w})
    (S : SiteCechComplex U (fun i ↦ homOfLE (le_top : U i ≤ ⊤)))

/-- Extend by the sorting sign and restriction from the sorted chosen intersection.
Repeated tuples are sent to zero; no witness of a postponed existence theorem is used.
Source: Stacks 01FG, the formula for c following Definition 01FI.
(blueprint: lem-pc-signed-cech-extension-differential) -/
noncomputable def signedCechExtensionValue (p : ℕ)
    (s : ∀ t : {t : Fin (p + 1) → I // StrictMono t}, F.obj (op (S.W p t.1))) :
    S.cochains F p := by
  classical
  exact fun t ↦ if ht : Function.Injective t then
    (Equiv.Perm.sign (Tuple.sort t) : ℤ) •
      F.map (S.indexMap t (Tuple.sort t)).op
        (s ⟨t ∘ Tuple.sort t, (Tuple.monotone_sort t).strictMono_of_injective
          (ht.comp (Tuple.sort t).injective)⟩)
    else 0

/-- The signed extension is additive.
Source: Stacks 01FG, the formula for c following Definition 01FI. Each branch is a
restriction homomorphism followed by integer multiplication, or zero, so it preserves
zero and addition componentwise.
(blueprint: lem-pc-signed-cech-extension-differential) -/
noncomputable def signedCechExtension (p : ℕ) :
    AddCommGrpCat.of
      (∀ t : {t : Fin (p + 1) → I // StrictMono t}, F.obj (op (S.W p t.1))) ⟶
        S.cochains F p :=
  AddCommGrpCat.ofHom
    { toFun := signedCechExtensionValue X U F S p
      map_zero' := by
        classical
        funext t
        simp [signedCechExtensionValue]
      map_add' := by
        classical
        intro a b
        funext t
        by_cases ht : Function.Injective t <;>
          simp [signedCechExtensionValue, ht, map_add, smul_add] }

/-- On increasing tuples signed extension is the identity.
Source: Stacks 01FK. The sorting permutation is the identity, its sign is one, and
restriction along the identity index map is the identity.
(blueprint: lem-pc-signed-cech-extension-differential) -/
theorem signedCechExtension_increasing (p : ℕ)
    (s : ∀ t : {t : Fin (p + 1) → I // StrictMono t}, F.obj (op (S.W p t.1)))
    (t : {t : Fin (p + 1) → I // StrictMono t}) :
    signedCechExtension X U F S p s t.1 = s t := by
  classical
  change signedCechExtensionValue X U F S p s t.1 = s t
  simp only [signedCechExtensionValue, dif_pos t.2.injective]
  have hs : Tuple.sort t.1 = Equiv.refl _ :=
    Tuple.sort_eq_refl_iff_monotone.mpr t.2.monotone
  have h (σ : Equiv.Perm (Fin (p + 1)))
      (hm : StrictMono (t.1 ∘ σ)) (hσ : σ = Equiv.refl _) :
      (Equiv.Perm.sign σ : ℤ) • F.map (S.indexMap t.1 σ).op
        (s ⟨t.1 ∘ σ, hm⟩) = s t := by
    subst σ
    simp only [Equiv.Perm.sign_refl, Units.val_one, one_smul]
    have hi : S.indexMap t.1 (Equiv.refl (Fin (p + 1))) = 𝟙 (S.W p t.1) :=
      Subsingleton.elim _ _
    rw [hi]
    simp
  exact h _ _ hs

/-- The differential of a signed extension is again a signed extension of its ordered
coordinates.

Source: Stacks 01FJ, with the explicit signed extension of Definition 01FI.
(blueprint: lem-pc-signed-cech-extension-differential)

Proof: Evaluate on a tuple t. If its entries are distinct, let sigma sort t and
reindex the differential sum by the position of the deleted entry in the sorted tuple.
If j is the position deleted from t and k its position in the sorted tuple, the
sorting permutation of the remaining entries has sign epsilon with
(-1)^j epsilon = sign(sigma) (-1)^k: move the deleted entry to the end before and
after sorting, contributing p+1-j and p+1-k transpositions, respectively. The two
restriction composites coincide because opens form a poset;
hence each summand equals the corresponding signed restriction of an ordered face.
If t has exactly one repeated pair and all other entries are distinct, only the two
faces deleting one member of that pair can contribute. Their sorted tuples agree,
and, for equal entries in positions a < b, their sorting signs differ by
(-1)^(b-a-1), since deleting the other occurrence moves it past b-a-1 entries.
Multiplication by the face signs (-1)^a and (-1)^b gives opposite coefficients;
their restriction maps agree,
so they cancel. If there are more repetitions, every face still has repeated entries
and every summand vanishes. Thus the differential has the sorting-sign transformation
law and is zero on repeated tuples. Its value on the sorted tuple is exactly its
ordered coordinate, yielding the asserted equality. For empty I there are no tuples;
for degree zero the same argument is the two-term difference on pairs. -/
theorem signedCechExtension_differential (p : ℕ)
    (s : ∀ t : {t : Fin (p + 1) → I // StrictMono t}, F.obj (op (S.W p t.1))) :
    S.differentialValue F p (signedCechExtension X U F S p s) =
      signedCechExtension X U F S (p + 1)
        (fun t ↦ S.differentialValue F p (signedCechExtension X U F S p s) t.1) := by sorry

end AlgebraicGeometry.Scheme
