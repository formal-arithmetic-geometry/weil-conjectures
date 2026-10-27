/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.KrullDimension
public import Mathlib.RingTheory.KrullDimension.Basic
public import WeilConjectures.Blowup.Gluing
public import WeilConjectures.Compactification.StrictTransform
public import Sheaf.AlgebraicGeometry.IsRegularScheme
import WeilConjectures.Blowup.Complement
import WeilConjectures.Blowup.FlatBaseChange
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Sheaf.AlgebraicGeometry.RegularPointBlowupGeometry
import Sheaf.AlgebraicGeometry.PointBlowdownFactorization

/-!
# Deleting an untouched point blowup from a regular surface tower

Source: Stacks Project, Resolution of Surfaces, Tag 0C5J, and Divisors,
Tags 0805 and 02OS; the tower refinement is the agent induction in the DAG
(blueprint: lem-sfb-delete-untouched-point-blowup).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Delete a point blowup whose exceptional curve is untouched by subsequent centres and
contracted by the final morphism. The original length is `n + 1`; `a` indexes the deleted
arrow starting at zero. The maps `q` are the original composites to level zero. The ideal
sheaves `E` encode the exceptional fibre and its scheme-theoretic strict transforms;
their values before level `a.succ` are irrelevant. The output maps `p` similarly encode
the shorter tower's composites, with its level zero identified with the original one by
`e₀`. Each output level has the structure map `p j ≫ (X 0 ↘ S)`.

Source: Stacks Project, Resolution of Surfaces, Tag 0C5J, and Divisors, Tags 0805 and 02OS
(blueprint: lem-sfb-delete-untouched-point-blowup).

Proof plan:
1. Start at the deleted arrow with the original point blowup. Its exceptional fibre
   is `E a.succ`, and it is an isomorphism away from that fibre by
   thm-nagata-global-blowup-complement. If this is the last arrow no swaps are needed.
2. Inductively let `cᵢ` be the moved point blowup and let `qᵢ` be the next centre.
   Its image `y` differs from the centre `z` of `cᵢ`, since `qᵢ` avoids `Eᵢ`.
   Properness makes `y` closed, and the complement isomorphism identifies its local
   ring with that at `qᵢ`, of dimension two. Blow up `y`. The node
   lem-sfb-regular-point-blowup-geometry gives an integral regular Noetherian scheme;
   the new surface has dimension two by its local rings at closed points. The unique
   point over `z` still has local dimension two (def-weil-proper-morphism).
3. Compare the two orders of blowing up over the opens complementary to `y` and `z`.
   def-nagata-blowup-flat-base-change-map and thm-nagata-blowup-flat-base-change give
   canonical identifications over both opens, using def-weil-flat-morphism for open
   immersions. On their overlap all maps are the complement identities. Glue the
   comparisons and their inverses with lem-weil-pbc-scheme-morphism-gluing.
4. The fibre over the moved centre is the strict transform of `Eᵢ` as a closed
   subscheme: the whole inverse image lies away from the next centre, so its
   scheme-theoretic closure adds nothing (def-nagata-strict-transform). Repeat the
   swaps and concatenate the unchanged prefix with the swapped arrows. There are
   exactly `n` arrows, and their composite after `c` equals the original composite.
5. Apply lem-sfb-point-blowdown-factorization to `c` and `f` to obtain `g`. Apply its
   uniqueness also to the structure map to `S`, showing `g` is over `S`; the other
   maps already are over `S` by their construction (def-weil-scheme-over-base).
6. Every new centre has the same image in level zero as the corresponding old centre.
   Thus centres remain outside any preserved open `V`. The complement isomorphisms
   identify all composites over `V` with `V`; the local swap maps are identities
   there and remain so after gluing. The displayed pullback map `r` records that
   the restriction of `c` is the identity under these identifications. -/
theorem exists_delete_untouched_point_blowup
    (S : Scheme.{u}) (n : ℕ) (X : Fin (n + 2) → Scheme.{u})
    [∀ i : Fin (n + 2), (X i).Over S]
    [∀ i : Fin (n + 2), IsIntegral (X i)]
    [∀ i : Fin (n + 2), IsNoetherian (X i)]
    (hregular : ∀ i : Fin (n + 2), IsRegularScheme (X i))
    (hdim : ∀ i : Fin (n + 2), topologicalKrullDim (X i) = 2)
    (b : ∀ i : Fin (n + 1), X i.succ ⟶ X i.castSucc)
    (hbS : ∀ i : Fin (n + 1), (b i).IsOver S)
    (q : ∀ i : Fin (n + 2), X i ⟶ X 0)
    (hq₀ : q 0 = 𝟙 (X 0))
    (hq : ∀ i : Fin (n + 1), b i ≫ q i.castSucc = q i.succ)
    (x : ∀ i : Fin (n + 1), X i.castSucc)
    (hx : ∀ i : Fin (n + 1), IsClosed ({x i} : Set (X i.castSucc)))
    (hx_dim : ∀ i : Fin (n + 1), ringKrullDim ((X i.castSucc).presheaf.stalk (x i)) = 2)
    (hb : ∀ i : Fin (n + 1),
      ∃ e : X i.succ ≅ (Scheme.IdealSheafData.vanishingIdeal ⟨{x i}, hx i⟩).blowup,
        e.hom ≫ (Scheme.IdealSheafData.vanishingIdeal ⟨{x i}, hx i⟩).blowupMap = b i)
    (a : Fin (n + 1)) (E : ∀ i : Fin (n + 2), (X i).IdealSheafData)
    (hEₐ : E a.succ = (Scheme.IdealSheafData.vanishingIdeal ⟨{x a}, hx a⟩).comap (b a))
    (hE : ∀ i : Fin (n + 1), a < i → E i.succ =
      (strictTransformMap (E i.castSucc).subschemeι (b i)
        (⟨({x i} : Set (X i.castSucc))ᶜ, (hx i).isOpen_compl⟩ : (X i.castSucc).Opens)).ker)
    (havoid : ∀ i : Fin (n + 1), a < i → x i ∉ (E i.castSucc).support)
    (Z : Scheme.{u}) [Z.Over S] (f : X (Fin.last (n + 1)) ⟶ Z) [f.IsOver S]
    (himage : ∃ z : Z, f '' (E (Fin.last (n + 1))).support = {z}) :
    ∃ (Y : Fin (n + 1) → Scheme.{u}) (e₀ : Y 0 ≅ X 0)
      (d : ∀ j : Fin n, Y j.succ ⟶ Y j.castSucc)
      (p : ∀ j : Fin (n + 1), Y j ⟶ X 0)
      (y : ∀ j : Fin n, Y j.castSucc)
      (hy : ∀ j : Fin n, IsClosed ({y j} : Set (Y j.castSucc)))
      (c : X (Fin.last (n + 1)) ⟶ Y (Fin.last n))
      (g : Y (Fin.last n) ⟶ Z)
      (z : Y (Fin.last n)) (hz : IsClosed ({z} : Set (Y (Fin.last n))))
      (ec : X (Fin.last (n + 1)) ≅ (Scheme.IdealSheafData.vanishingIdeal ⟨{z}, hz⟩).blowup),
      p 0 = e₀.hom ∧
      (∀ j : Fin n, d j ≫ p j.castSucc = p j.succ) ∧
      (∀ j : Fin (n + 1), IsIntegral (Y j) ∧ IsRegularScheme (Y j) ∧
        IsNoetherian (Y j) ∧ topologicalKrullDim (Y j) = 2) ∧
      (∀ j : Fin n,
        ∃ e : Y j.succ ≅ (Scheme.IdealSheafData.vanishingIdeal ⟨{y j}, hy j⟩).blowup,
          e.hom ≫ (Scheme.IdealSheafData.vanishingIdeal ⟨{y j}, hy j⟩).blowupMap = d j) ∧
      c ≫ p (Fin.last n) = q (Fin.last (n + 1)) ∧
      c ≫ g = f ∧
      c ≫ p (Fin.last n) ≫ (X 0 ↘ S) = (X (Fin.last (n + 1)) ↘ S) ∧
      g ≫ (Z ↘ S) = p (Fin.last n) ≫ (X 0 ↘ S) ∧
      ec.hom ≫ (Scheme.IdealSheafData.vanishingIdeal ⟨{z}, hz⟩).blowupMap = c ∧
      E (Fin.last (n + 1)) = (Scheme.IdealSheafData.vanishingIdeal ⟨{z}, hz⟩).comap c ∧
      IsIso (c ∣_ (⟨({z} : Set (Y (Fin.last n)))ᶜ, hz.isOpen_compl⟩ :
        (Y (Fin.last n)).Opens)) ∧
      ∀ V : (X 0).Opens,
        (∀ i : Fin (n + 1), q i.castSucc (x i) ∉ V) →
        (∀ j : Fin n, p j.castSucc (y j) ∉ V) ∧
        (∀ i : Fin (n + 2), IsIso (q i ∣_ V)) ∧
        (∀ j : Fin (n + 1), IsIso (p j ∣_ V)) ∧
        ∃ r : Limits.pullback (q (Fin.last (n + 1))) V.ι ⟶
            Limits.pullback (p (Fin.last n)) V.ι,
          IsIso r ∧
          r ≫ Limits.pullback.fst (p (Fin.last n)) V.ι =
            Limits.pullback.fst (q (Fin.last (n + 1))) V.ι ≫ c ∧
          r ≫ Limits.pullback.snd (p (Fin.last n)) V.ι =
            Limits.pullback.snd (q (Fin.last (n + 1))) V.ι := by
  sorry

end AlgebraicGeometry
