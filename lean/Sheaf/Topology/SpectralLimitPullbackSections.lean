/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Mathlib.Topology.Spectral.Basic
public import Mathlib.Topology.Spectral.Hom
public import Sheaf.Topology.SetsInverseImageComposition

/-!
# Sections of inverse images on spectral limits

Source: Stacks Project, Sheaves on Spaces, Tag 0A32, with the composition maps of Tag 008I
(blueprint: lem-weil-pbc-spectral-limit-pullback-sections).
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace

namespace TopCat.Sheaf

open Classical in
/-- Sections on a compact open pulled back to a directed spectral limit form the indicated
filtered colimit. The maps `rho` and `transition` are specified by their canonical section
formulas. `HEq` transports those formulas across the equal composite maps and opens; it
introduces no choice of a different comparison map.
Source: Stacks Project, Sheaves on Spaces, Tag 0A32, with Tag 008I
(blueprint: lem-weil-pbc-spectral-limit-pullback-sections).

Proof outline, following the node:
1. The spectral directed-limit theorem makes the limit and its projections spectral;
   compact opens remain compact under every transition and projection. Upper tails are
   cofinal: extend a compatible tail family using common upper bounds.
2. The units and the composition isomorphisms define the displayed section maps and
   commute with restriction (`def-weil-pbc-topological-inverse-image`, Tag 008I).
3. The composition isomorphisms obey triple-composition coherence: use naturality of
   units and the uniqueness characterization in `exists_sets_inverseImage_comp`, testing
   morphisms on successive unit images by the composite adjunction.
4. Coherence gives the cocone and transition identities; uniqueness for the identity
   map gives the diagonal identity.
5. The inverse-image stalk bijection (Tag 008H) identifies equality of the pulled-back
   germs with equality of the original germs; a sheaf isomorphism preserves this test.
6. The unequal-germ locus inside a compact open is constructibly closed: its complement
   there is open and hence a union of compact opens.
7. If two sections never become equal, the constructibly closed nonempty-limit theorem
   gives compatible unequal germs and hence an unequal germ at the limit, a contradiction.
   Equality of all germs determines a section (Tag 0079). This proves the last clause.
8. Locally represent a limit section by unit images using the stalk bijection. Refine by
   compact opens and choose a finite cover by compactness; the empty open is allowed.
9. Descend this finite cover, its inclusions and covering equality to a common stage
   using `lem-weil-pbc-spectral-limit-descend-opens` (Tag 0A30).
10. Pull back and restrict the local sections to this stage. Their images are the given
    limit section, so they agree after pullback on every pairwise intersection.
11. By step 7 and a common upper bound they agree at a later stage. Glue there by the
    sheaf axiom. Compatibility with restriction proves surjectivity, the middle clause.
12. The elementwise description of filtered colimits of sets, together with these
    identities, surjectivity and eventual equality, identifies the target with the colimit
    (`def-weil-pbc-category-colimit`). -/
theorem spectralLimit_pullback_sections
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (S : I → TopCat.{u}) [∀ j : I, SpectralSpace (S j)]
    (f : ∀ (j k : I), j ≤ k → (S k ⟶ S j))
    (hf : ∀ (j k : I) (h : j ≤ k), IsSpectralMap (f j k h))
    (hfid : ∀ j : I, f j j le_rfl = 𝟙 (S j))
    (hfcomp : ∀ (j k l : I) (hjk : j ≤ k) (hkl : k ≤ l),
      f k l hkl ≫ f j k hjk = f j l (hjk.trans hkl))
    (X : TopCat.{u}) (p : ∀ j : I, X ⟶ S j)
    (hpcomp : ∀ (j k : I) (h : j ≤ k), p k ≫ f j k h = p j)
    (hlimit : ∀ a : ∀ j : I, S j,
      (∀ (j k : I) (h : j ≤ k), f j k h (a k) = a j) →
      ∃! x : X, ∀ j : I, p j x = a j)
    (htop : X.str = ⨅ j : I, TopologicalSpace.induced (p j) (S j).str)
    (i : I) (G : (S i).Sheaf (Type u)) (U : Opens (S i)) (hU : IsCompact (U : Set (S i)))
    (rho : ∀ (j : I) (hij : i ≤ j),
      ((pullback (Type u) (f i j hij)).obj G).obj.obj (op ((Opens.map (f i j hij)).obj U)) →
      ((pullback (Type u) (p i)).obj G).obj.obj (op ((Opens.map (p i)).obj U)))
    (transition : ∀ (j k : I) (hij : i ≤ j) (hjk : j ≤ k),
      ((pullback (Type u) (f i j hij)).obj G).obj.obj (op ((Opens.map (f i j hij)).obj U)) →
      ((pullback (Type u) (f i k (hij.trans hjk))).obj G).obj.obj
        (op ((Opens.map (f i k (hij.trans hjk))).obj U)))
    (hrho : ∀ (j : I) (hij : i ≤ j) (t :
        ((pullback (Type u) (f i j hij)).obj G).obj.obj
          (op ((Opens.map (f i j hij)).obj U))),
      HEq (rho j hij t)
        (((Classical.choose
            (exists_sets_inverseImage_comp (p j) (f i j hij))).hom.app G).hom.app
          (op ((Opens.map (p j ≫ f i j hij)).obj U))
            (((pullbackPushforwardAdjunction (Type u) (p j)).unit.app
              ((pullback (Type u) (f i j hij)).obj G)).hom.app
                (op ((Opens.map (f i j hij)).obj U)) t)))
    (htransition : ∀ (j k : I) (hij : i ≤ j) (hjk : j ≤ k) (t :
        ((pullback (Type u) (f i j hij)).obj G).obj.obj
          (op ((Opens.map (f i j hij)).obj U))),
      HEq (transition j k hij hjk t)
        (((Classical.choose
            (exists_sets_inverseImage_comp (f j k hjk) (f i j hij))).hom.app G).hom.app
          (op ((Opens.map (f j k hjk ≫ f i j hij)).obj U))
            (((pullbackPushforwardAdjunction (Type u) (f j k hjk)).unit.app
              ((pullback (Type u) (f i j hij)).obj G)).hom.app
                (op ((Opens.map (f i j hij)).obj U)) t))) :
    ((∀ (j : I) (hij : i ≤ j) (t : _), transition j j hij le_rfl t = t) ∧
      (∀ (j k : I) (hij : i ≤ j) (hjk : j ≤ k) (t : _),
        rho k (hij.trans hjk) (transition j k hij hjk t) = rho j hij t) ∧
      (∀ (j k l : I) (hij : i ≤ j) (hjk : j ≤ k) (hkl : k ≤ l) (t : _),
        transition k l (hij.trans hjk) hkl (transition j k hij hjk t) =
          transition j l hij (hjk.trans hkl) t)) ∧
    (∀ s : ((pullback (Type u) (p i)).obj G).obj.obj (op ((Opens.map (p i)).obj U)),
      ∃ (j : I) (hij : i ≤ j) (t : _), rho j hij t = s) ∧
    (∀ (j : I) (hij : i ≤ j) (t t' : _), rho j hij t = rho j hij t' →
      ∃ (k : I) (hjk : j ≤ k), transition j k hij hjk t = transition j k hij hjk t') := by
  sorry

end TopCat.Sheaf
