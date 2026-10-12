/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U2
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.ClosedImmersionCoherentEquivalence
import Sheaf.AlgebraicGeometry.ModuleSupportProperOverBase
import Sheaf.AlgebraicGeometry.CoherentFormalModulesAbelian

/-! # Transport of a formal comparison through a closed immersion

Source: Stacks Project, Theorem 088E, closed quotient and final comparison step.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Transport a comparison whose kernel is killed by a positive power of an ideal
with nonempty complementary open through a closed immersion. Proper support of the
coherent target makes the transported completion properly supported.

Source: Stacks Project, Theorem 088E, paragraphs 2--4, Tag 087T and Lemma 0CYS.
(blueprint: lem-weil-pbc-closed-immersion-formal-comparison-transport).

Proof: Termwise closed pushforward identifies coherent formal systems on Z with
systems killed by j.ker. Apply this to the completion of H and the given alpha,
and use the specified pushforward isomorphism to obtain a map from M to that
pushed completion N. Let B be L^t as a quasi-coherent ideal on Z and let J be its
inverse image under O_X -> j_*O_Z. On affine opens, J is the inverse image ideal
under the quotient ring map, so j.ker <= J. Choose a point of the nonempty open
complement of L.support. At its stalk L, and hence L^t, is the unit ideal; thus
B is not zero and the inverse image J strictly contains j.ker. The limiting fork
identifies k.pt with the kernel of alpha. Closed pushforward is exact, and systems
killed by j.ker are closed under kernels in the ambient formal category. The
universal property therefore identifies its pushforward with the kernel of the
transported map. On affine opens multiplication by J on a pushed module is
multiplication by its quotient ideal B, so the assumed annihilation kills this
kernel termwise. Finally use the scheme-theoretic support of coherent H. Proper
support makes its closed immersion proper over S, and its ideal kills H and all
quotients H/Q^n H. Compose this immersion with j: the resulting proper closed
subscheme in X kills all terms of N. This proves the conclusion for any chosen
Abelian structure, since kernel identifications use their universal properties. -/
theorem exists_closedImmersionFormalComparisonTransport
    {X Z S : Scheme.{u}} [IsNoetherian X] [IsNoetherian Z]
    (f : X ⟶ S) (j : Z ⟶ X) [IsClosedImmersion j]
    [LocallyOfFiniteType (j ≫ f)] (Q : X.IdealSheafData)
    [Abelian (CoherentFormalModule X Q)]
    (M : CoherentFormalModule X Q) (G : CoherentFormalModule Z (Q.comap j))
    (e : M.obj ≅ G.obj ⋙ Scheme.Modules.pushforward j)
    (H : CoherentModules Z)
    (hH : Scheme.Modules.HasSupportProperOver (j ≫ f) H.obj)
    (L : Z.IdealSheafData) (hU : (L.support.compl : Set Z).Nonempty)
    (α : G ⟶ (completion Z (Q.comap j)).obj H)
    (t : ℕ) (ht : 1 ≤ t) (k : KernelFork α) (hk : IsLimit k)
    (hkill : ∀ n : ℕ, IsZero (Scheme.idealModuleProduct
      (Scheme.idealSheafPower L.toModulesι t).2 (k.pt.obj.obj (op n)))) :
    ∃ (N : CoherentFormalModule X Q) (a : M ⟶ N) (J : X.IdealSheafData),
      j.ker < J ∧ AnnihilatedBy Q J (kernel a) ∧
      ∃ (T : Scheme.{u}) (i : T ⟶ X) (_ : IsClosedImmersion i),
        IsProper (i ≫ f) ∧ AnnihilatedBy Q i.ker N := by sorry

end AlgebraicGeometry
