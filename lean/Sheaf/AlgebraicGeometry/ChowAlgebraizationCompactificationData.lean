/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Sheaf.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Sheaf.AlgebraicGeometry.FormalSystemsPullback
import Sheaf.AlgebraicGeometry.GrothendieckExistenceProjective
import Sheaf.AlgebraicGeometry.FiniteTypeModuleSupportPullback

/-! # Projective compactification algebraization before boundary removal

Source: Stacks Project, Theorem 088E, from Chow compactification through the displayed
support equation (blueprint: new-chow-algebraization-core-support-data).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry

/-- Construct an algebraization by restricting from a proper compactification, retaining
its degree-zero support on the adic closed fibre.
Source: Stacks Project, Theorem 088E, the paragraphs from "Choose an open immersion"
through the displayed equation for the support intersect V(I).
(blueprint: new-chow-algebraization-core-support-data)

Proof: Factor the supplied quasi-compact immersion into its scheme-theoretic image,
a closed subscheme of the projective space, obtaining an open immersion j:Y -> P.
The closed image P is projective, hence proper over A and Noetherian. Pull back G
termwise. Finite-type pullback support and Nakayama for the successive nilpotent
quotients identify every term's support with q inverse Supp(G_0). This set is proper
over A because q is proper and G_0 has proper support. Its image under j is closed in P.
Extend the terms by j_*: they are coherent by Stacks 0CYJ (coherent open pushforward
on closed support). On j(Y) the quotient compatibility is unchanged; off that closed
support the terms vanish, so the extended terms form a coherent formal system.
Projective existence algebraizes this system to F'. Restrict F' along j to F.
Restriction is coherent and commutes with the ideal-power quotients, yielding the
completion isomorphism on Y. On the adic closed fibre Nakayama identifies Supp(F')
with the support of its first quotient. That quotient is j_*q^*G_0 and has support
inside j(Y), giving the stated containment. No assertion about support away from the
closed fibre is made here; the separate support theorem proves boundary avoidance. -/
theorem exists_chow_algebraization_compactification_data
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) [IsAdicComplete I A]
    {Z : Scheme.{u}} [IsNoetherian Z] (f : Z ⟶ Spec (.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (Q : Z.IdealSheafData)
    (hQ : Q = (Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f)
    (G : CoherentFormalModule Z Q)
    (hR : Scheme.Modules.HasSupportProperOver f (G.obj.obj (op 0)))
    (Y : Scheme.{u}) (q : Y ⟶ Z) [IsProper q] (n : ℕ)
    (e : Y ⟶ ProjectiveSpace (ULift.{u} (Fin (n + 1))) (Spec (.of A)))
    [IsImmersion e]
    (he : e ≫ (ProjectiveSpace (ULift.{u} (Fin (n + 1))) (Spec (.of A)) ↘ Spec (.of A)) =
      q ≫ f) :
    ∃ (P : Scheme.{u}) (p : P ⟶ Spec (.of A)) (j : Y ⟶ P)
      (F' : CoherentModules P) (F : CoherentModules Y),
      IsNoetherian P ∧ IsProper p ∧ IsOpenImmersion j ∧
      j ≫ p = q ≫ f ∧
      Nonempty ((Scheme.Modules.tensorPullback j).obj F'.obj ≅ F.obj) ∧
      Nonempty (G.obj ⋙ Scheme.Modules.tensorPullback q ≅
        formalCompletionSystem (Q.comap q) F.obj) ∧
      {x : P | ¬ Subsingleton (F'.obj.presheaf.stalk x)} ∩
        p ⁻¹' PrimeSpectrum.zeroLocus (I : Set A) ⊆ Set.range j := by sorry

end AlgebraicGeometry
