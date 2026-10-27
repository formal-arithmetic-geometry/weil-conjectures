/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q07
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Mathlib.Topology.Compactness.Paracompact
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Topology.Sheaves.Flasque
import WeilConjectures.AlgebraicGeometry.InjectiveRestrictionSurjective
import WeilConjectures.CategoryTheory.Abelian.RightDerived.FullLongExactSequence
import WeilConjectures.Topology.FlasqueZariskiAcyclic

/-!
# Soft abelian sheaves are acyclic

Source: Demailly, Complex Analytic and Differential Geometry, IV §4, Definition (4.9),
Proposition (4.14), Theorem (4.15), printed pp.204–205
(blueprint: lem-sfb-soft-abelian-sheaf-acyclic).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Opposite

namespace TopCat.Sheaf

/-- Source: Demailly, Complex Analytic and Differential Geometry, IV §4, Definition (4.9),
Proposition (4.14), Theorem (4.15), printed pp.204–205
(blueprint: lem-sfb-soft-abelian-sheaf-acyclic).

The softness hypothesis uses the unit of inverse image/pushforward for the closed-subspace
inclusion, evaluated at the top open. Its target is the global sections of the inverse-image
sheaf, whose sections are locally represented families of germs along the closed subset.

Proof:
1. Using lem-weil-pbc-site-sheaves-enough-injectives on the opens site, embed the soft
   sheaf G into an injective I and take its cokernel Q, obtaining 0 → G → I → Q → 0.
2. Regard abelian sheaves as modules over the locally constant integer sheaf: locally an
   integer acts by repeated addition. This identifies objects, morphisms, and injectivity.
   Apply lem-sc-ringed-space-injective-restriction-surjective to make I flasque
   in the sense of def-sc-zariski-flasque.
3. A section of I along a closed subset extends to a neighborhood by the closed-section
   lemma lem-sfb-closed-section-neighborhood-extension; flasqueness extends it globally.
   Hence I is soft.
4. Demailly (4.14), lem-sfb-soft-kernel-closed-sections, implies that Q is soft and that
   Γ(X,I) → Γ(X,Q) is surjective (take the closed subset to be all of X).
5. Use def-weil-pbc-sites-and-cohomology, lem-weil-pbc-derived-functor-long-exact,
   and lem-sc-topological-flasque-acyclic. The resulting long exact sequence gives
   H¹(X,G) = 0 and H^q(X,Q) ≃ H^(q+1)(X,G) for q ≥ 1.
6. Induct on positive degree for all soft sheaves on X simultaneously: the quotient Q
   is soft, so its vanishing in degree q gives that of G in degree q+1.
-/
theorem subsingleton_H'_top_of_soft {X : TopCat.{u}} [ParacompactSpace X] [T2Space X]
    [HasExt.{u} (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
    (G : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (hG : ∀ (S : Set X), IsClosed S →
      Function.Surjective
        (((pullbackPushforwardAdjunction AddCommGrpCat.{u}
          (TopCat.ofHom ⟨(Subtype.val : S → X), continuous_subtype_val⟩)).unit.app G).hom.app
            (op (⊤ : Opens X))))
    (r : ℕ) (hr : 0 < r) :
    Subsingleton (CategoryTheory.Sheaf.H' G r ⊤) := by
  sorry

end TopCat.Sheaf
