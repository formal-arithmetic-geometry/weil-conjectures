/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T2
-/
module

public import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
public import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# Recovering finite generators and relations on an étale covering

Source: Stacks Project, Descent, Tag 05VG, lemma-equivalence-quasi-coherent-properties
(blueprint: lem-sfb-zariski-etale-finiteness-local-recovery).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- Étale local finite generators or relations can be lifted to Zariski modules on
members of an étale covering. This is the local recovery step, before fpqc descent.
The tensor pullback in the finite-type clause and the ordinary pullback in the
finite-presentation clause are canonically isomorphic left adjoints to pushforward.

Source: Stacks Project, Descent, Tag 05VG, lemma-equivalence-quasi-coherent-properties,
reduction of local properties to presentations on members of a covering
(blueprint: lem-sfb-zariski-etale-finiteness-local-recovery).

Proof: apply the site-local definition at the final étale object to obtain an étale
cover carrying finite generating epimorphisms, respectively finite free presentations.
For each member u:U to T, étale composition and cancellation identify the slice site
with U_et. The tensor-section formula and tensor-pullback composition identify the
restricted module with the extension of u^*F, compatibly with all maps. Pullback of F
is quasi-coherent. The unit-module comparison identifies the finite free terms with
extensions of Zariski finite free modules. Full faithfulness on quasi-coherent modules
lifts each presentation map. In the finite-type case the lifted generating map has a
quasi-coherent cokernel C, and its extension is zero by preservation of cokernels.
Faithfulness gives id_C = 0, so C is zero and the lifted map is an epimorphism. In the
finite-presentation case the Zariski cokernel of the lifted matrix is quasi-coherent;
its induced map to u^*F extends to an isomorphism by the given presentation. Full
faithfulness lifts its inverse and both inverse identities. This makes u^*F finitely
presented. Étale covers are fpqc, giving the displayed precoverage conditions. Finally
uniqueness of left adjoints identifies tensor and ordinary scheme-module pullback.
No descent of finiteness to T is performed here. The index can be taken in Type (u+1),
since objects and arrows of the small étale site lie in that universe. Empty covers,
zero modules and zero generator or relation ranks cause no exception. -/
theorem zariskiEtale_finiteness_local_recovery (T : Scheme.{u})
    (c : ZariskiEtaleModuleContext T) (F : T.Modules) [F.IsQuasicoherent] :
    ((c.extension.obj F).IsFiniteType →
      ∃ (I : Type (u + 1)) (Y : I → Scheme.{u}) (f : ∀ i, Y i ⟶ T),
        (∀ i, Etale (f i)) ∧
          Presieve.ofArrows Y f ∈ Scheme.fpqcPrecoverage T ∧
          ∀ i, ((tensorPullback (f i)).obj F).IsFiniteType) ∧
    ((c.extension.obj F).IsFinitePresentation →
      ∃ (I : Type (u + 1)) (Y : I → Scheme.{u}) (f : ∀ i, Y i ⟶ T),
        (∀ i, Etale (f i)) ∧
          Presieve.ofArrows Y f ∈ Scheme.fpqcPrecoverage T ∧
          ∀ i, ((pullback (f i)).obj F).IsFinitePresentation) := by sorry

end AlgebraicGeometry.Scheme.Modules
