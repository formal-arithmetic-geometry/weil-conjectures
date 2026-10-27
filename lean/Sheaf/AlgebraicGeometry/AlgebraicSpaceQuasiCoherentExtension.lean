/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q88
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

import Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import Sheaf.AlgebraicGeometry.EtaleExtensionFreePresentationsHom
import WeilConjectures.AlgebraicGeometry.EtaleAffineQcoherentULift
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.AlgebraicGeometry.Sites.TorsionAcyclic
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentExtension

/-! # Extensions of quasi-coherent modules on algebraic spaces

Source: Stacks Project, Properties of Spaces, Tag 03M1,
lemma-properties-quasi-coherent, clause (4), extension case
(blueprint: lem-sfb-space-qcoh-extension-closed).

The short exact sequence is in all modules on the small etale ringed site.
Only its outer terms are assumed quasi-coherent.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- An extension of quasi-coherent modules on an algebraic space is quasi-coherent.
Source: Stacks Project, Properties of Spaces, Tag 03M1, clause (4), extension case
(blueprint: lem-sfb-space-qcoh-extension-closed).

Proof:
1. Fix any etale scheme chart T → X. Identify the slice X_et/T with T_et using
   representable_etale_scheme_tests (lem-trf-space-representable-etale-scheme-tests).
   Restriction is exact by localizedSystemExact
   (lem-pur-site-restriction-module-adjunction-exact), and preserves the local free
   presentations of the two outer terms. Write the restricted sequence as M_T, N_T, Q_T.
2. Let L and R be canonical etale extension and Zariski restriction. By
   scheme_zariski_etale_quasiCoherent_equivalence
   (lem-trf-scheme-zariski-etale-quasi-coherent-equivalence), F1 = R(M_T) and F3 = R(Q_T)
   are quasi-coherent, with L(F1) ≅ M_T and L(F3) ≅ Q_T. Set E = R(N_T).
   The adjunction of etaleExtension_free_presentations_hom
   (lem-trf-etale-extension-free-presentations-hom) supplies the counit L(E) → N_T;
   it sends a scalar times a pulled-back section to that scalar times its restriction.
   Naturality makes a diagram with both arrows of the short exact sequence.
3. On an affine open W of T, the restriction comparison in
   etaleExtension_free_presentations_hom identifies M_T on W_et with the associated
   etale module of F1 restricted to W. Affine H^1 vanishes by etale_affine_qcoherent_ulift
   (lem-sc-etale-affine-qcoherent). The exact forgetful functor of
   moduleSheaves_colimits_forgetful (lem-weil-pbc-module-sheaves-colimits-forgetful)
   and surjective_app_of_subsingleton_H_one (lem-sc-lift-sections-h1-vanishing)
   therefore give surjectivity N_T(W) → Q_T(W).
4. Sectionwise kernels give left exactness of F1 → E → F3. Every section of F3 lifts
   on an affine open cover by step 3, so the last map is an epimorphism of Zariski
   sheaves. Apply Scheme.Modules.isQuasicoherent_of_shortExact
   (lem-pc-quasi-coherent-extension) to conclude that E is quasi-coherent.
5. The associated sequence L(F1) → L(E) → L(F3) is short exact in all etale modules,
   by lem-sfb-scheme-etale-module-exact-finiteness-comparison. The canonical counits
   give a morphism from it to M_T → N_T → Q_T, with the end counits isomorphisms.
6. A section killed by the middle counit locally comes from L(F1); injectivity on
   the left and the left counit isomorphism force it to vanish. Conversely, lift
   the quotient of a section of N_T locally through L(F3), then through L(E).
   The difference lies in M_T and lifts through L(F1). Hence the middle counit is
   injective and locally surjective, thus an isomorphism. Since L(E) is quasi-coherent
   by the scheme comparison, N_T is quasi-coherent.
7. This holds for every chart T. Its local free presentations are the same
   presentations and covers in X_et, so they prove quasi-coherence of N itself
   (def-trf-space-quasi-coherent-module). The argument allows empty charts and uses
   no quasi-compactness, separation or Noetherian hypothesis. -/
theorem isQuasicoherent_of_shortExact
    {S : Scheme.{u}} (X : AlgebraicSpace S) (c : ShortComplex X.Modules)
    (hc : c.ShortExact) (hM : c.X₁.IsQuasicoherent) (hQ : c.X₃.IsQuasicoherent) :
    c.X₂.IsQuasicoherent := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
