/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q122
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceArtinRees
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction
public import WeilConjectures.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.ResidueField

import Sheaf.AlgebraicGeometry.AlgebraicSpaceCoherentSupportIdealPower
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineEtaleCover
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Ideal-power annihilation of supported coherent algebraic-space modules

Source: Stacks Project, Spaces Cohomology, Tag 07UK, lemma-power-ideal-kills-sheaf
(blueprint: lem-sfb-space-power-ideal-kills).

The ideal is an arbitrary quasi-coherent submodule of the structure sheaf. On an
affine etale chart, its zero locus consists of the points where every ideal section
maps to zero in the residue field. Support containment is tested on those charts,
using ordinary stalks of the Zariski restriction. For quasi-coherent modules geometric
and ordinary stalks vanish simultaneously, since strict henselization is faithfully flat.
The conclusion uses the existing locally generated ideal-power section subsets from
Artin-Rees: equality with the singleton zero on every test is the zero submodule sheaf.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- A coherent module is supported in the zero locus of a quasi-coherent ideal if and
only if some ideal power annihilates it. The zero exponent is included.
Source: Stacks Project, Spaces Cohomology, Tag 07UK; Morphisms of Spaces, Tag 03MB
(blueprint: lem-sfb-space-power-ideal-kills).

Proof:
1. The ideal/closed-subspace correspondence
   (lem-sfb-space-ideal-closed-subspace-correspondence) associates to I the closed
   subspace Z with defining ideal I, also after every etale base change.
2. Choose the disjoint-affine atlas (lem-a1-space-affine-etale-cover). On each affine
   chart Spec A, the closed immersion (def-weil-closed-immersion) is Spec(A/J), with
   J the given ideal of sections. Its image is V(J), because primes of A/J are
   exactly primes containing J. Equivalently, all elements of J die in the residue
   field. The factorization criterion of step 1 identifies this image with the
   inverse image of the point image of Z. Surjectivity on point classes identifies
   the closed point subset with Z(I). The same test on affine etale charts detects
   support containment; faithful flatness of geometric stalk extensions identifies
   ordinary and geometric stalk vanishing.
3. Compare the locally generated products with the recursive powers in
   lem-sfb-space-coherent-support-ideal-power. At zero both are F. Multiplication
   of a finite sum of n-fold products by an ideal section gives (n+1)-fold products;
   conversely each such product is one ideal section times an n-fold product.
   Sheafifying these local products proves equality by induction.
4. Apply lem-sfb-space-coherent-support-ideal-power with this Z. Its hypotheses are
   precisely Noetherianity of X and coherence of F. Substitute the ideal equality
   from step 1, the closed point subset from step 2, and the product identification
   from step 3. A submodule sheaf is zero exactly when every section subset is {0}.
   This gives both implications with the same range n >= 0; Z need not be reduced. -/
theorem coherent_support_power_ideal_kills
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    (hln : ∀ T : X.EtaleSite, IsLocallyNoetherian (X.etaleForget.obj T))
    (hqc : CompactSpace (Point X.obj.obj))
    (hqs : ∀ (U V : Over S) (a : yoneda.obj U ⟶ X.obj.obj)
      (b : yoneda.obj V ⟶ X.obj.obj), IsAffine U.left → IsAffine V.left →
        CompactSpace (Point (Limits.pullback a b)))
    (F : X.Modules) (hFqc : F.IsQuasicoherent)
    (hFcoh : ∀ T : X.EtaleSite,
      RingedSpace.IsCoherent (X.etaleForget.obj T).toRingedSpace
        ((X.schemeRestriction T).obj F))
    (I : X.Modules) (i : I ⟶ SheafOfModules.unit X.structureSheaf)
    [Mono i] (hI : I.IsQuasicoherent) :
    (∀ (T : X.EtaleSite), IsAffine (X.etaleForget.obj T) →
      ∀ x : X.etaleForget.obj T,
        ¬ Subsingleton (((X.schemeRestriction T).obj F).presheaf.stalk x) →
          ∀ a ∈ idealSectionImage i T, (X.etaleForget.obj T).Γevaluation x a = 0) ↔
    ∃ n : ℕ, ∀ T : X.EtaleSite,
      idealPowerSubsheafSections i F (fun _ ↦ Set.univ) n T = {0} := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
