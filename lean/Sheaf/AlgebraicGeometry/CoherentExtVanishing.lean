/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.AlgebraicGeometry.Dimension
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import WeilConjectures.AlgebraicGeometry.Modules.Ext
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits

/-!
# Higher Ext vanishing for coherent modules on regular schemes

Source: Stacks Project, Derived Categories of Varieties, Lemma 57.9.4 (Tag 0FZ3), part (1)
(blueprint: lem-sc-p1-ext-coherent-dim-one-vanishing).

## Main statements

* `Scheme.Modules.coherent_ext_subsingleton_of_regular`: vanishing above finite dimension.
* `Scheme.Modules.projectiveLine_coherent_ext_subsingleton`: vanishing in degrees at least two.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- Ext between coherent modules on a regular Noetherian scheme vanishes above its dimension.
Source: Stacks Project, Tag 0FZ3 (1)
(blueprint: lem-sc-p1-ext-coherent-dim-one-vanishing).

Proof:
1. Use the first-quadrant local-to-global Ext spectral sequence
   (lem-sc-ext-sheaf-to-global-spectral-sequence), with terms H^p(X, sheaf Ext^q(F,G)).
2. The stalk comparison (lem-sc-ext-stalk-localization) identifies sheaf Ext stalks with Ext
   over the local rings. Coherence makes F's stalks finite modules; regularity and
   lem-sc-regular-local-ext-vanishing give vanishing for q > dim O_{X,x}.
3. The support bound and cohomology vanishing of lem-sc-ext-support-cohomology-vanishing
   make the E_2 terms zero for p + q > d.
4. The abutment clause of lem-sc-ext-sheaf-to-global-spectral-sequence then makes Ext^i(F,G)
   zero for i > d. A group is zero exactly when its underlying type is a subsingleton.

Regularity is the affine-neighbourhood condition of def-weil-regular-scheme. The dimension
is Scheme.dim (def-pc-dimension), and coherence is RingedSpace.IsCoherent (pqf-def-coherent).
HasExt is only the size infrastructure required by the recorded definition of Ext. -/
theorem coherent_ext_subsingleton_of_regular (X : Scheme.{u})
    [CompactSpace X] [IsLocallyNoetherian X] [HasExt.{u} X.Modules]
    (hregular : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧ IsRegularRing Γ(X, U))
    (d : ℕ) (hdim : X.dim = (d : WithBot ℕ∞)) (F G : X.Modules)
    (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (hG : RingedSpace.IsCoherent X.toRingedSpace G) (i : ℕ) (hi : d < i) :
    Subsingleton (Ext F G i) := by
  sorry

/-- On the projective line over any field, Ext between coherent modules vanishes in every
degree at least two. Source: Stacks Project, Tag 0FZ3 (1), applied to the projective line
(blueprint: lem-sc-p1-ext-coherent-dim-one-vanishing).

Proof: lem-sc-p1-regular-dimension-one gives regularity, Noetherianity and dimension one for
ProjectiveLine (Spec k), using its two standard affine charts (def-sc-p1-standard). Apply
coherent_ext_subsingleton_of_regular with d = 1, since i >= 2 implies i > 1. Its proof uses
lem-sc-ext-sheaf-to-global-spectral-sequence, lem-sc-ext-stalk-localization,
lem-sc-regular-local-ext-vanishing and lem-sc-ext-support-cohomology-vanishing as above. -/
theorem projectiveLine_coherent_ext_subsingleton (k : Type u) [Field k]
    [HasExt.{u} (ProjectiveLine (Spec (CommRingCat.of k))).Modules]
    (F G : (ProjectiveLine (Spec (CommRingCat.of k))).Modules)
    (hF : RingedSpace.IsCoherent (ProjectiveLine (Spec (CommRingCat.of k))).toRingedSpace F)
    (hG : RingedSpace.IsCoherent (ProjectiveLine (Spec (CommRingCat.of k))).toRingedSpace G)
    (i : ℕ) (hi : 2 ≤ i) : Subsingleton (Ext F G i) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
