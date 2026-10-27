/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.Picard.Group
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
import Sheaf.AlgebraicGeometry.StandardGroupSchemes

/-!
# Picard field invariance for connected affine groups

Source: M. Brion, On Linearization of Line Bundles (2015), Lemma 2.3 and
Remark 2.2(v), printed pp.117--118
(blueprint: lem-sfb-affine-group-picard-field-invariance).

The existing scheme Picard group uses multiplicative notation for tensor product.
Bijectivity of its canonical pullback homomorphism states that this pullback is an
isomorphism of abelian groups.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Pullback on Picard groups of a smooth connected affine group over an algebraically
closed field is an isomorphism after any field extension. Source: Brion, Lemma 2.3 and
Remark 2.2(v), printed pp.117--118
(blueprint: lem-sfb-affine-group-picard-field-invariance).

Proof plan:
1. By `lem-sfb-split-reductive-affine-space-quotient`, write G as H times affine space over
   a split reductive quotient H. This decomposition persists under arbitrary field extension.
2. By `lem-sfb-smooth-affine-space-picard-invariance`, both quotient pullbacks on Picard
   groups are isomorphisms. Functoriality of pullback (`def-pc-module-pullback`) identifies
   the desired map with scalar extension for H, conjugated by those isomorphisms.
3. Use `lem-sfb-split-reductive-characteristic-sequence` for a split Borel pair T inside B
   inside H: character group of T to Pic(H/B) to Pic(H) to zero is exact, naturally under
   scalar extension.
4. The Laurent Hopf coordinates of `def-sc-gm-ga` identify characters of a split torus
   with its integer exponent lattice over either field: a group-like Laurent polynomial
   has exactly one nonzero coefficient, equal to one. Character pullback is bijective.
5. The split Borel is split solvable. By `lem-sfb-split-flag-schubert-picard-lattice`,
   the Schubert boundary bases of the two flag Picard groups correspond under pullback.
   Thus this vertical map is also bijective, including the empty-basis case.
6. Chase the two exact rows. Lift a target Pic(H_K) class to the flag Picard group, then
   lift using its vertical bijection, proving surjectivity. If a source class maps to zero,
   lift it to the flag group; exactness expresses its image as a characteristic class.
   Lift that character, use commutativity and injectivity on the flag group, and conclude
   the original class is zero. Conjugate back using step 2. The trivial group is included.
-/
theorem affineGroup_picard_field_invariance
    (k : Type u) [Field k] [IsAlgClosed k]
    (G : Over (Spec (CommRingCat.of k))) [GrpObj G]
    [Smooth G.hom] [ConnectedSpace G.left] [IsAffine G.left]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    (K : Type u) [Field K] [Algebra k K] :
    Function.Bijective
      (Scheme.Pic.mapHom
        (pullback.fst G.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))))) := by
  sorry

end AlgebraicGeometry
