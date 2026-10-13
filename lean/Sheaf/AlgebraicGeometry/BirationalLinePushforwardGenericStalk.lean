/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q2
-/
module

public import Sheaf.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # The generic stalk of a birational line pushforward

Source: Stacks Project, Tag 02O5, proposition-proper-pushforward-coherent,
verification of property (a).
(blueprint: lem-pc-q2-birational-line-pushforward-generic-stalk)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- A line pushed forward through a morphism that is an isomorphism on a dense
open of an integral scheme has the residue-field stalk after closed pushforward.
The equivalence respects the original stalk action through the residue map.

Source: Stacks Project, Tag 02O5, proposition-proper-pushforward-coherent,
property (a) and the closed-immersion stalk comparison preceding Chow's lemma.
(blueprint: lem-pc-q2-birational-line-pushforward-generic-stalk)

Proof:
1. The generic point eta of integral W belongs to the dense open U. Restriction
   of pushforward to U is pushforward from pi^{-1}(U). As pi restricted to U is
   an isomorphism, this restricted module is invertible. A local trivialization
   gives its eta stalk an O_{W,eta}-linear equivalence with O_{W,eta}.
2. O_{W,eta} is a field. The residue quotient identifies it with kappa(eta).
   The stalk of i_* at i(eta) is that of the original module at eta, and its
   scalar action is induced by i.stalkMap eta (closed-pushforward stalks).
3. A closed immersion induces an isomorphism of residue fields at corresponding
   points. Compose the additive equivalences with this residue-field isomorphism.
   Naturality of the residue maps gives e(a v) = residue(a) e(v).
   This construction works for every invertible L, with no cohomological,
   projective, properness, or Noetherian hypothesis. -/
theorem birational_line_pushforward_generic_stalk {X W Y : Scheme.{u}}
    (i : W ⟶ X) [IsClosedImmersion i] [IsIntegral W]
    (π : Y ⟶ W) (U : W.Opens) (hU : Dense (U : Set W))
    [IsIso (π ∣_ U)] (L : Y.Modules) [L.IsInvertible] :
    ∃ e : ((RingedSpace.moduleStalkFunctor X.toRingedSpace
        (i.base (genericPoint W))).obj ((pushforward i).obj ((pushforward π).obj L))) ≃+
        X.residueField (i.base (genericPoint W)),
      ∀ (a : X.presheaf.stalk (i.base (genericPoint W)))
        (v : (RingedSpace.moduleStalkFunctor X.toRingedSpace
          (i.base (genericPoint W))).obj ((pushforward i).obj ((pushforward π).obj L))),
        e (a • v) = (X.residue (i.base (genericPoint W))) a * e v := by sorry

end AlgebraicGeometry.Scheme.Modules
