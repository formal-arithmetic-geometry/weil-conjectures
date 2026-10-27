/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.EtaleDifferentialPullbackPresentation
public import Sheaf.AlgebraicGeometry.LogMorphismOperations

/-!
# Canonical maps in the logarithmic differential comparison

Source: Step 3 and the tensor-generator assertion of Step 8 of
lem-per-strict-log-differentials-pushout; Stacks 01UM, 03DR, 03DU, 03D3 and 00RM.
(blueprint: lem-per-log-differential-canonical-square).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The ordinary differential and tensor presentations exist, and the canonical
symbol maps form a commuting square. Maps out of the pulled-back log differentials
are determined by the pulled-back ordinary and logarithmic symbols.

Source: Step 3 and the tensor-generator part of Step 8 of the agent proof of
lem-per-strict-log-differentials-pushout; Stacks Tags 01UM, 03DR, 03DU, 03D3, 00RM.
(blueprint: lem-per-log-differential-canonical-square).

Proof: equip the tensor sections of the Zariski relative differential sheaf with
its natural module structure and universal derivation on the small etale site.
On an etale affine chart these are the ordinary Kahler differentials: etaleness
kills the additional relative differentials, and the affine universal derivations
commute with restriction. Their universal maps therefore glue, giving both
ordinary presentations, with precisely the specified tensor-sections comparison.
Construct A and C by sheafifying inverse image and extending scalars along c.
The tensor adjunction gives their units on every relative etale diagram and their
full universal properties. The ordinary derivation on Z gives u. The ordinary
symbol in the differential quotient of g gives v. The ordinary symbol in the
quotient of c.comp g gives j. Pulling both types of symbols along c respects each
of the six quotient relations (including both base relations), and hence gives
iota by sheafification and the tensor adjunction. These constructions give the
five displayed formulas. The maps u followed by j and v followed by iota agree
on 1 tensor da, so agree by the ordinary and tensor universal properties.
Finally, maps from C correspond to semilinear relative section maps from the
logarithmic differential sheaf of g. Equality on the two types of pulled-back
symbols gives equality on the free symbol presheaf, hence on its quotient and
sheafification, and then on C by the tensor adjunction. This proves the last
clause. No strictness or fineness is used in this construction. -/
theorem logDifferential_canonical_square {Z W S : Scheme.{u}}
    {L : EtaleLogStructure Z} {M : EtaleLogStructure W} {N : EtaleLogStructure S}
    (c : EtaleLogMap L M) (g : EtaleLogMap M N) :
    ∃ (ΩW : EtaleOrdinaryDifferentialPresentation g.base)
      (ΩZ : EtaleOrdinaryDifferentialPresentation (c.base ≫ g.base))
      (A : EtaleDifferentialPullbackPresentation c.base ΩW.module)
      (C : EtaleDifferentialPullbackPresentation c.base g.differentialSheaf)
      (u : A.module ⟶ ΩZ.module) (v : A.module ⟶ C.module)
      (j : ΩZ.module ⟶ (c.comp g).differentialSheaf)
      (iota : C.module ⟶ (c.comp g).differentialSheaf),
      (∀ (U : W.Etale) (V : Z.Etale) (k : V.left ⟶ U.left)
        (hk : k ≫ U.hom = V.hom ≫ c.base) (a : Γ(U.left, ⊤)),
        u.val.app (op V) (A.unit.app U V k hk (ΩW.derivation.d (X := op U) a)) =
          ΩZ.derivation.d (X := op V) (k.appTop a)) ∧
      (∀ (U : W.Etale) (V : Z.Etale) (k : V.left ⟶ U.left)
        (hk : k ≫ U.hom = V.hom ≫ c.base) (a : Γ(U.left, ⊤)),
        v.val.app (op V) (A.unit.app U V k hk (ΩW.derivation.d (X := op U) a)) =
          C.unit.app U V k hk (g.sheafD U a)) ∧
      (∀ (V : Z.Etale) (a : Γ(V.left, ⊤)),
        j.val.app (op V) (ΩZ.derivation.d (X := op V) a) = (c.comp g).sheafD V a) ∧
      (∀ (U : W.Etale) (V : Z.Etale) (k : V.left ⟶ U.left)
        (hk : k ≫ U.hom = V.hom ≫ c.base) (a : Γ(U.left, ⊤)),
        iota.val.app (op V) (C.unit.app U V k hk (g.sheafD U a)) =
          (c.comp g).sheafD V (k.appTop a)) ∧
      (∀ (U : W.Etale) (V : Z.Etale) (k : V.left ⟶ U.left)
        (hk : k ≫ U.hom = V.hom ≫ c.base) (m : M.monoidSheaf.obj.obj (op U)),
        iota.val.app (op V) (C.unit.app U V k hk (g.sheafDLog U m)) =
          (c.comp g).sheafDLog V (c.sectionMap U V k hk m)) ∧
      u ≫ j = v ≫ iota ∧
      (∀ (T : DifferentialEtaleModules Z) (a b : C.module ⟶ T),
        (∀ (U : W.Etale) (V : Z.Etale) (k : V.left ⟶ U.left)
          (hk : k ≫ U.hom = V.hom ≫ c.base) (x : Γ(U.left, ⊤)),
          a.val.app (op V) (C.unit.app U V k hk (g.sheafD U x)) =
            b.val.app (op V) (C.unit.app U V k hk (g.sheafD U x))) →
        (∀ (U : W.Etale) (V : Z.Etale) (k : V.left ⟶ U.left)
          (hk : k ≫ U.hom = V.hom ≫ c.base) (m : M.monoidSheaf.obj.obj (op U)),
          a.val.app (op V) (C.unit.app U V k hk (g.sheafDLog U m)) =
            b.val.app (op V) (C.unit.app U V k hk (g.sheafDLog U m))) → a = b) := by
  sorry

end AlgebraicGeometry
