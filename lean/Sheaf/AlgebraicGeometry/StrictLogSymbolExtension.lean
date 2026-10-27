/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.EtaleDifferentialPullbackPresentation
public import Sheaf.AlgebraicGeometry.LogMorphismOperations
public import Sheaf.AlgebraicGeometry.LogInfinitesimalLifting

/-!
# Extension of differential symbols through strict logification

Source: Steps 1--2 and 4--7 of
lem-per-strict-log-differentials-pushout; ILO VI 1.1, X 1.2 and XVI 3.6.3; Stacks 00YR and 00WK.
(blueprint: lem-per-strict-log-symbol-extension).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Compatible ordinary and pulled-back logarithmic symbols extend uniquely
through a strict associated log structure. The unit formula holds for this map.

Source: Steps 1--2 and 4--7 of the agent proof of
lem-per-strict-log-differentials-pushout; ILO VI 1.1, printed p.69, and Stacks
Tags 00YR and 00WK. This is the symbol descent argument, before construction
of the comparison isomorphism or verification of either inverse composite.
(blueprint: lem-per-strict-log-symbol-extension).

Proof: write H for the inverse-image monoid sheaf and beta for its structural
map into O_Z. Strictness identifies L with the sheafification of the monoid
quotient of H times O_Z-units by (he,t)=(h,beta(e)t) for beta(e) invertible.
The geometric-stalk strictness predicate gives exactly this canonical quotient;
sheafification and inverse image commute with stalks, and geometric stalks detect
the resulting isomorphism. Thus it also gives the associated-log identification
on sheaves, with the prescribed relative section maps.
Put D(a)=p(da) and ell(m)=q(1 tensor dlog m). Agreement on A and the two
normalizations give D(beta(m))=beta(m) ell(m). D is an additive relative
derivation, ell is additive under multiplication, and both kill the appropriate
base symbols. For an invertible function t put lambda(t)=t^-1 D(t). The Leibniz
rule makes lambda a homomorphism to the additive group of T. If beta(e) is a
unit, the structural identity gives ell(e)=lambda(beta(e)). Consequently
ell(h)+lambda(t) respects each generating congruence relation (he,t)=(h,beta(e)t).
It descends to the quotient and uniquely extends to its monoid sheafification.
Denote the resulting map from L by ell_L. For l represented by c-flat(h)t,
Leibniz gives D(alpha(l))=alpha(l) ell_L(l). This identity holds locally and
hence globally, independently of all representative choices. The extension is
additive and kills base log sections, so D and ell_L kill all six relations of
the differential symbol quotient. Their map from the free module therefore
factors through the quotient and its module sheafification, giving psi. These
constructions prove its ordinary, pulled-back log and unit formulas. Any other
map with the first two formulas agrees on local log representatives: the unit
formula is forced by the structural relation and invertibility of t. It agrees
on all ordinary and log symbols and hence on their quotient and sheafification.
This proves uniqueness without requiring a unit formula as an extra hypothesis. -/
theorem strictLog_symbol_extension {Z W S : Scheme.{u}}
    {L : EtaleLogStructure Z} {M : EtaleLogStructure W} {N : EtaleLogStructure S}
    (c : EtaleLogMap L M) (g : EtaleLogMap M N)
    (hL : L.IsFine) (hM : M.IsFine) (hN : N.IsFine) (hc : c.IsStrict)
    (ΩW : EtaleOrdinaryDifferentialPresentation g.base)
    (ΩZ : EtaleOrdinaryDifferentialPresentation (c.base ≫ g.base))
    (A : EtaleDifferentialPullbackPresentation c.base ΩW.module)
    (C : EtaleDifferentialPullbackPresentation c.base g.differentialSheaf)
    (u : A.module ⟶ ΩZ.module) (v : A.module ⟶ C.module)
    (hu : ∀ (U : W.Etale) (V : Z.Etale) (k : V.left ⟶ U.left)
      (hk : k ≫ U.hom = V.hom ≫ c.base) (a : Γ(U.left, ⊤)),
      u.val.app (op V) (A.unit.app U V k hk (ΩW.derivation.d (X := op U) a)) =
        ΩZ.derivation.d (X := op V) (k.appTop a))
    (hv : ∀ (U : W.Etale) (V : Z.Etale) (k : V.left ⟶ U.left)
      (hk : k ≫ U.hom = V.hom ≫ c.base) (a : Γ(U.left, ⊤)),
      v.val.app (op V) (A.unit.app U V k hk (ΩW.derivation.d (X := op U) a)) =
        C.unit.app U V k hk (g.sheafD U a))
    (T : DifferentialEtaleModules Z) (p : ΩZ.module ⟶ T) (q : C.module ⟶ T)
    (hpq : u ≫ p = v ≫ q) :
    ∃ ψ : (c.comp g).differentialSheaf ⟶ T,
      (∀ (V : Z.Etale) (a : Γ(V.left, ⊤)),
        ψ.val.app (op V) ((c.comp g).sheafD V a) =
          p.val.app (op V) (ΩZ.derivation.d (X := op V) a)) ∧
      (∀ (U : W.Etale) (V : Z.Etale) (k : V.left ⟶ U.left)
        (hk : k ≫ U.hom = V.hom ≫ c.base) (m : M.monoidSheaf.obj.obj (op U)),
        ψ.val.app (op V) ((c.comp g).sheafDLog V (c.sectionMap U V k hk m)) =
          q.val.app (op V) (C.unit.app U V k hk (g.sheafDLog U m))) ∧
      (∀ (V : Z.Etale) (t : Γ(V.left, ⊤)ˣ)
        (l : L.monoidSheaf.obj.obj (op V)), L.alpha.app (op V) l = t.val →
        ψ.val.app (op V) ((c.comp g).sheafDLog V l) =
          p.val.app (op V)
            ((↑(t⁻¹) : Γ(V.left, ⊤)) • ΩZ.derivation.d (X := op V) t.val)) ∧
      (∀ ψ' : (c.comp g).differentialSheaf ⟶ T,
        (∀ (V : Z.Etale) (a : Γ(V.left, ⊤)),
          ψ'.val.app (op V) ((c.comp g).sheafD V a) =
            p.val.app (op V) (ΩZ.derivation.d (X := op V) a)) →
        (∀ (U : W.Etale) (V : Z.Etale) (k : V.left ⟶ U.left)
          (hk : k ≫ U.hom = V.hom ≫ c.base) (m : M.monoidSheaf.obj.obj (op U)),
          ψ'.val.app (op V) ((c.comp g).sheafDLog V (c.sectionMap U V k hk m)) =
            q.val.app (op V) (C.unit.app U V k hk (g.sheafDLog U m))) → ψ' = ψ) := by
  sorry

end AlgebraicGeometry
