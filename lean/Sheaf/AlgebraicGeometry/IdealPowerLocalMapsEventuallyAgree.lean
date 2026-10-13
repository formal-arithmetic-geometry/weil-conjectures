/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.AlgebraicGeometry.IdealModuleProductStalk

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
/-! # Eventual agreement of local ideal-power maps

Source: Stacks Project, Properties, Lemmas 01PM and 01PQ, injectivity arguments.
(blueprint: lem-weil-pbc-ideal-power-local-maps-eventually-agree).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Two local maps with equal evaluation agree on a sufficiently high ideal power
on their quasi-compact overlap. No lifting or quotient construction is asserted.

Source: Stacks Project, Properties, Lemma 01PM (injectivity) and Lemma 01PQ
(finite covering argument).
(blueprint: lem-weil-pbc-ideal-power-local-maps-eventually-agree).

Proof: Restrict both maps to V intersect V' and subtract them. Cover this
quasi-compact open by finitely many affine opens. On each, write I as a finitely
generated ideal J=(f_1,...,f_t) and F=M~. The difference is a linear map
J^n -> M by the affine tilde/Gamma equivalence. On D(f_i), heval says that its
value on f_i^n divided by f_i^n is zero, since one n is the unique preimage
of the unit under the monic power inclusion. Localization therefore gives
f_i^k_i phi(f_i^n)=0. Choose one k for all i, with n+k positive. Linearity
shows phi(f_i^(n+k))=0. Every monomial of degree t*(n+k-1)+1 contains one
such factor, so phi kills that power. Enlarge the degree to at least n.
If J=0, use any positive degree at least n. Take the maximum of the degrees
on the finite cover (and n). The equations hr and monicity of the power
inclusions identify all r with the genuine inclusions and give their
composition law; restriction to the maximum preserves vanishing. Sheaf
separation now makes the two restricted maps equal on the whole overlap,
hence on every W contained in it. An empty overlap needs no affine opens
and the same separation argument works at degree n. -/
theorem ideal_power_local_maps_eventually_agree
    {X : Scheme.{u}} {I : X.Modules}
    (ι : I ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono ι]
    [I.IsQuasicoherent] [I.IsFiniteType]
    (F : X.Modules) [F.IsQuasicoherent]
    (U : X.Opens) (one : ∀ n : ℕ, Γ((idealSheafPower ι n).1, U))
    (r : ∀ (n m : ℕ), n ≤ m →
      ((idealSheafPower ι m).1 ⟶ (idealSheafPower ι n).1))
    (hU : ∀ x : X, x ∈ U ↔ Function.Surjective
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map ι).hom)
    (hone : ∀ n : ℕ, (idealSheafPower ι n).2.app U (one n) = (1 : Γ(X, U)))
    (hr : ∀ (n m : ℕ) (h : n ≤ m),
      r n m h ≫ (idealSheafPower ι n).2 = (idealSheafPower ι m).2)
    (V V' : X.Opens) (hcompact : IsCompact ((V : Set X) ∩ (V' : Set X)))
    (n : ℕ)
    (α : ((idealSheafPower ι n).1).over V ⟶ F.over V)
    (β : ((idealSheafPower ι n).1).over V' ⟶ F.over V')
    (heval : ∀ (W : X.Opens) (hWU : W ≤ U) (hWV : W ≤ V) (hWV' : W ≤ V'),
      α.val.app (op (Over.mk (homOfLE hWV)))
          (((idealSheafPower ι n).1).presheaf.map (homOfLE hWU).op (one n)) =
        β.val.app (op (Over.mk (homOfLE hWV')))
          (((idealSheafPower ι n).1).presheaf.map (homOfLE hWU).op (one n))) :
    ∃ (m : ℕ) (h : n ≤ m),
      ∀ (W : X.Opens) (hWV : W ≤ V) (hWV' : W ≤ V'),
        (r n m h).val.app (op W) ≫ α.val.app (op (Over.mk (homOfLE hWV))) =
          (r n m h).val.app (op W) ≫ β.val.app (op (Over.mk (homOfLE hWV'))) := by sorry

end AlgebraicGeometry.Scheme
