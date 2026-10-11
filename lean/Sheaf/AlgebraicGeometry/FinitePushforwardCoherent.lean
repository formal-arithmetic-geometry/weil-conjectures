/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.AlgebraicGeometry.Coherent

/-! # Coherence of finite direct images

Source: Stacks Project, Cohomology of Schemes, Tags 01Y6 and 01XZ
(blueprint: lem-weil-pbc-finite-pushforward-coherent).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- A finite direct image of a coherent module is coherent, with finite sections on every
 affine open. Source: Stacks Project, Tags 01Y6 and 01XZ
(blueprint: lem-weil-pbc-finite-pushforward-coherent).

Proof:
1. On an affine open U = Spec R, finiteness gives f⁻¹U = Spec B with B finite over R
   (def-weil-finite-integral-morphism).
2. Coherence implies finite type and finite presentation: choose local finite generators;
   coherence makes the kernel finite type, hence gives a finite presentation. Thus F is
   quasi-coherent (pqf-def-coherent; lem-weil-pbc-quasi-coherent-finite-type-affine, part 0).
3. The affine criterion makes F(f⁻¹U) finite over B
   (lem-weil-pbc-quasi-coherent-finite-type-affine, part a;
   def-weil-finitely-generated-module).
4. Direct image has these same sections with scalars restricted along f.app U. A finite
   B-module is finite over R (def-pc-module-pullback;
   lem-weil-pbc-finite-module-over-finite-algebra).
5. Affine direct image preserves quasi-coherence
   (lem-weil-pbc-affine-pushforward-base-change, part 1).
6. The finite modules on an affine covering imply finite type
   (def-pc-scheme; lem-weil-pbc-quasi-coherent-finite-type-affine, part c).
7. On the locally Noetherian target, quasi-coherent finite type implies coherent
   (pqf-lem-coherent-ft-locnoeth), proving both conclusions.
8. The structure-sheaf example follows from the companion statement below: Y is locally
   Noetherian and its structure sheaf is coherent. -/
theorem isCoherent_pushforward_of_isFinite {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsFinite f] [IsLocallyNoetherian X] (F : Y.Modules)
    (hF : RingedSpace.IsCoherent Y.toRingedSpace F) :
    RingedSpace.IsCoherent X.toRingedSpace ((pushforward f).obj F) ∧
      ∀ (U : X.Opens), IsAffineOpen U →
        Γ((pushforward f).obj F, U) = Γ(F, f ⁻¹ᵁ U) ∧
          Module.Finite Γ(X, U) Γ((pushforward f).obj F, U) := by
  sorry

/-- The structure sheaf in the finite-direct-image statement satisfies its coherence
hypothesis. Source: Stacks Project, Tags 01Y6, 01XZ and 01T6
(blueprint: lem-weil-pbc-finite-pushforward-coherent).

Proof (step 8 of the node): choose an affine Noetherian covering of X
(pqf-def-locnoeth). Its inverse images are affine with finite coordinate algebras
(def-weil-finite-integral-morphism). Finite algebras over Noetherian rings are Noetherian
(lem-weil-pbc-finite-algebra-noetherian), so Y is locally Noetherian. The identity map from
one copy of O_Y gives finite type and the presentation with zero relations gives finite
presentation, hence quasi-coherence (pqf-def-coherent;
lem-weil-pbc-quasi-coherent-finite-type-affine, part 0). Apply
pqf-lem-coherent-ft-locnoeth on Y to obtain coherence. The preceding theorem now applies
with F = O_Y. -/
theorem isCoherent_unit_of_finite_to_locallyNoetherian {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsFinite f] [IsLocallyNoetherian X] :
    RingedSpace.IsCoherent Y.toRingedSpace (SheafOfModules.unit Y.ringCatSheaf) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
