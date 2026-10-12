module

public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

/-! # Equality of maps with finite free source near a stalk

Source: lem-pc-perfect-locus, finite germ calculation.
(blueprint: lem-pc-finite-free-stalk-map-eq-shrink)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- Equality after pullback to the local scheme spreads for maps with finite free source.

Source: blueprint sec-picard-framework/sk-thm-picard-perfect/lem-pc-perfect-locus,
finite germ calculation. (blueprint: lem-pc-finite-free-stalk-map-eq-shrink)

Proof: Use the given source isomorphism to obtain r generating sections over V.
The pullback equality implies equality of the germs of their images in N at y:
the stalk at the closed point of Spec O_{Y,y} of the pullback is canonically N_y.
For each generator the presheaf germ equality criterion gives an open neighbourhood
of y inside V on which its two images agree. Intersect these finitely many opens
with U. On that intersection the two maps agree on every generator, hence on the
whole restricted free source, and therefore on M. For r=0 there are no generators,
the source is zero, and W=U works. No finite generation of N is needed. -/
theorem exists_restrict_eq_of_pullback_eq
    {Y : Scheme.{u}} (r : ℕ) (y : Y) (V : Y.Opens) (hyV : y ∈ V)
    (M N : V.toScheme.Modules)
    (hM : Nonempty (M ≅ (restrictFunctor V.ι).obj
      (SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin r)))))
    (f g : M ⟶ N)
    (hfg : (Modules.pullback (V.fromSpecStalkOfMem y hyV)).map f =
      (Modules.pullback (V.fromSpecStalkOfMem y hyV)).map g)
    (U : Y.Opens) (hUV : U ≤ V) (hyU : y ∈ U) :
    ∃ (W : Y.Opens) (hWU : W ≤ U), y ∈ W ∧
      (restrictFunctor (Y.homOfLE (hWU.trans hUV))).map f =
      (restrictFunctor (Y.homOfLE (hWU.trans hUV))).map g := by
  sorry

end AlgebraicGeometry.Scheme.Modules
