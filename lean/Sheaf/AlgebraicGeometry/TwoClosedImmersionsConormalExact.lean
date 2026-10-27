module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import WeilConjectures.AlgebraicGeometry.ClosedImmersionConormalFunctorial
import Mathlib.RingTheory.Kaehler.Basic
import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
import WeilConjectures.AlgebraicGeometry.ClosedImmersionIdealStalkRange
import WeilConjectures.AlgebraicGeometry.Modules.TensorPullbackStalk
import WeilConjectures.Algebra.Homology.ModuleStalkExact

/-! # The right-exact conormal sequence for two closed immersions

Source: Stacks Project, Morphisms, Tag 067L (lemma-two-immersions), with the arrows
of Tags 01R4 and 01UZ (blueprint: lem-sfb-two-closed-immersions-conormal-exact).

The first arrow is the recorded functorial conormal map, transported through the
canonical identity-pullback isomorphism. The second arrow is normalized on the actual
sections `1 ⊗ a` of tensor pullback. Right exactness is sheaf exactness and an epimorphism.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- The two-immersions sequence with its canonical arrows, without finiteness assumptions.
Source: Stacks Project, Morphisms, Tags 067L, 01R4 and 01UZ
(blueprint: lem-sfb-two-closed-immersions-conormal-exact).

Proof (the five steps of the node):
1. Apply the relative universal derivation to ideal sections, then the pullback unit.
   Leibniz makes the resulting map into `i_* i^* Ω` linear because the ideal vanishes
   on `Z`. The pullback adjunction (lem-pc-module-pullback-adjunction) gives `v`, with
   the displayed formula, compatibly with restriction. Products of ideal sections die.
2. Use lem-weil-pbc-closed-immersion-conormal-functorial with top map `1_Z` to obtain
   `u`. Its equation-class formula sends `a` to `f^# a`, whose relative differential
   vanishes. These classes locally generate, giving `u ≫ v = 0`.
3. At `z`, put `A = O_{Y,jz}`, `B = O_{X,iz}` and `C = O_{Z,z}`. Closed immersions give
   surjections `A → C` and `B → C`, with the first factoring through the second.
   Lemmas lem-weil-pbc-closed-immersion-ideal-stalk-range and
   lem-weil-pbc-module-stalk-exact identify the ideal stalks with their kernel ideals
   `I` and `J`. Lemma lem-weil-pbc-module-stalk-pullback identifies conormal stalks
   with `C ⊗ I` and `C ⊗ J`, hence with `I/I²` and `J/J²`: multiplication and
   `a mod I² ↦ 1 ⊗ a` give inverse maps, and similarly for `J`.
4. Lemma lem-sfb-relative-differentials-stalk identifies the differential stalk with
   `Ω_{B/A}`. The pullback-stalk formula identifies the third stalk with `C ⊗_B Ω_{B/A}`.
   The section formulas identify the stalk arrows with `a mod I² ↦ f^#a mod J²` and
   `b mod J² ↦ 1 ⊗ db`.
5. Apply lem-sfb-ring-two-quotients-conormal-exact to `A → B → C`. It gives stalkwise
   exactness and surjectivity of `v`. Lemma lem-weil-pbc-module-stalk-exact detects
   sheaf exactness and, by applying it also to the sequence ending in zero, the
   epimorphism assertion. Empty `Z` is included: all these sheaves are zero. -/
theorem twoClosedImmersions_conormal_exact
    {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (i : Z ⟶ X) (j : Z ⟶ Y) [IsClosedImmersion i] [IsClosedImmersion j]
    (h : i ≫ f = j) :
    ∃ (u : (tensorPullback j).obj j.ker.toModules ⟶
        (tensorPullback i).obj i.ker.toModules)
      (v : (tensorPullback i).obj i.ker.toModules ⟶
        (tensorPullback i).obj f.relativeDifferentials),
      u = (tensorPullbackSectionId Z).inv.app ((tensorPullback j).obj j.ker.toModules) ≫
        Classical.choose ((Classical.choose_spec
          (closedImmersion_conormal_functorial i j f (𝟙 Z)
            (h.trans (Category.id_comp j).symm)).2).2) ∧
      (∀ (U : X.Opens) (a : Γ(i.ker.toModules, U)),
        v.app (i ⁻¹ᵁ U) (tensorPullbackSection i i.ker.toModules U a) =
          tensorPullbackSection i f.relativeDifferentials U
            (f.relativeDifferentialsDerivation.d (X := op U) (i.ker.toModulesι.app U a))) ∧
      Epi v ∧ ∃ w : u ≫ v = 0, (ShortComplex.mk u v w).Exact := by
  sorry

end AlgebraicGeometry.Scheme.Modules
