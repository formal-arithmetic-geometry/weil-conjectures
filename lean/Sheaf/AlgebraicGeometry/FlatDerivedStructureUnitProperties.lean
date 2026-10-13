module

public import Sheaf.AlgebraicGeometry.Picard.CanonicalSingleDirectImageComparison
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Sheaf.AlgebraicGeometry.RelativelyFlatCanonicalModuleBaseChange
import Sheaf.AlgebraicGeometry.TensorPullbackStructureSheaf
import Sheaf.AlgebraicGeometry.DerivedBaseChangeUnitCompatibility
import Sheaf.AlgebraicGeometry.Picard.CanonicalSingleAdjunctionTranspose
import Sheaf.AlgebraicGeometry.Picard.CanonicalDirectImageH0Unit

/-! # Derived fibres of the canonical structure map

Source: Stacks Project, Tags 0E62 (first paragraph), 0A1D, and 0096.
(blueprint: flat-derived-structure-unit-properties).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The explicit structure map, obtained by applying the single functor to the
ordinary structure map and composing with the canonical right-derived unit,
has nonnegative derived fibres and induces an isomorphism in degree zero when
the canonical map on fibre global functions is invertible.
Source: Stacks Project, Tag 0E62 (first paragraph), Tag 0A1D, and Tag 0096.
(blueprint: flat-derived-structure-unit-properties).

Proof: For a point s, use the cartesian residue-field square with projections
p : X_s → X and f_s : X_s → Spec κ(s). Flatness of f says the stalks of O_X
are flat over the corresponding base stalks, so O_X is relatively flat over S.
Apply exists_isIso_canonicalModuleBaseChange_of_isFlatOver to O_X. Its target
is R(f_s)_*((p^*O_X)[0]); tensorPullbackObjUnitToUnit identifies p^*O_X with
O_{X_s}. This gives an isomorphism b : Li_s^*Rf_*O_X[0] ≅ R(f_s)_*O_{X_s}[0].
An injective resolution of O_{X_s} in nonnegative degrees computes the latter
object, so its negative cohomology vanishes, and b transports this vanishing.
For the map assertion, O_S[0] is K-flat; hence the left-derived counit and the
adjoint structure-sheaf map give j : Li_s^*O_S[0] ≅ O_{Spec κ(s)}[0]. The mate
identity for canonical base change, evaluated on the single ordinary structure
map, says that Li_s^*(a) followed by b equals j followed by a_s, where a_s is
the single fibre structure map followed by its canonical right-derived unit.
This follows by transposing both composites under the derived adjunction for
f_s: the ordinary structure map transposes to p^*O_X → O_{X_s}, and the two
counit/adjunction-unit pairs cancel by the triangle identities. The chosen
left-derived counit is the same in the comparison and in the mate, so no
arbitrary map a can replace this explicit canonical composite.
Taking H0 and using canonicalDirectImageH0Unit identifies H0(a_s) with the
ordinary module structure map O_{Spec κ(s)} → (f_s)_*O_{X_s}. On Spec of a
field there are only the empty and the whole open set. At the empty open every
module sheaf is zero; on the whole open the underlying map is exactly appTop
of f_s, with the canonical Γ(Spec κ(s), O) identification. Thus the assumed
IsIso on appTop makes this module map an isomorphism. Cancel H0(j) and H0(b)
to obtain the claimed IsIso. Empty fibres satisfy the negative assertion; their
map κ(s) → 0 cannot satisfy the last hypothesis, so that implication is vacuous. -/
theorem flat_derived_structure_unit_properties
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [IsSeparated f] [Flat f] :
    (∀ (s : S) (i : ℤ), i < 0 → IsZero ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (Spec (S.residueField s)).toRingedSpace)) i).obj
        ((derivedPullback (S.fromSpecResidueField s)).obj
          ((schemeDerivedDirectImage f).obj ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj
              (SheafOfModules.unit X.ringCatSheaf)))))) ∧
    (∀ s : S, IsIso (f.fiberToSpecResidueField s).appTop →
      IsIso ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings (Spec (S.residueField s)).toRingedSpace)) 0).map
          ((derivedPullback (S.fromSpecResidueField s)).map
            ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).map
                (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫
              Scheme.Modules.canonicalSingleDirectImageMap f
                (SheafOfModules.unit X.ringCatSheaf))))) := by sorry

end AlgebraicGeometry
