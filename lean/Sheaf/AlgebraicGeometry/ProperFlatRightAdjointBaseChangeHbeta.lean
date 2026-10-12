module
public import Sheaf.AlgebraicGeometry.DerivedCategory
public import Sheaf.AlgebraicGeometry.SchemeDerivedBaseChangeMap
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Sheaf.AlgebraicGeometry.RelativelyFlatDerivedBaseChangeComplex
@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
/-- Flat proper finite-presentation morphisms satisfy derived base change after arbitrary pullback.
Source: Stacks Project, Derived Categories of Schemes, Tag 0A1D (Lemma 36.26.4).
(blueprint: lem-sc-proper-flat-right-adjoint-basechange-hbeta)
Proof: Properness implies that f is quasi-compact and quasi-separated.
Apply relatively flat complex base change (Tag 0A1D) with G = O_X[0].
This complex is bounded above and quasi-coherent; flatness of f makes its only
nonzero term flat over Y. For each E, choose a K-flat representative and use
the tensor unit isomorphism to identify E ⊗^L O_X[0] with E.
Pullback of the structure sheaf is the structure sheaf, and O_X is intrinsically
flat, so the derived-to-ordinary pullback comparison for G is an isomorphism.
The theorem therefore says that the canonical map β_E, composed with the
unit identifications and this invertible comparison, is invertible.
Cancel these isomorphisms to obtain IsIso β_E. This holds for arbitrary,
including unbounded, quasi-coherent E. No right adjoint is used.
Equivalently, flatness gives Tor independence and Stacks Tag 08IB applies.
-/
theorem proper_flat_rightAdjoint_baseChange_hβ
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X Y Y' : Scheme.{u}}
    [CompactSpace Y] [QuasiSeparatedSpace Y] [CompactSpace Y'] [QuasiSeparatedSpace Y']
    (g : Y' ⟶ Y) (f : X ⟶ Y) [IsProper f] [Flat f] [LocallyOfFinitePresentation f] :
    ∀ E : schemeDerivedQCohCategory X,
        IsIso (schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
          pullback.condition E.obj) := by sorry
end AlgebraicGeometry
