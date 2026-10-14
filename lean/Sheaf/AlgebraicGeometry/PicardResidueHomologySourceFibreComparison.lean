module

public import Sheaf.AlgebraicGeometry.DerivedFiberBetti
public import Sheaf.AlgebraicGeometry.TensorPullback
public import Sheaf.AlgebraicGeometry.StructureSheafCohomologyPullback
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Fiber
import Sheaf.AlgebraicGeometry.Picard.FlatInvertibleCanonicalDerivedBaseChange
import Sheaf.AlgebraicGeometry.Picard.CanonicalSinglePullbackComparison
import Sheaf.AlgebraicGeometry.TensorPullbackStructureSheaf
import Sheaf.AlgebraicGeometry.TensorPullbackCompositionIso
import Sheaf.AlgebraicGeometry.SchemeModulesEnoughInjectives
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility

/-! # Derived fibre of a line-bundle direct image

Source: Stacks Project, Tags 0A1D, 0B91, 0BF2 and 01XK.
(blueprint: new-picard-residue-homology-comparison-source-fibre)
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The derived fibre of the pulled-back invertible coefficient computes
structure-sheaf cohomology using the supplied fibre trivialization.
Source: Stacks Project, Tags 0A1D, 0B91, 0BF2 and 01XK.
(blueprint: new-picard-residue-homology-comparison-source-fibre)

Proof: Put fW = pullback.snd f k and G = pullback.fst f k applied to L.
Tensor pullback agrees with ordinary module pullback by uniqueness of left
adjoints; hence G is invertible. The morphism fW is proper, flat and locally
of finite presentation, by stability under base change. In particular it
is quasi-compact and separated. Set g = W.fromSpecResidueField w and form
its cartesian square with fW, with projections a and q. Apply
Modules.isIso_derivedBaseChange_of_flat_invertible to this square and G.
Modules.isIso_canonicalSinglePullbackMap identifies derived pullback of
G[0] with ordinary pullback of G in degree zero, since G is invertible.
Thus Li_w^* RfW_*G is Rq_* of (a^*G)[0]. This is the arbitrary base-change
comparison of Tag 0A1D; Tag 0B91 also supplies it in the proper case.
The residue map of the immersion k is an isomorphism. Compose it with the
residue congruence from hw, obtaining a field isomorphism from kappa(s) to
kappa(w). Naturality of residue points identifies g followed by k with the
residue point of s preceded by the spectrum of this field isomorphism.
The unique projection-preserving pullback isomorphisms identify the fibre
of fW over w with X_s after that spectrum isomorphism. Pullback composition
therefore identifies a^*G with the pullback of L_s. Pull back the supplied
trivialization tau and use the structure-unit pullback isomorphism to
identify this coefficient with the structure sheaf of that fibre.
Apply degree-one homology and sections on Spec kappa(w). The unbounded
right-derived functor comparison on a single module identifies this
homology with R^1 q_*O. Scheme module sheaves have injective resolutions.
Apply Modules.exists_addEquiv_sections_higherDirectImage_H (Tag 01XK)
to q and its quasi-coherent structure module. This gives Sheaf.H of the
underlying additive structure sheaf, since Modules.H is defined using
that abelian sheaf cohomology. The unit module's underlying sheaf is
the structure sheaf with only its additive group structure retained.
Finally transport
along the fibre scheme isomorphism just constructed to X_s and forget
scalars. This yields precisely the displayed additive equivalence; no
choice of an affine representative K, or of frames of K, is involved.
For an empty fibre both cohomology groups are zero, and the comparison
also handles nonreduced bases and nonclosed points. -/
theorem picard_residue_homology_source_fibre_comparison
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    {X S : Scheme.{v}} (f : X ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (L : X.Modules) [L.IsInvertible]
    (W : Scheme.{v}) (k : W ⟶ S) [IsImmersion k]
    (w : W) (s : S) (hw : k w = s)
    (τ : (Modules.tensorPullback (pullback.fst f (S.fromSpecResidueField s))).obj L ≅
      SheafOfModules.unit (pullback f (S.fromSpecResidueField s)).ringCatSheaf)
    :
    let E := (schemeDerivedDirectImage (pullback.snd f k)).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst f k)).obj L))
    Nonempty (derivedFiberCohomology W E 1 w ≃+
      Sheaf.H (structureSheafAb (pullback f (S.fromSpecResidueField s))) 1) := by sorry

end AlgebraicGeometry.Scheme
