/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.Paper.EtaleProEtaleScalarMate
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import Sheaf.Paper.PurEtaleScalarMateProjection
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Paper.RingedTopoiTensorComparisonData
import Sheaf.Paper.RingedTopoiTensorComparisonConstruction
import Sheaf.Paper.RingedTopoiDerivedPullback
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# The etale/pro-etale scalar and inverse-image cube

Source: Stacks Project, Cohomology on Sites, Tag 0D6D,
`lemma-derived-pullback-composition`, with Tags 06YS, 0G7E, 06YY and 07A4;
Modules on Sites, Tags 03EK and 03EL.
(blueprint: lem-sfb-etale-proetale-scalar-pullback-cube).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

/-- The canonical inverse-image square commutes with derived scalar extension.
Source: Stacks Project, Tag 0D6D, `lemma-derived-pullback-composition`.
(blueprint: lem-sfb-etale-proetale-scalar-pullback-cube).

Proof:
1. The ordinary inverse-image square of sk-thm-pe-direct-image-comparison is the
   lift of one geometric square to modules over each constant ring. Naturality
   for addition, scalar multiplication and constant sections identifies its ring
   components with the canonical constant-ring pullbacks, compatibly with a.
2. Apply that naturality to the universal balanced pairing B times N into
   B tensor_A N. Naturality for both product projections identifies the action on
   the product with the product of the two actions. Both ordinary cube paths
   therefore take b tensor m to b tensor theta(m). The balancing relation is
   preserved. The pure-tensor normalization of
   def-weil-pbc-canonical-ringed-tensor-comparison and
   lem-weil-pbc-canonical-ringed-tensor-comparison-construction, followed by module
   sheafification, proves equality on all generalized sections.
3. Resolve an arbitrary representative of M by a K-flat complex P with flat
   terms (lem-pc-kflat-resolution). Ringed pullback preserves this class
   (lem-weil-pbc-ringed-topoi-derived-tensor-pullback), including pullback along
   the identity geometric morphism with structural ring map a. Thus all iterated
   derived functors are computed by ordinary pullbacks of this same P, using
   lem-weil-pbc-ringed-topoi-derived-pullback and lem-pur-derived-change-of-rings.
4. The defining normalization of def-pur-etale-scalar-pullback-iso and the
   composition and specified-2-isomorphism normalization of
   lem-sfb-ringed-derived-monoidal-comparisons identify each scalar face with its
   ordinary face on P. The two d faces are the exact localization of the ordinary
   site square. Localizing the degreewise equality from step 2 proves the cube
   at Q(P). The coefficient is in degree zero, so no factors or signs are swapped.
5. Both paths are natural in M. Transport their equality along the resolution
   isomorphism Q(P) isomorphic to M to obtain the displayed equation. No
   finiteness of f, boundedness of M, or flatness of a is used. -/
theorem etaleProEtale_scalar_pullback_cube
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (scalarPullbackProEtaleIso a f).hom.app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj M) ≫
      (pbcFixedScalarExtension (Scheme.ProEt.topology X) a).map
        ((directImageComparisonAmbientPullbackIso A f).hom.app M) ≫
      (pbcComparisonReduction X a).hom.app
        (L(Etale.upperStar (ModuleCat.{u + 1} A) f).obj M) =
    L(upperStar (ModuleCat.{u + 1} B) f).map
        ((pbcComparisonReduction Y a).hom.app M) ≫
      (directImageComparisonAmbientPullbackIso B f).hom.app
        ((pbcFixedScalarExtension Y.smallEtaleTopology a).obj M) ≫
      (comparisonUpperStar (ModuleCat.{u + 1} B) X).mapDerivedCategory.map
        ((Etale.scalarPullbackIso a f).hom.app M) := by
  sorry

end AlgebraicGeometry.ProEtale
