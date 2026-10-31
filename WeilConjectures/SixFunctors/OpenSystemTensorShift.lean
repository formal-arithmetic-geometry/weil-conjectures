/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OpenTensorNormalization
public import WeilConjectures.AlgebraicGeometry.SemilinearDerivedSections
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.RingedSliceTensorGenerators
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.AlgebraicGeometry.RingedTopoiCanonicalTensorPullbackOfUniverses

/-! # Signed shifts of open tensor projection for strict coefficient systems

Source: Stacks Project, sites-cohomology.tex, Tag 0GL1, lemma-j-shriek-and-tensor;
more-algebra.tex, Tag 0FNH, item-shift-tensor; the strict-system refinement of
Unit Step 2 of sk-thm-purity-transport (blueprint: lem-pur-open-system-tensor-shift).

The published ordinary and vertical-diagram sites and normalized tensor models
are used verbatim. All derived categories are ordinary unbounded localizations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory AlgebraicGeometry.Scheme.ProjectionRestriction

namespace SheafOfModules.OpenTensorNormalization

/-- The open-unit-normalized tensor projection comparison commutes with the
signed second-slot shift, for arbitrary strict coefficient systems and for a
single ring sheaf. In mode `systems`, every arrow is a morphism on the vertical
ringed diagram site, so the equality includes the actual semilinear transitions.
The two `TensorShifts` structures are normalized on every flat-term K-flat pair
by `tensorShiftSecond`, using `CochainComplex.mapBifunctorShift₂Iso`; its summand
coefficient is `(a * r).negOnePow = (-1)^(r*a)`. Existence is part of the conclusion,
and the square holds for every such normalized choice. The composite after
`gamma` is the shift comparison of H; the first arrow on the right is that of F.
Naturality in both inputs is that of `gamma` and these functor shift comparisons.
No coefficient-transition flatness, Tor amplitude, or degree bound is imposed.

Source: Stacks Project, Tag 0GL1, lemma-j-shriek-and-tensor, and Tag 0FNH,
item-shift-tensor (blueprint: lem-pur-open-system-tensor-shift).

Proof:
1. Use lem-coef-semilinear-derived-sections to interpret strict systems as
modules on the vertical ringed site. Use lem-pc-kflat-resolution to resolve
both unbounded inputs by flat-term K-flat complexes on that site. For mode
ordinary make the same choices on the original pro-etale site.
2. Apply lem-sf-ringed-slice-tensor-generators at each coefficient level:
[x] tensor y maps to [x tensor y restricted to the open]. These maps respect
the actual semilinear transitions and both differentials. Extension is a
left adjoint, so lem-weil-pbc-left-adjoint-preserves-colimits moves it across
the total direct sums. The inverse is the open-adjunction transpose of unit
tensor identity. Thus this is exactly gamma from lem-sf-open-tensor-normalization.
3. Exact restriction takes acyclic complexes to acyclic complexes; tensoring
with a K-flat complex and then exact extension stays acyclic. The preceding
comparison proves extension preserves K-flatness. Applied to short exact
sequences and flat terms it proves termwise flatness as well, using
def-pc-kflat-complex and def-pc-flat-sheaf-modules.
4. By lem-weil-pbc-total-tensor-integer-shifts both paths on a total summand
with first degree a multiply [x tensor y restricted] by (-1)^(r*a).
Generator uniqueness and the coproduct universal property give equality of
chain maps for every integer r, including negative integers.
5. Localize this chain equality. The localization shift isomorphisms and
lem-weil-pbc-ringed-topoi-derived-tensor-pullback identify it with the stated
normalized shifts on resolving pairs. Tensor-model descent extends them and
the square to all unbounded derived inputs, independently of representatives.
6. The sign is a central integer scalar. Both paths across a coefficient
transition send the generator to (-1)^(r*a) times the generator of the two
transition images. This proves compatibility before localization. Naturality
follows from the same formulas and descends. Mode ordinary has no coefficient
transitions and includes the constant finite rings O_E / varpi_E^n. -/
theorem open_system_tensor_shift
    {m : Mode} {d : Input.{u} m} {t : SiteSquare d}
    (o : Operations d t) (a : Assertion o) :
    (Nonempty (TensorShifts o.tensorX) ∧ Nonempty (TensorShifts o.tensorU)) ∧
    ∀ [TensorShifts o.tensorX] [TensorShifts o.tensorU]
      (M : Der (restrictRing m d.j d.R)) (N : Der d.R) (r : ℤ),
      a.gamma.hom.app (M, N⟦r⟧) ≫
          o.opens.jShriek.map
            (o.tensorU.functor.map
                (Prod.mkHom (𝟙 M) ((o.opens.jStar.commShiftIso r).hom.app N)) ≫
              (((Functor.curry.obj o.tensorU.functor).obj M).commShiftIso r).hom.app
                (o.opens.jStar.obj N)) ≫
          (o.opens.jShriek.commShiftIso r).hom.app
            (o.tensorU.functor.obj (M, o.opens.jStar.obj N)) =
        (((Functor.curry.obj o.tensorX.functor).obj
          (o.opens.jShriek.obj M)).commShiftIso r).hom.app N ≫
          (a.gamma.hom.app (M, N))⟦r⟧' := by
  sorry

end SheafOfModules.OpenTensorNormalization
