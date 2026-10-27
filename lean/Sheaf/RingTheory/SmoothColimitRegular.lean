module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import WeilConjectures.RingTheory.GRing
import Mathlib.RingTheory.Smooth.Flat
import WeilConjectures.RingTheory.FilteredColimitAlgebrasUnderlyingModule
import WeilConjectures.Algebra.Category.ModuleCat.FilteredColimitFlat
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Noetherian.Basic
import WeilConjectures.RingTheory.FilteredColimitAlgebrasTensorElementwise
import Sheaf.RingTheory.SmoothOverFieldRegularLocal
import WeilConjectures.AlgebraicGeometry.FilteredColimitLocalizationAtPrime
import Mathlib.RingTheory.Localization.Submodule
import WeilConjectures.CategoryTheory.ExistsDirectedReindexing
import Sheaf.AlgebraicGeometry.IsRegularScheme

/-!
# Regularity of filtered colimits of smooth algebras

Source: Stacks Project, More on Algebra, Tag 07EP, lemma-colimit-smooth-regular
(blueprint: lem-per-smooth-colimit-regular).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CommAlgCat

/-- A filtered colimit of smooth algebras whose fibres are Noetherian is regular.
Source: Stacks Project, More on Algebra, Tag 07EP, lemma-colimit-smooth-regular
(blueprint: lem-per-smooth-colimit-regular).

The fibre is written as `p.Fiber (colimit A)`, namely `κ(p) ⊗[R] colimit A`, using
Mathlib's canonical tensor symmetry to identify it with the source's opposite order.

Proof:
1. Smooth algebras are flat (`lem-weil-pbc-smooth-ring-map-flat`). The algebra colimit
   is also the underlying module colimit
   (`lem-weil-pbc-filtered-colimit-algebras-underlying-module`), so the colimit is flat by
   `lem-weil-pbc-filtered-colimit-flat-modules`.
2. Fix a prime `p` and a finite purely inseparable extension `K/κ(p)`. Tensor cancellation
   (`lem-weil-pbc-tensor-cancel-base-change`) identifies `K ⊗[R] colimit A` with the
   base change of the Noetherian fibre to `K`. A finite basis of `K` over `κ(p)` generates
   this tensor product as a module over the fibre, so it is Noetherian by
   `lem-weil-pbc-finite-algebra-noetherian`.
3. By `lem-weil-pbc-filtered-colimit-algebras-tensor-elementwise`, this ring is the
   colimit of `K ⊗[R] A.obj j`. To check the ring universal property, descend a compatible
   ring cocone using the module universal property. Filteredness gives its common
   `R`-algebra structure, and representing two elements at a common stage proves
   multiplicativity and preservation of the unit.
4. Smooth base change (`lem-weil-pbc-smooth-ring-map-base-change-composition`) and
   `lem-weil-pbc-smooth-over-field-regular-local` make every prime localization of each
   stage regular local. Fix a prime of the colimit. By
   `lem-weil-pbc-filtered-colimit-localization-at-prime`, its localization is the colimit
   of the localizations at the contracted primes. The transition maps are local:
   the image of a fraction lies in the target maximal ideal exactly when its numerator
   belongs to the contracted prime. The apex is Noetherian by
   `lem-weil-pbc-localization-noetherian` and step 2.
5. Reindex by `lem-weil-pbc-filtered-category-directed-cofinal`. The stages remain
   regular local and the transition maps local. Apply
   `lem-per-noetherian-local-colimit-regular` to obtain a regular local apex at every
   prime. Thus the Noetherian base change from step 2 is a regular ring.
6. This proves geometric regularity of every fibre, including the zero fibre. Together
   with flatness from step 1, this is `RingHom.IsRegular` from `def-weil-pbc-g-ring`.
-/
theorem smooth_colimit_regular
    {R : Type u} [CommRing R] {J : Type v} [SmallCategory J] [IsFiltered J]
    (A : J ⥤ CommAlgCat.{v, u} R) [HasColimit A]
    (hsmooth : ∀ j : J, Algebra.Smooth R (A.obj j))
    (hfibres : ∀ (p : Ideal R) [p.IsPrime],
      IsNoetherianRing (p.Fiber (colimit A : CommAlgCat.{v, u} R))) :
    RingHom.IsRegular (algebraMap R (colimit A : CommAlgCat.{v, u} R)) := by
  sorry

end CommAlgCat
