/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q55
-/
module

public import Sheaf.CategoryTheory.RingedToposMorphism
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Yoneda

/-! # Totally acyclic modules and arbitrary ringed-topos direct images

Source: Stacks Project, sites-cohomology.tex, Tag 0731(4), Tag 072Y and
section-limp (blueprint: lem-sfb-totally-acyclic-direct-image).

The additive Hom functor out of the existing free module sheaf on `T` is
`Gamma(T,-)`: the free-module and sheafification adjunctions identify its elements
with maps of sheaves of sets to the underlying sheaf, with pointwise addition.
An arbitrary module injective resolution computes both kinds of cohomology in the
statement. Thus the conclusion is exactly vanishing of positive higher direct images.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.RingedToposMorphism

/-- A totally acyclic module is acyclic for every ringed-topos direct image.

Source: Stacks Project, sites-cohomology.tex, Tag 0731(4), Tag 072Y and section-limp
(blueprint: lem-sfb-totally-acyclic-direct-image).

Here `I` is any injective resolution of `N`. For every sheaf of sets `T`, the
hypothesis computes `H^q(T,N)` as the homology of additive Hom from its free module
sheaf into `I`. The conclusion computes `R^q f_* N` by applying `f.modules` to `I`.
The commutativity binders express that the given ring sheaves are commutative;
no flatness or presentation of the geometric morphism by a site functor is required.

Proof:
1. The module category is Grothendieck by lem-weil-pbc-ring-sheaves-grothendieck,
so lem-sp-grothendieck-enough-injectives supplies resolutions as in
def-sp-injective-resolutions. Use the given arbitrary resolution `I`.
2. For a target site object `V`, sheafification adjunction
(def-weil-pbc-sheafification), Yoneda (lem-galois-yoneda-hom-bijection), and the
geometric adjunction (def-weil-pbc-ringed-topos-morphism) identify sections of
`f.modules.obj M` over `V` with generalized sections of `M` over
`f.inverse.obj (sheafify h_V)`. These identifications are additive: the structural
map preserves one, and the module action identity with scalar one gives addition.
They are natural in `M`, hence commute with the differentials of `I`.
3. Apply the total-acyclicity hypothesis to that actual inverse-image sheaf of sets.
The complex of target sections has zero homology in every positive degree; each
cycle section therefore has a boundary preimage, without any representability
assumption on the source site.
4. Kernels of module sheaves are sectionwise and cokernels are sheafified
sectionwise cokernels (def-weil-sheaf-of-modules-category). The map from the
preceding term onto the cycle sheaf is sectionwise surjective by step 3, so its
cokernel is zero. This is the displayed homology sheaf of `f.modules` applied to
`I`, and hence the positive higher direct image of `N`. -/
theorem isZero_higherDirectImage_of_totallyAcyclic
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (A : Sheaf J RingCat.{u}) (B : Sheaf K RingCat.{u})
    (_commA : ∀ (U : Cᵒᵖ) (a b : A.obj.obj U), a * b = b * a)
    (_commB : ∀ (V : Dᵒᵖ) (a b : B.obj.obj V), a * b = b * a)
    (f : RingedToposMorphism A B) (N : ringedSiteModules.{u} A)
    (I : InjectiveResolution N)
    (hN : ∀ (T : Sheaf J (Type u)) (q : ℕ), 0 < q →
      IsZero
        (((preadditiveCoyoneda.obj
          (op ((PresheafOfModules.sheafification (𝟙 A.obj)).obj
            ((PresheafOfModules.free A.obj).obj T.obj)))).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj I.cocomplex |>.homology q))
    (q : ℕ) (hq : 0 < q) :
    IsZero ((f.modules.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
      |>.homology q) := by
  sorry

end CategoryTheory.RingedToposMorphism
