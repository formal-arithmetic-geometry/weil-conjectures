module

public import Sheaf.CategoryTheory.SheafDgModuleLocalization
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtension
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian

/-! # Grothendieck category of left sheaf dg modules

Source: Stacks Project, sdga.tex, Tags 0FRJ and 0FS9; left modules by the graded
opposite algebra (blueprint: lem-sfb-sheaf-dg-grothendieck).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.SheafDg

/-- Left sheaf dg modules form a Grothendieck abelian category. Kernels, cokernels,
coproducts and filtered colimits are computed in each degree of coefficient-module
sheaves, with the differential and action induced by their universal maps. Forgetting
the action is exact and faithful, and every underlying cohomology sheaf preserves
filtered colimits.

Source: Stacks Project, sdga.tex, Tags 0FRJ and 0FS9
(blueprint: lem-sfb-sheaf-dg-grothendieck).

Proof plan:
1. On the small open site, kernels restrict the differential and action. Cokernels
are sheafified coefficient-module cokernels; bilinear sheafification extends the
quotient action (lem-pc-sites-module-sheafification-bilinear-extension). The dg
identities descend by uniqueness. Coimage-to-image is an isomorphism degreewise,
and its inverse respects both structures. This proves abelianness and exactness
of the faithful underlying-complex functor.
2. Take the sheafification of finite sums in each degree for a coproduct. Extend
its differential and action from summands. For a diagram, take the cokernel of
its arrow-indexed sum mapping to its object-indexed sum, with component
inclusion_target composed with the arrow minus inclusion_source. Its universal
property gives the colimit, including the empty one, computed degreewise
(lem-pur-ringed-site-grothendieck-abelian).
3. Exact filtered colimits of coefficient-module sheaves give exact filtered
colimits of dg modules. Apply them to the short exact sequences of cycles,
terms, boundaries and cohomology. The canonical cocone maps identify colimits
of cycles and boundaries with those of the colimit differential, proving
preservation of every cohomology sheaf without boundedness.
4. On an open U form the free left disk with generators e,f of degrees n,n+1,
de=f and df=0. Put d(ae)=d(a)e+(-1)^|a| af and d(af)=d(a)f.
The two cross terms in d²(ae) cancel; the Leibniz rule holds on generators.
A dg map from this disk to M on U is uniquely e mapped to m and f mapped to dm,
for any section m of M in degree n.
5. The open-extension adjunction (lem-sfb-sheaf-dg-open-extension-adjunction)
identifies maps from the extended disk with those sections. The coproduct over
all opens and integer degrees is a generator: a nonzero map is nonzero on some
section, and the corresponding disk map, extended by zero on other summands,
detects it. The index is small. Together with steps 1--3 this gives exactly
IsGrothendieckAbelian (def-sp-grothendieck-abelian).
-/
theorem grothendieckAbelian_degreewise
    {X : TopCat.{u}}
    (S : Sheaf (Opens.grothendieckTopology X) CommRingCat.{max u v})
    (A : Algebra S) :
    IsGrothendieckAbelian.{max u v} (LeftModule A) ∧
    PreservesFiniteLimits (Mod.forget (D := Complex S) A.X) ∧
    PreservesFiniteColimits (Mod.forget (D := Complex S) A.X) ∧
    (Mod.forget (D := Complex S) A.X).Faithful ∧
    (∀ (n : ℤ) (M N : LeftModule A) (f : M ⟶ N),
      PreservesLimit (parallelPair f 0)
        (Mod.forget (D := Complex S) A.X ⋙ HomologicalComplex.eval _ (ComplexShape.up ℤ) n) ∧
      PreservesColimit (parallelPair f 0)
        (Mod.forget (D := Complex S) A.X ⋙ HomologicalComplex.eval _ (ComplexShape.up ℤ) n)) ∧
    (∀ (n : ℤ) (I : Type (max u v)),
      PreservesColimitsOfShape (Discrete I)
        (Mod.forget (D := Complex S) A.X ⋙ HomologicalComplex.eval _ (ComplexShape.up ℤ) n)) ∧
    (∀ (n : ℤ) (I : Type (max u v)) [SmallCategory I] [IsFiltered I],
      PreservesColimitsOfShape I
        (Mod.forget (D := Complex S) A.X ⋙ HomologicalComplex.eval _ (ComplexShape.up ℤ) n)) ∧
    (∀ (n : ℤ) (I : Type (max u v)) [SmallCategory I] [IsFiltered I],
      PreservesColimitsOfShape I
        (Mod.forget (D := Complex S) A.X ⋙
          HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) n)) := by
  sorry

end CategoryTheory.SheafDg
