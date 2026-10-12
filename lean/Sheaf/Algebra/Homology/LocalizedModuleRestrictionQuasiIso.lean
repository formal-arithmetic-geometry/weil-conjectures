module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.QuasiIso

/-! Exact restriction of module complexes to a localized site. -/

@[expose] public section

universe u v
open CategoryTheory
namespace CategoryTheory

/-- Restriction of a quasi-isomorphism of module complexes to `C/U` is a quasi-isomorphism.
Source: Stacks Project, Section 18.19 (Tag 03DH), restriction exactness recalled in
Lemma 18.19.4 (Tag 03DK), as used in Tag 0A95.
(blueprint: lem-pur-localized-module-restriction-quasi-iso).

Proof: restriction to the slice site preserves kernels: kernels of module sheaves are
computed sectionwise. It also preserves cokernels: the presheaf cokernel is computed
sectionwise and restriction commutes with sheafification. For the latter, a covering
sieve of an object `(V,f)` of `C/U` is precisely a covering sieve of `V` equipped with
its forced maps to `U`; the local representatives and local equalities used by
sheafification are therefore identical on both sites. Thus restriction is an exact
additive functor of abelian categories. Exact functors preserve homology, by preserving
the kernels and cokernels defining it. The restricted homology map is consequently
isomorphic to restriction of the original homology map, hence is invertible. This works
for arbitrary Grothendieck topologies, including the trivial and maximal ones, and
requires no boundedness of the complexes. -/
theorem localizedModule_restriction_quasiIso
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{max u v}) (U : C)
    (hzero : (SheafOfModules.overFunctor.{max u v} R U).PreservesZeroMorphisms)
    {L' L : CochainComplex (SheafOfModules.{max u v} R) ℤ}
    (t : L' ⟶ L) [QuasiIso t] :
    letI := hzero
    QuasiIso (((SheafOfModules.overFunctor.{max u v} R U).mapHomologicalComplex
      (ComplexShape.up ℤ)).map t) := by
  sorry

end CategoryTheory
