module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Sheaf.CategoryTheory.FilteredComplexPageDifferential

@[expose] public section
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Every successor-cycle map satisfying the representative equation is epic.
Source: Stacks Project, Homology, Tag 012K, displayed cycle, boundary and
differential formulas preceding lemma-spectral-sequence-filtered-complex.
(blueprint: lem-sp-filtered-complex-successor-cycles-cover-epi).

Proof. Put p = pq.1, n = pq.1 + pq.2 and j = (p+r,pq.2-r+1). To show that f
covers the kernel, take any morphism into D.page.cycles pq. After pulling back
the page quotient epimorphism and then the image epimorphism from unquotiented
r-cycle representatives, its composite with iCycles is represented by x in F^p
with dx in F^(p+r). The representative equation for D and the kernel condition
say that the class of dx vanishes in the target page quotient. Its kernel is
the target boundary subobject. Pull back the epimorphisms defining that image
and its sum with F^(p+r+1); on this further epimorphic refinement write dx = dy+z,
where y lies in F^((p+r)-r+1) = F^(p+1) and z lies in F^(p+r+1).
Then x-y lies in F^p and d(x-y) = z, so it is an (r+1)-cycle representative.
Since y lies in F^(p+1), x-y and x have the same source graded class. Its map
into graded successor cycles followed by f therefore equals the given kernel
morphism on this refinement: postcomposing with the monomorphism iCycles gives
this equality by hf. Apply this to the identity of the kernel object. We obtain
an epimorphism onto that object factoring through f, so f is epic. All local
lifts here mean pullbacks of image or cokernel epimorphisms; those pullbacks
are epic in an abelian category. Thus no projective objects or elementwise
lifting assumption is used. -/
theorem filteredComplex_successor_cycles_cover_epi
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K) (r : ℤ) (hr : 1 ≤ r)
    (D : FilteredComplexPageDifferential K F r) (pq : ℤ × ℤ)
    (hZ : F.complexCycles pq.1 (pq.1 + pq.2) (r + 1) ≤
      F.complexCycles pq.1 (pq.1 + pq.2) r)
    (f : (F.complexCycles pq.1 (pq.1 + pq.2) (r + 1) : C) ⟶ D.page.cycles pq)
    (hf : f ≫ D.page.iCycles pq =
      Subobject.ofLE _ _ hZ ≫ filteredComplexPageπ K F r pq) : Epi f := by sorry

end CategoryTheory
