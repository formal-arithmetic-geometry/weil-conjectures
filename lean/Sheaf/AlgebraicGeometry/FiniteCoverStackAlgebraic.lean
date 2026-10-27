module

public import Sheaf.AlgebraicGeometry.RelativeFiniteHilbertGroupoids
public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
import WeilConjectures.AlgebraicGeometry.AffineMorphismRelativeSpec
import Sheaf.AlgebraicGeometry.FiniteFreeAlgebraSpectrum
import Sheaf.AlgebraicGeometry.RelativeSpecBaseChange
import Sheaf.AlgebraicGeometry.FiniteLocallyFreeStructureSheaf
import Sheaf.CategoryTheory.GroupoidStackificationLocalDescription

/-! # Algebraicity of the stack of finite locally free covers

Source: Stacks Project, criteria.tex, Tag 05YQ (proposition-finite-hilbert-point)
(blueprint: lem-sfb-finite-cover-stack-algebraic).

The finite-cover category is the existing relative finite Hilbert category at the
identity of the discrete groupoid represented by the terminal S-scheme. Its base
projection is independent of the stack proofs accepted by `RelativeFiniteHilbert.groupoid`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The category of degree-d finite locally free covers over S, with cartesian arrows.
This is H_d(id_{h_S}), using the recorded Hilbert category and its base projection.
The objects and comparison arrows in h_S carry only the unique structural maps to S.
The fibre over T retains all T-isomorphisms of covers; its pullback is scheme base change.
Source: Stacks Project, criteria.tex, Tag 05YQ
(blueprint: lem-sfb-finite-cover-stack-algebraic). -/
def finiteCoverStack (S : Scheme.{u}) (d : ℕ+) : BasedCategory (Over S) :=
  BasedCategory.ofFunctor (RelativeFiniteHilbert.base
    (F := BasedFunctor.id (discreteModuli (yoneda.obj (Over.mk (𝟙 S))))) (d := d))

/-- Finite locally free covers of a fixed positive degree form an algebraic stack
on the big fppf site of an arbitrary base scheme.
Source: Stacks Project, criteria.tex, Tag 05YQ (proposition-finite-hilbert-point)
(blueprint: lem-sfb-finite-cover-stack-algebraic).

Proof:
1. The unit-framed algebra-law construction of
   lem-sfb-unit-framed-algebra-smooth-groupoid gives a smooth groupoid G ×_S X over X.
   Its fppf stackification Q is algebraic by lem-sfb-smooth-groupoid-fppf-quotient.
   Only the source and target maps are smooth; X need not be smooth over S.
2. Send a multiplication m on O_T^d to its relative spectrum, using
   lem-weil-pbc-affine-morphism-relative-spec. It is finite locally free by
   lem-weil-pbc-finite-free-algebra-spectrum and its fibre algebra has dimension d.
   A matrix g labelling m → m' is an algebra map m' → m, so Spec has the requested
   arrow direction. The construction commutes with arbitrary scheme base change by
   lem-weil-pbc-relative-spec-base-change, including the coefficient maps on arrows.
3. The relative-Spec anti-equivalence identifies T-isomorphisms with algebra
   isomorphisms in the opposite direction. Linear endomorphisms of O_T^d are matrices
   over Γ(T,O_T). Preserving the unit and multiplication says exactly that g fixes
   e₁ and m' = g⁻¹ m (g ⊗ g). Thus this functor is fully faithful on every fibre.
4. For a cover p, lem-pc-flf-properties makes p_*O_Z locally free of rank d with
   the specified fibre algebra. Since d > 0, the unit is nonzero in every residue
   algebra. In a local basis choose a unit coordinate u_j nonzero at the point and
   shrink to D(u_j). The columns (1,e₁,...,ê_j,...,e_d) have determinant ±u_j and
   give a unit-adapted basis. Since p is finite it is affine, and the relative-Spec
   anti-equivalence identifies it with the spectrum of this algebra. These Zariski
   neighbourhoods are fppf covers, proving local essential surjectivity.
5. Apply lem-sfb-finite-hilbert-stack-descent at id_{h_S} to obtain fppf descent
   for the finite-cover category. Extend the preceding functor from Q using
   lem-sfb-groupoid-stackification-local-description. Its isomorphism sheaves are
   identified locally by step 3, hence globally by sheaf descent. Local lifts from
   step 4 have unique overlap comparisons by full faithfulness; their cocycle
   equations follow by uniqueness. Stack descent glues them and their comparison
   with the prescribed cover. Thus Q is equivalent to the finite-cover category.
   Transport its representable diagonal and smooth surjective atlas through this
   equivalence, yielding IsAlgebraicModuliStack. No restriction on S was used. -/
theorem finiteCoverStack_isAlgebraic (S : Scheme.{u}) (d : ℕ+) :
    IsAlgebraicModuliStack (finiteCoverStack S d) := by
  sorry

end AlgebraicGeometry
