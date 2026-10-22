module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.ResidueField
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
import WeilConjectures.AlgebraicGeometry.AffineAlgebraModuleGenerators
import WeilConjectures.AlgebraicGeometry.GlobalGenerationNonvanishingCover
import WeilConjectures.AlgebraicGeometry.NonvanishingSectionTrivializes

/-! # A section of an invertible module avoiding a finite set on an affine scheme

Source: Stacks Project, Tag 0F20, `properties-lemma-quasi-affine-invertible-nonvanishing-section`
in `literature/stacks-project/properties.tex`, specialized to affine X and W = X;
also its invocation in Tag 0BUT, `divisors-lemma-finite-trivialize-invertible-upstairs`.
(blueprint: lem-sfb-affine-invertible-finite-set-section)
-/

@[expose] public section

universe u

set_option autoImplicit false

namespace AlgebraicGeometry.Scheme.Modules

/-- An invertible module on an affine scheme has a global section whose germ has nonzero
image in the residue fibre at every point of any prescribed finite subset. The points
need not be closed. Nonzero image in the quotient L_x / m_x L_x is expressed by the germ
not belonging to the submodule m_x L_x.

Source: Stacks Project, Tag 0F20, `properties-lemma-quasi-affine-invertible-nonvanishing-section`,
specialized to affine X and W = X; invoked in Tag 0BUT.

Proof:
1. Identify X with Spec A for A = Gamma(X, O_X), using `def-weil-affine-spectrum`.
   By `lem-weil-pbc-affine-open-stalk-localization`, the germ map at x is localization
   at its prime p_x. A scalar has nonzero residue exactly when it lies outside p_x:
   such a scalar becomes a unit, and if an element of p_x had inverse b/c, clearing
   denominators would give u*c = u*a*b in p_x with both u and c outside p_x.
2. Invertibility gives quasi-coherence (`def-sc-invertible-module`). Apply
   `lem-weil-pbc-affine-algebra-module-generators` with the identity O_X-algebra and
   U = X to generate L by global sections. By `lem-sc-global-generation-nonvanishing-cover`,
   at each point at least one global section has nonzero residue-fibre value.
3. Induct strongly on the cardinality of E. For E empty choose zero. Nonvanishing loci
   are open by `lem-weil-pbc-nonvanishing-section-trivializes`. If distinct x, y in E
   satisfy x specializes to y, omit x and use induction: the resulting open containing y
   contains its generalization x. Thus only pairwise incomparable points remain.
4. Choose z in E and, by induction, a section s nonzero on F = E minus {z}. If s is
   nonzero at z, finish. Otherwise choose t nonzero at z by step 2. This also handles
   the case F empty directly.
5. For each x in F, incomparability gives a_x in p_x outside p_z: inclusion of primes
   would imply specialization by the definition of the Zariski closed sets V(I).
   Their product f is in every p_x for x in F and outside p_z; the empty product is one.
   Step 1 says f has zero residue on F and nonzero residue at z.
6. The section s + f*t remains nonzero on F, where f has zero residue. At z its value
   is f(z)*t(z), which is nonzero since multiplication by the nonzero field element
   f(z) is invertible on L_z / m_z L_z. Germs and quotient maps respect addition and
   scalar multiplication. This completes the induction for arbitrary finite E.

(blueprint: lem-sfb-affine-invertible-finite-set-section) -/
theorem exists_section_nonvanishing_on_finite_set (X : AlgebraicGeometry.Scheme.{u})
    [AlgebraicGeometry.IsAffine X] (L : X.Modules) [L.IsInvertible]
    (E : Set X) (hE : E.Finite) :
    ∃ s : Γ(L, ⊤), ∀ (x : X), x ∈ E →
      L.presheaf.germ ⊤ x trivial s ∉
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) •
          (⊤ : Submodule (X.presheaf.stalk x) (L.presheaf.stalk x)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
