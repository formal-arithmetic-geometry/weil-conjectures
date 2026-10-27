module

public import WeilConjectures.AlgebraicGeometry.FunctionField
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
public import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace

/-!
# Gluing multiplicative affine section maps by generic germs

Source: Stacks Project, Divisors, Tag 0BD3, proof of
`divisors-lemma-norm-in-normal-case`, compatible affine section maps and property (1).
The abstract generic-function gluing argument is the six-step DAG expansion
(blueprint: lem-sfb-generic-multiplicative-affine-gluing).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

/-- Multiplicative affine section maps with a common generic formula extend uniquely to
all opens, commute with restriction, and retain the scalar power and generic formulas.

Source: Stacks Project, Divisors, Tag 0BD3, proof of
`divisors-lemma-norm-in-normal-case`, compatible affine section maps and property (1)
(blueprint: lem-sfb-generic-multiplicative-affine-gluing).

Proof: (1) Every nonempty open contains the generic point (`def-sc-generic-point`), and
its inverse image does too by `hp`. Generic germs are unchanged by restriction
(`def-weil-pbc-module-stalk`); the germ map on every nonempty open of the integral
scheme Z is injective (`lem-sc-integral-scheme-stalks-in-function-field`).
(2) On nested nonempty affines, the generic formula therefore forces compatibility.
For an empty smaller open compatibility follows from its singleton section ring
(`def-pc-scheme`, `def-weil-locally-ringed-space-morphism`).
(3) Cover any nonempty V by all nonempty affine opens inside it
(`lem-weil-pbc-affine-opens-basis`). Apply the specified maps to restrictions of b.
On each overlap their generic germs agree, so injectivity gives equality even when
that overlap is not affine; the empty overlap is automatic. The structure-sheaf axiom
(`def-pc-scheme`, `def-weil-locally-ringed-space-morphism`) glues them uniquely.
Use the unique map of singleton section rings for the empty open.
(4) Sheaf uniqueness on affine covers proves extension and restriction compatibility.
Restrict to one nonempty affine to recover the generic formula.
(5) Check multiplication, 1, and the scalar power identity on the same affine cover,
using naturality of p.app (`def-weil-locally-ringed-space-morphism`), and glue the
identities by sheaf uniqueness. All identities on the empty open are automatic.
(6) Any other restriction-compatible affine extension has the same restrictions on
this cover, hence is equal by sheaf uniqueness, including on the empty open.

The binders `hx` index exactly the nonempty opens, since Z is integral. They also
supply the membership proof for the actual generic germ. Transport along the equality `hp`
supplies membership in the inverse image. The empty open occurs in the extended family, whose
maps are monoid homomorphisms, with no additivity requirement. The last conjunct is the
uniqueness of the node: it holds among all families of plain maps of sections that extend the
specified affine maps and commute with restriction, not only among multiplicative ones. -/
theorem Scheme.existsUnique_multiplicative_affine_extension
    {Y Z : Scheme.{u}} [IsIntegral Y] [IsIntegral Z] (p : Y ⟶ Z)
    (hp : p (genericPoint Y) = genericPoint Z)
    (F : Y.functionField → Z.functionField) (d : ℕ) (hd : 1 ≤ d)
    (nAffine : ∀ (U : Z.Opens), IsAffineOpen U →
      genericPoint Z ∈ U → (Γ(Y, p ⁻¹ᵁ U) →* Γ(Z, U)))
    (hscalar : ∀ (U : Z.Opens) (hU : IsAffineOpen U) (hx : genericPoint Z ∈ U)
      (a : Γ(Z, U)), nAffine U hU hx (p.app U a) = a ^ d)
    (hgeneric : ∀ (U : Z.Opens) (hU : IsAffineOpen U) (hx : genericPoint Z ∈ U)
      (b : Γ(Y, p ⁻¹ᵁ U)),
      Z.presheaf.germ U (genericPoint Z) hx (nAffine U hU hx b) =
        F (Y.presheaf.germ (p ⁻¹ᵁ U) (genericPoint Y)
          ((congrArg (fun z : Z => z ∈ U) hp).mpr hx) b)) :
    ∃ n : ∀ V : Z.Opens, Γ(Y, p ⁻¹ᵁ V) →* Γ(Z, V),
      (∀ (U : Z.Opens) (hU : IsAffineOpen U) (hx : genericPoint Z ∈ U),
        n U = nAffine U hU hx) ∧
      (∀ (V W : Z.Opens) (i : W ⟶ V) (b : Γ(Y, p ⁻¹ᵁ V)),
        Z.presheaf.map i.op (n V b) =
          n W (Y.presheaf.map ((Opens.map p.base).map i).op b)) ∧
      (∀ (V : Z.Opens) (a : Γ(Z, V)), n V (p.app V a) = a ^ d) ∧
      (∀ (V : Z.Opens) (hx : genericPoint Z ∈ V) (b : Γ(Y, p ⁻¹ᵁ V)),
        Z.presheaf.germ V (genericPoint Z) hx (n V b) =
          F (Y.presheaf.germ (p ⁻¹ᵁ V) (genericPoint Y)
            ((congrArg (fun z : Z => z ∈ V) hp).mpr hx) b)) ∧
      (∀ m : ∀ V : Z.Opens, Γ(Y, p ⁻¹ᵁ V) → Γ(Z, V),
        (∀ (U : Z.Opens) (hU : IsAffineOpen U) (hx : genericPoint Z ∈ U),
          m U = ⇑(nAffine U hU hx)) →
        (∀ (V W : Z.Opens) (i : W ⟶ V) (b : Γ(Y, p ⁻¹ᵁ V)),
          Z.presheaf.map i.op (m V b) =
            m W (Y.presheaf.map ((Opens.map p.base).map i).op b)) →
        ∀ V : Z.Opens, m V = ⇑(n V)) := by
  sorry

end AlgebraicGeometry
