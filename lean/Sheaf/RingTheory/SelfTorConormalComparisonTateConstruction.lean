/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.RingTheory.SelfTorConormalComparisonPredicate

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct
namespace AlgebraicGeometry

/-- A comparison computed by one augmentation lift for each Koszul complex and
projective resolution. This records the actual wedge formula, without claiming
it for arbitrary lifts. Source: Stacks Project, Tags 09PQ and 00LS.
(blueprint: new-r4-self-tor-conormal-comparison-tate-construction). -/
def TateComparisonCertificate (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ)
    (c : conormalExteriorModule A I n ⟶
      ((Tor' (ModuleCat.{u} A) n).obj (ModuleCat.of A (A ⧸ I))).obj
        (ModuleCat.of A (A ⧸ I))) : Prop :=
  ∀ (r : ℕ) (g : Fin r → I) (P : ProjectiveResolution (ModuleCat.of A (A ⧸ I))),
    ∃ a : ExteriorAlgebra.koszulComplex A r (fun j ↦ (g j : A)) ⟶ P.complex,
      a.f 0 ≫ P.π.f 0 =
        ModuleCat.ofHom (I.mkQ.comp
          (exteriorPower.zeroEquiv A (Fin r →₀ A)).toLinearMap) ∧
      let K := ExteriorAlgebra.koszulComplex A r (fun j ↦ (g j : A))
      let T := (tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex (.down ℕ)
      ∀ (v : Fin n → (Fin r →₀ A)) (z : (T.obj K).cycles n),
        (T.obj K).iCycles n z =
          (exteriorPower.ιMulti A n v) ⊗ₜ[A] (1 : A ⧸ I) →
        (P.isoLeftDerivedObj (tensorRight (ModuleCat.of A (A ⧸ I))) n).hom
            (c (exteriorPower.ιMulti (A ⧸ I) n
              (fun j ↦ I.toCotangent (Finsupp.linearCombination A g (v j))))) =
          ((HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (.down ℕ) n).map
            (T.map a)) ((T.obj K).homologyπ n z)

/-- The Tate construction supplies a comparison with a wedge formula for a
chosen augmentation lift, for each tuple and projective resolution.
Source: Stacks Project, Tag 09PQ (strictly graded commutative Tor via Tate
resolutions), and Tag 00LS, part (1) (lifting a free complex to a resolution).
(blueprint: new-r4-self-tor-conormal-comparison-tate-construction).

Proof: Resolve A/I by a free strictly commutative Tate dg algebra Q. The
connecting map for 0 → I → A → A/I → 0 identifies I/I² with self-Tor in
degree one: lift x in I to degree one of Q with differential x, and take its
class after tensoring with A/I. Boundaries identify precisely the relations
in I/I². Products of these classes give alternating A/I-multilinear maps,
since odd elements square to zero even in characteristic two. The exterior
universal property defines c in degree n, restricted to A-linear scalars.
For a tuple g, choose degree-one lifts in Q of its ideal elements. Sending
Koszul generators to those lifts gives an augmentation-preserving dg algebra
map to Q: the differential and exterior relations hold by construction and
strict commutativity. Its value on every wedge is the defining product for c.
Lift Q's augmentation to any projective resolution P, using freeness and
exactness, and compose with this Koszul map. Tensoring with A/I and passing
to homology transports the product formula along the canonical derived
comparison isomorphism, giving the stated equality. This only constructs one
lift a; independence from arbitrary Koszul lifts is proved separately.
For n=0 the product is the quotient unit. For I=0 the positive conormal
exterior powers vanish; for I=A all quotient modules vanish. -/
theorem tate_selfTor_conormal_map (A : Type u) [CommRing A]
    (I : Ideal A) (n : ℕ) :
    ∃ c : conormalExteriorModule A I n ⟶
      ((Tor' (ModuleCat.{u} A) n).obj (ModuleCat.of A (A ⧸ I))).obj
        (ModuleCat.of A (A ⧸ I)), TateComparisonCertificate A I n c := by sorry

end AlgebraicGeometry
