module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

@[expose] public section
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry
open Scheme Etale

/-- An injective embedding gives a right exact cohomology ladder for dimension shifting.
Source: Stacks Project, Tags 03FD, 095T and 010S.
(blueprint: new-module-acyclic-effacement-ladder)

Proof: Embed M into an injective module-valued sheaf J, using enough injectives
in the Grothendieck abelian category of module-valued sheaves. Let Q be its cokernel
and g : J → Q the quotient. Forgetting coefficients is exact, so 0 → U(M) → U(J)
→ U(Q) → 0 is short exact. Exact abelian inverse image gives the second short exact
sequence. Take the canonical connecting homomorphisms δX and δY in degree q.
The long exact sequences give exactness at H^q(U(Q)) and its pullback.
Module-valued sheaves are equivalent to modules over the constant ring sheaf:
extend the constant scalar action uniquely over sheafification. This equivalence
commutes with underlying abelian sheaves and preserves injectivity. Thus Tag 03FD
makes H^{q+1}(U(J)) zero. The canonical isomorphism i^*U(J) ≅ U(i^*J), obtained
by commuting the coefficient forgetful functor with inverse image, and hacyclic
make the corresponding group on Y zero as well. Exactness then makes both
connecting maps surjective. Naturality of the long exact sequence under exact
inverse image, including the constant-integer-sheaf comparison in cohomologyMap,
gives the commuting boundary square. The case q = 0 uses only vanishing in degree
one, and includes M = 0. None of these steps asserts comparison for M or Q. -/
theorem Etale.exists_module_acyclic_effacement_ladder
    {X Y : Scheme.{u}} (i : Y ⟶ X) (r : ℕ)
    (hacyclic : ∀ (J : Sheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))) [Injective J]
        (q : ℕ), 0 < q →
      Subsingleton (Sheaf.H
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))
          AddCommGrpCat.{u + 1})).obj
            ((i)^*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))].obj J)) q))
    (M : Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))) (q : ℕ) :
    let U := sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) AddCommGrpCat.{u + 1})
    let V := (i)^*[AddCommGrpCat.{u + 1}]
    ∃ (J Q : Sheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))) (g : J ⟶ Q),
    ∃ δX : Sheaf.H (U.obj Q) q →+ Sheaf.H (U.obj M) (q + 1),
    ∃ δY : Sheaf.H (V.obj (U.obj Q)) q →+ Sheaf.H (V.obj (U.obj M)) (q + 1),
      Function.Exact (Sheaf.H.map (U.map g) q) δX ∧
      Function.Exact (Sheaf.H.map (V.map (U.map g)) q) δY ∧
      Function.Surjective δX ∧ Function.Surjective δY ∧
      δY.comp (cohomologyMap i (U.obj Q) q) =
        (cohomologyMap i (U.obj M) (q + 1)).comp δX := by sorry

end AlgebraicGeometry
