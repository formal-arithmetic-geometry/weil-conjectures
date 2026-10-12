module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.GeometricFiber
public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.RepresentationTheory.Rep.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.GroupTheory.PGroup
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

import Sheaf.AlgebraicGeometry.FiniteFiberDegreeBaseChange
import Sheaf.AlgebraicGeometry.FiniteLocallyFreeDegreeLocallyConstant
import Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence
import Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence
import Sheaf.Paper.GaloisLisseRepresentations
import Mathlib.GroupTheory.Sylow
import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry
open Etale

/-- Construct the Sylow cover and the associated-sheaf functor with its stalk description.
Source: Stacks Project, Tags 0A3R, 0DV5 and 0DV6.
(blueprint: lem-weil-pbc-sylow-cover-stalk-data)

Proof: Choose a geometric point of the nonempty irreducible scheme U. The finite locally
constant sheaf G gives a finite-dimensional representation with finite monodromy image Q.
Choose an ℓ-Sylow subgroup P of Q. The connected finite étale Q-torsor Y yields the
connected quotient V = Y/P; its degree d = [Q:P] is prime to ℓ. Finite étale maps are
finite locally free, so their degree is constant on connected U and invariant under
field extension. Over every separably closed field their fibre algebra splits into d
copies of that field; hence every geometric fibre has cardinality d.
Restrict the monodromy representation to P to obtain M. The P-torsor Y over V defines
T by descent of constant module sheaves on Y with the transition actions of P,
transporting coefficients along ZMod ℓ ≃ ULift (ZMod ℓ). The cocycle identity is the
group-action identity, and equivariant linear maps descend; addition descends too.
This construction applies to all representations, including infinite modules: actions
of the finite discrete group P are continuous. A choice of a point of the torsor above
each geometric point of V trivializes its fibre and gives, naturally in every
representation, the displayed isomorphism of stalk functors with the underlying-module
functor. The restricted monodromy representation descends to v*G, while the trivial
rank-one representation descends to the constant coefficient sheaf. For G = 0, take
Q = P = 1, V = U and M = 0. Global preservation of finite limits and colimits is not
asserted here; it follows from the stalk description and conservativity. -/
theorem Scheme.IsFiniteLocallyConstantSheaf.exists_sylow_cover_stalk_data
    {U : Scheme.{u}} [IrreducibleSpace U] (ℓ : ℕ) [Fact ℓ.Prime]
    (G : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))))
    [IsFiniteLocallyConstantSheaf G] :
    ∃ (V : Scheme.{u}) (v : V ⟶ U) (_ : IsFinite v) (_ : Etale v) (_ : ConnectedSpace V)
      (d : ℕ), ¬ ℓ ∣ d ∧
      (∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ U),
        Nat.card (v.GeometricFiber s) = d) ∧
      ∃ (P : Type u) (_ : Group P) (_ : Finite P), IsPGroup ℓ P ∧
        ∃ (M : Rep.{u + 1} (ZMod ℓ) P) (_ : FiniteDimensional (ZMod ℓ) M.V)
          (T : Rep.{u + 1} (ZMod ℓ) P ⥤
            Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))))
          (_ : T.Additive),
          (∀ x : V, Nonempty
            (T ⋙ (V.uliftPointSmallEtale x).sheafFiber
                  (A := ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) ⋙
                ModuleCat.restrictScalars.{u + 1}
                  (ULift.ringEquiv.symm.toRingHom : ZMod ℓ →+* ULift.{u + 1} (ZMod ℓ)) ≅
              forget₂ (Rep.{u + 1} (ZMod ℓ) P) (ModuleCat.{u + 1} (ZMod ℓ)))) ∧
          Nonempty (T.obj M ≅ (v)^*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))].obj G) ∧
          Nonempty (T.obj (Rep.trivial (ZMod ℓ) P (ULift.{u + 1} (ZMod ℓ))) ≅
            (constantSheaf V.smallEtaleTopology
              (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj
              (ModuleCat.of _ (ULift.{u + 1} (ZMod ℓ)))) := by sorry

end AlgebraicGeometry
