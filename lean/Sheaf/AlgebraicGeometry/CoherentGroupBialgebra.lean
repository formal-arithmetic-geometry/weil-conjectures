module

public import Mathlib.Algebra.DirectSum.Module
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import WeilConjectures.AlgebraicGeometry.PQFCohomology
public import WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
public import WeilConjectures.AlgebraicGeometry.ScalarGlobalSectionsComparison
public import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf

import Mathlib.AlgebraicGeometry.Properties
import Sheaf.AlgebraicGeometry.GlobalSectionsGeomConnected
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.ScalarCupPullbackCoefficientNaturality
import WeilConjectures.AlgebraicGeometry.ScalarPullbackZeroGlobalSections
import Sheaf.AlgebraicGeometry.ScalarModuleCohomologyPullbackComparison
import WeilConjectures.AlgebraicGeometry.BasicPropertiesIdentity
import Sheaf.AlgebraicGeometry.ScalarCohomologyPullbackComposition
import Sheaf.AlgebraicGeometry.PicardKunnethQcoh
import Sheaf.AlgebraicGeometry.PicardKunnethQcohFunctoriality
import Mathlib.CategoryTheory.Monoidal.Grp
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech

/-! # The coherent cohomology bialgebra of a proper group

Source: Stacks Project, Varieties, Tag 0BED; Cohomology, Tags 0FP4 and 0FP5;
Milne, Abelian Varieties I, printed p.55 before Lemma 12.2, adapted from etale
cohomology to coherent Zariski cohomology by the recorded Kunneth theorem.
(blueprint: lem-sfb-coherent-group-bialgebra).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct DirectSum

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

/-- Structure-sheaf cohomology with the recorded restricted field action.
Source: Stacks, Tag 0BED (blueprint: lem-sfb-coherent-group-bialgebra). -/
abbrev coherentCohomologyDegree {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (n : ℕ) : ModuleCat.{u} k :=
  scalarCohomology f (SheafOfModules.unit X.ringCatSheaf) n

/-- The direct sum of the nonnegative coherent cohomology degrees.
Source: Stacks, Tag 0BED; Milne AV I, p.55
(blueprint: lem-sfb-coherent-group-bialgebra). -/
abbrev coherentTotal {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) :=
  ⨁ n : ℕ, coherentCohomologyDegree f n

/-- Inclusion of one coherent cohomology degree into its direct sum.
Source: Stacks, Tag 0BED (blueprint: lem-sfb-coherent-group-bialgebra). -/
def coherentInclusion {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (n : ℕ) :
    coherentCohomologyDegree f n →ₗ[k] coherentTotal f :=
  DirectSum.lof k ℕ (fun i ↦ coherentCohomologyDegree f i) n

/-- The degree-zero class of the global section 1.
Source: Stacks, Tags 01DZ and 0FP4
(blueprint: lem-sfb-coherent-group-bialgebra). -/
def coherentOneDegree {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) : coherentCohomologyDegree f 0 :=
  (scalarGlobalSectionsEquiv f (SheafOfModules.unit X.ringCatSheaf)).symm (1 : Γ(X, ⊤))

/-- The unit class in the direct sum.
Source: Stacks, Tag 0FP4 (blueprint: lem-sfb-coherent-group-bialgebra). -/
def coherentOne {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) : coherentTotal f :=
  coherentInclusion f 0 (coherentOneDegree f)

/-- Cup followed by multiplication of structure-sheaf coefficients, the tensor unitor.
Source: Stacks, Cohomology, Tags 0FP4 and 0FP5
(blueprint: lem-sfb-coherent-group-bialgebra). -/
def coherentCup {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (p q : ℕ)
    (a : coherentCohomologyDegree f p) (b : coherentCohomologyDegree f q) : coherentCohomologyDegree
      f (p + q) :=
  scalarCohomologyMap f (λ_ (𝟙_ X.Modules)).hom (p + q)
    (scalarCohomologyCup f _ _ p q a b)

/-- Pullback on coherent cohomology with its canonical structure-sheaf coefficient map.
Source: Stacks, Tags 0096 and 01F7
(blueprint: lem-sfb-coherent-group-bialgebra). -/
def coherentPullback {k : Type u} [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (a : Y ⟶ X) (h : a ≫ f = g) (n : ℕ) (x : coherentCohomologyDegree f n) :
    coherentCohomologyDegree g n :=
  scalarCohomologyMap g (tensorPullbackObjUnitToUnit a) n
    (scalarCohomologyPullback f g a h _ n x)

/-- The subspace of total tensor degree n, using finite sums of homogeneous pure tensors.
Source: Stacks, Tag 0BED (blueprint: lem-sfb-coherent-group-bialgebra). -/
def coherentTensorDegree {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (n : ℕ) :
    Submodule k (coherentTotal f ⊗[k] coherentTotal f) :=
  Submodule.span k {z | ∃ (p q : ℕ) (a : coherentCohomologyDegree f p) (b : coherentCohomologyDegree
    f q),
    p + q = n ∧ z = coherentInclusion f p a ⊗ₜ[k] coherentInclusion f q b}

/-- The connected graded coherent cohomology bialgebra, including its canonical maps.

Source: Stacks, Varieties, Tag 0BED; Cohomology, Tags 0FP4 and 0FP5; Milne AV I,
p.55 before Lemma 12.2, adapted from etale to coherent Zariski cohomology.
(blueprint: lem-sfb-coherent-group-bialgebra).

Proof:
1. Use lem-pc-h0-geom-connected, lem-weil-pbc-qcqs-over-affine,
lem-pc-proper-base-change and lem-weil-pbc-proper-composition.
Geometric integrality implies geometric reducedness and connectedness. The proper
geometrically connected H0 theorem identifies the structure map with H0 = k. Properness
makes G, its square and its cube quasi-compact with affine diagonals, by base change and
composition, so coherent Kunneth applies to all of them.
2. Use lem-sfb-module-cup-associativity-symmetry-unit,
lem-sc-scalar-cup-pullback-coefficient-naturality,
lem-sc-scalar-pullback-zero-global-sections,
lem-sc-scalar-module-cohomology-pullback-comparison,
lem-weil-pbc-module-cohomology-fmap-basic-identity and
lem-sc-scalar-cohomology-pullback-composition. Compose the recorded coefficient cup with
  multiplication of the structure sheaf.
Cup associativity, signed symmetry and the unit law give an associative unital graded
algebra; bilinearity extends it uniquely to the direct sum. Scalars are degree-zero
constant classes. Pullback coefficient naturality makes scheme pullback multiplicative
and unital, and pullback composition agrees with composition of scheme morphisms.
3. Apply lem-sc-picard-kunneth-qcoh and
lem-weil-pbc-module-pullback-structure-sheaf. Coherent Kunneth identifies the external cup map with
  an isomorphism in each degree.
On homogeneous pure tensors, exchange the middle two factors to obtain the sign
(-1)^(q*r) in the tensor multiplication. The exponents agree for either association of
three factors, and the unit is 1 tensor 1. Hence Kunneth is an algebra isomorphism.
4. Define Delta as inverse Kunneth after multiplication pullback. Both maps preserve
degree, units and multiplication, giving all three assertions for Delta.
5. Use lem-sc-picard-kunneth-qcoh-functoriality, pullback composition and
the def-sc-group-scheme associativity diagram. Iterated Kunneth identifies either triple coproduct
  with pullback along the
corresponding composite of group multiplication. Both triple external products have
the same pure-tensor formula by cup associativity. Group associativity equates the
scheme morphisms, and injectivity of triple Kunneth gives coassociativity.
6. Use lem-pc-affine-vanishing, coefficient naturality, pullback composition
and the def-sc-group-scheme unit diagrams. Affine vanishing on Spec k identifies identity-section
  pullback with the projection
to H0 = k. Pulling the external product back along either identity slice gives scalar
multiplication by this projection in the corresponding factor. The two group unit
diagrams give the counit equations under the tensor-unit identifications.
7. In total degree one, Delta(x) lies in H1 tensor H0 plus H0 tensor H1. Since H0 = k,
it has the form a tensor 1 + 1 tensor b. The two counit equations force a = b = x.
The argument applies in every characteristic, including two; a group scheme is nonempty
because it has its identity section. -/
theorem coherentGroupBialgebra {k : Type u} [Field k]
    (G : Over (Spec (CommRingCat.of k))) [GrpObj G]
    [IsProper G.hom] [GeometricallyIntegral G.hom] :
    ∃ (mulH : coherentTotal G.hom →ₗ[k] coherentTotal G.hom →ₗ[k] coherentTotal G.hom)
      (mulP : coherentTotal (G ⊗ G).hom →ₗ[k]
        coherentTotal (G ⊗ G).hom →ₗ[k] coherentTotal (G ⊗ G).hom)
      (mulT : (coherentTotal G.hom ⊗[k] coherentTotal G.hom) →ₗ[k]
        (coherentTotal G.hom ⊗[k] coherentTotal G.hom) →ₗ[k]
        (coherentTotal G.hom ⊗[k] coherentTotal G.hom))
      (κ : (coherentTotal G.hom ⊗[k] coherentTotal G.hom) ≃ₗ[k]
        coherentTotal (G ⊗ G).hom)
      (pullM : coherentTotal G.hom →ₗ[k] coherentTotal (G ⊗ G).hom)
      (Δ : coherentTotal G.hom →ₗ[k] coherentTotal G.hom ⊗[k] coherentTotal G.hom)
      (c : k ≃ₗ[k] coherentCohomologyDegree G.hom 0) (ε : coherentTotal G.hom →ₗ[k] k),
      (∀ r : k, c r = r • coherentOneDegree G.hom) ∧
      ε = c.symm.toLinearMap.comp
        (DirectSum.component k ℕ (fun n ↦ coherentCohomologyDegree G.hom n) 0) ∧
      (∀ p q (a : coherentCohomologyDegree G.hom p) (b : coherentCohomologyDegree G.hom q),
        mulH (coherentInclusion G.hom p a) (coherentInclusion G.hom q b) =
          coherentInclusion G.hom (p + q) (coherentCup G.hom p q a b)) ∧
      (∀ p q (a : coherentCohomologyDegree (G ⊗ G).hom p) (b : coherentCohomologyDegree (G ⊗ G).hom
        q),
        mulP (coherentInclusion (G ⊗ G).hom p a) (coherentInclusion (G ⊗ G).hom q b) =
          coherentInclusion (G ⊗ G).hom (p + q) (coherentCup (G ⊗ G).hom p q a b)) ∧
      (∀ x y z, mulH (mulH x y) z = mulH x (mulH y z)) ∧
      (∀ x, mulH (coherentOne G.hom) x = x ∧ mulH x (coherentOne G.hom) = x) ∧
      (∀ x y z, mulP (mulP x y) z = mulP x (mulP y z)) ∧
      (∀ x, mulP (coherentOne (G ⊗ G).hom) x = x ∧
        mulP x (coherentOne (G ⊗ G).hom) = x) ∧
      (∀ p q (a : coherentCohomologyDegree G.hom p) (b : coherentCohomologyDegree G.hom q),
        mulH (coherentInclusion G.hom p a) (coherentInclusion G.hom q b) =
          (-1 : k) ^ (p * q) •
            mulH (coherentInclusion G.hom q b) (coherentInclusion G.hom p a)) ∧
      (∀ p q r s (a : coherentCohomologyDegree G.hom p) (b : coherentCohomologyDegree G.hom q)
        (d : coherentCohomologyDegree G.hom r) (e : coherentCohomologyDegree G.hom s),
        mulT (coherentInclusion G.hom p a ⊗ₜ[k] coherentInclusion G.hom q b)
          (coherentInclusion G.hom r d ⊗ₜ[k] coherentInclusion G.hom s e) =
          (-1 : k) ^ (q * r) •
            (mulH (coherentInclusion G.hom p a) (coherentInclusion G.hom r d) ⊗ₜ[k]
              mulH (coherentInclusion G.hom q b) (coherentInclusion G.hom s e))) ∧
      (∀ x y z, mulT (mulT x y) z = mulT x (mulT y z)) ∧
      (∀ x, mulT (coherentOne G.hom ⊗ₜ[k] coherentOne G.hom) x = x ∧
        mulT x (coherentOne G.hom ⊗ₜ[k] coherentOne G.hom) = x) ∧
      (∀ p q (a : coherentCohomologyDegree G.hom p) (b : coherentCohomologyDegree G.hom q),
        κ (coherentInclusion G.hom p a ⊗ₜ[k] coherentInclusion G.hom q b) =
          coherentInclusion (G ⊗ G).hom (p + q)
            (coherentCup (G ⊗ G).hom p q
              (coherentPullback G.hom (G ⊗ G).hom
                (pullback.fst G.hom G.hom) rfl p a)
              (coherentPullback G.hom (G ⊗ G).hom
                (pullback.snd G.hom G.hom) pullback.condition.symm q b))) ∧
      (∀ x y, κ (mulT x y) = mulP (κ x) (κ y)) ∧
      κ (coherentOne G.hom ⊗ₜ[k] coherentOne G.hom) = coherentOne (G ⊗ G).hom ∧
      (∀ n (x : coherentCohomologyDegree G.hom n),
        pullM (coherentInclusion G.hom n x) = coherentInclusion (G ⊗ G).hom n
          (coherentPullback G.hom (G ⊗ G).hom
            (MonObj.mul (X := G)).left (MonObj.mul (X := G)).w n x)) ∧
      Δ = κ.symm.toLinearMap.comp pullM ∧
      (∀ n (x : coherentCohomologyDegree G.hom n),
        Δ (coherentInclusion G.hom n x) ∈ coherentTensorDegree G.hom n) ∧
      Δ (coherentOne G.hom) = coherentOne G.hom ⊗ₜ[k] coherentOne G.hom ∧
      (∀ x y, Δ (mulH x y) = mulT (Δ x) (Δ y)) ∧
      (∀ x, TensorProduct.assoc k _ _ _
          (TensorProduct.map Δ (LinearMap.id) (Δ x)) =
        TensorProduct.map (LinearMap.id) Δ (Δ x)) ∧
      (∀ x, TensorProduct.lid k _ (TensorProduct.map ε (LinearMap.id) (Δ x)) = x ∧
        TensorProduct.rid k _ (TensorProduct.map (LinearMap.id) ε (Δ x)) = x) ∧
      (∀ x : coherentCohomologyDegree G.hom 1,
        Δ (coherentInclusion G.hom 1 x) =
          coherentInclusion G.hom 1 x ⊗ₜ[k] coherentOne G.hom +
            coherentOne G.hom ⊗ₜ[k] coherentInclusion G.hom 1 x) := by
  sorry

end
end AlgebraicGeometry.Scheme.Modules
