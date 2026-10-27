/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q150
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.Topology.Connected.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Sheaf.AlgebraicGeometry.LinearGroupSchemes
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Mathlib.AlgebraicGeometry.Birational.RationalMap
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.AlgebraicGeometry.DensePoints
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Separated
import Sheaf.AlgebraicGeometry.ClosedPointField
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.CategoryTheory.Yoneda

/-! # Jet actions at a rationally fixed section

Source: Milne, Algebraic Groups (2017), Propositions 8.9 and 8.25, pp.150,154.
(blueprint: lem-sfb-rational-fixed-section-jets)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped TensorProduct MonObj

namespace AlgebraicGeometry.RationalFixedSectionJets

variable {k : Type u} [Field k]

/-- The scalar structure on the stalk is the structure morphism followed by the germ.
Source: Milne, Proposition 8.9 (blueprint: lem-sfb-rational-fixed-section-jets). -/
instance stalkAlgebra (X : Over (Spec (.of k))) (x : X.left) :
    Algebra k (X.left.presheaf.stalk x) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop ≫
    X.left.presheaf.germ ⊤ x trivial).hom.toAlgebra

/-- Q_(n+1) = O_(X,x)/m^(n+2), so n=0 indexes the first jet in the node.
Source: Milne, Proposition 8.9 (blueprint: lem-sfb-rational-fixed-section-jets). -/
abbrev JetRing (X : Over (Spec (.of k))) (x : X.left) (n : ℕ) :=
  (X.left.presheaf.stalk x) ⧸ IsLocalRing.maximalIdeal (X.left.presheaf.stalk x) ^ (n + 2)

/-- The affine scheme of the local quotient, with its canonical scalar structure.
Source: Milne, Proposition 8.9 (blueprint: lem-sfb-rational-fixed-section-jets). -/
def jetScheme (X : Over (Spec (.of k))) (x : X.left) (n : ℕ) : Over (Spec (.of k)) :=
  (Spec (.of (JetRing X x n))).asOver (Spec (.of k))

/-- The canonical morphism of the jet to X, before bundling the base compatibility.
Source: Milne, Proposition 8.9 (blueprint: lem-sfb-rational-fixed-section-jets). -/
def jetInclusion (X : Over (Spec (.of k))) (x : X.left) (n : ℕ) :
    (jetScheme X x n).left ⟶ X.left :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
    (IsLocalRing.maximalIdeal (X.left.presheaf.stalk x) ^ (n + 2)))) ≫
      X.left.fromSpecStalk x

/-- The quotient Q_(n+2) -> Q_(n+1) induced by the inclusion of ordinary ideal powers.
Source: Milne, Proposition 8.9 (blueprint: lem-sfb-rational-fixed-section-jets). -/
def jetTransition (X : Over (Spec (.of k))) (x : X.left) (n : ℕ) :
    JetRing X x (n + 1) →ₐ[k] JetRing X x n :=
  Ideal.Quotient.factorₐ k (Ideal.pow_le_pow_right (Nat.le_succ (n + 2)))

/-- The closed-section map g |-> (g,P) in the scheme fibre product.
Source: Milne, Proposition 8.25 (blueprint: lem-sfb-rational-fixed-section-jets). -/
def sectionMap (G X : Over (Spec (.of k))) (P : 𝟙_ (Over (Spec (.of k))) ⟶ X) :
    G ⟶ G ⊗ X :=
  lift (𝟙 G) (toUnit G ≫ P)

/-- Scalar extension of a jet, with its canonical map to Spec B.
Source: Milne, Proposition 8.9 (blueprint: lem-sfb-rational-fixed-section-jets). -/
def tensorBase (X : Over (Spec (.of k))) (x : X.left) (n : ℕ)
    (B : Type u) [CommRing B] [Algebra k B] :
    (Spec (.of (B ⊗[k] JetRing X x n))).asOver (Spec (.of k)) ⟶
      (Spec (.of B)).asOver (Spec (.of k)) :=
  (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft
    (R := k) (B := JetRing X x n) : B →ₐ[k] B ⊗[k] JetRing X x n).toRingHom)).asOver _

/-- Scalar extension of a jet, with its canonical map to the jet itself.
Source: Milne, Proposition 8.9 (blueprint: lem-sfb-rational-fixed-section-jets). -/
def tensorJet (X : Over (Spec (.of k))) (x : X.left) (n : ℕ)
    (B : Type u) [CommRing B] [Algebra k B] :
    (Spec (.of (B ⊗[k] JetRing X x n))).asOver (Spec (.of k)) ⟶ jetScheme X x n :=
  (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
    (R := k) (A := B) (B := JetRing X x n)).toRingHom)).asOver _

/-- A rational action fixing a rational section induces actions on all finite jets and
compatible algebraic representations with descending closed finite-type kernels.
Source: Milne, Algebraic Groups, Propositions 8.9 and 8.25, pp.150,154
(blueprint: lem-sfb-rational-fixed-section-jets).

Proof:
1. Apply lem-sfb-rational-point-thickenings-base-change: the local quotients are nonzero
finite-dimensional, embed as closed subschemes, and commute with arbitrary base change.
2. On any open of T × X, for T = G^r, the open T × Y is schematically dense: on an affine
chart tensor the injection A -> A_f with the k-vector space of functions on T. The separated
morphism equality lemma extends identities from this dense open. Representatives therefore
glue to the maximal representative f.
3. Smoothness and connectedness make G integral, by lem-weil-pbc-smooth-scheme-over-field-regular
and lem-sc-regular-connected-integral. If V is the open where (g,P) lies in the domain, then
V contains e. For each g in G(k), irreducibility and lem-pc-rational-points-dense give
u,v in V(k) with g=uv.
4. Translate the representative by u and compose with its u-slice. This gives a representative
at (g,P), since both u and v fix P. Maximality extends the domain there. The Jacobson and
closed-point residue-field lemmas imply V=G, including its nonclosed points.
5. The maps (g,x) -> (g,alpha(g,x)) and (g,x) -> (g,alpha(g^-1,x)) are inverse on suitable
opens containing the full section: compare their composites on G × Y and apply separated
morphism equality. They identify the actual section ideals and all their powers.
6. The support of G × X_n is the section, so it lies in these opens. Restrict the preceding
isomorphism to obtain a_n. Compare both sides of the unit and multiplication laws on Y,
extend over the opens, and restrict to the jets. Cancel the closed immersion i_n.
7. For every test scheme the inverse pullback of a_n is an automorphism of its scalar-extended
jet algebra. In a basis it is an invertible matrix, natural in the test scheme. The affine
adjunction and Yoneda give rho_n. Contravariance and inversion give the homomorphism law.
The displayed Spec equation specifies inverse pullback, rather than an arbitrary representation.
8. Preservation of successive ideal powers gives quotient compatibility after every scalar
extension. Apply lem-sc-kernel-subgroup to get the closed subgroup kernels. Their closed
immersions into finite-type G make them finite type. Surjectivity of the tensor-extended
quotient gives K_(n+1) -> K_n on every test algebra; glue using monomorphy. The
closed-immersion factor/ideal-inclusion lemma makes this a closed immersion. -/
theorem rational_fixed_section_jets [IsAlgClosed k]
    (G X Y : Over (Spec (.of k))) [GrpObj G]
    [Smooth G.hom] [ConnectedSpace G.left] [IsSeparated G.hom]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    [IsIntegral X.left] [IsSeparated X.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (j : Y ⟶ X) [IsOpenImmersion j.left] [Nonempty Y.left]
    (hY : DenseRange j.left) [ModObj G Y]
    (f : (G ⊗ X).left.PartialMap X.left)
    (hmax : f.domain = f.toRationalMap.domain)
    (hrestrict : ∃ dY : (G ⊗ Y).left ⟶ f.domain.toScheme,
      dY ≫ f.domain.ι = (G ◁ j).left ∧ dY ≫ f.hom = (γ[G,Y] ≫ j).left)
    (P : 𝟙_ (Over (Spec (.of k))) ⟶ X)
    (he : (sectionMap G X P).left ((η[G]).left (IsLocalRing.closedPoint k)) ∈ f.domain)
    (hfix : ∀ (T : Scheme.{u}) (g : T ⟶ G.left) (d : T ⟶ f.domain.toScheme),
      d ≫ f.domain.ι = g ≫ (sectionMap G X P).left →
        d ≫ f.hom = g ≫ (toUnit G ≫ P).left) :
    (∃ d : G.left ⟶ f.domain.toScheme,
      d ≫ f.domain.ι = (sectionMap G X P).left ∧ d ≫ f.hom = (toUnit G ≫ P).left) ∧
    ∃ (c : ℕ → ℕ)
      (b : ∀ n, Module.Basis (LinearGroupSchemes.Index.{u} (c n)) k
        (JetRing X (P.left (IsLocalRing.closedPoint k)) n))
      (i : ∀ n, jetScheme X (P.left (IsLocalRing.closedPoint k)) n ⟶ X)
      (a : ∀ n, ModObj G (jetScheme X (P.left (IsLocalRing.closedPoint k)) n))
      (ρ : ∀ n, Grp.mk G ⟶ Grp.mk (GeneralLinearGroup
        (LinearGroupSchemes.Index.{u} (c n)) k))
      (r : ∀ (n : ℕ) (B : Type u) [CommRing B] [Algebra k B],
        ((Spec (.of B)).asOver (Spec (.of k)) ⟶ G) →
        (B ⊗[k] JetRing X (P.left (IsLocalRing.closedPoint k)) n) ≃ₐ[B]
          (B ⊗[k] JetRing X (P.left (IsLocalRing.closedPoint k)) n)),
      (∀ n, 0 < c n ∧ Nontrivial (JetRing X (P.left (IsLocalRing.closedPoint k)) n) ∧
        FiniteDimensional k (JetRing X (P.left (IsLocalRing.closedPoint k)) n) ∧
        (i n).left = jetInclusion X (P.left (IsLocalRing.closedPoint k)) n ∧
        IsClosedImmersion (i n).left) ∧
      (∀ n, ∃ dn : (G ⊗ jetScheme X (P.left (IsLocalRing.closedPoint k)) n).left ⟶
          f.domain.toScheme,
        dn ≫ f.domain.ι = (G ◁ i n).left ∧ dn ≫ f.hom = ((a n).smul ≫ i n).left) ∧
      (∀ (n : ℕ) (B : Type u) [CommRing B] [Algebra k B]
          (g : (Spec (.of B)).asOver (Spec (.of k)) ⟶ G),
        LinearMap.toMatrix ((b n).baseChange B) ((b n).baseChange B)
          (r n B g).toLinearMap =
            (GeneralLinearGroup.homMulEquiv (LinearGroupSchemes.Index.{u} (c n)) k B
              (g ≫ (ρ n).hom.hom) :
                Matrix (LinearGroupSchemes.Index.{u} (c n))
                  (LinearGroupSchemes.Index.{u} (c n)) B) ∧
        Spec.map (CommRingCat.ofHom (r n B g).toRingHom) ≫
            (tensorJet X (P.left (IsLocalRing.closedPoint k)) n B).left =
          (lift (tensorBase X (P.left (IsLocalRing.closedPoint k)) n B ≫ g⁻¹)
            (tensorJet X (P.left (IsLocalRing.closedPoint k)) n B) ≫ (a n).smul).left) ∧
      (∀ (n : ℕ) (B : Type u) [CommRing B] [Algebra k B]
          (g : (Spec (.of B)).asOver (Spec (.of k)) ⟶ G)
          (z : B ⊗[k] JetRing X (P.left (IsLocalRing.closedPoint k)) (n + 1)),
        Algebra.TensorProduct.map (AlgHom.id k B)
            (jetTransition X (P.left (IsLocalRing.closedPoint k)) n) (r (n + 1) B g z) =
          r n B g (Algebra.TensorProduct.map (AlgHom.id k B)
            (jetTransition X (P.left (IsLocalRing.closedPoint k)) n) z)) ∧
      (∀ n, IsClosedSubgroupScheme (GrpObj.kerι (ρ n).hom.hom) ∧
        LocallyOfFiniteType (GrpObj.ker (ρ n).hom.hom).hom ∧
        QuasiCompact (GrpObj.ker (ρ n).hom.hom).hom) ∧
      (∀ n, ∃ t : GrpObj.ker (ρ (n + 1)).hom.hom ⟶ GrpObj.ker (ρ n).hom.hom,
        IsClosedImmersion t.left ∧
          t ≫ GrpObj.kerι (ρ n).hom.hom = GrpObj.kerι (ρ (n + 1)).hom.hom) := by
  sorry

end AlgebraicGeometry.RationalFixedSectionJets
