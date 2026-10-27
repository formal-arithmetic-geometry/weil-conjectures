/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O4
-/
module

public import Sheaf.AlgebraicGeometry.RingDiagonalizableGroup
public import Sheaf.AlgebraicGeometry.EquivariantCoherentGZero
public import Sheaf.AlgebraicGeometry.SchemeGroupoidModule
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.LinearAlgebra.TensorProduct.Associator
import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.RingHom.Flat

/-! # The normalized Laurent coaction on sections of a linearized line

Source: Stacks Project, coherent.tex, Tag 02KH, lemma-flat-base-change-cohomology,
degree zero, with the inverse-action construction in the DAG proof.
(blueprint: lem-sfb-relative-linearized-line-sections-coaction).

The normalization is written after pullback to arbitrary test schemes. At (g,x) it
says ev_g(c(s))(gx) = theta_(g,x)(s(x)). Substitution x = g⁻¹y gives precisely
(g · s)(y) = theta_(g,g⁻¹y)(s(g⁻¹y)). These are equalities of sections of actual
pulled-back module sheaves, including on nonreduced and nonflat test schemes.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.RelativeLinearizedLineSections

variable (A : Type u) [CommRing A] (r : ℕ)

/-- The Laurent algebra on the rank-r character lattice, including r = 0.
Source: the Laurent basis in the node, Stacks 02KH
(blueprint: lem-sfb-relative-linearized-line-sections-coaction). -/
abbrev Coordinate := AddMonoidAlgebra A (ULift.{u} (Fin r → ℤ))

/-- The existing Hopf spectrum of that Laurent algebra, over Spec A.
Source: the Laurent torus in the node; Conrad, Appendix B.1
(blueprint: lem-sfb-relative-linearized-line-sections-coaction). -/
abbrev torus : Grp (Over (Spec (.of A))) :=
  ringDiagonalizableGroup A (ULift.{u} (Fin r → ℤ))

/-- Global sections with scalars restricted along the given structure map.
This is the actual module Γ(X,L), with no finiteness requirement.
Source: Stacks 02KH, degree zero
(blueprint: lem-sfb-relative-linearized-line-sections-coaction). -/
def sections (X : Over (Spec (.of A))) (L : X.left.Modules) : ModuleCat A :=
  (ModuleCat.restrictScalars
    (((Scheme.ΓSpecIso (.of A)).inv ≫ X.hom.appTop).hom)).obj
      (ModuleCat.of Γ(X.left, ⊤) Γ(L, ⊤))

/-- Pullback of a section by the section-normalized tensor adjunction, restricted
from the preimage of top to top. This is the canonical section 1 tensor s.
Source: Stacks 0096 and 02KH
(blueprint: lem-sfb-relative-linearized-line-sections-coaction). -/
def pullSection {Y X : Scheme.{u}} (f : Y ⟶ X) (L : X.Modules) (s : Γ(L, ⊤)) :
    Γ((Scheme.Modules.tensorPullback f).obj L, ⊤) :=
  ((Scheme.Modules.tensorPullback f).obj L).presheaf.map
    (homOfLE f.preimage_top.ge).op
      ((Scheme.Modules.tensorPullbackSectionAdjunction f).unit.app L |>.app ⊤ <| s)

variable {A r} {X : Over (Spec (.of A))} [ModObj (torus A r).X X]

/-- Pullback of the forward linearization along an arbitrary test arrow, using
only the canonical section-normalized composition comparisons. It maps the
pullback by x to the pullback by gx, as actual module sheaves.
Source: the explicit linearization in the node, Stacks 0097
(blueprint: lem-sfb-relative-linearized-line-sections-coaction). -/
def thetaAt (L : X.left.Modules)
    (theta : (Scheme.groupoidModulePullback
        (EquivariantCoherent.source (torus A r).X X)).obj L ≅
      (Scheme.groupoidModulePullback
        (EquivariantCoherent.target (torus A r).X X)).obj L)
    (W : Over (Spec (.of A))) (j : W ⟶ (torus A r).X ⊗ X) :
    (Scheme.Modules.tensorPullback
      (j.left ≫ EquivariantCoherent.source (torus A r).X X)).obj L ≅
    (Scheme.Modules.tensorPullback
      (j.left ≫ EquivariantCoherent.target (torus A r).X X)).obj L :=
  (Scheme.Modules.tensorPullbackSectionComp j.left
    (EquivariantCoherent.source (torus A r).X X)).app L ≪≫
  (Scheme.Modules.tensorPullback j.left).mapIso
    ((EquivariantCoherent.pullbackIso _).symm.app L ≪≫ theta ≪≫
      (EquivariantCoherent.pullbackIso _).app L) ≪≫
  (Scheme.Modules.tensorPullbackSectionComp j.left
    (EquivariantCoherent.target (torus A r).X X)).symm.app L

/-- Evaluate a Laurent coefficient along the group coordinate of a test arrow.
On t^m this is the product of the m-th powers of the invertible coordinates.
Source: the explicit evaluation map in the node, Stacks 022U
(blueprint: lem-sfb-relative-linearized-line-sections-coaction). -/
def coefficientAt (W : Over (Spec (.of A))) (j : W ⟶ (torus A r).X ⊗ X)
    (f : Coordinate A r) : Γ(W.left, ⊤) :=
  (j ≫ fst (torus A r).X X).left.appTop
    ((Scheme.ΓSpecIso (.of (Coordinate A r))).inv f)

/-- A linearized invertible module has a counital, coassociative A-linear Laurent
coaction on its actual global sections, with the forward action normalization.
The model D only presents the given action groupoid; its composition is pinned
by its group-coordinate identity. The unit and cocycle use canonical pullbacks.
The normalization is expressed on every test scheme and every finite tensor
presentation, so it asserts an equality of sections, not of geometric fibres.
Its one-term specialization is the stated weight formula. In particular it can
be pulled back along (g,g⁻¹x) on X_B for any commutative A-algebra B; no assertion
that section base change is invertible for such B is made.

Source: Stacks Project, coherent.tex, Tag 02KH, degree zero, and the explicit
inverse-action section construction in the node.
(blueprint: lem-sfb-relative-linearized-line-sections-coaction).

Proof:
1. Finite type gives quasi-compactness (def-weil-finite-type-morphism), and
separatedness gives quasi-separatedness (lem-pc-separated-quasi-separated).
The line is quasi-coherent (def-sc-invertible-module). Both C and C tensor C
are free A-modules on their Laurent bases; tensoring preserves injections, so
their structural ring maps are flat (def-weil-pbc-flat-ring-map), and so are
the maps of spectra (lem-weil-pbc-flat-ring-map-iff-flat-affine).
2. The canonical section map beta_B sends s tensor b to b p_B^*s. It is an
isomorphism for B = C and C tensor C by lem-pc-flat-base-change-cohom (02KH).
For every algebra map B → B', the formula on pure tensors proves naturality,
without needing flatness or invertibility of beta_B' (def-pc-module-pullback).
3. On Y = T times X set q(g,x) = g⁻¹x and b(g,x) = (g,g⁻¹x), using the fibre
product (def-pc-fibre-product). The action identities give ab = p and pb = q.
Pull theta back by b to obtain lambda : q^*L ≅ p^*L. Define K(s) = lambda(q^*s)
and c(s) = beta_C⁻¹(K(s)). All these maps respect A, giving A-linearity.
4. Pull this identity back along (g,p_B): X_B → Y for any B, using naturality
of beta. It gives beta_B(ev_g(c(s))) = theta_(g,g⁻¹x)(s_B(g⁻¹x)). The displayed
normalization is the same equality after the action automorphism, written on
an arbitrary test arrow (g,x). It is an equality of pulled-back sheaf sections.
5. Pull the cocycle back at (g,h,h⁻¹g⁻¹x). It gives g·(h·v) = (gh)·v for
arbitrary sections v after any base change; the unit gives 1·v = v. These
operators are B-linear, since all maps and sheaf isomorphisms are over B.
6. Over D = C tensor C use the universal points g,h and finite expansions
c(s) = sum s_i tensor f_i, c(s_i) = sum s_ij tensor f_ij. Applying the preceding
formula twice identifies beta_D((c tensor 1)c(s)) with g·(h·s_D), and applying
it at gh identifies beta_D((1 tensor Delta)c(s)) with (gh)·s_D. Injectivity of
beta_D (lem-pc-flat-base-change-cohom) gives coassociativity.
7. Set B = A and g = 1 to get the counit law. A one-term Laurent expansion
gives the weight formula. Only beta_C and beta_D were inverted, and both are
flat cases. The construction covers empty X, zero A, r = 0 and arbitrary torsion.
-/
theorem exists_normalized_coaction
    (A : Type u) [CommRing A] (r : ℕ)
    (X : Over (Spec (.of A))) [ModObj (torus A r).X X]
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (L : X.left.Modules) [L.IsInvertible]
    (D : EquivariantCoherent.ActionGroupoidModel (torus A r).X X)
    (theta : (Scheme.groupoidModulePullback
        (EquivariantCoherent.source (torus A r).X X)).obj L ≅
      (Scheme.groupoidModulePullback
        (EquivariantCoherent.target (torus A r).X X)).obj L)
    (hunit : Scheme.groupoidModuleUnitLaw
      (EquivariantCoherent.source (torus A r).X X)
      (EquivariantCoherent.target (torus A r).X X)
      (EquivariantCoherent.identityArrow (torus A r).X X)
      D.laws.source_id D.laws.target_id L theta.symm)
    (hcocycle : Scheme.groupoidModuleCocycleLaw
      (EquivariantCoherent.source (torus A r).X X)
      (EquivariantCoherent.target (torus A r).X X) D.comp
      D.laws.source_comp D.laws.target_comp L theta.symm) :
    ∃ c : sections A X L →ₗ[A] (sections A X L ⊗[A] Coordinate A r),
      (∀ s : sections A X L,
        (TensorProduct.assoc A (sections A X L) (Coordinate A r) (Coordinate A r))
            ((LinearMap.rTensor (Coordinate A r) c) (c s)) =
          TensorProduct.map (LinearMap.id : sections A X L →ₗ[A] sections A X L)
            (Coalgebra.comul : Coordinate A r →ₗ[A]
              Coordinate A r ⊗[A] Coordinate A r) (c s)) ∧
      (∀ s : sections A X L,
        (TensorProduct.rid A (sections A X L))
          (TensorProduct.map (LinearMap.id : sections A X L →ₗ[A] sections A X L)
            (Coalgebra.counit : Coordinate A r →ₗ[A] A) (c s)) = s) ∧
      (∀ (W : Over (Spec (.of A))) (j : W ⟶ (torus A r).X ⊗ X)
        (s : sections A X L) (n : ℕ)
        (v : Fin n → sections A X L) (f : Fin n → Coordinate A r),
        c s = ∑ i, v i ⊗ₜ[A] f i →
          ∑ i, coefficientAt W j (f i) •
            pullSection (j.left ≫ EquivariantCoherent.target (torus A r).X X) L (v i) =
          (thetaAt L theta W j).hom.app ⊤
            (pullSection (j.left ≫ EquivariantCoherent.source (torus A r).X X) L s)) ∧
      (∀ (s : sections A X L) (m : Fin r → ℤ),
        c s = s ⊗ₜ[A] (AddMonoidAlgebra.single (ULift.up m) 1) →
        ∀ (W : Over (Spec (.of A))) (j : W ⟶ (torus A r).X ⊗ X),
          (thetaAt L theta W j).hom.app ⊤
              (pullSection (j.left ≫ EquivariantCoherent.source (torus A r).X X) L s) =
            coefficientAt W j (AddMonoidAlgebra.single (ULift.up m) 1) •
              pullSection (j.left ≫ EquivariantCoherent.target (torus A r).X X) L s) := by
  sorry

end AlgebraicGeometry.RelativeLinearizedLineSections
