/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N8
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceIdealPowerQuotients
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests
public import Sheaf.AlgebraicGeometry.SpaceCotangentRingMap
public import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Ample
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
import WeilConjectures.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import WeilConjectures.RingTheory.AssociatedGradedRing
import WeilConjectures.RingTheory.AssociatedGradedFiniteType
import WeilConjectures.AlgebraicGeometry.GradedSerreVanishing
import WeilConjectures.AlgebraicGeometry.EtaleZariskiQcohComparison

/-! # Uniform vanishing of conormal layers on a proper algebraic space

Source: Stacks Project, Spaces Divisors, Tag 0D39, lemma-ample-on-fibre,
proof, second displayed graded-layer vanishing, with F = O and p = 1
(blueprint: lem-sfb-space-conormal-uniform-vanishing).

The layer is the kernel of O/J^(n+1) -> O/J^n. All kernels, tensors and additive
cohomology are computed on the existing equivalent small affine etale model.
The schematic closed fibre is specified by its cartesian square, not a chosen map.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- The closed point Spec(A/m), as a scheme over Spec A, with its quotient-ring map.
Source: Stacks, Tag 0D39, local-base paragraph
(blueprint: lem-sfb-space-conormal-uniform-vanishing). -/
def conormalClosedPoint (A : Type u) [CommRing A] [IsLocalRing A] :
    Over (Spec (CommRingCat.of A)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))))

/-- The ordinary scheme module corresponding to the tensor pullback to a schematic fibre.
Restriction uses its identity etale chart and hence the canonical Zariski/etale comparison.
Source: Stacks, Tag 0D39 and Descent, Tag 03FH
(blueprint: lem-sfb-space-conormal-uniform-vanishing). -/
def conormalFibreLine {S : Scheme.{u}} {X : AlgebraicSpace S} {T : Over S}
    (i : schemeSpace T ⟶ X) (N : X.Modules) : T.left.Modules :=
  (schemeRestriction (schemeSpace T)
    ⟨CostructuredArrow.mk (𝟙 (yoneda.obj T)),
      ((representable_etale_scheme_tests (S := S)).2.2.2.2.2.2.2.1 T T (𝟙 T)).2
        (inferInstance : Etale (𝟙 T.left))⟩).obj ((moduleTensorPullback i).obj N)

/-- J^n/J^(n+1) is the kernel of the canonical map O/J^(n+1) -> O/J^n.
The quotient tower uses J = I O_X, including J^0 = O_X, and sheaf cokernels.
Source: Stacks, Tag 0D39, short exact sequences following the graded-layer vanishing
(blueprint: lem-sfb-space-conormal-uniform-vanishing). -/
def conormalGradedLayer {A : Type u} [CommRing A]
    (X : AlgebraicSpace (Spec (CommRingCat.of A))) (I : Ideal A) (n : ℕ) :
    X.SmallModules :=
  kernel (X.smallModuleRestriction.map
    ((baseIdealQuotientTower X I (SheafOfModules.unit X.structureSheaf)).transition
      (n + 1) n (Nat.le_succ n)))

/-- The indicated twist of the conormal layer. Degree zero is the structure module;
positive powers and the tensor are exactly the existing sheafified sectionwise tensors.
Source: Stacks, Tag 0D39, second displayed graded-layer vanishing; Modules on Sites, 03EK
(blueprint: lem-sfb-space-conormal-uniform-vanishing). -/
def conormalLayerTwist {A : Type u} [CommRing A]
    (X : AlgebraicSpace (Spec (CommRingCat.of A))) (I : Ideal A)
    (N : X.Modules) (n d : ℕ) : X.SmallModules :=
  (SheafOfModules.monoidalCategory X.smallStructureSheaf).tensorObj
    (conormalGradedLayer X I n)
    (if h : d = 0 then SheafOfModules.unit X.smallStructureRings
     else SheafOfModules.positiveTensorPower X.smallStructureSheaf
       (X.smallModuleRestriction.obj N) d (Nat.pos_of_ne_zero h))

/-- One ample-twist bound kills H^1 of every conormal layer, with no flatness assumption.
Natural indices encode exactly n >= 0 and d >= d0 >= 0 in the node.
The cartesian square specifies the schematic closed fibre; its ordinary pulled-back
line module is the canonical restriction of tensor pullback, not an auxiliary line.
Vanishing is Subsingleton because Mathlib's additive sheaf H^1 is a type.

Source: Stacks Project, Spaces Divisors, Tag 0D39, lemma-ample-on-fibre, proof,
second displayed graded-layer vanishing, F = O_Z and p = 1
(blueprint: lem-sfb-space-conormal-uniform-vanishing).

Proof (the accepted DAG split):
1. Proper base change (lem-sfb-space-proper-base-change) makes the closed fibre proper.
Its scheme properness agrees with MapIsProper by the diagonal, identity-chart and atlas
point-topology tests (def-sfb-space-morphism-properties, def-weil-proper-morphism,
def-a1-space-point-topology). On affine charts the fibre is Spec(R/mR), so its immersion
is closed and affine, with ideal J = m O_Z (lem-weil-pbc-spec-quotient-closed-immersion,
def-weil-closed-immersion).
2. Finite generators of m give finite generators of every J^n. Chart calculations
(lem-weil-pbc-ideal-times-quasi-coherent-affine-sections) identify the sheaf products
and quotients with their ordinary affine modules. Quasi-coherent kernels and colimits
(lem-sfb-space-qcoh-kernels-colimits) and scheme Zariski/etale comparison show that
Q_n = J^n/J^(n+1) is quasi-coherent. Since J Q_n = 0, closed-immersion descent gives
Q_n = i_*G_n with G_n quasi-coherent and G_0 = O_(Z_0)
(lem-sfb-space-closed-immersion-quasi-coherent-modules).
3. The associated graded B = gr_m A is a graded k-algebra of finite type, since m is
finitely generated (lem-weil-pbc-associated-graded-ring-structure and
lem-weil-pbc-associated-graded-finite-type). Pull its associated algebra to Z_0.
4. G = direct sum G_n has the graded B-action given by multiplication of representatives.
Changing either representative changes a product by the next ideal power. These maps
descend uniquely by closed-immersion full faithfulness. On each affine chart,
(mR)^n = m^n R, so G is generated by 1 in degree zero over the pulled-back algebra.
5. Graded Serre vanishing (lem-weil-pbc-formal-systems-graded-vanishing) applied on the
proper scheme Z_0 with its ample line L gives one d0 for H^1(G tensor L^d). Each G_n
is a retract of G, and tensor and cohomology preserve that retraction, so the same bound
kills every H^1(G_n tensor L^d). No infinite-sum cohomology interchange is needed.
The etale/Zariski comparison (lem-sc-etale-zariski-qcoh-comparison and
lem-trf-scheme-zariski-etale-quasi-coherent-equivalence) gives the additive etale vanishing.
6. On a frame e of N, both Q_n tensor N^d and i_*(G_n tensor (i^*N)^d) identify with
Q_n. Under e' = u e both identifications change by u^d, hence glue, also for d = 0.
This is the line-module projection formula on the canonical ringed etale model
(lem-trf-space-enlarged-etale-ringed-site-model, def-trf-space-etale-module-functors).
7. Affine cohomology (lem-sfb-space-affine-cohomology) along the closed immersion i
identifies H^1 on Z with that on Z_0, which vanishes by step 5. The same d0 works for
all n and all d >= d0. Restriction to the small affine model preserves these kernels,
sheaf tensors and underlying additive cohomology by its specified equivalence. -/
theorem conormal_uniform_vanishing
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (X : AlgebraicSpace (Spec (CommRingCat.of A)))
    (g : X ⟶ schemeSpace (Over.mk (𝟙 (Spec (CommRingCat.of A)))))
    (hg : MapIsProper g) (N : X.Modules) (hN : X.IsLineModule N)
    (T : Over (Spec (CommRingCat.of A))) (i : schemeSpace T ⟶ X)
    (p : T ⟶ conormalClosedPoint A)
    (hcart : IsPullback i.hom.hom (yoneda.map p) g.hom.hom
      (yoneda.map (Over.homMk (conormalClosedPoint A).hom :
        conormalClosedPoint A ⟶ Over.mk (𝟙 (Spec (CommRingCat.of A))))))
    [(conormalFibreLine i N).IsInvertible]
    (hample : Scheme.Modules.IsAmple T.left (conormalFibreLine i N)) :
    ∃ d₀ : ℕ, ∀ (n d : ℕ), d₀ ≤ d →
      Subsingleton (Sheaf.H ((SheafOfModules.toSheaf X.smallStructureRings).obj
        (conormalLayerTwist X (IsLocalRing.maximalIdeal A) N n d)) 1) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
