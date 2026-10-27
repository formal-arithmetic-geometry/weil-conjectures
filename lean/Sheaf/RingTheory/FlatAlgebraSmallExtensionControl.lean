module

public import Sheaf.RingTheory.FlatAlgebraLiftingData
public import Sheaf.RingTheory.CotangentTransitivityTriangle
import Sheaf.RingTheory.CotangentFlatBaseChange
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.Flat.Basic
import Sheaf.RingTheory.NilpotentIdealFlatnessCriterion
import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import Sheaf.TraceFormula.OnePointDerivedRingIdentification
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Sheaf.RingTheory.NaiveCotangentComparison
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.CategoryTheory.Triangulated.TStructure.Basic
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.Stability

/-!
# Cotangent obstruction and marked flat lifts across a small base extension

Source: Stacks Project, cotangent.tex, Tags 08SP, 08QQ and 08SF; algebra.tex,
Tag 051C; defos.tex, Tag 08S7
(blueprint: lem-sfb-flat-algebra-small-extension-control).

Obstructions and actions are supplied simultaneously for every flat algebra.
Localization maps are characterized by the actual standard cotangent and
coefficient maps, and localized lift classes by actual localizations of algebras.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Simplicial
open scoped TensorProduct ChangeOfRings

namespace Algebra.FlatLifting

/-- The ordinary special-fibre square commutes by tensor balancing.
Source: Stacks, Tag 08QQ (blueprint: lem-sfb-flat-algebra-small-extension-control).
Proof: on c in C the equality is ε(c) tensor 1 = 1 tensor c, exactly the
balancing relation of the tensor product k tensor_C B. -/
theorem specialFibreSquare_condition {k : Type u} [Field k] (D : Base k)
    (B : CommAlgCat.{u} D.thin) :
    CommRingCat.ofHom D.thinResidue.toRingHom ≫
        CommRingCat.ofHom (algebraMap k (fibre D B)) =
      CommRingCat.ofHom (algebraMap D.thin B) ≫ CommRingCat.ofHom (reduction D B) := by
  sorry

/-- The actual base-change square from C → B to k → P.
Source: Stacks, Tag 08QQ (blueprint: lem-sfb-flat-algebra-small-extension-control). -/
def specialFibreSquare {k : Type u} [Field k] (D : Base k)
    (B : CommAlgCat.{u} D.thin) :
    Arrow.mk (CommRingCat.ofHom (algebraMap D.thin B)) ⟶
      Arrow.mk (CommRingCat.ofHom (algebraMap k (fibre D B))) :=
  Arrow.homMk' (CommRingCat.ofHom D.thinResidue.toRingHom)
    (CommRingCat.ofHom (reduction D B)) (specialFibreSquare_condition D B)

/-- The coefficient module restricted to B, with its prescribed special-fibre action.
Source: Stacks, Tag 08SP (blueprint: lem-sfb-flat-algebra-small-extension-control). -/
noncomputable def coefficientOverBase {k : Type u} [Field k] (D : Base k)
    (B : CommAlgCat.{u} D.thin) : ModuleCat.{u} B :=
  (ModuleCat.restrictScalars (reduction D B)).obj (coefficient D B)

/-- The source's connecting-class normalization of the obstruction. A lift t of
standard polynomial generators to C' evaluates the difference of the two faces
in I. The degree minus one formula is its extension cocycle. The connecting
image is compared with the stated obstruction via the actual base-change square.
Source: Stacks, proof of Tag 08SP and defos.tex Tag 0GPU
(blueprint: lem-sfb-flat-algebra-small-extension-control). -/
def IsConnectingObstruction
    [dc : ∀ R : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} R)]
    (K : CotangentResolution.Coherence.{u}) {k : Type u} [Field k]
    (D : Base k) (B : CommAlgCat.{u} D.thin) (o : T K D B 2) : Prop :=
  letI := dc (CommRingCat.of B)
  letI := dc (CommRingCat.of (fibre D B))
  ∃ t : (K.standard (Arrow.mk (CommRingCat.ofHom D.quotient.toRingHom))).algebra.obj
      (Opposite.op ⦋0⦌) →+* D.thick,
    (t.comp ((K.standard (Arrow.mk (CommRingCat.ofHom D.quotient.toRingHom))).base.app
      (Opposite.op ⦋0⦌)).hom = RingHom.id D.thick) ∧
    (D.quotient.toRingHom.comp t =
      ((K.standard (Arrow.mk (CommRingCat.ofHom D.quotient.toRingHom))).augmentation.app
        (Opposite.op ⦋0⦌)).hom) ∧
    ∃ z : CotangentResolution.transitivityFirstComplex K
        (CommRingCat.ofHom D.quotient.toRingHom) (CommRingCat.ofHom (algebraMap D.thin B)) ⟶
      (CochainComplex.singleFunctor (ModuleCat.{u} B) (-1)).obj (coefficientOverBase D B),
    (∀ (b : B) (c : D.thin)
      (x : (K.standard (Arrow.mk (CommRingCat.ofHom D.quotient.toRingHom))).algebra.obj
        (Opposite.op ⦋1⦌)) (i : ideal D),
      t ((K.standard (Arrow.mk (CommRingCat.ofHom D.quotient.toRingHom))).algebra.δ
          (0 : Fin 2) x -
        (K.standard (Arrow.mk (CommRingCat.ofHom D.quotient.toRingHom))).algebra.δ
          (1 : Fin 2) x) = i.val →
      (HomologicalComplex.singleObjXSelf (.up ℤ) (-1) (coefficientOverBase D B)).hom
        (z.f (-1) (b ⊗ₜ[D.thin, algebraMap D.thin B]
          CotangentResolution.complexGenerator
            (K.differentials (K.standard
              (Arrow.mk (CommRingCat.ofHom D.quotient.toRingHom)))) 1 c x)) =
        (reduction D B b * algebraMap k (fibre D B) (D.thinResidue c)) ⊗ₜ[k] i) ∧
    ∃ δ : CotangentResolution.cotangentComplex K
        (Arrow.mk (CommRingCat.ofHom (algebraMap D.thin B))) ⟶
      (DerivedCategory.Q.obj (CotangentResolution.transitivityFirstComplex K
        (CommRingCat.ofHom D.quotient.toRingHom)
        (CommRingCat.ofHom (algebraMap D.thin B))))⟦(1 : ℤ)⟧,
      CotangentResolution.transitivityTriangle K
          (CommRingCat.ofHom D.quotient.toRingHom)
          (CommRingCat.ofHom (algebraMap D.thin B)) δ ∈
        distTriang (DerivedCategory (ModuleCat.{u} B)) ∧
      CotangentResolution.cotangentMap K (specialFibreSquare D B) ≫
          (ModuleCat.restrictScalars (reduction D B)).mapDerivedCategory.map o ≫
          ((ModuleCat.restrictScalars (reduction D B)).mapDerivedCategory.commShiftIso
            (2 : ℤ)).hom.app _ ≫
          ((ModuleCat.restrictScalars (reduction D B)).mapDerivedCategorySingleFunctor
            0).hom.app (coefficient D B)⟦(2 : ℤ)⟧' =
        δ ≫ (DerivedCategory.Q.map z ≫
          ((DerivedCategory.singleFunctors (ModuleCat.{u} B)).shiftIso
            1 (-1) 0 (add_neg_cancel (1 : ℤ))).inv.app (coefficientOverBase D B))⟦(1 : ℤ)⟧' ≫
          (shiftFunctorAdd (DerivedCategory (ModuleCat.{u} B)) (1 : ℤ) (1 : ℤ)).inv.app _

/-- The canonical obstruction vanishes precisely when a marked flat lift exists;
when nonempty the marked lift classes form a torsor under T¹. Both constructions
commute with every localization, including the zero localization. No finite-type,
isolated-singularity or complete-intersection hypothesis occurs.

Source: Stacks, Tags 08SP, 08QQ, 08SF, 051C and 08S7
(blueprint: lem-sfb-flat-algebra-small-extension-control).

Proof (the ten steps of the reviewed DAG):
1. The augmentation places I inside the maximal ideal, so I² = 0. Its action
factors through k. Tensor over the quotient and interchange factors to identify
I tensor_C B with P tensor_k I, by lem-weil-pbc-tensor-over-quotient-ring.
2. Tensor the base extension with a flat lift. Exactness
(lem-weil-pbc-flat-tensor-exact) canonically identifies its square-zero kernel
with N by i tensor b mapping to i times a lift of b. Marking-preserving maps
fix this identification.
3. Conversely a square-zero solution has IE = N and quotient B. Its ideal
multiplication map is injective. Apply lem-sfb-nilpotent-ideal-flatness-criterion
with exponent two. This gives a marked flat lift, inverse to step 2.
4. By lem-sfb-ring-square-zero-extension-classification the base extension gives
its canonical degree-one class xi. Push it along i mapping to 1 tensor i.
Solutions are exactly the fibre of restriction over this pushed-forward class;
the thick-base structure map is forced, with no extra choice of marking.
5. Use lem-pur-sheaf-ring-derived-coefficient-adjunction and
lem-trf-one-point-derived-ring-identification for ordinary modules. The
transitivity triangle (lem-trf-cotangent-transitivity-triangle) has first term
A0 = L_{C/C'} tensor_C^L B, middle L_{B/C'}, and third L_{B/C}.
6. Define the obstruction as the connecting image eta[1] composed with the
boundary. Hom exactness (lem-weil-pbc-hom-out-of-triangle-exact) identifies its
vanishing with the nonempty class fibre. Differences of solutions are obtained
by precomposition with the triangle's second arrow.
7. The empty-variable presentation and lem-trf-lci-naive-cotangent-model give
H⁰(L_{C/C'}) = 0. Nonpositivity and
lem-pc-derived-tstructure-orthogonality imply Hom(A0,N) = 0. Rotated Hom
exactness therefore makes that difference class unique. Addition in the fibre
gives the zero and addition laws and simple transitivity on marked lift classes.
8. Flatness of B identifies B tensor_C^L k with P, computed by B[0] and its
ordinary tensor augmentation (lem-trf-flat-resolution-canonical-tensor-comparison).
Apply lem-trf-cotangent-flat-base-change and the adjunction from step 5 to
transport the obstruction and action to the displayed full cotangent groups Tʲ.
9. Localize at the inverse image of S in B and every lift. Exact localization
(lem-weil-pbc-localization-module-exact) identifies the kernel with S inverse N.
Localization flatness and lem-pc-module-flat-transitive preserve base flatness.
The localized maps retain the given marking. If zero belongs to S, every
localized algebra and module is zero and the same argument applies.
10. Functoriality of extension classes, the natural transitivity triangle, and
lem-trf-cotangent-augmentation-localization carry eta[1]d to eta_S[1]d_S
and z + t v to z_S + t_S v_S. Adjunction identifies the induced group maps
with the uniquely characterized maps IsLocalizedClass. Thus obstruction and
action commute with localization, without asserting that localized Ext is Ext
of the localization. Universal localization gives the class map on marked
lifts and retains the reduction on their allowed isomorphisms. -/
theorem exists_smallExtensionControl
    [∀ R : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} R)]
    (K : CotangentResolution.Coherence.{u})
    (k : Type u) [Field k] (D : Base k) :
    ∃ obstruction : ∀ (B : CommAlgCat.{u} D.thin), Module.Flat D.thin B → T K D B 2,
    ∃ action : ∀ (B : CommAlgCat.{u} D.thin), Module.Flat D.thin B →
        T K D B 1 → Classes D B → Classes D B,
      (∀ (B : CommAlgCat.{u} D.thin) (hB : Module.Flat D.thin B),
        IsConnectingObstruction K D B (obstruction B hB) ∧
        (obstruction B hB = 0 ↔ Nonempty (Classes D B)) ∧
        (∀ x : Classes D B, action B hB 0 x = x) ∧
        (∀ (t v : T K D B 1) (x : Classes D B),
          action B hB (t + v) x = action B hB t (action B hB v x)) ∧
        (∀ x y : Classes D B, ∃! t : T K D B 1, action B hB t x = y)) ∧
      (∀ (B : CommAlgCat.{u} D.thin) (hB : Module.Flat D.thin B)
        (S : Submonoid (fibre D B)) (U : CommAlgCat.{u} D.thin)
        (f : B →ₐ[D.thin] U)
        (_hf : @IsLocalization B _ (S.comap (reduction D B).toMonoidHom)
          U _ f.toRingHom.toAlgebra),
        ∃ hU : Module.Flat D.thin U,
        ∃ groupMap : ∀ j : ℤ, T K D B j →+ T K D U j,
        ∃ liftMap : Classes D B → Classes D U,
          (∀ (j : ℤ) (t : T K D B j),
            IsLocalizedClass K D f j t (groupMap j t) ∧
              ∀ v : T K D U j, IsLocalizedClass K D f j t v → v = groupMap j t) ∧
          (∀ E : Lift D B, ∃ F : Lift D U,
            IsLocalizedLift S f E F ∧ liftMap (classOf E) = classOf F) ∧
          (∀ (E : Lift D B) (F : Lift D U),
            IsLocalizedLift S f E F → liftMap (classOf E) = classOf F) ∧
          groupMap 2 (obstruction B hB) = obstruction U hU ∧
          (∀ (t : T K D B 1) (x : Classes D B),
            liftMap (action B hB t x) = action U hU (groupMap 1 t) (liftMap x))) := by
  sorry

end Algebra.FlatLifting
