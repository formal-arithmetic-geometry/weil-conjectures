module

public import Sheaf.AlgebraicGeometry.NodalGeometricFibres
public import Sheaf.AlgebraicGeometry.PinchingLineData
public import Sheaf.AlgebraicGeometry.ReducedNormalization
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.Picard.Group
public import WeilConjectures.AlgebraicGeometry.Modules.Endomorphism
public import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_
import Sheaf.AlgebraicGeometry.FinitePinchingInvertiblePatching
import Sheaf.AlgebraicGeometry.SmoothConnectedCurveLocalRings
import WeilConjectures.AlgebraicGeometry.GlobalSectionsProper
import WeilConjectures.AlgebraicGeometry.GlobalSectionsBijective
import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-! # The normalization sequence of a proper nodal curve

Source: Stacks Project, curves.tex, Tag 0C1M and Example 0C1J;
pic.tex, Tag 0BA0; groupoids.tex, Tag 049C.
(blueprint: lem-sfb-nodal-normalization-picard-sequence).

The structures below package the clauses of this one statement. All groups of sections
are evaluated on arbitrary schemes, including nonreduced schemes. Covering sieves express
images as images of fppf sheaves, rather than images on geometric points.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.MonObj
namespace AlgebraicGeometry
namespace NodalNormalizationPicard

/-- A normalized irreducible component, with its canonical map to the curve.
Source: Stacks, Tag 0C1M (blueprint: lem-sfb-nodal-normalization-picard-sequence). -/
noncomputable def componentMap (C : Scheme.{u}) (i : irreducibleComponents C) :
    (C.reducedNormalizationComponent i).normalization ⟶ C :=
  Sigma.ι (fun j : irreducibleComponents C ↦
    (C.reducedNormalizationComponent j).normalization) i ≫ C.fromReducedNormalization

/-- The component as a scheme over the ground field.
Source: Stacks, Tag 0C1M (blueprint: lem-sfb-nodal-normalization-picard-sequence). -/
noncomputable def component {k : Type u} [Field k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) (i : irreducibleComponents C) : Over (Spec (.of k)) :=
  Over.mk (componentMap C i ≫ f)

/-- The actual nonsmooth points are the nodes; they are not an arbitrary indexing set.
Source: Stacks, Tag 0C1M (blueprint: lem-sfb-nodal-normalization-picard-sequence). -/
abbrev Nodes {k : Type u} [Field k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
    [LocallyOfFinitePresentation f] :=
  {x : C // x ∉ f.smoothLocus}

/-- The geometric clauses of the normalization assertion, with an ordering of both branches.
The two points exhaust the normalization fibre, and their component indices may coincide.
Source: Stacks, Tags 0C1M and 0C1J
(blueprint: lem-sfb-nodal-normalization-picard-sequence). -/
structure Branches {k : Type u} [Field k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
    [LocallyOfFinitePresentation f] where
  finite_components : Finite (irreducibleComponents C)
  finite_nodes : Finite (Nodes f)
  smooth : ∀ i, Smooth (component f i).hom
  relative_dimension : ∀ i, SmoothOfRelativeDimension 1 (component f i).hom
  projective : ∀ i, IsProjective (component f i).hom
  connected : ∀ i, ConnectedSpace (component f i).left
  curve : ∀ i, IsCurve (component f i).hom
  proper : ∀ i, IsProper (component f i).hom
  geometricallyIntegral : ∀ i, GeometricallyIntegral (component f i).hom
  index : Nodes f → Fin 2 → irreducibleComponents C
  point : ∀ (e : Nodes f) (a : Fin 2), Spec (.of k) ⟶ (component f (index e a)).left
  section_eq : ∀ e a, point e a ≫ (component f (index e a)).hom = 𝟙 _
  same_node : ∀ e, point e 0 ≫ componentMap C (index e 0) =
    point e 1 ≫ componentMap C (index e 1)
  image : ∀ e a, (point e a ≫ componentMap C (index e a)) (IsLocalRing.closedPoint k) = e.1
  distinct : ∀ e,
    (point e 0 ≫ Sigma.ι (fun i : irreducibleComponents C ↦
      (C.reducedNormalizationComponent i).normalization) (index e 0))
        (IsLocalRing.closedPoint k) ≠
    (point e 1 ≫ Sigma.ι (fun i : irreducibleComponents C ↦
      (C.reducedNormalizationComponent i).normalization) (index e 1))
        (IsLocalRing.closedPoint k)
  exhaustive : ∀ (e : Nodes f) (y : C.reducedNormalization),
    C.fromReducedNormalization y = e.1 ↔ ∃ a : Fin 2,
      y = (point e a ≫ Sigma.ι (fun i : irreducibleComponents C ↦
        (C.reducedNormalizationComponent i).normalization) (index e a))
          (IsLocalRing.closedPoint k)


/-- The branch map after an arbitrary base change.
Source: Stacks, Tag 0C1J (blueprint: lem-sfb-nodal-normalization-picard-sequence). -/
noncomputable abbrev branchSection {k : Type u} [Field k] {C : Scheme.{u}}
    {f : C ⟶ Spec (.of k)} [LocallyOfFinitePresentation f]
    (N : Branches f) (T : Over (Spec (.of k)))
    (e : Nodes f) (a : Fin 2) :=
  sectionBaseChange (component f (N.index e a)).hom (N.point e a) (N.section_eq e a) T

/-- The canonical map from the base-changed normalized component to the base-changed curve.
Source: Stacks, Tag 0C1J (blueprint: lem-sfb-nodal-normalization-picard-sequence). -/
noncomputable abbrev componentBaseMap {k : Type u} [Field k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) (T : Over (Spec (.of k))) (i : irreducibleComponents C) :=
  Scheme.Modules.pinchingBaseMap f (componentMap C i) T.hom

/-- The frame of a line bundle pulled all the way back to one branch copy of the base.
Source: Stacks, Tag 0C1J (blueprint: lem-sfb-nodal-normalization-picard-sequence). -/
noncomputable def branchFrame {k : Type u} [Field k] {C : Scheme.{u}}
    {f : C ⟶ Spec (.of k)} [LocallyOfFinitePresentation f]
    (N : Branches f) (T : Over (Spec (.of k)))
    (L : (pullback f T.hom).Modules)
    (frames : ∀ i, (Scheme.Modules.pullback (componentBaseMap f T i)).obj L ≅
      𝟙_ (pullback (component f i).hom T.hom).Modules) (e : Nodes f) (a : Fin 2) :
    (Scheme.Modules.pullback
      (branchSection N T e a ≫ componentBaseMap f T (N.index e a))).obj L ≅
      𝟙_ T.left.Modules :=
  ((Scheme.Modules.pullbackComp _ _).app L).symm ≪≫
    (Scheme.Modules.pullback (branchSection N T e a)).mapIso (frames (N.index e a)) ≪≫
      Scheme.Modules.pullbackObjUnitIso (branchSection N T e a)

/-- What it means for given parameters to glue trivial component lines. Equality of the two
branch maps is kept explicitly, so the comparison uses the canonical pullback congruence.
Source: Stacks, Tags 0C1J and 0C1M
(blueprint: lem-sfb-nodal-normalization-picard-sequence). -/
def Glues {k : Type u} [Field k] {C : Scheme.{u}} {f : C ⟶ Spec (.of k)}
    [LocallyOfFinitePresentation f]
    (N : Branches f) (T : Over (Spec (.of k)))
    (z : Nodes f → Γ(T.left, ⊤)ˣ) (L : (pullback f T.hom).Modules) : Prop :=
  ∃ frames : ∀ i, (Scheme.Modules.pullback (componentBaseMap f T i)).obj L ≅
      𝟙_ (pullback (component f i).hom T.hom).Modules,
    ∀ e : Nodes f, ∃ h :
      branchSection N T e 0 ≫ componentBaseMap f T (N.index e 0) =
        branchSection N T e 1 ≫ componentBaseMap f T (N.index e 1),
      ((Scheme.Modules.pullbackCongr h).app L).hom ≫
          (branchFrame N T L frames e 1).hom =
        (branchFrame N T L frames e 0).hom ≫
          (𝟙_ T.left.Modules).smulHom (z e : Γ(T.left, ⊤))

/-- The exact sequence, its geometric quotient, and its inverse image over the Jacobian product.
The families of homomorphisms and their naturality equations are the componentwise form of
morphisms of group-valued functors. `quotient_kernel` and `quotient_epi` characterize the
sheaf cokernel; `inverse_image` identifies the actual inverse-image subsheaf. Local sections
and unique translation on each fibre express an fppf torsor, including its specified action.
Source: Stacks, Tags 0C1M, 0BA0 and 049C
(blueprint: lem-sfb-nodal-normalization-picard-sequence). -/
structure Sequence {k : Type u} [Field k] {C : Scheme.{u}} {f : C ⟶ Spec (.of k)}
    [LocallyOfFinitePresentation f] (N : Branches f) where
  glue : ∀ T : Over (Spec (.of k)),
    (Nodes f → Γ(T.left, ⊤)ˣ) →* (picardFunctorGrp f).obj (.op T)
  glue_natural : ∀ (T V : Over (Spec (.of k))) (h : V ⟶ T) (z : Nodes f → Γ(T.left, ⊤)ˣ),
    (picardFunctorGrp f).map h.op (glue T z) =
      glue V (fun e ↦ Units.map h.left.appTop.hom.toMonoidHom (z e))
  glue_spec : ∀ (T : Over (Spec (.of k))) (z : Nodes f → Γ(T.left, ⊤)ˣ),
    ∃ (L : (pullback f T.hom).Modules) (hL : L.IsInvertible),
      Glues N T z L ∧
      glue T z = (toPicardFunctor f).app (.op T) (@Scheme.Pic.ofIsInvertible _ L hL)
  restrict : ∀ T : Over (Spec (.of k)), (picardFunctorGrp f).obj (.op T) →*
    (∀ i : irreducibleComponents C, (picardFunctorGrp (component f i).hom).obj (.op T))
  restrict_natural : ∀ (T V : Over (Spec (.of k))) (h : V ⟶ T)
    (x : (picardFunctorGrp f).obj (.op T)) (i : irreducibleComponents C),
    restrict V ((picardFunctorGrp f).map h.op x) i =
      (picardFunctorGrp (component f i).hom).map h.op (restrict T x i)
  restrict_spec : ∀ (T : Over (Spec (.of k))) (L : (pullback f T.hom).Pic)
    (i : irreducibleComponents C),
    restrict T ((toPicardFunctor f).app (.op T) L) i =
      (toPicardFunctor (component f i).hom).app (.op T)
        (Scheme.Pic.map (componentBaseMap f T i) L)
  commutative : ∀ (T : Over (Spec (.of k))) (x y : (picardFunctorGrp f).obj (.op T)),
    x * y = y * x
  component_commutative : ∀ (T : Over (Spec (.of k))) (i : irreducibleComponents C)
    (x y : (picardFunctorGrp (component f i).hom).obj (.op T)), x * y = y * x
  diagonal_injective : ∀ T : Over (Spec (.of k)),
    Function.Injective (fun a : Γ(T.left, ⊤)ˣ ↦ fun _ : irreducibleComponents C ↦ a)
  diagonal_kernel : ∀ (T : Over (Spec (.of k))) (a : irreducibleComponents C → Γ(T.left, ⊤)ˣ),
    (fun e : Nodes f ↦ a (N.index e 1) * (a (N.index e 0))⁻¹) = 1 ↔
      ∃ c : Γ(T.left, ⊤)ˣ, a = fun _ ↦ c
  glue_kernel : ∀ (T : Over (Spec (.of k))) (z : Nodes f → Γ(T.left, ⊤)ˣ),
    glue T z = 1 ↔
      Sieve.generate (fun (V : Over (Spec (.of k))) (h : V ⟶ T) ↦
        ∃ a : irreducibleComponents C → Γ(V.left, ⊤)ˣ,
          (fun e : Nodes f ↦ a (N.index e 1) * (a (N.index e 0))⁻¹) =
            (fun e ↦ Units.map h.left.appTop.hom.toMonoidHom (z e))) ∈
        (Scheme.fppfTopology.over (Spec (.of k))) T
  restrict_kernel : ∀ (T : Over (Spec (.of k))) (x : (picardFunctorGrp f).obj (.op T)),
    restrict T x = 1 ↔
      Sieve.generate (fun (V : Over (Spec (.of k))) (h : V ⟶ T) ↦
        ∃ z : Nodes f → Γ(V.left, ⊤)ˣ,
          glue V z = (picardFunctorGrp f).map h.op x) ∈
        (Scheme.fppfTopology.over (Spec (.of k))) T
  restrict_epi : ∀ (T : Over (Spec (.of k)))
    (x : ∀ i : irreducibleComponents C, (picardFunctorGrp (component f i).hom).obj (.op T)),
    Sieve.generate (fun (V : Over (Spec (.of k))) (h : V ⟶ T) ↦
      ∃ y : (picardFunctorGrp f).obj (.op V),
        restrict V y = fun i ↦ (picardFunctorGrp (component f i).hom).map h.op (x i)) ∈
      (Scheme.fppfTopology.over (Spec (.of k))) T
  jacobians : irreducibleComponents C → Over (Spec (.of k))
  [jacobian_groups : ∀ i, CommGrpObj (jacobians i)]
  isJacobian : ∀ i, @IsJacobian k _ (component f i).left (component f i).hom
    (N.curve i) (N.smooth i) (N.proper i) (N.geometricallyIntegral i) (jacobians i) _
  jacobian_rep : ∀ i, (picardFunctorDegree (component f i).hom 0).obj.RepresentableBy
    (jacobians i)
  jacobian_rep_mul : ∀ i, IsPicardZeroMul (component f i).hom (jacobian_rep i)
  B : Over (Spec (.of k))
  [b_group : CommGrpObj B]
  projections : ∀ i, B ⟶ jacobians i
  projections_group : ∀ i, IsMonHom (projections i)
  product : IsLimit (Fan.mk B projections)
  abelian : IsAbelianVariety B
  b_inclusion : ∀ T : Over (Spec (.of k)), (T ⟶ B) →*
    (∀ i : irreducibleComponents C, (picardFunctorGrp (component f i).hom).obj (.op T))
  b_inclusion_spec : ∀ (T : Over (Spec (.of k))) (b : T ⟶ B) (i : irreducibleComponents C),
    b_inclusion T b i = (picardFunctorDegreeι (component f i).hom 0).hom.app (.op T)
      ((jacobian_rep i).homEquiv (b ≫ projections i))
  Q : Over (Spec (.of k))
  [q_group : CommGrpObj Q]
  q_finite_type : LocallyOfFiniteType Q.hom
  q_quasiCompact : QuasiCompact Q.hom
  q_separated : IsSeparated Q.hom
  quotient : ∀ T : Over (Spec (.of k)), (Nodes f → Γ(T.left, ⊤)ˣ) →* (T ⟶ Q)
  quotient_natural : ∀ (T V : Over (Spec (.of k))) (h : V ⟶ T)
    (z : Nodes f → Γ(T.left, ⊤)ˣ),
    h ≫ quotient T z = quotient V (fun e ↦ Units.map h.left.appTop.hom.toMonoidHom (z e))
  quotient_kernel : ∀ (T : Over (Spec (.of k))) (z : Nodes f → Γ(T.left, ⊤)ˣ),
    quotient T z = 1 ↔
      Sieve.generate (fun (V : Over (Spec (.of k))) (h : V ⟶ T) ↦
        ∃ a : irreducibleComponents C → Γ(V.left, ⊤)ˣ,
          (fun e : Nodes f ↦ a (N.index e 1) * (a (N.index e 0))⁻¹) =
            (fun e ↦ Units.map h.left.appTop.hom.toMonoidHom (z e))) ∈
        (Scheme.fppfTopology.over (Spec (.of k))) T
  quotient_epi : ∀ (T : Over (Spec (.of k))) (q : T ⟶ Q),
    Sieve.generate (fun (V : Over (Spec (.of k))) (h : V ⟶ T) ↦
      ∃ z : Nodes f → Γ(V.left, ⊤)ˣ, quotient V z = h ≫ q) ∈
      (Scheme.fppfTopology.over (Spec (.of k))) T
  D : (Over (Spec (.of k)))ᵒᵖ ⥤ GrpCat.{u}
  d_sheaf : Presheaf.IsSheaf (Scheme.fppfTopology.over (Spec (.of k))) (D ⋙ forget GrpCat)
  d_space : AlgebraicSpace.IsAlgebraicSpace ⟨D ⋙ forget GrpCat, d_sheaf⟩
  d_smooth : ∀ (T : Over (Spec (.of k))) (a : yoneda.obj T ⟶ D ⋙ forget GrpCat),
    AlgebraicSpace.IsEtale a → Smooth T.hom
  d_commutative : ∀ (T : Over (Spec (.of k))) (x y : D.obj (.op T)), x * y = y * x
  d_inclusion : ∀ T : Over (Spec (.of k)), D.obj (.op T) →*
    (picardFunctorGrp f).obj (.op T)
  d_inclusion_natural : ∀ (T V : Over (Spec (.of k))) (h : V ⟶ T) (d : D.obj (.op T)),
    d_inclusion V (D.map h.op d) = (picardFunctorGrp f).map h.op (d_inclusion T d)
  d_inclusion_injective : ∀ T : Over (Spec (.of k)), Function.Injective (d_inclusion T)
  inverse_image : ∀ (T : Over (Spec (.of k))) (x : (picardFunctorGrp f).obj (.op T)),
    (∃ d : D.obj (.op T), d_inclusion T d = x) ↔ ∃ b : T ⟶ B,
      restrict T x = b_inclusion T b
  projection : D ⋙ forget GrpCat ⟶ yoneda.obj B
  projection_mul : ∀ (T : Over (Spec (.of k))) (d e : D.obj (.op T)),
    projection.app (.op T) (d * e) =
      CartesianMonoidalCategory.lift (projection.app (.op T) d) (projection.app (.op T) e) ≫ μ[B]
  projection_one : ∀ T : Over (Spec (.of k)), projection.app (.op T) 1 = (1 : T ⟶ B)
  projection_spec : ∀ (T : Over (Spec (.of k))) (d : D.obj (.op T)),
    restrict T (d_inclusion T d) = b_inclusion T (projection.app (.op T) d)
  projection_geometry : AlgebraicSpace.IsRepresentableWith
    (fun _ _ p ↦ Smooth p.left ∧ Surjective p.left ∧ IsOpenMap p.left) projection
  local_sections : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over (Spec (.of k)))
    projection
  kernel_inclusion : ∀ T : Over (Spec (.of k)), (T ⟶ Q) →* D.obj (.op T)
  kernel_natural : ∀ (T V : Over (Spec (.of k))) (h : V ⟶ T) (q : T ⟶ Q),
    D.map h.op (kernel_inclusion T q) = kernel_inclusion V (h ≫ q)
  kernel_spec : ∀ (T : Over (Spec (.of k))) (z : Nodes f → Γ(T.left, ⊤)ˣ),
    d_inclusion T (kernel_inclusion T (quotient T z)) = glue T z
  action_over : ∀ (T : Over (Spec (.of k))) (q : T ⟶ Q) (d : D.obj (.op T)),
    projection.app (.op T) (kernel_inclusion T q * d) = projection.app (.op T) d
  torsor : ∀ (T : Over (Spec (.of k))) (d e : D.obj (.op T)),
    projection.app (.op T) d = projection.app (.op T) e →
      ∃! q : T ⟶ Q, kernel_inclusion T q * d = e

/-- The normalization sequence holds for every ordering of the actual branches. Its quotient
is an algebraic group, the product of component Jacobians is an abelian variety, and the
inverse-image group algebraic space is a smooth surjective open torsor over that product.
Source: Stacks, curves.tex, Tag 0C1M and Example 0C1J; pic.tex, Tag 0BA0;
groupoids.tex, Tag 049C (blueprint: lem-sfb-nodal-normalization-picard-sequence).

Proof plan:
1. Apply lem-sfb-nodal-completed-normalization-model. The completed node model and faithful
flatness of completion (lem-weil-pbc-local-completion-faithfully-flat), flat tensor exactness
(lem-weil-pbc-flat-tensor-exact), and faithfully flat detection
(lem-sc-faithfully-flat-tensor-zero) give the conductor square: functions on the normalization
come from the curve precisely when their two residues agree. The two-point fibre is reduced.
2. Every base scheme over the field is flat. Base change preserves this conductor square,
also for nonreduced bases. Apply lem-sfb-finite-pinching-invertible-patching. Eliminate the
node lines from its triples to obtain one branch identification per node. The equivalence
respects tensor products and arbitrary base change, and defines the specified gluing map.
3. Component integrality (lem-sc-smooth-connected-curve-local-rings), proper global sections
(lem-pc-h0-proper-variety), and degree-zero flat base change (lem-pc-flat-base-change-cohom)
identify changes of frames with tuples of base units. Their effect is exactly the displayed
coboundary. Connectedness of the dual graph makes its kernel the diagonal.
4. By sk-def-picard-pic, sections have local line representatives. Locally trivialize the
finitely many branch lines to lift any tuple of component classes. Trivialize component
pullbacks to identify the kernel with gluing parameters. A gluing has zero class exactly
locally when it is a coboundary. This proves exactness as fppf sheaves on all bases.
5. Choose a root and spanning tree. Changing vertex frames recursively sets every tree
parameter to one. The remaining parameters identify the sheaf cokernel with the split torus
on non-tree edges; its Laurent monomials work over every base. It is an algebraic group,
smooth by lem-trf-split-lattice-torus-projection. Loops contribute unrestricted factors.
6. By sk-thm-picard-main and def-sc-jacobian each component degree-zero functor has a
Jacobian. The finite product represents their product and is proper, smooth and connected,
using lem-pc-proper-base-change, lem-weil-pbc-proper-composition,
lem-sbc-smooth-relative-dimension-permanence and
lem-weil-pbc-geometrically-connected-product-components. Hence it is an abelian variety.
7. Pull back the Picard epimorphism to this product. Differences of two lifts are unique
sections of the quotient. Local sections therefore trivialize its translation action.
Apply lem-sfb-smooth-affine-group-torsor-representability: this torsor is represented by a
smooth surjective open scheme over the product, hence by an algebraic space. Group laws
are morphisms by Yoneda, and lem-trf-smooth-composition gives absolute smoothness.
-/
theorem normalization_picard_sequence (k : Type u) [Field k] [IsAlgClosed k]
    (C : Scheme.{u}) (f : C ⟶ Spec (.of k)) [IsProper f] [IsReduced C]
    [LocallyOfFinitePresentation f] (hnodal : HasNodalGeometricFibres f) :
    Nonempty (Branches f) ∧ ∀ N : Branches f, Nonempty (Sequence N) := by
  sorry

end NodalNormalizationPicard
end AlgebraicGeometry
