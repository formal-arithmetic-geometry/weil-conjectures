/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Sheaf.AlgebraicGeometry.ConormalGradedAlgebra
public import Sheaf.AlgebraicGeometry.SymmetricAlgebraSheafConstruction
public import WeilConjectures.AlgebraicGeometry.RelativeProj.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebraCore
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism
public import WeilConjectures.AlgebraicGeometry.RelativeProj.Rees
public import WeilConjectures.AlgebraicGeometry.RelativeProj.BaseChange
public import WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.UnitToTwist
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules
import WeilConjectures.AlgebraicGeometry.Modules.VeryAmple
import WeilConjectures.AlgebraicGeometry.ClosedImmersionPushforwardAnnihilated
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.RingTheory.FiniteType
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import Mathlib.RingTheory.LocalRing.Module
import WeilConjectures.AlgebraicGeometry.Cohomology.QuasicoherentExtension
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.Topology.SheafIsomorphismLocalOpenCover
import Sheaf.RingTheory.SymmetricAlgebraBaseChange
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.RingTheory.Noetherian.Defs
import Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebra
import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.LinearAlgebra.SymmetricAlgebra.Graded
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-!
# Base change of the modified blowup of a conormal presentation

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, XVI 2.2.1.1--2.2.1.5,
pp. 229--230 (blueprint: lem-per-conormal-presentation-proj-base-change).

The auxiliary structures specify constructions by their section formulas. In particular,
`Model.pairs` is the fibre-product equation in every degree, and the two ring projections
fix multiplication on pairs. They do not postulate a replacement graded algebra as an input.
The theorem asserts existence of these presentations and the canonical comparisons.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ConormalPresentation

/-- Input to ILO XVI 2.2.1: a finite locally free presentation of the conormal module.
The rank can vary, and rank zero is allowed.
(blueprint: lem-per-conormal-presentation-proj-base-change). -/
structure Datum where
  X : Scheme.{u}
  Y : Scheme.{u}
  i : Y ⟶ X
  [closed : IsClosedImmersion i]
  [noetherianX : IsNoetherian X]
  [noetherianY : IsNoetherian Y]
  E : Y.Modules
  [finiteFree : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf) E]
  q : E ⟶ ConormalGradedAlgebra.piece i 1
  [epi : Epi q]

attribute [instance] Datum.closed Datum.noetherianX Datum.noetherianY
  Datum.finiteFree Datum.epi

/-- The actual symmetric-to-conormal map, uniquely extending the given degree-one map.
Source: ILO XVI 2.2.1, the defining Cartesian square
(blueprint: lem-per-conormal-presentation-proj-base-change). -/
noncomputable def symmetricComparison (D : Datum.{u}) :
    SymmetricAlgebraSheaf.algebra D.E ⟶ (ConormalGradedAlgebra.presentation D.i).algebra :=
  (exists_quasiCoherentSymmetricAlgebra_core D.Y D.E
    (ConormalGradedAlgebra.presentation D.i).algebra
    (D.q ≫ (ConormalGradedAlgebra.presentation D.i).inclusion 1)).choose

/-- The open complement, with its actual scheme structure.
Source: ILO XVI 2.2.1 (blueprint: lem-per-conormal-presentation-proj-base-change). -/
def complement (D : Datum.{u}) : D.X.Opens :=
  ⟨(Set.range D.i)ᶜ, D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩

/-- A relative degree-one twist with affine Proj charts. The compatibility of these charts
will be imposed by `Model.twistRestriction` below.
Source: ILO XVI 2.2.1.3--2.2.1.5; Stacks 01MN
(blueprint: lem-per-conormal-presentation-proj-base-change). -/
structure Twist {X : Scheme.{u}} (A : X.GradedAlgebraData) where
  line : A.relProj.Modules
  chart : ∀ U : X.affineOpens,
    (Scheme.Modules.tensorPullback (A.relProjι U)).obj line ≅ Proj.twist (A.grading U) 1

/-- Canonical comparison of the twists on two affine Proj models: it carries every
homogeneous degree-one section to its image, including sections that are not frames.
Source: ILO XVI 2.2.1.5, degree-one localizations; Stacks 01N1
(blueprint: lem-per-conormal-presentation-proj-base-change). -/
def NormalizedTwist {X X' : Scheme.{u}} (A : X.GradedAlgebraData)
    (A' : X'.GradedAlgebraData) (U : X.affineOpens) (U' : X'.affineOpens)
    (β : A.grading U →+*ᵍ A'.grading U')
    (hβ : HomogeneousIdeal.irrelevant (A'.grading U') ≤
      (HomogeneousIdeal.irrelevant (A.grading U)).map β)
    (e : (Scheme.Modules.tensorPullback (Proj.map β hβ)).obj
      (Proj.twist (A.grading U) 1) ≅ Proj.twist (A'.grading U') 1) : Prop :=
  ∀ a : A.grading U 1,
    e.hom.app ((Proj.map β hβ) ⁻¹ᵁ ⊤)
      (Scheme.Modules.tensorPullbackSection (Proj.map β hβ)
        (Proj.twist (A.grading U) 1) ⊤
        ((Proj.unitToTwist a.property).app ⊤ (1 : Γ(Proj (A.grading U), ⊤)))) =
      (Proj.unitToTwist (β.map_mem a.property)).app ((Proj.map β hβ) ⁻¹ᵁ ⊤)
        (1 : Γ(Proj (A'.grading U'), (Proj.map β hβ) ⁻¹ᵁ ⊤))

/-- Compatibility of a global line comparison with the normalized affine twist maps.
Source: ILO XVI 2.2.1.5, degree-one chart calculation
(blueprint: lem-per-conormal-presentation-proj-base-change). -/
def TwistCompatibility {X X' : Scheme.{u}} {A : X.GradedAlgebraData}
    {A' : X'.GradedAlgebraData} (L : Twist A) (L' : Twist A')
    (c : A'.relProj ⟶ A.relProj)
    (e : (Scheme.Modules.tensorPullback c).obj L.line ≅ L'.line)
    (U : X.affineOpens) (U' : X'.affineOpens)
    (β : A.grading U →+*ᵍ A'.grading U')
    (hβ : HomogeneousIdeal.irrelevant (A'.grading U') ≤
      (HomogeneousIdeal.irrelevant (A.grading U)).map β)
    (hc : A'.relProjι U' ≫ c = Proj.map β hβ ≫ A.relProjι U) : Prop :=
  ∃ t : (Scheme.Modules.tensorPullback (Proj.map β hβ)).obj
      (Proj.twist (A.grading U) 1) ≅ Proj.twist (A'.grading U') 1,
    NormalizedTwist A A' U U' β hβ t ∧
    (Scheme.Modules.tensorPullback (A'.relProjι U')).mapIso e ≪≫ L'.chart U' =
      ((Scheme.Modules.tensorPullbackSectionComp (A'.relProjι U') c).app L.line).symm ≪≫
      eqToIso (congrArg (fun f => (Scheme.Modules.tensorPullback f).obj L.line) hc) ≪≫
      (Scheme.Modules.tensorPullbackSectionComp (Proj.map β hβ) (A.relProjι U)).app L.line ≪≫
      (Scheme.Modules.tensorPullback (Proj.map β hβ)).mapIso (L.chart U) ≪≫ t

/-- The modified-blowup algebra, its relative Proj, and its degree-one line. The exact range
condition says A_n = I^n times over gr_n(I) Sym^n(E). Projections are ring maps, so the
multiplication is precisely multiplication on pairs; injectivity excludes extra summands.
Source: ILO XVI 2.2.1.1--2.2.1.4
(blueprint: lem-per-conormal-presentation-proj-base-change). -/
structure Model (D : Datum.{u}) where
  algebra : D.X.GradedAlgebraData
  first : algebra ⟶ D.i.ker.reesData
  second : ∀ U : D.X.affineOpens,
    algebra.obj U →+* SymmetricAlgebraSheaf.sections D.E (op (D.i ⁻¹ᵁ U.1))
  second_scalars : ∀ (U : D.X.affineOpens) (r : Γ(D.X, U.1)),
    second U (algebraMap _ _ r) = algebraMap _ _ (D.i.app U.1 r)
  second_restriction : ∀ {U V : D.X.affineOpens} (h : U ≤ V) (a : algebra.obj V),
    second U (algebra.res h a) = SymmetricAlgebraSheaf.restriction D.E
      (homOfLE (D.i.preimage_mono h)).op (second V a)
  injectivePair : ∀ (U : D.X.affineOpens) (a b : algebra.obj U),
    first.app U a = first.app U b → second U a = second U b → a = b
  pairs : ∀ (U : D.X.affineOpens) (n : ℕ) (r : Γ(D.X, U.1))
      (b : SymmetricAlgebraSheaf.sections D.E (op (D.i ⁻¹ᵁ U.1))),
    (∃ a : algebra.grading U n,
      (Subtype.val (@id (reesAlgebra (D.i.ker.ideal U)) (first.app U a))).coeff n = r ∧
        second U a = b) ↔
    b ∈ (SymmetricAlgebra.ι Γ(D.Y, D.i ⁻¹ᵁ U.1)
      (D.E.val.obj (op (D.i ⁻¹ᵁ U.1)))).range ^ n ∧
    ∃ z : (ConormalGradedAlgebra.power D.i n).val.obj (op U.1),
      (ConormalGradedAlgebra.powerInclusion D.i n).app U.1 z = r ∧
      (symmetricComparison D).right.hom.app (op (D.i ⁻¹ᵁ U.1))
        (SymmetricAlgebraSheaf.sectionMap D.E (op (D.i ⁻¹ᵁ U.1)) b) =
      ConormalGradedAlgebra.homogeneousClass D.i
        (ConormalGradedAlgebra.presentation D.i).algebra
        (ConormalGradedAlgebra.presentation D.i).inclusion n U.1 z
  quasicoherentE : D.E.IsQuasicoherent
  closedIso : pullback D.i algebra.relProjHom ≅
    (@SymmetricAlgebraSheaf.gradedAlgebraData D.Y D.E quasicoherentE).relProj
  closedIso_over : closedIso.hom ≫
    (@SymmetricAlgebraSheaf.gradedAlgebraData D.Y D.E quasicoherentE).relProjHom =
      pullback.fst D.i algebra.relProjHom
  closedIso_formula : ∀ (U : D.X.affineOpens) (V : D.Y.affineOpens)
      (h : V.1 ≤ D.i ⁻¹ᵁ U.1),
    ∃ (β : algebra.grading U →+*ᵍ
        (@SymmetricAlgebraSheaf.gradedAlgebraData D.Y D.E quasicoherentE).grading V)
      (hi : HomogeneousIdeal.irrelevant
          ((@SymmetricAlgebraSheaf.gradedAlgebraData D.Y D.E quasicoherentE).grading V) ≤
        (HomogeneousIdeal.irrelevant (algebra.grading U)).map β),
      (∀ a : algebra.obj U,
        β a = SymmetricAlgebraSheaf.restriction D.E (homOfLE h).op (second U a)) ∧
      (@SymmetricAlgebraSheaf.gradedAlgebraData D.Y D.E quasicoherentE).relProjι V ≫
        closedIso.inv ≫ pullback.snd D.i algebra.relProjHom =
          Proj.map β hi ≫ algebra.relProjι U
  outside : IsIso (pullback.fst (complement D).ι algebra.relProjHom)
  twist : Twist algebra
  twistRestriction : ∀ {U V : D.X.affineOpens} (h : U ≤ V),
    ∃ t : (Scheme.Modules.tensorPullback (Proj.map (algebra.res h)
        (algebra.irrelevant_le_map_res h))).obj (Proj.twist (algebra.grading V) 1) ≅
          Proj.twist (algebra.grading U) 1,
      NormalizedTwist algebra algebra V U (algebra.res h)
        (algebra.irrelevant_le_map_res h) t ∧
      twist.chart U =
        eqToIso (congrArg (fun f => (Scheme.Modules.tensorPullback f).obj twist.line)
          (algebra.relProjFunctor_map_relProjι (homOfLE h)).symm) ≪≫
        (Scheme.Modules.tensorPullbackSectionComp
          (Proj.map (algebra.res h) (algebra.irrelevant_le_map_res h))
            (algebra.relProjι V)).app twist.line ≪≫
        (Scheme.Modules.tensorPullback
          (Proj.map (algebra.res h) (algebra.irrelevant_le_map_res h))).mapIso
            (twist.chart V) ≪≫ t

/-- An arbitrary base morphism of conormal presentations. The Cartesian square fixes Y',
and the adjoint of `moduleMap` is an isomorphism, so E' is exactly the pullback of E.
The conormal map is fixed on ideal representatives, and its square with q commutes.
Source: ILO XVI 2.2.1.5 (blueprint: lem-per-conormal-presentation-proj-base-change). -/
structure BaseMap (D' D : Datum.{u}) where
  f : D'.X ⟶ D.X
  g : D'.Y ⟶ D.Y
  square : IsPullback D'.i g f D.i
  moduleMap : D.E ⟶ (Scheme.Modules.pushforward g).obj D'.E
  pullbackModule : IsIso
    (((Scheme.Modules.tensorPullbackSectionAdjunction g).homEquiv D.E D'.E).symm moduleMap)
  conormalMap : ConormalGradedAlgebra.piece D.i 1 ⟶
    (Scheme.Modules.pushforward g).obj (ConormalGradedAlgebra.piece D'.i 1)
  conormal_representatives : ∀ (U : D.X.Opens)
      (a : (ConormalGradedAlgebra.power D.i 1).val.obj (op U))
      (a' : (ConormalGradedAlgebra.power D'.i 1).val.obj (op (f ⁻¹ᵁ U))),
    (ConormalGradedAlgebra.powerInclusion D'.i 1).app (f ⁻¹ᵁ U) a' =
      f.app U ((ConormalGradedAlgebra.powerInclusion D.i 1).app U a) →
    HEq (conormalMap.app (D.i ⁻¹ᵁ U) (ConormalGradedAlgebra.representative D.i 1 U a))
      (ConormalGradedAlgebra.representative D'.i 1 (f ⁻¹ᵁ U) a')
  conormal_square : D.q ≫ conormalMap =
    moduleMap ≫ (Scheme.Modules.pushforward g).map D'.q

/-- The comparison characterized on scalar sections, symmetric generators and ideal
coefficients. Surjectivity in each degree is stated by span of the image after extending
scalars, equivalently surjectivity of the corresponding tensor-product map.
Source: ILO XVI 2.2.1.5 (blueprint: lem-per-conormal-presentation-proj-base-change). -/
structure Comparison {D' D : Datum.{u}} (v : BaseMap D' D) (M : Model D) (M' : Model D') where
  map : ∀ {U : D.X.affineOpens} {U' : D'.X.affineOpens}
    (_h : U'.1 ≤ v.f ⁻¹ᵁ U.1), M.algebra.grading U →+*ᵍ M'.algebra.grading U'
  scalars : ∀ {U : D.X.affineOpens} {U' : D'.X.affineOpens}
    (h : U'.1 ≤ v.f ⁻¹ᵁ U.1) (r : Γ(D.X, U.1)),
      map h (algebraMap _ _ r) = algebraMap _ _ (v.f.appLE U.1 U'.1 h r)
  symmetricMap : ∀ {U : D.X.affineOpens} {U' : D'.X.affineOpens}
    (_hy : D'.i ⁻¹ᵁ U'.1 ≤ v.g ⁻¹ᵁ (D.i ⁻¹ᵁ U.1)),
    SymmetricAlgebraSheaf.sections D.E (op (D.i ⁻¹ᵁ U.1)) →+*
      SymmetricAlgebraSheaf.sections D'.E (op (D'.i ⁻¹ᵁ U'.1))
  symmetric_scalars : ∀ {U : D.X.affineOpens} {U' : D'.X.affineOpens}
    (hy : D'.i ⁻¹ᵁ U'.1 ≤ v.g ⁻¹ᵁ (D.i ⁻¹ᵁ U.1)) (r : Γ(D.Y, D.i ⁻¹ᵁ U.1)),
    symmetricMap hy (algebraMap _ _ r) =
      algebraMap _ _ (v.g.appLE (D.i ⁻¹ᵁ U.1) (D'.i ⁻¹ᵁ U'.1) hy r)
  symmetric_generators : ∀ {U : D.X.affineOpens} {U' : D'.X.affineOpens}
    (hy : D'.i ⁻¹ᵁ U'.1 ≤ v.g ⁻¹ᵁ (D.i ⁻¹ᵁ U.1)) (e : Γ(D.E, D.i ⁻¹ᵁ U.1)),
    symmetricMap hy (SymmetricAlgebra.ι _ _ e) = SymmetricAlgebra.ι _ _
      (D'.E.val.map (homOfLE hy).op (v.moduleMap.app (D.i ⁻¹ᵁ U.1) e))
  first_formula : ∀ {U : D.X.affineOpens} {U' : D'.X.affineOpens}
    (h : U'.1 ≤ v.f ⁻¹ᵁ U.1) (a : M.algebra.obj U),
    Subtype.val (@id (reesAlgebra (D'.i.ker.ideal U')) (M'.first.app U' (map h a))) =
      (Subtype.val (@id (reesAlgebra (D.i.ker.ideal U)) (M.first.app U a))).map
        (v.f.appLE U.1 U'.1 h).hom
  second_formula : ∀ {U : D.X.affineOpens} {U' : D'.X.affineOpens}
    (h : U'.1 ≤ v.f ⁻¹ᵁ U.1) (hy : D'.i ⁻¹ᵁ U'.1 ≤ v.g ⁻¹ᵁ (D.i ⁻¹ᵁ U.1))
    (a : M.algebra.obj U), M'.second U' (map h a) = symmetricMap hy (M.second U a)
  surjective_degree : ∀ {U : D.X.affineOpens} {U' : D'.X.affineOpens}
    (h : U'.1 ≤ v.f ⁻¹ᵁ U.1) (n : ℕ),
    Submodule.span Γ(D'.X, U'.1)
      (Set.range (fun a : M.algebra.grading U n =>
        (⟨map h a, (map h).map_mem a.property⟩ : M'.algebra.grading U' n))) = ⊤
  c : M'.algebra.relProj ⟶ M.algebra.relProj
  over : c ≫ M.algebra.relProjHom = M'.algebra.relProjHom ≫ v.f
  proj_formula : ∀ {U : D.X.affineOpens} {U' : D'.X.affineOpens}
    (h : U'.1 ≤ v.f ⁻¹ᵁ U.1),
    ∃ hi : HomogeneousIdeal.irrelevant (M'.algebra.grading U') ≤
        (HomogeneousIdeal.irrelevant (M.algebra.grading U)).map (map h),
      M'.algebra.relProjι U' ≫ c = Proj.map (map h) hi ≫ M.algebra.relProjι U
  h : M'.algebra.relProj ⟶ pullback v.f M.algebra.relProjHom
  h_fst : h ≫ pullback.fst _ _ = M'.algebra.relProjHom
  h_snd : h ≫ pullback.snd _ _ = c
  closed : IsClosedImmersion h
  locally_nilpotent : ∀ x : (pullback v.f M.algebra.relProjHom : Scheme.{u}),
    ∃ U : (pullback v.f M.algebra.relProjHom).affineOpens,
      x ∈ U.1 ∧ ∃ n : ℕ, 0 < n ∧ h.ker.ideal U ^ n = ⊥
  universalHomeomorphism : (topologically IsHomeomorph).universally h
  outside : IsIso (pullback.snd h
    ((pullback.fst v.f M.algebra.relProjHom ⁻¹ᵁ complement D').ι))
  closedFibre : IsIso (pullback.snd h
    (pullback.snd D'.i (pullback.fst v.f M.algebra.relProjHom)))
  lineIso : (Scheme.Modules.tensorPullback c).obj M.twist.line ≅ M'.twist.line
  line_formula : ∀ {U : D.X.affineOpens} {U' : D'.X.affineOpens}
    (h : U'.1 ≤ v.f ⁻¹ᵁ U.1)
    (hi : HomogeneousIdeal.irrelevant (M'.algebra.grading U') ≤
      (HomogeneousIdeal.irrelevant (M.algebra.grading U)).map (map h))
    (hc : M'.algebra.relProjι U' ≫ c = Proj.map (map h) hi ≫ M.algebra.relProjι U),
      TwistCompatibility M.twist M'.twist c lineIso U U' (map h) hi hc

/-- Existence and canonical arbitrary base change of the conormal-presentation Proj.
Source: ILO XVI 2.2.1.1--2.2.1.5, pp. 229--230; Stacks 01O3, 07ZI and 01N1
(blueprint: lem-per-conormal-presentation-proj-base-change).

Proof, following the twelve steps of the DAG node:
1. The symmetric-degree comparison onto I^a/I^(a+1) is onto: lift each factor in a
   product of a elements of I through E -> I/I^2. Degree zero is the quotient identity.
2. Define the sheaf fibre product in each degree as the kernel of the difference of
   its two maps. Powers, conormal pieces and symmetric powers are quasi-coherent;
   closed pushforward, kernels and direct sums preserve this property. Multiply pairs.
3. The kernel of A_a -> Sym^a(E) is I^(a+1) times zero, and is I A_a, since
   A_a -> I^a is onto. Therefore A/IA = Sym(E). Outside Y the algebra is O[t].
4. On Noetherian affine charts the pieces are finite. Their quotients by the image
   of A_1 tensor-power a vanish modulo I and off Y, so Nakayama proves degree-one
   generation. This includes degree zero and the empty Proj case.
5. Pullback of conormals is onto, by ideal generators and tensor right exactness.
   The symmetric-algebra base-change formula gives the map on pairs (z,m) -> (z,m)
   with scalars extended. These formulas glue and determine the comparison uniquely.
6. Reduction of that map modulo I' is the identity of Sym(E'), and off Y' it is
   the identity on O[t]. Its finite cokernel vanishes by local Nakayama. This proves
   surjectivity of every degree after scalar extension, with no flatness assumption.
7. Arbitrary relative-Proj base change and surjective graded functoriality give the
   closed immersion h. Its restrictions off Y' and over Y' are isomorphisms. The
   latter is the symmetric-algebra comparison P(E') = Y' times over Y P(E).
8. These two inverse images cover all underlying points, so h is surjective. Its
   affine ideal is contained in the nilradical by the prime-spectrum zero-locus lemma.
9. The finitely many degree-one standard charts have finite-type Noetherian coordinate
   rings. Their finitely generated nil ideals have a zero power by the radical-power
   lemma. Thus the immersion ideal is locally nilpotent.
10. After any base change those powers still vanish. Quotient by a nilpotent ideal
    induces a homeomorphism on spectra; this proves universal homeomorphism.
11. On D_+(f) for f of degree one, the twist has basis f. The comparison sends this
    basis to its image. The relations f = (f/g) g agree on overlaps, so the normalized
    twist maps glue. Off Y the distinguished basis is t=(1,0), which is preserved.
12. Identity and successive base changes have the same formulas on pairs and pure
    tensors. Proj chart maps and normalized line maps therefore respect identities
    and composition. Injectivity of the pair coordinates and chart-cover descent
    give the uniqueness assertions. -/
theorem conormalPresentation_proj_baseChange :
    (∀ D : Datum.{u}, Nonempty (Model D)) ∧
    (∀ (D : Datum.{u}) (X' : Scheme.{u}) [IsNoetherian X'] (f : X' ⟶ D.X),
      ∃ (D' : Datum.{u}) (v : BaseMap D' D), D'.X = X' ∧ HEq v.f f) ∧
    (∀ (D' D : Datum.{u}) (v : BaseMap D' D) (M : Model D) (M' : Model D'),
      Nonempty (Comparison v M M')) ∧
    (∀ (D' D : Datum.{u}) (v : BaseMap D' D) (M : Model D) (M' : Model D')
      (C₁ C₂ : Comparison v M M'), C₁.c = C₂.c ∧ HEq C₁.lineIso C₂.lineIso) ∧
    (∀ (D : Datum.{u}) (M : Model D) (v : BaseMap D D) (C : Comparison v M M),
      v.f = 𝟙 D.X → v.g = 𝟙 D.Y →
      (∀ (U : D.Y.Opens) (e : Γ(D.E, U)), HEq (v.moduleMap.app U e) e) →
      (∀ (U : D.X.affineOpens) (h : U.1 ≤ v.f ⁻¹ᵁ U.1) (a : M.algebra.obj U),
        C.map h a = a) ∧
      C.c = 𝟙 M.algebra.relProj ∧
        HEq C.lineIso ((Scheme.Modules.tensorPullbackSectionId M.algebra.relProj).app
          M.twist.line)) ∧
    (∀ (D₁ D₂ D₃ : Datum.{u}) (v₁₂ : BaseMap D₂ D₁) (v₂₃ : BaseMap D₃ D₂)
      (v₁₃ : BaseMap D₃ D₁) (M₁ : Model D₁) (M₂ : Model D₂) (M₃ : Model D₃)
      (C₁₂ : Comparison v₁₂ M₁ M₂) (C₂₃ : Comparison v₂₃ M₂ M₃)
      (C₁₃ : Comparison v₁₃ M₁ M₃),
      v₁₃.f = v₂₃.f ≫ v₁₂.f → v₁₃.g = v₂₃.g ≫ v₁₂.g →
      (∀ (U : D₁.Y.Opens) (e : Γ(D₁.E, U)),
        HEq (v₁₃.moduleMap.app U e)
          (v₂₃.moduleMap.app (v₁₂.g ⁻¹ᵁ U) (v₁₂.moduleMap.app U e))) →
      (∀ (U₁ : D₁.X.affineOpens) (U₂ : D₂.X.affineOpens) (U₃ : D₃.X.affineOpens)
        (h₁₂ : U₂.1 ≤ v₁₂.f ⁻¹ᵁ U₁.1) (h₂₃ : U₃.1 ≤ v₂₃.f ⁻¹ᵁ U₂.1)
        (h₁₃ : U₃.1 ≤ v₁₃.f ⁻¹ᵁ U₁.1) (a : M₁.algebra.obj U₁),
        C₁₃.map h₁₃ a = C₂₃.map h₂₃ (C₁₂.map h₁₂ a)) ∧
      C₁₃.c = C₂₃.c ≫ C₁₂.c ∧
      HEq C₁₃.lineIso
        ((Scheme.Modules.tensorPullbackSectionComp C₂₃.c C₁₂.c).app M₁.twist.line ≪≫
          (Scheme.Modules.tensorPullback C₂₃.c).mapIso C₁₂.lineIso ≪≫ C₂₃.lineIso)) := by
  sorry

end AlgebraicGeometry.ConormalPresentation
