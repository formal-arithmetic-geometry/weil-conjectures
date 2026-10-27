module

public import Sheaf.AlgebraicGeometry.SpaceRelativeProjSchemeTests
public import Sheaf.TraceFormula.SpaceLineModuleProjInput
public import Sheaf.TraceFormula.LineProjAffineChartAtlas
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.AlgebraicGeometry.SpaceFlatDirectImageBaseChange
import Sheaf.AlgebraicGeometry.EtaleOpenChartMorphismDescent
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import Sheaf.CategoryTheory.ModulePullbackTensorIso
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Sites.MorphismProperty
import Sheaf.TraceFormula.LineProjChartPullback
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence

/-! # Degree-one line quotients and relative Proj over an algebraic space

Source: Stacks Project, spaces-divisors.tex, Tags 085D(1) and 0D2Z(3)
(blueprint: lem-sfb-space-proj-degree-one-quotients).

The quotient is written in the adjoint, cartesian scheme-test presentation of
`GradedLineMap`: homogeneous linear maps to the actual pullbacks of the line module,
with units, products, and coefficientwise base-change equations. The fraction condition
is intrinsic: multiplying the scalar by the denominator's tensor power gives the
numerator. Thus it includes all trivializations and is unchanged by a change of frame.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- A scheme test of a space, retaining its actual morphism.
Source: Stacks, 0D2Z(3) (blueprint: lem-sfb-space-proj-degree-one-quotients). -/
def spaceQuotientTest {Y : AlgebraicSpace S} (W : Over S) (g : schemeSpace W ⟶ Y) :
    SchemeTests Y.obj.obj := CostructuredArrow.mk g.hom.hom

/-- The commuting triangle between a scheme test and its pullback.
Source: Stacks, 0D2Z(3) (blueprint: lem-sfb-space-proj-degree-one-quotients). -/
def spaceQuotientTestMap {Y : AlgebraicSpace S} {U W : Over S} (a : U ⟶ W)
    (g : schemeSpace W ⟶ Y) :
    spaceQuotientTest U (evaluationSchemeMap a ≫ g) ⟶ spaceQuotientTest W g :=
  CostructuredArrow.homMk a rfl

/-- Pullback of a homogeneous line-power section, by the specified cartesian line
identifications and the ordinary tensor-pullback unit, rather than an arbitrary map.
Source: Stacks, 03G7 and 0D2Z(3)
(blueprint: lem-sfb-space-proj-degree-one-quotients). -/
def spaceQuotientPowerSection {Y : AlgebraicSpace S} (P : TestLineFamily Y.obj.obj)
    {U W : Over S} (a : U ⟶ W) (g : schemeSpace W ⟶ Y)
    (V : W.left.Opens) (V' : U.left.Opens) (h : V' ≤ a.left ⁻¹ᵁ V)
    (n : ℕ) (s : Γ((P.module (spaceQuotientTest W g)).tensorPow n, V)) :
    Γ((P.module (spaceQuotientTest U (evaluationSchemeMap a ≫ g))).tensorPow n, V') :=
  (Scheme.Modules.boundaryPullbackPowIso a.left (P.module (spaceQuotientTest W g)) n ≪≫
    Scheme.Modules.boundaryTensorPowIso (P.pullbackIso (spaceQuotientTestMap a g)) n).hom.app V'
      (((Scheme.Modules.tensorPullback a.left).obj
        ((P.module (spaceQuotientTest W g)).tensorPow n)).presheaf.map (homOfLE h).op
          (Scheme.Modules.tensorPullbackSection a.left
            ((P.module (spaceQuotientTest W g)).tensorPow n) V s))

/-- The graded map to line powers, presented on every scheme pullback. The affine
source is the actual normalized algebra `C.scheme`, and the target is the cartesian
realization of the given line. Linearity, products, units and arbitrary scheme-map
naturality are exactly the adjoint description of a homogeneous sheaf-algebra map.
The HEq in naturality only transports the associativity equality `(a ≫ g) ≫ f = a ≫ (g ≫ f)`.
Source: Stacks, 085D(1), 0D2Z(3), and 03G7
(blueprint: lem-sfb-space-proj-degree-one-quotients). -/
structure SpaceProjLineQuotient (C : SpaceProjCoefficients S)
    {X Y : AlgebraicSpace S} (A : SpaceProjInput X) (f : Y ⟶ X)
    (P : TestLineFamily Y.obj.obj) where
  component (W : Over S) (g : schemeSpace W ⟶ Y) (V : W.left.affineOpens) (n : ℕ) :
    (C.scheme A W (g ≫ f)).affine.grading V n →ₗ[Γ(W.left, V.1)]
      Γ((P.module (spaceQuotientTest W g)).tensorPow n, V.1)
  unit (W : Over S) (g : schemeSpace W ⟶ Y) (V : W.left.affineOpens) :
    component W g V 0 ⟨1, SetLike.one_mem_graded _⟩ =
      Scheme.Modules.unitSectionsEquiv V.1 1
  mul (W : Over S) (g : schemeSpace W ⟶ Y) (V : W.left.affineOpens)
      (m n : ℕ) (a : (C.scheme A W (g ≫ f)).affine.grading V m)
      (b : (C.scheme A W (g ≫ f)).affine.grading V n) :
    component W g V (m + n) ⟨a * b, SetLike.mul_mem_graded a.property b.property⟩ =
      ((P.module (spaceQuotientTest W g)).tensorPowAddIso m n).inv.app V.1
        (Scheme.Modules.tmulSection (component W g V m a) (component W g V n b))
  naturality {U W : Over S} (a : U ⟶ W) (g : schemeSpace W ⟶ Y)
      (V : W.left.affineOpens) (V' : U.left.affineOpens) (h : V'.1 ≤ a.left ⁻¹ᵁ V.1)
      (n : ℕ) (s : (C.scheme A W (g ≫ f)).affine.grading V n)
      (s' : (C.scheme A U ((evaluationSchemeMap a ≫ g) ≫ f)).affine.grading V' n) :
    HEq s' (⟨(C.schemeBaseChange A a (g ≫ f)).map h s,
      ((C.schemeBaseChange A a (g ≫ f)).map h).map_mem s.property⟩ :
        (C.scheme A U (evaluationSchemeMap a ≫ (g ≫ f))).affine.grading V' n) →
    component U (evaluationSchemeMap a ≫ g) V' n s' =
      spaceQuotientPowerSection P a g V.1 V'.1 h n (component W g V n s)

/-- Surjectivity in degree one as a sheaf condition. Near every point of every scheme
test, the image of a degree-one section is a basis of the pulled-back line. For a
quasi-coherent source and an invertible target this is equivalent to sheaf surjectivity:
a lifted local basis exists after shrinking, and an affine neighbourhood suffices.
Source: Stacks, 085D(1), 0D2Z; Constructions, 01O9
(blueprint: lem-sfb-space-proj-degree-one-quotients). -/
def SpaceProjLineQuotient.IsSurjectiveInDegreeOne {C : SpaceProjCoefficients S}
    {X Y : AlgebraicSpace S} {A : SpaceProjInput X} {f : Y ⟶ X}
    {P : TestLineFamily Y.obj.obj} (ψ : SpaceProjLineQuotient C A f P) : Prop :=
  ∀ (W : Over S) (g : schemeSpace W ⟶ Y) (x : W.left),
    ∃ (V : W.left.affineOpens), x ∈ V.1 ∧
      ∃ a : (C.scheme A W (g ≫ f)).affine.grading V 1,
        Scheme.Modules.IsFreeGenerator (ψ.component W g V 1 a)

/-- The specified map to the space Proj. On every scheme test, every degree-one
homogeneous section, and every smaller open where its image is a basis, there is
an actual factorization through its homogeneous-localization chart. The scalar
formula is psi(v)/psi(a)^n, expressed without division, including n=0 and empty opens.
Source: Stacks, 0D2Z(3); Constructions, 01NK and 01O9
(blueprint: lem-sfb-space-proj-degree-one-quotients). -/
def SpaceProjLineQuotient.IsCanonicalMap {C : SpaceProjCoefficients S}
    {X Y : AlgebraicSpace S} {A : SpaceProjInput X} {f : Y ⟶ X}
    {P : TestLineFamily Y.obj.obj} (ψ : SpaceProjLineQuotient C A f P)
    (R : SpaceProjRealization C A) (r : Y ⟶ R.space) : Prop :=
  r ≫ R.projection = f ∧
    ∀ (W : Over S) (g : schemeSpace W ⟶ Y) (V : W.left.affineOpens)
      (a : (C.scheme A W (g ≫ f)).affine.grading V 1)
      (U : W.left.Opens) (h : U ≤ V.1),
      Scheme.Modules.IsFreeGenerator
        (((P.module (spaceQuotientTest W g)).tensorPow 1).presheaf.map (homOfLE h).op
          (ψ.component W g V 1 a)) →
      ∃ (q : U.toScheme ⟶ Spec (.of (HomogeneousLocalization.Away
          ((C.scheme A W (g ≫ f)).affine.grading V) a.val)))
        (b : Over.mk (U.ι ≫ W.hom) ⟶
          spaceProjScheme W (C.scheme A W (g ≫ f)).affine),
        b.left = q ≫ Proj.awayι ((C.scheme A W (g ≫ f)).affine.grading V)
          a.val a.property (by decide) ≫ (C.scheme A W (g ≫ f)).affine.relProjι V ∧
        yoneda.map b ≫ R.compare W (g ≫ f) =
          yoneda.map (Over.homMk U.ι : Over.mk (U.ι ≫ W.hom) ⟶ W) ≫
            g.hom.hom ≫ r.hom.hom ∧
        ∀ (n : ℕ) (v : (C.scheme A W (g ≫ f)).affine.grading V n),
          (Scheme.Modules.lineProjScalar U q
            (HomogeneousLocalization.Away.mk
              ((C.scheme A W (g ≫ f)).affine.grading V) a.property n v.val
              (by simp))) •
            Scheme.Modules.lineProjFramePower (P.module (spaceQuotientTest W g)) U
              ((ρ_ (P.module (spaceQuotientTest W g))).hom.app U
                (((P.module (spaceQuotientTest W g)).tensorPow 1).presheaf.map
                  (homOfLE h).op (ψ.component W g V 1 a))) n =
            ((P.module (spaceQuotientTest W g)).tensorPow n).presheaf.map (homOfLE h).op
              (ψ.component W g V n v)

/-- A degree-one surjective line quotient gives the canonical morphism to relative Proj.
The degree-zero structural map is an isomorphism, and generation by degree one is
expressed by the degree-one subalgebra on every affine scheme test. This is equivalent
to surjectivity of the iterated sheaf multiplication maps, with no finite set of generators.

Source: Stacks Project, spaces-divisors.tex, 085D(1) and 0D2Z(3)
(blueprint: lem-sfb-space-proj-degree-one-quotients).

Proof:
1. Choose an etale scheme atlas V of X, then a scheme atlas T of Y times_X V.
   The maps T to Y and the scheme overlaps are surjective etale, by
   lem-trf-space-fibre-products-etale-covers and lem-weil-pbc-etale-covering-composition.
   Use the comparisons of lem-sfb-space-relative-proj-scheme-tests for the target.
2. Restrict the quotient and the line to these charts. The equivalence
   lem-trf-scheme-zariski-etale-quasi-coherent-equivalence and the normalized tensor
   comparison lem-weil-pbc-ringed-topoi-module-pullback-tensor identify their units,
   products and tensor pullbacks. The displayed naturality equation retains precisely
   the composition comparison def-sfb-space-module-tensor-composition.
3. By lem-weil-pbc-module-pullback-affine-sections, local surjectivity expresses a
   line basis as a finite linear combination of homogeneous images. In a local ring
   some coefficient image is a unit. Degree-one generator loci therefore cover T,
   without a finite cover or finite generation hypothesis.
4. Apply lem-trf-line-proj-affine-chart-atlas on these loci. Its fraction formula
   gives the chart maps and their agreement, including different affine base opens.
   Glue by lem-weil-pbc-scheme-morphism-gluing; the degree-zero formula makes them
   morphisms over the base. Compose with the space-Proj scheme-test comparison.
5. On both scheme overlap projections, lem-trf-line-proj-chart-pullback applies to
   the commutative comparison squares, with the coefficient equations above. Its
   fraction identities show that the two maps into the space Proj agree.
6. Descend by lem-trf-etale-open-chart-morphism-descent with the whole atlas as open.
   The same equality detection, now with target X, gives r followed by p equals f.
7. Compare any two atlases on a common refinement. The fraction charts agree, so
   descent gives independence and uniqueness. Further scheme tests have the same
   formulas by coefficientwise base change. In an arbitrary frame both numerator
   and denominator change by the same n-th power of a unit, so their ratio agrees.
   Empty tests use the unique empty-domain map throughout. -/
theorem existsUnique_spaceProj_degreeOne_quotient
    (C : SpaceProjCoefficients S) {X Y : AlgebraicSpace S}
    (A : SpaceProjInput X) (R : SpaceProjRealization C A)
    (_hzero : IsIso A.algebra.unit)
    (_hgen : ∀ (W : Over S) (g : schemeSpace W ⟶ X) (V : W.left.affineOpens),
      Algebra.adjoin Γ(W.left, V.1)
        (Set.range (fun a : (C.scheme A W g).affine.grading V 1 ↦ a.val)) = ⊤)
    (f : Y ⟶ X) (L : Y.Modules) (hL : Y.IsLineModule L)
    (ψ : SpaceProjLineQuotient C A f (lineTestFamily Y L hL))
    (_hψ : ψ.IsSurjectiveInDegreeOne) :
    ∃! r : Y ⟶ R.space, ψ.IsCanonicalMap R r := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
