module

public import Sheaf.AlgebraicGeometry.Curve.PicardDuality
public import Mathlib.Algebra.DualNumber
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyBoundary
public import WeilConjectures.AlgebraicGeometry.CechH1MapNatural
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.PicardScalarCechComparison
public import WeilConjectures.Algebra.Category.ModuleCat.DerivedBaseChange
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import WeilConjectures.AlgebraicGeometry.GlobalDerivedHom
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Sheaf.Paper.BoundaryCechCompatibility
import WeilConjectures.AlgebraicGeometry.Regular
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.AlgebraicGeometry.AffineDerivedPullbackTensorTilde
import Sheaf.Paper.ProjectionMateExact
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections
import WeilConjectures.AlgebraicGeometry.DerivedDirectImagePreservesQCoh
import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence
import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImageComposition
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.SplitSESBoundaryComparison

/-! # First-order obstruction for sections of a line bundle

Source: Stacks Project, More on Morphisms, Tag 0C6R
(lemma-picard-group-first-order-thickening), Curves, Tags 0BS2 and 0BS4,
and Homology, Tags 011J and 011K.
(blueprint: lem-sfb-line-section-first-order-obstruction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u wC wD

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {k : Type u} [Field k] {C : Scheme.{u}}

/-- The split dual-number base change. Source: Stacks 0C6R, split thickening.
(blueprint: lem-sfb-line-section-first-order-obstruction). -/
abbrev lineDualBase (f : C ⟶ Spec (.of k)) : Scheme.{u} :=
  CategoryTheory.Limits.pullback f
    (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))))

/-- The split projection. Source: Stacks 0C6R, split thickening.
(blueprint: lem-sfb-line-section-first-order-obstruction). -/
abbrev lineDualProjection (f : C ⟶ Spec (.of k)) : lineDualBase f ⟶ C :=
  pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))))

/-- The dual-number structure map. Source: Stacks 0C6R, split thickening.
(blueprint: lem-sfb-line-section-first-order-obstruction). -/
abbrev lineDualStructure (f : C ⟶ Spec (.of k)) :
    lineDualBase f ⟶ Spec (.of (DualNumber k)) :=
  pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))))

/-- The coefficient maps defining the zero section commute.
Source: Stacks 0C6R, split thickening.
(blueprint: lem-sfb-line-section-first-order-obstruction).
Proof: reduction composed with inclusion of constants is the identity, and Spec is
contravariant. Compose this identity with f. -/
theorem lineDual_zero_condition (f : C ⟶ Spec (.of k)) :
    (𝟙 C) ≫ f =
      (f ≫ Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) := by
  sorry

/-- The canonical reduction immersion. Source: Stacks 0C6R, split thickening.
(blueprint: lem-sfb-line-section-first-order-obstruction). -/
def lineDualZero (f : C ⟶ Spec (.of k)) : C ⟶ lineDualBase f :=
  pullback.lift (𝟙 C)
    (f ≫ Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom))
    (lineDual_zero_condition f)

/-- The zero section splits the projection. Source: Stacks 0C6R, split thickening.
(blueprint: lem-sfb-line-section-first-order-obstruction).
Proof: this is the first projection identity for the displayed pullback lift. -/
theorem lineDual_zero_projection (f : C ⟶ Spec (.of k)) :
    lineDualZero f ≫ lineDualProjection f = 𝟙 C := by
  sorry

/-- Reduction as a morphism on the thickened scheme, adjoint to the specified
identification of the tensor pullback with L. Source: Stacks 0C6R.
(blueprint: lem-sfb-line-section-first-order-obstruction). -/
def lineReductionOnBase (f : C ⟶ Spec (.of k)) (L : C.Modules)
    (LA : (lineDualBase f).Modules) (e : (tensorPullback (lineDualZero f)).obj LA ≅ L) :
    LA ⟶ (pushforward (lineDualZero f)).obj L :=
  (Classical.choose (exists_tensorPullbackAdjunction (lineDualZero f))).homEquiv _ _ e.hom

/-- Reduction on the common underlying space, with the O_C action restricted along p.
Source: Stacks 0C6R, split thickening.
(blueprint: lem-sfb-line-section-first-order-obstruction). -/
def lineReduction (f : C ⟶ Spec (.of k)) (L : C.Modules)
    (LA : (lineDualBase f).Modules) (e : (tensorPullback (lineDualZero f)).obj LA ≅ L) :
    (pushforward (lineDualProjection f)).obj LA ⟶ L :=
  (pushforward (lineDualProjection f)).map (lineReductionOnBase f L LA e) ≫
    (pushforwardComp (lineDualZero f) (lineDualProjection f)).hom.app L ≫
    (pushforwardCongr (lineDual_zero_projection f)).hom.app L ≫
    (pushforwardId C).hom.app L

/-- The coefficient A → Γ(C_A,O) from its specified structural morphism.
Source: Stacks 0C6R.
(blueprint: lem-sfb-line-section-first-order-obstruction). -/
def lineDualScalars (f : C ⟶ Spec (.of k)) :
    DualNumber k →+* Γ(lineDualBase f, ⊤) :=
  (lineDualStructure f).appTop.hom.comp (Scheme.ΓSpecIso (.of (DualNumber k))).inv.hom

/-- Multiplication by epsilon on the actual line bundle, then restriction to C.
Source: Stacks 0C6R.
(blueprint: lem-sfb-line-section-first-order-obstruction). -/
def lineEpsilon (f : C ⟶ Spec (.of k)) (LA : (lineDualBase f).Modules) :
    (pushforward (lineDualProjection f)).obj LA ⟶
      (pushforward (lineDualProjection f)).obj LA :=
  (pushforward (lineDualProjection f)).map
    (smulHom LA (lineDualScalars f DualNumber.eps))

/-- Epsilon descends uniquely through reduction; its descended map is injective and
has precisely the reduction kernel as image. Source: Stacks 0C6R, split thickening.
(blueprint: lem-sfb-line-section-first-order-obstruction).
Proof (node step 1): on a trivializing open L_A is free of rank one over O_C[epsilon].
Reduction is the first coefficient and multiplication by epsilon takes (a,b) to (0,a).
It therefore factors uniquely through reduction. The factor is injective and its image
is the kernel of reduction. These local maps agree on overlaps by uniqueness. -/
theorem lineInclusion_existsUnique (f : C ⟶ Spec (.of k)) (L : C.Modules)
    (LA : (lineDualBase f).Modules) [LA.IsInvertible]
    (e : (tensorPullback (lineDualZero f)).obj LA ≅ L) :
    ∃! a : L ⟶ (pushforward (lineDualProjection f)).obj LA,
      lineReduction f L LA e ≫ a = lineEpsilon f LA := by
  sorry

/-- The uniquely determined epsilon inclusion, not a choice of an extension class.
Source: Stacks 0C6R.
(blueprint: lem-sfb-line-section-first-order-obstruction). -/
def lineInclusion (f : C ⟶ Spec (.of k)) (L : C.Modules)
    (LA : (lineDualBase f).Modules) [LA.IsInvertible]
    (e : (tensorPullback (lineDualZero f)).obj LA ≅ L) :
    L ⟶ (pushforward (lineDualProjection f)).obj LA :=
  (lineInclusion_existsUnique f L LA e).exists.choose

/-- The epsilon inclusion followed by reduction is zero. Source: Stacks 0C6R.
(blueprint: lem-sfb-line-section-first-order-obstruction).
Proof: in each line frame the composite sends a to (0,a) and then to zero. -/
theorem lineInclusion_reduction (f : C ⟶ Spec (.of k)) (L : C.Modules)
    (LA : (lineDualBase f).Modules) [LA.IsInvertible]
    (e : (tensorPullback (lineDualZero f)).obj LA ≅ L) :
    lineInclusion f L LA e ≫ lineReduction f L LA e = 0 := by
  sorry

/-- The canonical epsilon sequence on C. Source: Stacks 0C6R.
(blueprint: lem-sfb-line-section-first-order-obstruction). -/
def lineEpsilonSequence (f : C ⟶ Spec (.of k)) (L : C.Modules)
    (LA : (lineDualBase f).Modules) [LA.IsInvertible]
    (e : (tensorPullback (lineDualZero f)).obj LA ≅ L) : ShortComplex C.Modules :=
  ShortComplex.mk (lineInclusion f L LA e) (lineReduction f L LA e)
    (lineInclusion_reduction f L LA e)

/-- Exactness of the canonical epsilon sequence. Source: Stacks 0C6R.
(blueprint: lem-sfb-line-section-first-order-obstruction).
Proof (node step 1): on each frame the sequence is the direct sum of the inclusion
of the second coefficient and projection onto the first coefficient of O_C[epsilon].
Exactness is local, hence these computations prove short exactness. -/
theorem lineEpsilonSequence_shortExact (f : C ⟶ Spec (.of k)) (L : C.Modules)
    (LA : (lineDualBase f).Modules) [LA.IsInvertible]
    (e : (tensorPullback (lineDualZero f)).obj LA ≅ L) :
    (lineEpsilonSequence f L LA e).ShortExact := by
  sorry

/-- The actual connecting map, with scalars restricted from Γ(C,O_C) to k.
Source: Stacks 01DZ, 0B8S and 0C6R.
(blueprint: lem-sfb-line-section-first-order-obstruction). -/
def lineSectionBoundary (f : C ⟶ Spec (.of k)) (L : C.Modules)
    (LA : (lineDualBase f).Modules) [LA.IsInvertible]
    (e : (tensorPullback (lineDualZero f)).obj LA ≅ L) :
    scalarCohomology f L 0 ⟶ scalarCohomology f L 1 :=
  (ModuleCat.restrictScalars (scalarMap f ⊤)).map
    (RingedSpace.moduleCohomologyBoundary C.toRingedSpace
      (lineEpsilonSequence f L LA e) (lineEpsilonSequence_shortExact f L LA e) 0)

/-- The ordinary module Čech complex. Source: Stacks 01EQ.
(blueprint: lem-sfb-line-section-first-order-obstruction). -/
abbrev lineCech {ι : Type u} (U : ι → C.Opens) (F : C.Modules) :=
  (cechComplexFunctor U).obj F.presheafModuleCat

/-- A component of a Čech cochain, indexed by an ordered tuple of opens.
Source: Stacks 01EQ (blueprint: lem-sfb-line-section-first-order-obstruction). -/
def lineCechComponent {ι : Type u} (U : ι → C.Opens) (F : C.Modules)
    (n : ℕ) (z : (lineCech U F).X n) (y : Fin (n + 1) → ι) :
    Γ(F, ∏ᶜ fun j : Fin (n + 1) ↦ U (y j)) :=
  (Pi.π (fun w : Fin (n + 1) → ι ↦
    F.presheafModuleCat.obj (op (∏ᶜ fun j : Fin (n + 1) ↦ U (w j)))) y) z

/-- Canonical degree-one comparison, characterized by injective resolutions.
Source: Stacks 01EQ (blueprint: lem-sfb-line-section-first-order-obstruction). -/
def lineCechComparison {ι : Type u} (U : ι → C.Opens) (hU : iSup U = ⊤)
    (F : C.Modules) :=
  Classical.choose (cechH1Map_natural C U hU) F

/-- The class of the additive transition cocycle in ordinary Zariski cohomology.
Source: Stacks 0C6R (blueprint: lem-sfb-line-section-first-order-obstruction). -/
def lineDeformationClass (f : C ⟶ Spec (.of k)) {ι : Type u}
    (U : ι → C.Opens) (hU : iSup U = ⊤)
    (a : (lineCech U (𝟙_ C.Modules)).cycles 1) : scalarCohomology f (𝟙_ C.Modules) 1 :=
  lineCechComparison U hU _ ((lineCech U _).homologyπ 1 a)

/-- Transition data in the convention e_j = t_ij e_i. The thickened frames are
actual free generators; their reductions are computed by the specified reduction.
Source: Stacks 0C6R, units 1+epsilon a.
(blueprint: lem-sfb-line-section-first-order-obstruction). -/
structure LineTransitionData (f : C ⟶ Spec (.of k)) (L : C.Modules)
    (LA : (lineDualBase f).Modules) (e : (tensorPullback (lineDualZero f)).obj LA ≅ L)
    {ι : Type u} (U : ι → C.Opens)
    (a : (lineCech U (𝟙_ C.Modules)).cycles 1) where
  frame : ∀ i, Γ(LA, lineDualProjection f ⁻¹ᵁ U i)
  generator : ∀ i, IsFreeGenerator (frame i)
  transition : ∀ y : Fin 2 → ι, (Γ(C, ∏ᶜ fun j : Fin 2 ↦ U (y j)))ˣ
  relation : ∀ y : Fin 2 → ι,
    let W := ∏ᶜ fun j : Fin 2 ↦ U (y j)
    let E := (pushforward (lineDualProjection f)).obj LA
    let ei := E.presheaf.map (Pi.π (fun j : Fin 2 ↦ U (y j)) 0).op (frame (y 0))
    let ej := E.presheaf.map (Pi.π (fun j : Fin 2 ↦ U (y j)) 1).op (frame (y 1))
    let aij := (unitSectionsEquiv W).symm
      (lineCechComponent U (𝟙_ C.Modules) 1 ((lineCech U _).iCycles 1 a) y)
    ej = (transition y : Γ(C, W)) • ei +
      (lineEpsilon f LA).app W (aij • (transition y : Γ(C, W)) • ei)

/-- A smooth connected curve has constant relative dimension one.
Source: Stacks 0BS2 and the dimension formula for smooth morphisms.
(blueprint: lem-sfb-line-section-first-order-obstruction).
Proof: a smooth scheme over a field is regular; its irreducible components are
open and closed. Connectedness leaves a single component, of dimension one by
IsConnectedCurve. Smooth relative dimension equals the component dimension. -/
theorem lineCurve_relativeDimension (f : C ⟶ Spec (.of k))
    [IsConnectedCurve f] [Smooth f] : SmoothOfRelativeDimension 1 f := by
  sorry

/-- The residue-normalized trace supplied by the recorded Picard duality theorem.
Its normalization on each integral component determines it uniquely, so this is
not a choice of a scalar multiple of a perfect pairing.
Source: Stacks 0BS2, 0BS4 and det-thm-picard-duality.
(blueprint: lem-sfb-line-section-first-order-obstruction). -/
def lineResidueTrace (f : C ⟶ Spec (.of k)) [IsAlgClosed k]
    [IsConnectedCurve f] [Smooth f] [IsHProjective f] :
    Module.Dual k (scalarCohomology f f.relativeDifferentials 1) :=
  letI : C.Over (Spec (.of k)) := ⟨f⟩
  letI : SmoothOfRelativeDimension 1 (C ↘ Spec (.of k)) := lineCurve_relativeDimension f
  letI : IsProper (C ↘ Spec (.of k)) := IsHProjective.isProper f
  Classical.choose (Scheme.picard_duality_one (k := k) (X := C))

/-- A section as its canonical multiplication morphism O_C → L.
Source: Stacks 0BS4 (blueprint: lem-sfb-line-section-first-order-obstruction). -/
def lineSectionMap (f : C ⟶ Spec (.of k)) (L : C.Modules)
    (s : scalarCohomology f L 0) : (𝟙_ C.Modules) ⟶ L :=
  homOfGlobalSection L (scalarGlobalSectionsEquiv f L s)

/-- First-order section obstruction, its exact residue-trace duality formula,
and the simultaneous opposite-sign convention.
Source: Stacks 0C6R, 01EQ, 0BS2 and 0BS4; the node's local-frame calculation.
(blueprint: lem-sfb-line-section-first-order-obstruction).
Proof (node steps 1--4 and 8): the epsilon sequence is locally the coefficient
sequence (a,b) ↦ a, with epsilon inclusion a ↦ (0,a). In the displayed frames,
s_i=t_ij s_j and the difference of lifts is epsilon t_ij a_ij s_j e_i.
The boundary/Čech comparison therefore sends the coefficient cocycle multiplied
by s to the boundary of s. Naturality gives H¹(m_s)(v). Naturality of the
recorded cup/evaluation/residue-trace pairing with respect to m_s identifies its
pairing with t with that of v and (m_s dual tensor omega)(t), which is s t.
Negating the comparison and boundary negates v and the boundary; bilinearity
negates both sides together, also in characteristic two. -/
theorem line_section_first_order_obstruction (f : C ⟶ Spec (.of k))
    [IsAlgClosed k] [IsConnectedCurve f] [Smooth f] [IsHProjective f]
    (L : C.Modules) [L.IsInvertible] (LA : (lineDualBase f).Modules) [LA.IsInvertible]
    (e : (tensorPullback (lineDualZero f)).obj LA ≅ L)
    {ι : Type u} (U : ι → C.Opens) (hU : iSup U = ⊤)
    (a : (lineCech U (𝟙_ C.Modules)).cycles 1)
    (_frames : LineTransitionData f L LA e U a) (s : scalarCohomology f L 0) :
    letI : MonoidalCategory (SheafOfModules.{u} C.ringCatSheaf) :=
      SheafOfModules.monoidalCategory C.sheaf;
    (∃ z : (lineCech U L).cycles 1,
      (∀ y : Fin 2 → ι,
        lineCechComponent U L 1 ((lineCech U L).iCycles 1 z) y =
          (unitSectionsEquiv (∏ᶜ fun j : Fin 2 ↦ U (y j))).symm
            (lineCechComponent U (𝟙_ C.Modules) 1 ((lineCech U _).iCycles 1 a) y) •
            L.presheaf.map (homOfLE le_top).op (scalarGlobalSectionsEquiv f L s)) ∧
      lineCechComparison U hU L ((lineCech U L).homologyπ 1 z) =
        lineSectionBoundary f L LA e s) ∧
    lineSectionBoundary f L LA e s =
      scalarCohomologyMap f (lineSectionMap f L s) 1 (lineDeformationClass f U hU a) ∧
    (∀ t : scalarCohomology f (dual L ⊗ f.relativeDifferentials) 0,
      picardTracePairing f f.relativeDifferentials 1 (lineResidueTrace f) L 1
          (lineSectionBoundary f L LA e s) t =
        picardTracePairing f f.relativeDifferentials 1 (lineResidueTrace f) (𝟙_ C.Modules) 1
          (lineDeformationClass f U hU a)
          (scalarCohomologyMap f (dualMap (lineSectionMap f L s) ▷ f.relativeDifferentials)
            0 t)) ∧
    (∀ t : scalarCohomology f (dual L ⊗ f.relativeDifferentials) 0,
      picardTracePairing f f.relativeDifferentials 1 (lineResidueTrace f) L 1
          (-(lineSectionBoundary f L LA e s)) t =
        picardTracePairing f f.relativeDifferentials 1 (lineResidueTrace f) (𝟙_ C.Modules) 1
          (-(lineDeformationClass f U hU a))
          (scalarCohomologyMap f (dualMap (lineSectionMap f L s) ▷ f.relativeDifferentials)
            0 t)) := by
  sorry

/-- Restriction of a dual-number complex to the constant field.
Source: Stacks 011J (blueprint: lem-sfb-line-section-first-order-obstruction). -/
abbrev lineUnderlyingComplex (E : CochainComplex (ModuleCat.{u} (DualNumber k)) ℤ) :=
  ((ModuleCat.restrictScalars (algebraMap k (DualNumber k))).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj E

/-- The reduced complex k tensor_A E, with its induced differential d_0.
Source: Stacks 011J (blueprint: lem-sfb-line-section-first-order-obstruction). -/
abbrev lineReducedComplex (E : CochainComplex (ModuleCat.{u} (DualNumber k)) ℤ) :=
  ((ModuleCat.extendScalars (TrivSqZeroExt.fstHom k k k).toRingHom).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj E

/-- Reduction on each term, the unit of coefficient extension/restriction.
Source: Stacks 011J (blueprint: lem-sfb-line-section-first-order-obstruction). -/
def lineTermReduction (E : CochainComplex (ModuleCat.{u} (DualNumber k)) ℤ)
    (n : ℤ) (x : E.X n) : (lineReducedComplex E).X n :=
  ((ModuleCat.extendRestrictScalarsAdj (TrivSqZeroExt.fstHom k k k).toRingHom).unit.app
    (E.X n)) x

/-- The scalar section Čech complex, extended by zero to negative degrees.
Source: Stacks 01EQ (blueprint: lem-sfb-line-section-first-order-obstruction). -/
abbrev lineScalarCech (f : C ⟶ Spec (.of k)) {ι : Type u}
    (U : ι → C.Opens) (F : C.Modules) :=
  ((picardCechFunctor f U).obj F).extend ComplexShape.embeddingUpNat

/-- The coefficient map on the specified scalar section complexes.
Source: Stacks 01EQ (blueprint: lem-sfb-line-section-first-order-obstruction). -/
def lineScalarCechMap (f : C ⟶ Spec (.of k)) {ι : Type u} (U : ι → C.Opens)
    {F G : C.Modules} (g : F ⟶ G) : lineScalarCech f U F ⟶ lineScalarCech f U G :=
  HomologicalComplex.extendMap ((picardCechFunctor f U).map g) ComplexShape.embeddingUpNat

/-- Normalization of a scalar comparison in integer degree n ≥ 0.
It must be exactly the recorded canonical Čech comparison after extension by zero.
Source: Stacks 01EQ (blueprint: lem-sfb-line-section-first-order-obstruction). -/
def IsLineModelComparison (f : C ⟶ Spec (.of k)) {ι : Type u}
    (U : ι → C.Opens) (F : C.Modules) (n : ℕ)
    (c : (lineScalarCech f U F).homology (n : ℤ) ≃ₗ[k] scalarCohomology f F n) : Prop :=
  ∃ b : ((picardCechFunctor f U).obj F).homology n ≃ₗ[k] scalarCohomology f F n,
    IsPicardScalarCechComparison f U F n b ∧ ∀ x,
      c x = b ((((picardCechFunctor f U).obj F).extendHomologyIso
        ComplexShape.embeddingUpNat (j := n) rfl).hom x)

/-- The actual A-module presheaf of L_A on the opens of C. Its action is
restricted along the specified A-structure map; it is not an arbitrary epsilon action.
Source: Stacks 0C6R (blueprint: lem-sfb-line-section-first-order-obstruction). -/
def lineAPresheaf (f : C ⟶ Spec (.of k)) (LA : (lineDualBase f).Modules) :
    C.Opensᵒᵖ ⥤ ModuleCat.{u} (DualNumber k) :=
  (TopologicalSpace.Opens.map (lineDualProjection f).base).op ⋙
    LA.presheafModuleCat ⋙ ModuleCat.restrictScalars (lineDualScalars f)

/-- An A-linear Čech representative of derived sections of L_A.
Source: Stacks 01EQ, 01XD (blueprint: lem-sfb-line-section-first-order-obstruction). -/
def lineACech (f : C ⟶ Spec (.of k)) {ι : Type u} (U : ι → C.Opens)
    (LA : (lineDualBase f).Modules) : CochainComplex (ModuleCat.{u} (DualNumber k)) ℤ :=
  ((cechComplexFunctor U).obj (lineAPresheaf f LA)).extend ComplexShape.embeddingUpNat

/-- The coordinate-preserving identification between forgetting A on the section
complex and taking the scalar section complex of p_* L_A. Its coordinate equation
uniquely determines the map, including its normalization in degree zero.
Source: Stacks 01EQ (blueprint: lem-sfb-line-section-first-order-obstruction).
Proof: both sides have the same section groups on the same intersections. The k
scalar action is obtained by the same structural morphism since p is over k.
Identity on each section group is therefore k-linear and commutes with all signed
restriction differentials. The product projections determine these maps uniquely.
In negative degrees both sides are zero, so the maps are again unique. -/
theorem lineACech_forget_existsUnique (f : C ⟶ Spec (.of k)) {ι : Type u}
    (U : ι → C.Opens) (LA : (lineDualBase f).Modules) :
    ∃! ψ : lineUnderlyingComplex (lineACech f U LA) ⟶
        lineScalarCech f U ((pushforward (lineDualProjection f)).obj LA),
      ∀ (n : ℕ) (x : (lineUnderlyingComplex (lineACech f U LA)).X (n : ℤ))
        (y : Fin (n + 1) → ι),
        (Pi.π (fun w : Fin (n + 1) → ι ↦
          (scalarPresheaf f ((pushforward (lineDualProjection f)).obj LA)).obj
            (op (∏ᶜ fun j : Fin (n + 1) ↦ U (w j)))) y)
          ((((picardCechFunctor f U).obj
            ((pushforward (lineDualProjection f)).obj LA)).extendXIso
              ComplexShape.embeddingUpNat (i := n) rfl).hom (ψ.f (n : ℤ) x)) =
        (Pi.π (fun w : Fin (n + 1) → ι ↦
          (lineAPresheaf f LA).obj (op (∏ᶜ fun j : Fin (n + 1) ↦ U (w j)))) y)
          ((((cechComplexFunctor U).obj (lineAPresheaf f LA)).extendXIso
            ComplexShape.embeddingUpNat (i := n) rfl).hom x) := by
  sorry

/-- The unique coordinate-preserving scalar-forgetful comparison.
Source: Stacks 01EQ (blueprint: lem-sfb-line-section-first-order-obstruction). -/
def lineACechForget (f : C ⟶ Spec (.of k)) {ι : Type u}
    (U : ι → C.Opens) (LA : (lineDualBase f).Modules) :
    lineUnderlyingComplex (lineACech f U LA) ⟶
      lineScalarCech f U ((pushforward (lineDualProjection f)).obj LA) :=
  (lineACech_forget_existsUnique f U LA).exists.choose

/-- A supplied A-linear complex model, viewed on the common k-scalar section complex.
Source: Stacks 011J (blueprint: lem-sfb-line-section-first-order-obstruction). -/
def lineForgetModel (f : C ⟶ Spec (.of k)) {ι : Type u}
    (U : ι → C.Opens) (LA : (lineDualBase f).Modules)
    (E : CochainComplex (ModuleCat.{u} (DualNumber k)) ℤ) (φ : E ⟶ lineACech f U LA) :
    lineUnderlyingComplex E ⟶
      lineScalarCech f U ((pushforward (lineDualProjection f)).obj LA) :=
  ((ModuleCat.restrictScalars (algebraMap k (DualNumber k))).mapHomologicalComplex
    (ComplexShape.up ℤ)).map φ ≫ lineACechForget f U LA

/-- RΓ(C_A,L_A) in D(A), using the actual global-sections functor and scalar restriction.
Source: Stacks 0B6A (blueprint: lem-sfb-line-section-first-order-obstruction). -/
def lineDerivedSectionsA (f : C ⟶ Spec (.of k)) (LA : (lineDualBase f).Modules) :=
  ((RingedSpace.globalSectionsFunctor (lineDualBase f).toRingedSpace ⋙
    ModuleCat.restrictScalars (lineDualScalars f)).rightDerivedFunctor).obj
      ((DerivedCategory.singleFunctor _ 0).obj LA)

/-- Every specified derived two-term finite-free model can be represented by an
A-linear quasi-isomorphism to this section complex. This is why specifying a chain
comparison in the model formula adds no restriction to the node's derived model.
Source: Stacks 01EQ, 01XD, 064K; node steps 5--8.
(blueprint: lem-sfb-line-section-first-order-obstruction).
Proof: the affine-cover Čech resolution computes the displayed derived sections.
Its canonical comparison is an isomorphism in D(A). A bounded complex of finite
free modules is K-projective. The localization map from its homotopy morphisms to
derived morphisms is bijective. Lift the supplied derived isomorphism composed
with the inverse Čech comparison, then choose a chain representative. Its image
in the derived category is invertible, so it is a quasi-isomorphism. -/
theorem lineModel_chainRepresentative (f : C ⟶ Spec (.of k))
    [IsConnectedCurve f] [Smooth f] [IsHProjective f]
    (LA : (lineDualBase f).Modules) [LA.IsInvertible]
    {ι : Type u} (U : ι → C.Opens) (_hcover : iSup U = ⊤)
    (_hU : ∀ (n : ℕ) (y : Fin (n + 1) → ι), IsAffineOpen (⨅ j, U (y j)))
    (E : CochainComplex (ModuleCat.{u} (DualNumber k)) ℤ)
    (_hge : E.IsStrictlyGE 0) (_hle : E.IsStrictlyLE 1)
    (_hfree : ∀ n : ℤ, Module.Free (DualNumber k) (E.X n))
    (_hfinite : ∀ n : ℤ, Module.Finite (DualNumber k) (E.X n))
    (_model : DerivedCategory.Q.obj E ≅ lineDerivedSectionsA f LA) :
    ∃ φ : E ⟶ lineACech f U LA, QuasiIso φ := by
  sorry

/-- Every specified derived comparison to the actual Čech representative lifts
to a chain comparison; its equality after localization retains the given model.
Source: Stacks 064K (blueprint: lem-sfb-line-section-first-order-obstruction).
Proof: a bounded complex of projective modules is K-projective. Full faithfulness
of its localization on morphisms gives a homotopy class mapping to α.hom. Choose
a chain representative; invertibility of α makes it a quasi-isomorphism. -/
theorem lineModel_specifiedComparison (f : C ⟶ Spec (.of k))
    (LA : (lineDualBase f).Modules) {ι : Type u} (U : ι → C.Opens)
    (E : CochainComplex (ModuleCat.{u} (DualNumber k)) ℤ)
    (_hge : E.IsStrictlyGE 0) (_hle : E.IsStrictlyLE 1)
    (_hfree : ∀ n : ℤ, Module.Free (DualNumber k) (E.X n))
    (_hfinite : ∀ n : ℤ, Module.Finite (DualNumber k) (E.X n))
    (α : DerivedCategory.Q.obj E ≅ DerivedCategory.Q.obj (lineACech f U LA)) :
    ∃ φ : E ⟶ lineACech f U LA, QuasiIso φ ∧ DerivedCategory.Q.map φ = α.hom := by
  sorry

/-- The reduced comparison of a finite-free model is uniquely determined by its
unreduced comparison and the actual reduction map. This defines the natural
identifications, rather than supplying arbitrary isomorphisms on cohomology.
Source: Stacks 011J and the coefficient triangle in node steps 5--7.
(blueprint: lem-sfb-line-section-first-order-obstruction).
Proof: reduction is the tensor adjunction unit, a surjection whose kernel is epsilon.
The displayed equivariance and reduction times epsilon equal to zero show that the
right side factors uniquely through that quotient in each degree. These maps are
k-linear and commute with differential by uniqueness and the chain-map identity. -/
theorem lineModel_reduction_existsUnique (f : C ⟶ Spec (.of k))
    (L : C.Modules) (LA : (lineDualBase f).Modules)
    (e : (tensorPullback (lineDualZero f)).obj LA ≅ L)
    {ι : Type u} (U : ι → C.Opens)
    (E : CochainComplex (ModuleCat.{u} (DualNumber k)) ℤ)
    (φ : lineUnderlyingComplex E ⟶
      lineScalarCech f U ((pushforward (lineDualProjection f)).obj LA))
    (_hε : ∀ (n : ℤ) (x : E.X n), φ.f n ((DualNumber.eps : DualNumber k) • x) =
      (lineScalarCechMap f U (lineEpsilon f LA)).f n (φ.f n x)) :
    ∃! β : lineReducedComplex E ⟶ lineScalarCech f U L,
      ∀ (n : ℤ) (x : E.X n), β.f n (lineTermReduction E n x) =
        (lineScalarCechMap f U (lineReduction f L LA e)).f n (φ.f n x) := by
  sorry

/-- The canonical reduced comparison exists for every A-linear model; thus the
model formula does not assume a factorization not supplied by the deformation.
Source: Stacks 011J and node steps 5--7.
(blueprint: lem-sfb-line-section-first-order-obstruction).
Proof: the coefficient reduction is surjective with kernel epsilon. A-linearity
of φ and epsilon times reduction equal to zero give the unique factorization of
lineModel_reduction_existsUnique. The coordinate-preserving forgetful comparison
intertwines the actual epsilon action with lineEpsilon, term by term. -/
theorem lineModel_reducedComparison (f : C ⟶ Spec (.of k))
    (L : C.Modules) (LA : (lineDualBase f).Modules)
    (e : (tensorPullback (lineDualZero f)).obj LA ≅ L)
    {ι : Type u} (U : ι → C.Opens)
    (E : CochainComplex (ModuleCat.{u} (DualNumber k)) ℤ) (φ : E ⟶ lineACech f U LA) :
    ∃! β : lineReducedComplex E ⟶ lineScalarCech f U L,
      ∀ (n : ℤ) (x : E.X n), β.f n (lineTermReduction E n x) =
        (lineScalarCechMap f U (lineReduction f L LA e)).f n
          ((lineForgetModel f U LA E φ).f n x) := by
  sorry

/-- The normalized identifications of the scalar Čech model with ordinary module
cohomology exist in every nonnegative degree.
Source: Stacks 01EQ, 01XD (blueprint: lem-sfb-line-section-first-order-obstruction).
Proof: apply picardScalarCechComparison_exists to the affine-intersection cover,
then precompose with the canonical extendHomologyIso. This supplies exactly the
normalization in IsLineModelComparison, without an arbitrary cohomology isomorphism. -/
theorem lineModel_cohomologyComparison (f : C ⟶ Spec (.of k))
    (L : C.Modules) [L.IsInvertible] {ι : Type u} (U : ι → C.Opens)
    (_hcover : iSup U = ⊤)
    (_hU : ∀ (n : ℕ) (y : Fin (n + 1) → ι), IsAffineOpen (⨅ j, U (y j)))
    (n : ℕ) :
    ∃ c : (lineScalarCech f U L).homology (n : ℤ) ≃ₗ[k] scalarCohomology f L n,
      IsLineModelComparison f U L n c := by
  sorry

/-- The end cohomology groups of the reduced two-term complex are canonically
ker d_0 and coker d_0, with their actual inclusion and quotient maps.
Source: Stacks 011J (blueprint: lem-sfb-line-section-first-order-obstruction).
Proof: the incoming differential at zero is zero, so cycles are exactly the kernel
of d_0 and the boundary quotient is the identity. The outgoing differential at one
is zero, so every degree-one element is a cycle and homology is its quotient by
the image of d_0. Kernel and cokernel universal properties uniquely determine the
displayed isomorphisms with these normalization equations. -/
theorem lineModel_kernelCokernel
    (E : CochainComplex (ModuleCat.{u} (DualNumber k)) ℤ)
    (_hge : E.IsStrictlyGE 0) (_hle : E.IsStrictlyLE 1) :
    (∃! b₀ : (lineReducedComplex E).cycles 0 ≅ kernel ((lineReducedComplex E).d 0 1),
      b₀.hom ≫ kernel.ι ((lineReducedComplex E).d 0 1) =
        (lineReducedComplex E).iCycles 0) ∧
    (∃! b₁ : (lineReducedComplex E).homology 1 ≅ cokernel ((lineReducedComplex E).d 0 1),
      ∀ z : (lineReducedComplex E).cycles 1,
        b₁.hom ((lineReducedComplex E).homologyπ 1 z) =
          cokernel.π ((lineReducedComplex E).d 0 1) ((lineReducedComplex E).iCycles 1 z)) := by
  sorry

/-- Epsilon inverse of d_A of any lifted cycle gives the canonical section
obstruction, in every two-term finite-free model. A model is supplied as an
A-linear quasi-isomorphism to the affine Čech representative: A-linearity is
expressed by k-linearity together with epsilon equivariance. A bounded finite
projective complex realizes every derived model by such a comparison.
Source: Stacks 011J, 011K, 01EQ, 01XD, and node steps 5--8.
(blueprint: lem-sfb-line-section-first-order-obstruction).
Proof: the affine-intersection Čech section terms are A-flat, and their reduction
is exactly the section complex of L. The comparison φ is A-linear since it is
k-linear and epsilon equivariant. Both this flat Čech model and the bounded free
model compute derived coefficient extension. Thus the uniquely descended β is
a quasi-isomorphism. The canonical coefficient triangles are identified, including
the connecting arrow, by this same comparison and projection-formula naturality.
For a reduced cycle x and any lift y, d_A y lies in epsilon E_A¹; freeness identifies
epsilon E_A¹ with E¹. Choose z with d_A y = epsilon z. Its reduction is a degree-one
cycle, since the complex has no term in degree two. The split coefficient sequence
computes the boundary by its class. If y changes by epsilon w, the class changes by
d_0 of the reduction of w, hence vanishes in the cokernel. Every φ and every E gives
the same boundary under the normalized comparisons, proving model independence.
The zero-term and zero-rank cases use the same coefficient sequence. -/
theorem line_section_first_order_obstruction_model (f : C ⟶ Spec (.of k))
    [IsAlgClosed k] [IsConnectedCurve f] [Smooth f] [IsHProjective f]
    (L : C.Modules) [L.IsInvertible] (LA : (lineDualBase f).Modules) [LA.IsInvertible]
    (e : (tensorPullback (lineDualZero f)).obj LA ≅ L)
    {ι : Type u} (U : ι → C.Opens) (hcover : iSup U = ⊤)
    (hU : ∀ (n : ℕ) (y : Fin (n + 1) → ι), IsAffineOpen (⨅ j, U (y j)))
    (E : CochainComplex (ModuleCat.{u} (DualNumber k)) ℤ)
    (_hge : E.IsStrictlyGE 0) (_hle : E.IsStrictlyLE 1)
    (_hfree : ∀ n : ℤ, Module.Free (DualNumber k) (E.X n))
    (_hfinite : ∀ n : ℤ, Module.Finite (DualNumber k) (E.X n))
    (φ : E ⟶ lineACech f U LA) (_hφ : QuasiIso φ)
    (β : lineReducedComplex E ⟶ lineScalarCech f U L)
    (_hβ : ∀ (n : ℤ) (x : E.X n), β.f n (lineTermReduction E n x) =
      (lineScalarCechMap f U (lineReduction f L LA e)).f n ((lineForgetModel f U LA E φ).f n x))
    (c₀ : (lineScalarCech f U L).homology (0 : ℤ) ≃ₗ[k] scalarCohomology f L 0)
    (_hc₀ : IsLineModelComparison f U L 0 c₀)
    (c₁ : (lineScalarCech f U L).homology (1 : ℤ) ≃ₗ[k] scalarCohomology f L 1)
    (_hc₁ : IsLineModelComparison f U L 1 c₁) :
    QuasiIso β ∧ IsIso ((lineReducedComplex E).homologyπ 0) ∧
    (∀ z : (lineReducedComplex E).X 1,
      ∃! z' : (lineReducedComplex E).cycles 1, (lineReducedComplex E).iCycles 1 z' = z) ∧
    (∀ x : (lineReducedComplex E).cycles 0,
      ∃ y : E.X 0, lineTermReduction E 0 y = (lineReducedComplex E).iCycles 0 x) ∧
    (∀ (x : (lineReducedComplex E).cycles 0) (y : E.X 0),
      lineTermReduction E 0 y = (lineReducedComplex E).iCycles 0 x →
      (∃ z : E.X 1, E.d 0 1 y = (DualNumber.eps : DualNumber k) • z) ∧
      ∀ (z : E.X 1) (z' : (lineReducedComplex E).cycles 1),
        E.d 0 1 y = (DualNumber.eps : DualNumber k) • z →
        (lineReducedComplex E).iCycles 1 z' = lineTermReduction E 1 z →
        c₁ (HomologicalComplex.homologyMap β 1 ((lineReducedComplex E).homologyπ 1 z')) =
          lineSectionBoundary f L LA e
            (c₀ (HomologicalComplex.homologyMap β 0
              ((lineReducedComplex E).homologyπ 0 x)))) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
