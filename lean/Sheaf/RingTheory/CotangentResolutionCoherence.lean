/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q106
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Differentials.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.Algebra.MvPolynomial.Eval
import Sheaf.CategoryTheory.AdjunctionStandardSimplicialHomotopy
import Sheaf.Paper.TrivialKanHomotopyEquivalence

/-!
# Cotangent complexes from polynomial resolutions

Source: Stacks Project, Cotangent Complex, Tags 08PM, 08PN, 08QI and 08QL
(blueprint: lem-trf-cotangent-resolution-coherence).

The data below spell out the construction and its coherence, including the values
on polynomial generators. The existence theorem supplies these specified data
simultaneously. No definition chooses an object from a mere existence assertion.
-/

@[expose] public noncomputable section

universe u v w

open CategoryTheory Opposite Simplicial
open scoped ChangeOfRings

namespace Algebra.CotangentResolution

/-- The alternating complex in nonpositive cohomological degrees. Source: Stacks,
Tag 08PN (blueprint: lem-trf-cotangent-resolution-coherence). -/
def negativeComplex (C : Type v) [Category.{w} C] [Preadditive C]
    [Limits.HasZeroObject C] : SimplicialObject C ⥤ CochainComplex C ℤ :=
  AlgebraicTopology.alternatingFaceMapComplex C ⋙
    ComplexShape.embeddingDownNat.extendFunctor C

/-- An augmented simplicial algebra over the ring map `f`, including its base
structure. Source: Stacks, Tags 08PM and 08QI
(blueprint: lem-trf-cotangent-resolution-coherence). -/
structure Augmentation (f : Arrow CommRingCat.{u}) where
  algebra : SimplicialObject CommRingCat.{u}
  base : (SimplicialObject.const CommRingCat).obj f.left ⟶ algebra
  augmentation : algebra ⟶ (SimplicialObject.const CommRingCat).obj f.right
  triangle : ∀ n : ℕ, base.app (op ⦋n⦌) ≫ augmentation.app (op ⦋n⦌) = f.hom

/-- An augmented semilinear map over the commutative ring square `q`.
Source: Stacks, Tag 08QL (blueprint: lem-trf-cotangent-resolution-coherence). -/
structure AugmentedMap {f g : Arrow CommRingCat.{u}} (q : f ⟶ g)
    (P : Augmentation f) (Q : Augmentation g) where
  map : P.algebra ⟶ Q.algebra
  base : ∀ n : ℕ, P.base.app (op ⦋n⦌) ≫ map.app (op ⦋n⦌) =
    q.left ≫ Q.base.app (op ⦋n⦌)
  augmentation : ∀ n : ℕ, map.app (op ⦋n⦌) ≫ Q.augmentation.app (op ⦋n⦌) =
    P.augmentation.app (op ⦋n⦌) ≫ q.right

/-- The actual polynomial rings `(F_A U)^(n+1) B`. Source: Stacks, Tag 08PM
(blueprint: lem-trf-cotangent-resolution-coherence). -/
def standardTerm (f : Arrow CommRingCat.{u}) : ℕ → CommRingCat.{u}
  | 0 => .of (MvPolynomial f.right f.left)
  | n + 1 => .of (MvPolynomial (standardTerm f n) f.left)

/-- Inclusion of coefficients into a standard term. Source: Stacks, Tag 08PM
(blueprint: lem-trf-cotangent-resolution-coherence). -/
def standardBase (f : Arrow CommRingCat.{u}) : (n : ℕ) → f.left ⟶ standardTerm f n
  | 0 => CommRingCat.ofHom MvPolynomial.C
  | _ + 1 => CommRingCat.ofHom MvPolynomial.C

/-- The iterated evaluation augmentation. Source: Stacks, Tag 08PM
(blueprint: lem-trf-cotangent-resolution-coherence). -/
def standardAugmentation (f : Arrow CommRingCat.{u}) :
    (n : ℕ) → standardTerm f n ⟶ f.right
  | 0 => CommRingCat.ofHom (MvPolynomial.eval₂Hom f.hom.hom (fun b ↦ b))
  | n + 1 => CommRingCat.ofHom
      (MvPolynomial.eval₂Hom f.hom.hom (standardAugmentation f n))

/-- The prescribed faces: evaluate the outer layer for `i = 0`, and otherwise
apply the preceding face to variable labels. Source: Stacks, Tag 08PM
(blueprint: lem-trf-cotangent-resolution-coherence). -/
def standardFace (f : Arrow CommRingCat.{u}) :
    (n : ℕ) → Fin (n + 2) → (standardTerm f (n + 1) ⟶ standardTerm f n)
  | 0, i => CommRingCat.ofHom (MvPolynomial.eval₂Hom MvPolynomial.C
      (if i = 0 then (fun p ↦ p) else fun p ↦ MvPolynomial.X (standardAugmentation f 0 p)))
  | n + 1, i => CommRingCat.ofHom (MvPolynomial.eval₂Hom MvPolynomial.C
      (if h : i = 0 then (fun p ↦ p)
       else fun p ↦ MvPolynomial.X (standardFace f n (i.pred h) p)))

/-- The prescribed degeneracies insert the unit on variable labels.
Source: Stacks, Tag 08PM (blueprint: lem-trf-cotangent-resolution-coherence). -/
def standardDegeneracy (f : Arrow CommRingCat.{u}) :
    (n : ℕ) → Fin (n + 1) → (standardTerm f n ⟶ standardTerm f (n + 1))
  | 0, _ => CommRingCat.ofHom (MvPolynomial.eval₂Hom MvPolynomial.C
      (fun b ↦ MvPolynomial.X (MvPolynomial.X b)))
  | n + 1, i => CommRingCat.ofHom (MvPolynomial.eval₂Hom MvPolynomial.C
      (if h : i = 0 then fun p ↦ MvPolynomial.X (MvPolynomial.X p)
       else fun p ↦ MvPolynomial.X (standardDegeneracy f n (i.pred h) p)))

/-- The recursive ring-square map, sending coefficients through `q.left` and
`[p]` to `[q_n(p)]`. Source: Stacks, Tag 08QL
(blueprint: lem-trf-cotangent-resolution-coherence). -/
def standardSquareMap {f g : Arrow CommRingCat.{u}} (q : f ⟶ g) :
    (n : ℕ) → standardTerm f n ⟶ standardTerm g n
  | 0 => CommRingCat.ofHom (MvPolynomial.eval₂Hom
      (MvPolynomial.C.comp q.left.hom) (fun b ↦ MvPolynomial.X (q.right b)))
  | n + 1 => CommRingCat.ofHom (MvPolynomial.eval₂Hom
      (MvPolynomial.C.comp q.left.hom)
      (fun p ↦ MvPolynomial.X (standardSquareMap q n p)))

/-- Equality with the prescribed terms and operators, rather than an arbitrary
polynomial replacement. Source: Stacks, Tag 08PM
(blueprint: lem-trf-cotangent-resolution-coherence). -/
def IsStandard {f : Arrow CommRingCat.{u}} (P : Augmentation f) : Prop :=
  (∀ n : ℕ, P.algebra.obj (op ⦋n⦌) = standardTerm f n) ∧
  (∀ n : ℕ, HEq (P.base.app (op ⦋n⦌)) (standardBase f n)) ∧
  (∀ n : ℕ, HEq (P.augmentation.app (op ⦋n⦌)) (standardAugmentation f n)) ∧
  (∀ (n : ℕ) (i : Fin (n + 2)), HEq (P.algebra.δ i) (standardFace f n i)) ∧
  (∀ (n : ℕ) (i : Fin (n + 1)), HEq (P.algebra.σ i) (standardDegeneracy f n i))

/-- The additive augmentation to `B[0]`, constructed by the alternating-complex
augmentation and extension by zero. Source: Stacks, Tag 08QI
(blueprint: lem-trf-cotangent-resolution-coherence). -/
def additiveAugmentation {f : Arrow CommRingCat.{u}} (P : Augmentation f) :=
  HomologicalComplex.extendMap
    (AlgebraicTopology.AlternatingFaceMapComplex.ε.app
      (⟨P.algebra ⋙ (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat),
        (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).obj f.right,
        Functor.whiskerRight P.augmentation
          (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)⟩))
    ComplexShape.embeddingDownNat

/-- Polynomial, degreewise surjective, and a quasi-isomorphism to `B[0]`.
The displayed coefficient equation makes the polynomial isomorphism an
`A`-algebra isomorphism. Source: Stacks, Tag 08QI
(blueprint: lem-trf-cotangent-resolution-coherence). -/
def IsPolynomialResolution {f : Arrow CommRingCat.{u}} (P : Augmentation f) : Prop :=
  (∀ n : ℕ, ∃ (E : Type u)
    (e : CommRingCat.of (MvPolynomial E f.left) ≅ P.algebra.obj (op ⦋n⦌)),
    ∀ a : f.left, e.hom (MvPolynomial.C a) = P.base.app (op ⦋n⦌) a) ∧
  (∀ n : ℕ, Function.Surjective (P.augmentation.app (op ⦋n⦌))) ∧
  QuasiIso (additiveAugmentation P)

/-- The actual term `B ⊗_{P_n} Ω¹_{P_n/A}` (the symmetric order of the tensor
factors in the source). Source: Stacks, Tag 08PN
(blueprint: lem-trf-cotangent-resolution-coherence). -/
def differentialTerm {f : Arrow CommRingCat.{u}} (P : Augmentation f) (n : ℕ) :
    ModuleCat.{u} f.right :=
  (ModuleCat.extendScalars (P.augmentation.app (op ⦋n⦌)).hom).obj
    (CommRingCat.KaehlerDifferential (P.base.app (op ⦋n⦌)))

/-- The generating tensor `b ⊗ dx`. Source: Stacks, Tags 08PN and 08QL
(blueprint: lem-trf-cotangent-resolution-coherence). -/
def differentialGenerator {f : Arrow CommRingCat.{u}} (P : Augmentation f) (n : ℕ)
    (b : f.right) (x : P.algebra.obj (op ⦋n⦌)) : differentialTerm P n :=
  b ⊗ₜ[_, (P.augmentation.app (op ⦋n⦌)).hom] CommRingCat.KaehlerDifferential.d x

/-- The simplicial differential module, with the actual tensor terms identified
and every simplicial operator normalized on generators. Source: Stacks, Tag 08PN
(blueprint: lem-trf-cotangent-resolution-coherence). -/
structure DifferentialModel {f : Arrow CommRingCat.{u}} (P : Augmentation f) where
  module : SimplicialObject (ModuleCat.{u} f.right)
  termIso : ∀ n : ℕ, module.obj (op ⦋n⦌) ≅ differentialTerm P n
  operator : ∀ (m n : ℕ) (θ : ⦋m⦌ ⟶ ⦋n⦌) (b : f.right)
    (x : P.algebra.obj (op ⦋n⦌)),
    (termIso m).hom (module.map θ.op ((termIso n).inv (differentialGenerator P n b x))) =
      differentialGenerator P m b (P.algebra.map θ.op x)

/-- The differential complex `s(Ω¹_{P/A} ⊗_P B)`, with no positive terms.
Source: Stacks, Tag 08PN (blueprint: lem-trf-cotangent-resolution-coherence). -/
def differentialComplex {f : Arrow CommRingCat.{u}} {P : Augmentation f}
    (D : DifferentialModel P) : CochainComplex (ModuleCat.{u} f.right) ℤ :=
  (negativeComplex (ModuleCat.{u} f.right)).obj D.module

/-- The coordinate tensor in degree `-n` of the differential complex.
Source: Stacks, Tag 08PN (blueprint: lem-trf-cotangent-resolution-coherence). -/
def complexGenerator {f : Arrow CommRingCat.{u}} {P : Augmentation f}
    (D : DifferentialModel P) (n : ℕ) (b : f.right)
    (x : P.algebra.obj (op ⦋n⦌)) : (differentialComplex D).X (-(n : ℤ)) :=
  (((AlgebraicTopology.alternatingFaceMapComplex _).obj D.module).extendXIso
    ComplexShape.embeddingDownNat (i := n) rfl).inv
      ((D.termIso n).inv (differentialGenerator P n b x))

/-- Restriction on complexes, retaining both the coefficient ring and all degrees.
Source: Stacks, Tag 08QL (blueprint: lem-trf-cotangent-resolution-coherence). -/
def restrictComplex {B B' : CommRingCat.{u}} (β : B ⟶ B') :=
  (ModuleCat.restrictScalars.{u} β.hom).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The map on differential complexes specified by `b ⊗ dx ↦ β(b) ⊗ d(h(x))`.
Source: Stacks, Tag 08QL (blueprint: lem-trf-cotangent-resolution-coherence). -/
structure DifferentialMap {f g : Arrow CommRingCat.{u}} {q : f ⟶ g}
    {P : Augmentation f} {Q : Augmentation g} (h : AugmentedMap q P Q)
    (D : DifferentialModel P) (E : DifferentialModel Q) where
  map : differentialComplex D ⟶ (restrictComplex q.right).obj (differentialComplex E)
  generator : ∀ (n : ℕ) (b : f.right) (x : P.algebra.obj (op ⦋n⦌)),
    map.f (-(n : ℤ)) (complexGenerator D n b x) =
      complexGenerator E n (q.right b) (h.map.app (op ⦋n⦌) x)

/-- The derived object represented by the displayed differential complex. Applied
to the specified standard resolution, this is `L_{B/A}`. Source: Stacks, Tag 08PN
(blueprint: lem-trf-cotangent-resolution-coherence). -/
def derivedDifferentials {f : Arrow CommRingCat.{u}} {P : Augmentation f}
    [HasDerivedCategory.{u + 1} (ModuleCat.{u} f.right)] (D : DifferentialModel P) :=
  DerivedCategory.Q.obj (differentialComplex D)

/-- The full coherence assertion. All standard terms and ring-square maps have
prescribed polynomial formulas; all differential maps have prescribed tensor
formulas. Comparisons are simultaneously natural, including across base rings.
Source: Stacks, Tags 08PM, 08PN, 08QI and 08QL
(blueprint: lem-trf-cotangent-resolution-coherence). -/
structure Coherence
    [∀ B : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} B)] where
  standard : ∀ f : Arrow CommRingCat.{u}, Augmentation f
  standard_spec : ∀ f : Arrow CommRingCat.{u}, IsStandard (standard f)
  standard_resolution : ∀ f : Arrow CommRingCat.{u},
    IsPolynomialResolution (standard f)
  standardMap : ∀ {f g : Arrow CommRingCat.{u}} (q : f ⟶ g),
    AugmentedMap q (standard f) (standard g)
  standardMap_formula : ∀ {f g : Arrow CommRingCat.{u}} (q : f ⟶ g) (n : ℕ),
    HEq ((standardMap q).map.app (op ⦋n⦌)) (standardSquareMap q n)
  standardMap_id : ∀ f : Arrow CommRingCat.{u}, (standardMap (𝟙 f)).map = 𝟙 _
  standardMap_comp : ∀ {f g j : Arrow CommRingCat.{u}} (q : f ⟶ g) (r : g ⟶ j),
    (standardMap (q ≫ r)).map = (standardMap q).map ≫ (standardMap r).map
  differentials : ∀ {f : Arrow CommRingCat.{u}} (P : Augmentation f), DifferentialModel P
  differentialMap : ∀ {f g : Arrow CommRingCat.{u}} {q : f ⟶ g}
    {P : Augmentation f} {Q : Augmentation g} (h : AugmentedMap q P Q),
    DifferentialMap h (differentials P) (differentials Q)
  standardDifferentialMap_id : ∀ (f : Arrow CommRingCat.{u}) (i : ℤ)
    (x : (differentialComplex (differentials (standard f))).X i),
    (differentialMap (standardMap (𝟙 f))).map.f i x = x
  standardDifferentialMap_comp : ∀ {f g j : Arrow CommRingCat.{u}}
    (q : f ⟶ g) (r : g ⟶ j) (i : ℤ)
    (x : (differentialComplex (differentials (standard f))).X i),
    (differentialMap (standardMap (q ≫ r))).map.f i x =
      (differentialMap (standardMap r)).map.f i
        ((differentialMap (standardMap q)).map.f i x)
  comparison : ∀ {f : Arrow CommRingCat.{u}} (P : Augmentation f)
    (_hP : IsPolynomialResolution P),
    derivedDifferentials (differentials P) ≅
      derivedDifferentials (differentials (standard f))
  comparison_standard : ∀ f : Arrow CommRingCat.{u},
    comparison (standard f) (standard_resolution f) = Iso.refl _
  compatibility : ∀ {f g : Arrow CommRingCat.{u}} {q : f ⟶ g}
    {P : Augmentation f} {Q : Augmentation g}
    (hP : IsPolynomialResolution P) (hQ : IsPolynomialResolution Q)
    (h : AugmentedMap q P Q),
    DerivedCategory.Q.map (differentialMap h).map ≫
        (ModuleCat.restrictScalars q.right.hom).mapDerivedCategoryFactors.inv.app
          (differentialComplex (differentials Q)) ≫
        (ModuleCat.restrictScalars q.right.hom).mapDerivedCategory.map
          (comparison Q hQ).hom =
      (comparison P hP).hom ≫
        DerivedCategory.Q.map (differentialMap (standardMap q)).map ≫
        (ModuleCat.restrictScalars q.right.hom).mapDerivedCategoryFactors.inv.app
          (differentialComplex (differentials (standard g)))

/-- The cotangent complex `L_{B/A}`, represented by the explicitly specified standard
resolution. Source: Stacks, Tag 08PN
(blueprint: lem-trf-cotangent-resolution-coherence). -/
def cotangentComplex
    [∀ B : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} B)]
    (C : Coherence.{u}) (f : Arrow CommRingCat.{u}) :=
  derivedDifferentials (C.differentials (C.standard f))

/-- The canonical derived map of a ring square, with its target restricted along
`B → B'`. Source: Stacks, Tag 08QL
(blueprint: lem-trf-cotangent-resolution-coherence). -/
def cotangentMap
    [∀ B : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} B)]
    (C : Coherence.{u}) {f g : Arrow CommRingCat.{u}} (q : f ⟶ g) :
    cotangentComplex C f ⟶
      (ModuleCat.restrictScalars q.right.hom).mapDerivedCategory.obj (cotangentComplex C g) :=
  DerivedCategory.Q.map (C.differentialMap (C.standardMap q)).map ≫
    (ModuleCat.restrictScalars q.right.hom).mapDerivedCategoryFactors.inv.app
      (differentialComplex (C.differentials (C.standard g)))

/-- The map between arbitrary chosen polynomial resolutions, transported through
their canonical comparisons. It agrees with every supplied augmented resolution
map by `Coherence.compatibility`. Source: Stacks, Tags 08QI and 08QL
(blueprint: lem-trf-cotangent-resolution-coherence). -/
def transportedMap
    [∀ B : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} B)]
    (C : Coherence.{u}) {f g : Arrow CommRingCat.{u}} (q : f ⟶ g)
    (P : Augmentation f) (Q : Augmentation g)
    (hP : IsPolynomialResolution P) (hQ : IsPolynomialResolution Q) :
    derivedDifferentials (C.differentials P) ⟶
      (ModuleCat.restrictScalars q.right.hom).mapDerivedCategory.obj
        (derivedDifferentials (C.differentials Q)) :=
  (C.comparison P hP).hom ≫ cotangentMap C q ≫
    (ModuleCat.restrictScalars q.right.hom).mapDerivedCategory.map (C.comparison Q hQ).inv

/-- Standard polynomial resolutions, cotangent complexes, their canonical
comparison isomorphisms, and strict standard functoriality exist with all the
specified formulas. Source: Stacks, Tags 08PM, 08PN, 08QI and 08QL
(blueprint: lem-trf-cotangent-resolution-coherence).

Proof: (1) Apply lem-trf-adjunction-standard-simplicial-homotopy to the free
polynomial algebra/underlying set adjunction. Evaluation is surjective since
`[b]` evaluates to `b`, and the unit gives the underlying set contraction.
(2) Apply lem-trf-simplicial-abelian-set-homotopy-quasi-iso to the standard
augmentation. The alternating complex of the constant simplicial group has
identity differentials in even negative degrees and zero differentials in odd
negative degrees, so its augmentation to `B[0]` is a quasi-isomorphism.
(3) For any polynomial resolution, apply
lem-trf-simplicial-abelian-surjective-quasi-iso-boundary-lifting to obtain every
boundary lift, including in degree zero.
(4) In a containing universe form the small category of polynomial A-algebras
over B, without a surjectivity condition on its objects. Maps from A[E] into
a resolution are choices of lifts of the images of all generators.
(5) Boundary fillers exist generator by generator by (3), including for empty
or infinite E. Apply lem-weil-pbc-trivial-kan-homotopy-equivalence to conclude
that each such representable simplicial set is contractible.
(6) The functor T ↦ Ω¹[T/A] ⊗_T B has maps determined by the universal derivation
of def-weil-pbc-kahler-differentials. Apply
lem-trf-simplicial-derived-colimit-computation to obtain a_Q: K(Q) ≅ H.
Set c_Q = a_Q followed by the inverse of a_standard. Naturality gives
K(h) followed by c_R = c_Q, and c_standard is the identity.
(7) Define standard ring-square maps recursively by coefficients and variable
labels as displayed in standardSquareMap. Evaluation and insertion of the unit
commute with them on coefficients and generators; uniqueness of polynomial
maps proves strict identity and composition. The universal derivation induces
the displayed maps on differential generators, also strictly functorial.
(8) Base change T ↦ T ⊗_A A' preserves polynomial presentations and gives the
natural transformation on differential modules. A supplied map of resolutions
extends to this base change by q ⊗ a' ↦ h(q)a'. No assertion that this base
change is a resolution is used.
(9) Reindexing naturality of lem-trf-simplicial-derived-colimit-computation gives
a_Q' K(h) = H(α,β) a_Q, and the same equality for the standard resolutions.
Cancel the two standard comparisons to obtain compatibility. For arbitrary
choices of resolutions the transported map is c_Q followed by the standard
map and the inverse of c_Q'; cancellation proves identity, composition and
agreement with every supplied resolution map. All target objects and maps in
these equations are restricted along β, with the canonical localization
comparison mapDerivedCategoryFactors making this explicit. -/
theorem exists_coherence
    [∀ B : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} B)] :
    Nonempty (Coherence.{u}) := by
  sorry

end Algebra.CotangentResolution
