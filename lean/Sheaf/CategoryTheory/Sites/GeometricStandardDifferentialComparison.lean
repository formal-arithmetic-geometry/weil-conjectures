module

public import Sheaf.CategoryTheory.Sites.InverseImageDifferentials
public import Sheaf.CategoryTheory.ComonadStandardResolution
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Monad.Adjunction
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Sheaf.CategoryTheory.AdjunctionStandardSimplicialHomotopy
import Sheaf.CategoryTheory.SimplicialOperatorsReconstruction
import Sheaf.CategoryTheory.Sites.GeometricInverseImageExact
import Sheaf.CategoryTheory.Sites.SheafifiedDifferentialsCokernel
import Sheaf.SecSmoothPurity.CochainInverseComparison
import Sheaf.CategoryTheory.Adjunction.LiftsGroupRingObjects
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal

/-!
# Geometric comparison of standard polynomial differential complexes

Source: Stacks Project, Cotangent, Tags 08SR, 08SS and 08SV, and Modules on Sites,
Tags 08TP, 08TQ and 03EL
(blueprint: lem-trf-geometric-standard-differential-comparison).

Presentations below retain the free/forgetful adjunction, the actual comonad
operators, universal differential tensors and actual complex isomorphisms.
They specify canonical constructions up to their normalized isomorphisms;
no object is selected from a mere existence assertion.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option backward.isDefEq.respectTransparency false

universe uC vC uD vD uE vE w

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open scoped ChangeOfRings

namespace CategoryTheory.GeometricStandardDifferentials

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C}

/-- The existing underlying-set functor, with the lift required by the algebraic
inverse-image interface. Source: Stacks 08SV
(blueprint: lem-trf-geometric-standard-differential-comparison). -/
abbrev setsFunctor (J : GrothendieckTopology C) :
    Sheaf J CommRingCat.{w} ⥤ Sheaf J (Type w) :=
  sheafCompose J (forget CommRingCat.{w} ⋙ uliftFunctor.{w, w})

/-- Forget an algebra sheaf to its underlying sheaf of sets. Source: Stacks 08SR
(blueprint: lem-trf-geometric-standard-differential-comparison). -/
abbrev algebraSets (A : Sheaf J CommRingCat.{w}) : Under A ⥤ Sheaf J (Type w) :=
  Under.forget A ⋙ setsFunctor J

/-- A presentation of the free sheaf-algebra adjunction and its standard comonad
resolution. An adjunction to the specified forgetful functor determines the free
object uniquely; sectionwise polynomial evaluation followed by sheafification
is its construction. The standard predicate fixes every face and degeneracy,
not only the terms. Source: Stacks 08SR and Simplicial 08NC
(blueprint: lem-trf-geometric-standard-differential-comparison). -/
structure AlgebraConstruction (J : GrothendieckTopology C) where
  free : ∀ A : Sheaf J CommRingCat.{w}, Sheaf J (Type w) ⥤ Under A
  adjunction : ∀ A : Sheaf J CommRingCat.{w}, free A ⊣ algebraSets A
  standard : ∀ A : Sheaf J CommRingCat.{w}, SimplicialObject (Under A ⥤ Under A)
  augmentation : ∀ A : Sheaf J CommRingCat.{w},
    standard A ⟶ (SimplicialObject.const _).obj (𝟭 (Under A))
  standard_spec : ∀ A : Sheaf J CommRingCat.{w},
    Comonad.IsStandardSimplicialResolution (adjunction A).toComonad
      (standard A) (augmentation A)

namespace AlgebraConstruction

/-- The free algebra `A[E]`, characterized by the recorded adjunction.
Source: Stacks 08SR (blueprint: lem-trf-geometric-standard-differential-comparison). -/
abbrev polynomial (M : AlgebraConstruction J) (A : Sheaf J CommRingCat.{w})
    (E : Sheaf J (Type w)) : Sheaf J CommRingCat.{w} :=
  ((M.free A).obj E).right

/-- Coefficients in the free algebra. Source: Stacks 08SR
(blueprint: lem-trf-geometric-standard-differential-comparison). -/
abbrev coefficient (M : AlgebraConstruction J) (A : Sheaf J CommRingCat.{w})
    (E : Sheaf J (Type w)) : A ⟶ M.polynomial A E :=
  ((M.free A).obj E).hom

/-- The free-algebra unit (variable map). Source: Stacks 08SR
(blueprint: lem-trf-geometric-standard-differential-comparison). -/
abbrev variableMap (M : AlgebraConstruction J) (A : Sheaf J CommRingCat.{w})
    (E : Sheaf J (Type w)) : E ⟶ SheafDifferentials.sets (M.polynomial A E) :=
  (M.adjunction A).unit.app E

/-- Polynomial evaluation in an algebra sheaf, using the free/forgetful adjunction.
Source: Stacks 08SR (blueprint: lem-trf-geometric-standard-differential-comparison). -/
def evaluate (M : AlgebraConstruction J) {A B : Sheaf J CommRingCat.{w}}
    (a : A ⟶ B) {E : Sheaf J (Type w)} (v : E ⟶ SheafDifferentials.sets B) :
    M.polynomial A E ⟶ B :=
  (((M.adjunction A).homEquiv E (Under.mk a)).symm v).right

/-- Polynomial functoriality with both coefficients and variables changing.
Source: Stacks 08SV (blueprint: lem-trf-geometric-standard-differential-comparison). -/
def polynomialMap (M : AlgebraConstruction J) {A B : Sheaf J CommRingCat.{w}}
    (a : A ⟶ B) {E E' : Sheaf J (Type w)} (v : E ⟶ E') :
    M.polynomial A E ⟶ M.polynomial B E' :=
  M.evaluate (a ≫ M.coefficient B E') (v ≫ M.variableMap B E')

/-- Evaluation of the standard simplicial endofunctor at the given algebra.
Source: Stacks 08SR (blueprint: lem-trf-geometric-standard-differential-comparison). -/
def resolution (M : AlgebraConstruction J) {A B : Sheaf J CommRingCat.{w}}
    (φ : A ⟶ B) : SimplicialObject (Sheaf J CommRingCat.{w}) :=
  M.standard A ⋙ (evaluation (Under A) (Under A)).obj (Under.mk φ) ⋙ Under.forget A

/-- The algebra structure of a standard term. Source: Stacks 08SR
(blueprint: lem-trf-geometric-standard-differential-comparison). -/
abbrev base (M : AlgebraConstruction J) {A B : Sheaf J CommRingCat.{w}}
    (φ : A ⟶ B) (n : ℕ) : A ⟶ (M.resolution φ).obj (op ⦋n⦌) :=
  (((M.standard A).obj (op ⦋n⦌)).obj (Under.mk φ)).hom

/-- The iterated evaluation augmentation. Source: Stacks 08SR
(blueprint: lem-trf-geometric-standard-differential-comparison). -/
abbrev augment (M : AlgebraConstruction J) {A B : Sheaf J CommRingCat.{w}}
    (φ : A ⟶ B) (n : ℕ) : (M.resolution φ).obj (op ⦋n⦌) ⟶ B :=
  (((M.augmentation A).app (op ⦋n⦌)).app (Under.mk φ)).right

/-- The prior comonad iterate, with the target algebra as zeroth iterate.
Source: Stacks 08SR (blueprint: lem-trf-geometric-standard-differential-comparison). -/
abbrev prior (M : AlgebraConstruction J) {A B : Sheaf J CommRingCat.{w}}
    (φ : A ⟶ B) (n : ℕ) : Under A :=
  (Comonad.resolutionPower (M.adjunction A).toComonad.toFunctor n).obj (Under.mk φ)

/-- The prescribed variables in degree n are the underlying previous iterate.
Source: Stacks 08SR (blueprint: lem-trf-geometric-standard-differential-comparison). -/
abbrev labels (M : AlgebraConstruction J) {A B : Sheaf J CommRingCat.{w}}
    (φ : A ⟶ B) (n : ℕ) : Sheaf J (Type w) :=
  (algebraSets A).obj (M.prior φ n)

/-- The standard-term identification supplied by the comonad specification.
Source: Stacks 08SR (blueprint: lem-trf-geometric-standard-differential-comparison). -/
def coordinates (M : AlgebraConstruction J) {A B : Sheaf J CommRingCat.{w}}
    (φ : A ⟶ B) (n : ℕ) :
    (M.resolution φ).obj (op ⦋n⦌) ≅ M.polynomial A (M.labels φ n) :=
  (Under.forget A).mapIso (eqToIso
    (congrArg (fun H : Under A ⥤ Under A ↦ H.obj (Under.mk φ))
      ((M.standard_spec A).1 n)))

/-- The universal variable map into the actual standard term.
Source: Stacks 08SR (blueprint: lem-trf-geometric-standard-differential-comparison). -/
def generator (M : AlgebraConstruction J) {A B : Sheaf J CommRingCat.{w}}
    (φ : A ⟶ B) (n : ℕ) :
    M.labels φ n ⟶ SheafDifferentials.sets ((M.resolution φ).obj (op ⦋n⦌)) :=
  M.variableMap A (M.labels φ n) ≫ (setsFunctor J).map (M.coordinates φ n).inv

/-- The exact degreewise differential tensor, using the existing sheafification
of differentials and existing change of rings. Coefficients are written first.
Source: Stacks 08SS (blueprint: lem-trf-geometric-standard-differential-comparison). -/
def differentialTerm (M : AlgebraConstruction J) {A B : Sheaf J CommRingCat.{w}}
    (φ : A ⟶ B) (n : ℕ) : ringedSiteModules.{w} (SheafDifferentials.ring B) :=
  SheafOfModules.changeOfRingsOfUniverses.{vC, uC, w, w} (M.augment φ n)
    (SheafDifferentials.omega (M.base φ n))

/-- The canonical scalar-extension pairing on sections of the differential module.
Source: Stacks 08SS and 03EL
(blueprint: lem-trf-geometric-standard-differential-comparison). -/
def tensorSection (M : AlgebraConstruction J) {A B : Sheaf J CommRingCat.{w}}
    (φ : A ⟶ B) (n : ℕ) (U : Cᵒᵖ) (b : B.obj.obj U)
    (x : (SheafDifferentials.omega (M.base φ n)).val.obj U) :
    (M.differentialTerm φ n).val.obj U :=
  (((PresheafOfModules.sheafificationAdjunction
    (𝟙 (SheafDifferentials.ring B).obj)).unit.app
      (SheafOfModules.changeOfRingsPresheafOfUniverses.{vC, uC, w, w} (M.augment φ n)
        (SheafDifferentials.omega (M.base φ n)))).app U)
    (b ⊗ₜ[_, ((M.augment φ n).hom.app U).hom] x)

/-- The standard differential-tensor generator. Source: Stacks 08SS
(blueprint: lem-trf-geometric-standard-differential-comparison). -/
abbrev tensorD (M : AlgebraConstruction J) {A B : Sheaf J CommRingCat.{w}}
    (φ : A ⟶ B) (n : ℕ) (U : Cᵒᵖ) (b : B.obj.obj U)
    (p : ((M.resolution φ).obj (op ⦋n⦌)).obj.obj U) :=
  M.tensorSection φ n U b (SheafDifferentials.derivation (M.base φ n) |>.d p)

end AlgebraConstruction

/-- The simplicial differential tensor, with every operator normalized on `b ⊗ dp`.
Source: Stacks 08SS (blueprint: lem-trf-geometric-standard-differential-comparison). -/
structure DifferentialConstruction (M : AlgebraConstruction J)
    {A B : Sheaf J CommRingCat.{w}} (φ : A ⟶ B) where
  simplicial : SimplicialObject (ringedSiteModules.{w} (SheafDifferentials.ring B))
  term : ∀ n : ℕ, simplicial.obj (op ⦋n⦌) ≅ M.differentialTerm φ n
  operator : ∀ {n m : ℕ} (α : (op ⦋n⦌) ⟶ (op ⦋m⦌))
    (U : Cᵒᵖ) (b : B.obj.obj U)
    (p : ((M.resolution φ).obj (op ⦋n⦌)).obj.obj U),
    (term m).hom.val.app U ((simplicial.map α).val.app U
      ((term n).inv.val.app U (M.tensorD φ n U b p))) =
        M.tensorD φ m U b (((M.resolution φ).map α).hom.app U p)

/-- An alternating complex, with zero positive terms, presented by its term
identifications and alternating-face differential. Source: Stacks 08SS
(blueprint: lem-trf-geometric-standard-differential-comparison). -/
structure AlternatingConstruction {A B : Sheaf J CommRingCat.{w}}
    {M : AlgebraConstruction J} {φ : A ⟶ B} (D : DifferentialConstruction M φ) where
  complex : CochainComplex (ringedSiteModules.{w} (SheafDifferentials.ring B)) ℤ
  term : ∀ n : ℕ, complex.X (-(n : ℤ)) ≅ D.simplicial.obj (op ⦋n⦌)
  positive_zero : ∀ i : ℤ, 0 < i → IsZero (complex.X i)
  differential : ∀ n : ℕ,
    (term (n + 1)).inv ≫ complex.d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) ≫
      (term n).hom = ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • D.simplicial.δ i

variable {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D]
  {K : GrothendieckTopology D}

/-- A simultaneous finite-product lift on rings and their modules. The ring
underlying isomorphisms are precisely those of the existing algebraic transport.
Source: Stacks 08SV and Sites 00YV
(blueprint: lem-trf-geometric-standard-differential-comparison). -/
structure InverseLift (F : Sheaf J (Type w) ⥤ Sheaf K (Type w)) where
  rings : Sheaf J CommRingCat.{w} ⥤ Sheaf K CommRingCat.{w}
  underlying : rings ⋙ setsFunctor K ≅ setsFunctor J ⋙ F
  modules : ∀ R : Sheaf J CommRingCat.{w},
    SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w}
      F R (rings.obj R)
  additive : ∀ R : Sheaf J CommRingCat.{w}, (modules R).modules.Additive
  ring_underlying : ∀ R : Sheaf J CommRingCat.{w},
    (modules R).ringUnderlying = (underlying.app R).symm

attribute [instance] InverseLift.additive

/-- The free-algebra comparison, including coefficients, variables, evaluation,
and naturality with changing coefficient rings. Source: Stacks 08SV
(blueprint: lem-trf-geometric-standard-differential-comparison). -/
structure FreeComparison (M : AlgebraConstruction J) (N : AlgebraConstruction K)
    {F : Sheaf J (Type w) ⥤ Sheaf K (Type w)} (I : InverseLift F) where
  iso : ∀ (R : Sheaf J CommRingCat.{w}) (E : Sheaf J (Type w)),
    I.rings.obj (M.polynomial R E) ≅ N.polynomial (I.rings.obj R) (F.obj E)
  coefficient : ∀ (R : Sheaf J CommRingCat.{w}) (E : Sheaf J (Type w)),
    I.rings.map (M.coefficient R E) ≫ (iso R E).hom =
      N.coefficient (I.rings.obj R) (F.obj E)
  variable_map : ∀ (R : Sheaf J CommRingCat.{w}) (E : Sheaf J (Type w)),
    F.map (M.variableMap R E) ≫ (I.underlying.inv.app (M.polynomial R E)) ≫
      (setsFunctor K).map (iso R E).hom = N.variableMap (I.rings.obj R) (F.obj E)
  evaluation : ∀ {R S : Sheaf J CommRingCat.{w}} (a : R ⟶ S)
    {E : Sheaf J (Type w)} (v : E ⟶ SheafDifferentials.sets S),
    I.rings.map (M.evaluate a v) = (iso R E).hom ≫
      N.evaluate (I.rings.map a) (F.map v ≫ I.underlying.inv.app S)
  naturality : ∀ {R S : Sheaf J CommRingCat.{w}} (a : R ⟶ S)
    {E E' : Sheaf J (Type w)} (v : E ⟶ E'),
    I.rings.map (M.polynomialMap a v) ≫ (iso S E').hom =
      (iso R E).hom ≫ N.polynomialMap (I.rings.map a) (F.map v)

namespace FreeComparison

/-- The comparison viewed on underlying sheaves. Source: Stacks 08SV
(blueprint: lem-trf-geometric-standard-differential-comparison). -/
def arrow {M : AlgebraConstruction J} {N : AlgebraConstruction K}
    {F : Sheaf J (Type w) ⥤ Sheaf K (Type w)} {I : InverseLift F}
    (e : FreeComparison M N I) (R : Sheaf J CommRingCat.{w}) (E : Sheaf J (Type w)) :=
  I.underlying.inv.app (M.polynomial R E) ≫ (setsFunctor K).map (e.iso R E).hom

end FreeComparison

/-- The label map induced by a candidate standard-resolution square. In degree zero
it is the given map of target rings; subsequently it is the preceding degree map.
Source: Stacks 08SS (blueprint: lem-trf-geometric-standard-differential-comparison). -/
def squareLabels (M : AlgebraConstruction J) {A B A' B' : Sheaf J CommRingCat.{w}}
    (φ : A ⟶ B) (φ' : A' ⟶ B') (b : B ⟶ B')
    (p : M.resolution φ ⟶ M.resolution φ') :
    (n : ℕ) → M.labels φ n ⟶ M.labels φ' n
  | 0 => (setsFunctor J).map b
  | n + 1 => (setsFunctor J).map (M.coordinates φ n).inv ≫
      (setsFunctor J).map (p.app (op ⦋n⦌)) ≫
        (setsFunctor J).map (M.coordinates φ' n).hom

/-- A ring-square map of standard resolutions, fixed on coefficients and all
recursive generators. Source: Stacks 08SS, paragraph after the definition
(blueprint: lem-trf-geometric-standard-differential-comparison). -/
structure ResolutionSquare (M : AlgebraConstruction J)
    {A B A' B' : Sheaf J CommRingCat.{w}} (φ : A ⟶ B) (φ' : A' ⟶ B')
    (a : A ⟶ A') (b : B ⟶ B') where
  map : M.resolution φ ⟶ M.resolution φ'
  base : ∀ n : ℕ, M.base φ n ≫ map.app (op ⦋n⦌) = a ≫ M.base φ' n
  augmentation : ∀ n : ℕ,
    map.app (op ⦋n⦌) ≫ M.augment φ' n = M.augment φ n ≫ b
  generator : ∀ n : ℕ,
    M.generator φ n ≫ (setsFunctor J).map (map.app (op ⦋n⦌)) =
      squareLabels M φ φ' b map n ≫ M.generator φ' n

/-- A complete presentation of the source construction. All module terms and
operators are the specified sheafified differential tensors. Source: Stacks 08SS
(blueprint: lem-trf-geometric-standard-differential-comparison). -/
structure Construction (J : GrothendieckTopology C) where
  algebra : AlgebraConstruction J
  differential : ∀ {A B : Sheaf J CommRingCat.{w}} (φ : A ⟶ B),
    DifferentialConstruction algebra φ
  alternating : ∀ {A B : Sheaf J CommRingCat.{w}} (φ : A ⟶ B),
    AlternatingConstruction (differential φ)

/-- The recursively transported labels of a standard-resolution comparison.
Source: Stacks 08SV (blueprint: lem-trf-geometric-standard-differential-comparison). -/
def inverseLabels (M : AlgebraConstruction J) (N : AlgebraConstruction K)
    {F : Sheaf J (Type w) ⥤ Sheaf K (Type w)} (I : InverseLift F)
    {A B : Sheaf J CommRingCat.{w}} (φ : A ⟶ B)
    (p : M.resolution φ ⋙ I.rings ≅ N.resolution (I.rings.map φ)) :
    (n : ℕ) → F.obj (M.labels φ n) ⟶ N.labels (I.rings.map φ) n
  | 0 => I.underlying.inv.app B
  | n + 1 => F.map ((setsFunctor J).map (M.coordinates φ n).inv) ≫
      I.underlying.inv.app ((M.resolution φ).obj (op ⦋n⦌)) ≫
        (setsFunctor K).map (p.hom.app (op ⦋n⦌)) ≫
          (setsFunctor K).map (N.coordinates (I.rings.map φ) n).hom

/-- A module comparison on differentials of a term, with the scalar ring
transported by the standard algebra comparison. Source: Stacks 08TQ and 08SV
(blueprint: lem-trf-geometric-standard-differential-comparison). -/
abbrev TermDifferentialIso (M : AlgebraConstruction J) (N : AlgebraConstruction K)
    {F : Sheaf J (Type w) ⥤ Sheaf K (Type w)} (I : InverseLift F)
    {A B : Sheaf J CommRingCat.{w}} (φ : A ⟶ B)
    (p : M.resolution φ ⋙ I.rings ≅ N.resolution (I.rings.map φ)) (n : ℕ) :=
  (I.modules ((M.resolution φ).obj (op ⦋n⦌))).modules.obj
      (SheafDifferentials.omega (M.base φ n)) ≅
    (SheafOfModules.restrictScalars
      ((sheafCompose K (forget₂ CommRingCat.{w} RingCat.{w})).map (p.hom.app (op ⦋n⦌)))).obj
        (SheafDifferentials.omega (N.base (I.rings.map φ) n))

/-- The underlying differential comparison. Source: Stacks 08TQ
(blueprint: lem-trf-geometric-standard-differential-comparison). -/
def termDifferentialArrow {M : AlgebraConstruction J} {N : AlgebraConstruction K}
    {F : Sheaf J (Type w) ⥤ Sheaf K (Type w)} {I : InverseLift F}
    {A B : Sheaf J CommRingCat.{w}} {φ : A ⟶ B}
    {p : M.resolution φ ⋙ I.rings ≅ N.resolution (I.rings.map φ)}
    {n : ℕ} (e : TermDifferentialIso M N I φ p n) :=
  (I.modules ((M.resolution φ).obj (op ⦋n⦌))).moduleUnderlying.inv.app
      (SheafDifferentials.omega (M.base φ n)) ≫
    (SheafDifferentials.moduleSets (I.rings.obj ((M.resolution φ).obj (op ⦋n⦌)))).map e.hom

/-- The normalized comparison of the augmented algebra resolution, differential
tensors and actual alternating complex. The pairing condition quantifies over
test sheaves, and therefore includes the universal derivation and the map
`ω ↦ 1 ⊗ ω`, not just pointwise transported sections. Source: Stacks 08SV
(blueprint: lem-trf-geometric-standard-differential-comparison). -/
structure StandardComparison (M : Construction J) (N : Construction K)
    {F : Sheaf J (Type w) ⥤ Sheaf K (Type w)} (I : InverseLift F)
    {A B : Sheaf J CommRingCat.{w}} (φ : A ⟶ B) where
  algebra : M.algebra.resolution φ ⋙ I.rings ≅ N.algebra.resolution (I.rings.map φ)
  base : ∀ n : ℕ,
    I.rings.map (M.algebra.base φ n) ≫ algebra.hom.app (op ⦋n⦌) =
      N.algebra.base (I.rings.map φ) n
  augmentation : ∀ n : ℕ,
    algebra.hom.app (op ⦋n⦌) ≫ N.algebra.augment (I.rings.map φ) n =
      I.rings.map (M.algebra.augment φ n)
  generator : ∀ n : ℕ,
    F.map (M.algebra.generator φ n) ≫
      I.underlying.inv.app ((M.algebra.resolution φ).obj (op ⦋n⦌)) ≫
        (setsFunctor K).map (algebra.hom.app (op ⦋n⦌)) =
      inverseLabels M.algebra N.algebra I φ algebra n ≫
        N.algebra.generator (I.rings.map φ) n
  omega : ∀ n : ℕ, TermDifferentialIso M.algebra N.algebra I φ algebra n
  omega_derivation : ∀ n : ℕ,
    F.map (SheafDifferentials.d (M.algebra.base φ n)) ≫ termDifferentialArrow (omega n) =
      I.underlying.inv.app ((M.algebra.resolution φ).obj (op ⦋n⦌)) ≫
        (setsFunctor K).map (algebra.hom.app (op ⦋n⦌)) ≫
          SheafDifferentials.d (N.algebra.base (I.rings.map φ) n)
  simplicial : (M.differential φ).simplicial ⋙ (I.modules B).modules ≅
    (N.differential (I.rings.map φ)).simplicial
  pairing : ∀ (n : ℕ) (T : Sheaf J (Type w))
    (b : T ⟶ SheafDifferentials.sets B)
    (x : T ⟶ (SheafDifferentials.moduleSets
      ((M.algebra.resolution φ).obj (op ⦋n⦌))).obj
        (SheafDifferentials.omega (M.algebra.base φ n)))
    (z : T ⟶ (SheafDifferentials.moduleSets B).obj
      ((M.differential φ).simplicial.obj (op ⦋n⦌))),
    (∀ (U : Cᵒᵖ) (t : T.obj.obj U),
      ((M.differential φ).term n).hom.val.app U (z.hom.app U t).down =
        M.algebra.tensorSection φ n U (b.hom.app U t).down (x.hom.app U t).down) →
    ∀ (V : Dᵒᵖ) (t : (F.obj T).obj.obj V),
      ((N.differential (I.rings.map φ)).term n).hom.val.app V
        ((simplicial.hom.app (op ⦋n⦌)).val.app V
          (((F.map z ≫ (I.modules B).moduleUnderlying.inv.app
            ((M.differential φ).simplicial.obj (op ⦋n⦌))).hom.app V t).down)) =
        N.algebra.tensorSection (I.rings.map φ) n V
          ((F.map b ≫ I.underlying.inv.app B).hom.app V t).down
          ((F.map x ≫ termDifferentialArrow (omega n)).hom.app V t).down
  complex : ((I.modules B).modules.mapHomologicalComplex (.up ℤ)).obj
      (M.alternating φ).complex ≅ (N.alternating (I.rings.map φ)).complex
  complex_degree : ∀ n : ℕ,
    (complex.hom.f (-(n : ℤ))) ≫ ((N.alternating (I.rings.map φ)).term n).hom =
      (I.modules B).modules.map ((M.alternating φ).term n).hom ≫
        simplicial.hom.app (op ⦋n⦌)

/-- The existing sheafification construction transported to the small model of
an essentially small site, at the ring coefficient universe. Source: Stacks 00W1
(blueprint: lem-trf-geometric-standard-differential-comparison). -/
instance ringSheafification (J : GrothendieckTopology C) : HasSheafify J CommRingCat.{w} :=
  hasSheafifyEssentiallySmallSite.{vC, w, uC, w + 1, w} J CommRingCat.{w}

/-- The polynomial sheaf really is the sheafification of the sectionwise
multivariate polynomial ring. Section isomorphisms fix the restrictions, and
coefficient and variable equations fix its identification with the free object.
Source: Stacks 08SR and its preceding free/forgetful adjunction
(blueprint: lem-trf-geometric-standard-differential-comparison). -/
structure PolynomialPresentation (M : AlgebraConstruction J)
    (R : Sheaf J CommRingCat.{w}) (E : Sheaf J (Type w)) where
  presheaf : Cᵒᵖ ⥤ CommRingCat.{w}
  sectionIso : ∀ U : Cᵒᵖ,
    presheaf.obj U ≅ CommRingCat.of (MvPolynomial (E.obj.obj U) (R.obj.obj U))
  restriction : ∀ {U V : Cᵒᵖ} (r : U ⟶ V)
    (p : MvPolynomial (E.obj.obj U) (R.obj.obj U)),
    (sectionIso V).hom (presheaf.map r ((sectionIso U).inv p)) =
      MvPolynomial.eval₂Hom (MvPolynomial.C.comp (R.obj.map r).hom)
        (fun e ↦ MvPolynomial.X (E.obj.map r e)) p
  sheafification : (presheafToSheaf J CommRingCat.{w}).obj presheaf ≅ M.polynomial R E
  coefficient : ∀ (U : Cᵒᵖ) (r : R.obj.obj U),
    sheafification.hom.hom.app U
      ((toSheafify J presheaf).app U ((sectionIso U).inv (MvPolynomial.C r))) =
        (M.coefficient R E).hom.app U r
  generator : ∀ (U : Cᵒᵖ) (e : E.obj.obj U),
    ULift.up (sheafification.hom.hom.app U
      ((toSheafify J presheaf).app U ((sectionIso U).inv (MvPolynomial.X e)))) =
        (M.variableMap R E).hom.app U e

/-- The full canonical map for a commutative square of ring sheaves, including
its simplicial differential-tensor map and alternating-complex map.
Source: Stacks 08SS, paragraph on commutative squares
(blueprint: lem-trf-geometric-standard-differential-comparison). -/
structure ConstructionSquare (M : Construction J)
    {A B A' B' : Sheaf J CommRingCat.{w}} (φ : A ⟶ B) (φ' : A' ⟶ B')
    (a : A ⟶ A') (b : B ⟶ B') where
  algebra : ResolutionSquare M.algebra φ φ' a b
  simplicial : (M.differential φ).simplicial ⟶
    (M.differential φ').simplicial ⋙ SheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map b)
  tensor_generator : ∀ (n : ℕ) (U : Cᵒᵖ) (c : B.obj.obj U)
    (p : ((M.algebra.resolution φ).obj (op ⦋n⦌)).obj.obj U),
    ((M.differential φ').term n).hom.val.app U
      ((simplicial.app (op ⦋n⦌)).val.app U
        (((M.differential φ).term n).inv.val.app U
          (M.algebra.tensorD φ n U c p))) =
      M.algebra.tensorD φ' n U (b.hom.app U c) ((algebra.map.app (op ⦋n⦌)).hom.app U p)
  complex : (M.alternating φ).complex ⟶
    ((SheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map b)).mapHomologicalComplex
        (.up ℤ)).obj (M.alternating φ').complex
  complex_degree : ∀ n : ℕ,
    complex.f (-(n : ℤ)) ≫
      (SheafOfModules.restrictScalars
        ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map b)).map
          ((M.alternating φ').term n).hom =
      ((M.alternating φ).term n).hom ≫ simplicial.app (op ⦋n⦌)

namespace StandardComparison

/-- Underlying algebra comparison. Source: Stacks 08SV
(blueprint: lem-trf-geometric-standard-differential-comparison). -/
def algebraArrow {M : Construction J} {N : Construction K}
    {F : Sheaf J (Type w) ⥤ Sheaf K (Type w)} {I : InverseLift F}
    {A B : Sheaf J CommRingCat.{w}} {φ : A ⟶ B}
    (e : StandardComparison M N I φ) (n : ℕ) :=
  I.underlying.inv.app ((M.algebra.resolution φ).obj (op ⦋n⦌)) ≫
    (setsFunctor K).map (e.algebra.hom.app (op ⦋n⦌))

/-- Underlying simplicial-module comparison. Source: Stacks 08SV
(blueprint: lem-trf-geometric-standard-differential-comparison). -/
def moduleArrow {M : Construction J} {N : Construction K}
    {F : Sheaf J (Type w) ⥤ Sheaf K (Type w)} {I : InverseLift F}
    {A B : Sheaf J CommRingCat.{w}} {φ : A ⟶ B}
    (e : StandardComparison M N I φ) (n : ℕ) :=
  (I.modules B).moduleUnderlying.inv.app ((M.differential φ).simplicial.obj (op ⦋n⦌)) ≫
    (SheafDifferentials.moduleSets (I.rings.obj B)).map (e.simplicial.hom.app (op ⦋n⦌))

/-- Underlying comparison of actual complexes in every integer degree.
Source: Stacks 08SV (blueprint: lem-trf-geometric-standard-differential-comparison). -/
def complexArrow {M : Construction J} {N : Construction K}
    {F : Sheaf J (Type w) ⥤ Sheaf K (Type w)} {I : InverseLift F}
    {A B : Sheaf J CommRingCat.{w}} {φ : A ⟶ B}
    (e : StandardComparison M N I φ) (i : ℤ) :=
  (I.modules B).moduleUnderlying.inv.app ((M.alternating φ).complex.X i) ≫
    (SheafDifferentials.moduleSets (I.rings.obj B)).map (e.complex.hom.f i)

end StandardComparison

namespace ConstructionSquare

/-- The underlying differential-tensor square map, including a change of scalars.
Source: Stacks 08SS (blueprint: lem-trf-geometric-standard-differential-comparison). -/
def moduleArrow {M : Construction J}
    {A B A' B' : Sheaf J CommRingCat.{w}} {φ : A ⟶ B} {φ' : A' ⟶ B'}
    {a : A ⟶ A'} {b : B ⟶ B'} (q : ConstructionSquare M φ φ' a b) (n : ℕ) :=
  (SheafDifferentials.moduleSets B).map (q.simplicial.app (op ⦋n⦌))

/-- The underlying complex square map, including a change of scalars.
Source: Stacks 08SS (blueprint: lem-trf-geometric-standard-differential-comparison). -/
def complexArrow {M : Construction J}
    {A B A' B' : Sheaf J CommRingCat.{w}} {φ : A ⟶ B} {φ' : A' ⟶ B'}
    {a : A ⟶ A'} {b : B ⟶ B'} (q : ConstructionSquare M φ φ' a b) (i : ℤ) :=
  (SheafDifferentials.moduleSets B).map (q.complex.f i)

end ConstructionSquare

/-- The standard localization of the existing module-complex category.
Source: Stacks 05RU and 08SS
(blueprint: lem-trf-geometric-standard-differential-comparison). -/
abbrev derived (B : Sheaf J CommRingCat.{w}) :=
  @DerivedCategory (ringedSiteModules.{w} (SheafDifferentials.ring B)) _ _
    (HasDerivedCategory.standard _)

/-- The existing localization functor, with an explicit localization universe.
Source: Stacks 05RU (blueprint: lem-trf-geometric-standard-differential-comparison). -/
def localization (B : Sheaf J CommRingCat.{w}) :
    CochainComplex (ringedSiteModules.{w} (SheafDifferentials.ring B)) ℤ ⥤ derived B :=
  @DerivedCategory.Q (ringedSiteModules.{w} (SheafDifferentials.ring B)) _ _
    (HasDerivedCategory.standard _)

/-- The derived isomorphism is the image of the actual complex isomorphism,
not an independently chosen equivalence. Source: Stacks 08SS and 08SV
(blueprint: lem-trf-geometric-standard-differential-comparison). -/
def derivedComparison {M : Construction J} {N : Construction K}
    {F : Sheaf J (Type w) ⥤ Sheaf K (Type w)} {I : InverseLift F}
    {A B : Sheaf J CommRingCat.{w}} {φ : A ⟶ B}
    (e : StandardComparison M N I φ) :=
  (localization (I.rings.obj B)).mapIso e.complex

/-- The free algebra, standard resolution, differential tensor and alternating
complex have the presentations used in this statement. The free objects are
precisely sheafifications of sectionwise polynomial rings.
Source: Stacks 08SR and 08SS
(blueprint: lem-trf-geometric-standard-differential-comparison).

Proof: polynomial evaluation gives a natural bijection between algebra maps
from the sheafified polynomial presheaf and maps from its generator sheaf.
Thus it gives the free/forgetful adjunction, with the coefficient and variable
normalizations in PolynomialPresentation. Apply the standard-adjunction
resolution theorem to its comonad; its specified counit and comultiplication
give every face, degeneracy and augmentation. In each degree sheafify the
sectionwise differential module and extend scalars by the augmentation.
The differential and balanced tensor universal properties induce all simplex
operators; their uniqueness gives the simplicial identities. The alternating
sum of faces squares to zero by cancellation of the paired simplicial face
identities. Place these terms in degrees -n and put zero in positive degrees.
This constructs all data without choosing an undetermined object. -/
theorem construction_exists (J : GrothendieckTopology C) :
    ∃ M : Construction J, ∀ (R : Sheaf J CommRingCat.{w}) (E : Sheaf J (Type w)),
      Nonempty (PolynomialPresentation M.algebra R E) := by
  sorry

/-- A ring square induces the specified standard algebra, differential tensor
and actual complex maps, including when both coefficient rings change.
Source: Stacks 08SS, functoriality paragraph
(blueprint: lem-trf-geometric-standard-differential-comparison).

Proof: send coefficients by a and the degree-zero variable b to its image
under b. In each later degree send a variable to the image under the previous
polynomial map. Polynomial uniqueness intertwines evaluation and the unit,
hence every face, degeneracy and augmentation. Differentiating sends dp to
d of its image; scalar extension sends c tensor dp to b(c) tensor d(p's image).
The sheafified differential and balanced tensor universal properties give
these module maps and their simplex naturality. Alternating the face equations
gives the displayed actual complex map and its degree normalization. -/
theorem constructionSquare_exists (M : Construction J)
    {A B A' B' : Sheaf J CommRingCat.{w}}
    (φ : A ⟶ B) (φ' : A' ⟶ B') (a : A ⟶ A') (b : B ⟶ B')
    (_h : a ≫ φ' = φ ≫ b) : Nonempty (ConstructionSquare M φ φ' a b) := by
  sorry

/-- Geometric inverse image compares the canonical free algebras, augmented
standard resolutions, simplicial differential tensors and actual alternating
complexes. The derived comparison is derivedComparison, the image of the actual
complex isomorphism. No condition on the topology excludes presheaf topoi.
Source: Stacks 08SR, 08SS, 08SV, 08TQ and 03EL
(blueprint: lem-trf-geometric-standard-differential-comparison).

Proof, following the seven DAG steps:
1. Sectionwise polynomial evaluation and sheafification give the free-algebra
   universal property, with evaluation counit and generator unit.
2. Lift the geometric adjunction to ring objects using finite products. For an
   FR-algebra H, the lifted adjunction followed by the free adjunction represents
   maps FE to its underlying sheaf. The unique representing isomorphism gives
   the free comparison, fixing coefficients and variables.
3. Polynomial uniqueness proves its evaluation, unit and ring-square equations,
   as well as identity and composition coherence.
4. Iterate this comparison on the free/forgetful comonad. The counit and unit
   equations intertwine every face and degeneracy; evaluation gives augmentation
   compatibility. The same recursion fixes the displayed generator equations.
5. In each degree use inverse image of differentials, normalized on the universal
   derivation. Transport its scalar ring by the algebra comparison. Apply the
   normalized inverse-image tensor comparison to extend scalars by the augmentation.
6. Both orders of every simplex or ring-square map send dp tensor c to the same
   transported differential tensor. Differential and bilinear universal properties
   prove equality on sheaf morphisms. This also proves identity and composition
   coherence, including the coefficient tensor maps.
7. The algebraic module inverse image is additive and sends zero to zero. Sum
   the face equations to obtain the actual complex isomorphism with the given
   degree components. Applying the derived localization gives derivedComparison.
   All arguments apply to the topology with only maximal covering sieves. -/
theorem geometric_standard_differential_comparison
    (f : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w)))
    (M : Construction J) (N : Construction K) :
    ∃ I : InverseLift f.inverse, Nonempty (FreeComparison M.algebra N.algebra I) ∧
      ∀ {A B : Sheaf J CommRingCat.{w}} (φ : A ⟶ B),
        Nonempty (StandardComparison M N I φ) := by
  sorry

/-- Naturality in every commutative square of ring sheaves, on the augmented
algebra resolutions, differential tensors and actual complexes in every degree.
The free-algebra naturality is included in FreeComparison.naturality, and
localizing the last equation gives naturality of derivedComparison.
Source: Stacks 08SS, functoriality paragraph, and 08SV
(blueprint: lem-trf-geometric-standard-differential-comparison).

Proof: compare on coefficients and the recursive generators. The two algebra
maps agree by polynomial uniqueness in each degree. For differential tensors
both composites send dp tensor c to d of the same image times the same image
of c. Differential universality and bilinear universality identify them.
Alternating faces gives equality on the actual complexes; zero positive terms
supply the remaining degrees. Apply localization for the derived equation. -/
theorem comparison_naturality
    (f : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w)))
    {M : Construction J} {N : Construction K} {I : InverseLift f.inverse}
    {A B A' B' : Sheaf J CommRingCat.{w}}
    {φ : A ⟶ B} {φ' : A' ⟶ B'} {a : A ⟶ A'} {b : B ⟶ B'}
    (_h : a ≫ φ' = φ ≫ b)
    (q : ConstructionSquare M φ φ' a b)
    (q' : ConstructionSquare N (I.rings.map φ) (I.rings.map φ')
      (I.rings.map a) (I.rings.map b))
    (e : StandardComparison M N I φ) (e' : StandardComparison M N I φ') :
    (∀ n : ℕ,
      f.inverse.map ((setsFunctor J).map (q.algebra.map.app (op ⦋n⦌))) ≫
        e'.algebraArrow n =
      e.algebraArrow n ≫ (setsFunctor K).map (q'.algebra.map.app (op ⦋n⦌))) ∧
    (∀ n : ℕ, f.inverse.map (q.moduleArrow n) ≫ e'.moduleArrow n =
      e.moduleArrow n ≫ q'.moduleArrow n) ∧
    (∀ i : ℤ, f.inverse.map (q.complexArrow i) ≫ e'.complexArrow i =
      e.complexArrow i ≫ q'.complexArrow i) := by
  sorry

/-- The canonical identity lift is available with its identity ring functor and
underlying comparison. Source: Stacks 08SV
(blueprint: lem-trf-geometric-standard-differential-comparison).
Proof: take identity functors on rings and on every module category. Their
underlying comparisons are identities. Every graph-transport equation is then
the original equation, and the module identity functor is additive. -/
theorem identityLift_exists (J : GrothendieckTopology C) :
    ∃ I : InverseLift (𝟭 (Sheaf J (Type w))),
      I.rings = 𝟭 (Sheaf J CommRingCat.{w}) ∧
        HEq I.underlying (Iso.refl (setsFunctor J)) := by
  sorry

/-- Identity inverse-image comparisons are identities under their canonical
ring and module identifications. Heterogeneous equality retains the chosen
presentations while comparing the actual arrows, without imposing equality
of independently presented module structures.
Source: Stacks 08SV (blueprint: lem-trf-geometric-standard-differential-comparison).

Proof: the identity fixes coefficients and variables, so free-algebra uniqueness
gives the first equation. Induction gives the algebra equations. The identity
fixes universal differentials and the coefficient tensor pairing, so the
representing and bilinear universal properties give the module equations.
The prescribed degree components and zero positive terms give the complex
equations. Localization carries this identity to the derived category. -/
theorem comparison_identity (M : Construction J)
    (I : InverseLift (𝟭 (Sheaf J (Type w))))
    (_hR : I.rings = 𝟭 (Sheaf J CommRingCat.{w}))
    (_hU : HEq I.underlying (Iso.refl (setsFunctor J)))
    (t : FreeComparison M.algebra M.algebra I)
    {A B : Sheaf J CommRingCat.{w}} {φ : A ⟶ B}
    (e : StandardComparison M M I φ) :
    (∀ (R : Sheaf J CommRingCat.{w}) (E : Sheaf J (Type w)),
      HEq (t.arrow R E) (𝟙 (SheafDifferentials.sets (M.algebra.polynomial R E)))) ∧
    (∀ n : ℕ, HEq (e.algebraArrow n)
      (𝟙 (SheafDifferentials.sets ((M.algebra.resolution φ).obj (op ⦋n⦌))))) ∧
    (∀ n : ℕ, HEq (e.moduleArrow n)
      (𝟙 ((SheafDifferentials.moduleSets B).obj
        ((M.differential φ).simplicial.obj (op ⦋n⦌))))) ∧
    (∀ i : ℤ, HEq (e.complexArrow i)
      (𝟙 ((SheafDifferentials.moduleSets B).obj ((M.alternating φ).complex.X i)))) := by
  sorry

variable {E : Type uE} [Category.{vE} E] [EssentiallySmall.{w} E]
  {L : GrothendieckTopology E}

/-- Successive algebraic lifts have a composite lift with exactly the
canonical composed underlying identifications. Source: Stacks 08SV
(blueprint: lem-trf-geometric-standard-differential-comparison).
Proof: compose the ring functors. For each ring compose its two module functors;
whisker and compose their underlying natural isomorphisms. Applying the graph
transport equations twice gives the composite graph equations, while naturality
of the underlying isomorphisms fixes all module morphisms. Additivity composes.
The resulting ring underlying map is the displayed successive composite. -/
theorem compositeLift_exists
    (f : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w)))
    (g : GeometricMorphism (Sheaf L (Type w)) (Sheaf K (Type w)))
    (I : InverseLift f.inverse) (G : InverseLift g.inverse) :
    ∃ H : InverseLift (g.comp f).inverse,
      H.rings = I.rings ⋙ G.rings ∧
        ∀ R : Sheaf J CommRingCat.{w}, HEq (H.underlying.inv.app R)
          (g.inverse.map (I.underlying.inv.app R) ≫ G.underlying.inv.app (I.rings.obj R)) := by
  sorry

/-- Composite inverse-image comparisons equal successive comparisons under the
canonical ring and module identifications. These are equations of sheaf arrows
in every degree, and hence also equations of complexes and their localized maps.
Source: Stacks 08SV and 08TQ
(blueprint: lem-trf-geometric-standard-differential-comparison).

Proof: the direct and successive free comparisons carry the twice transported
coefficients and generators to the same coefficients and generators. Polynomial
uniqueness identifies them. Iteration identifies the augmented resolutions.
Both differential comparisons preserve the same universal derivation, and both
tensor comparisons preserve the same bilinear pairing. The two universal
properties identify the resulting module maps. Their alternating-complex
components agree in all nonpositive degrees, and positive terms are zero.
The derived equations follow by applying the localization functor. -/
theorem comparison_composition
    (f : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w)))
    (g : GeometricMorphism (Sheaf L (Type w)) (Sheaf K (Type w)))
    {M : Construction J} {N : Construction K} {O : Construction L}
    (I : InverseLift f.inverse) (G : InverseLift g.inverse)
    (H : InverseLift (g.comp f).inverse)
    (_hR : H.rings = I.rings ⋙ G.rings)
    (_hU : ∀ R : Sheaf J CommRingCat.{w}, HEq (H.underlying.inv.app R)
      (g.inverse.map (I.underlying.inv.app R) ≫ G.underlying.inv.app (I.rings.obj R)))
    (tI : FreeComparison M.algebra N.algebra I)
    (tG : FreeComparison N.algebra O.algebra G)
    (tH : FreeComparison M.algebra O.algebra H)
    {A B : Sheaf J CommRingCat.{w}} {φ : A ⟶ B}
    (eI : StandardComparison M N I φ)
    (eG : StandardComparison N O G (I.rings.map φ))
    (eH : StandardComparison M O H φ) :
    (∀ (R : Sheaf J CommRingCat.{w}) (X : Sheaf J (Type w)),
      HEq (tH.arrow R X)
        (g.inverse.map (tI.arrow R X) ≫ tG.arrow (I.rings.obj R) (f.inverse.obj X))) ∧
    (∀ n : ℕ, HEq (eH.algebraArrow n)
      (g.inverse.map (eI.algebraArrow n) ≫ eG.algebraArrow n)) ∧
    (∀ n : ℕ, HEq (eH.moduleArrow n)
      (g.inverse.map (eI.moduleArrow n) ≫ eG.moduleArrow n)) ∧
    (∀ i : ℤ, HEq (eH.complexArrow i)
      (g.inverse.map (eI.complexArrow i) ≫ eG.complexArrow i)) := by
  sorry

end CategoryTheory.GeometricStandardDifferentials
