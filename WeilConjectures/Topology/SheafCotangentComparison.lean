/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.CotangentResolutionCoherence
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import WeilConjectures.RingTheory.CotangentTransitivityTriangle
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.Sites.InverseImageDifferentials
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.CommRingCat
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.RingTheory.LocalizationCotangentVanishing
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.CategoryTheory.SiteInverseImageTensor
import WeilConjectures.CategoryTheory.ModulePullbackTensorIso
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import WeilConjectures.Topology.InverseImageStalk
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.Localization
import Mathlib.CategoryTheory.Sites.Sheafification

/-!
# Sections, inverse images and stalks of cotangent complexes

Source: Stacks Project, Cotangent Complex, Tags 08SR, 08SS, 08SV, 08SW, 08SX,
08T0 and 08SF (blueprint: lem-trf-affine-cotangent-comparison).

All models below retain their coordinates in the recorded standard resolution.
The module complex is the actual termwise module sheafification. Comparison maps
are normalized on every local section, rather than chosen without a normalization.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Algebra.CotangentResolution Simplicial
open scoped ChangeOfRings

namespace TopCat.SheafCotangent

variable [∀ B : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} B)]

/-- The arrow of section rings. Source: Stacks 08SX
(blueprint: lem-trf-affine-cotangent-comparison). -/
def sectionArrow {T : TopCat.{u}} (f : Arrow (T.Sheaf CommRingCat.{u}))
    (V : (Opens T)ᵒᵖ) : Arrow CommRingCat.{u} :=
  Arrow.mk (f.hom.hom.app V)

/-- The commutative square of restriction maps. Source: Stacks 08SX
(blueprint: lem-trf-affine-cotangent-comparison). -/
def restrictionSquare {T : TopCat.{u}} (f : Arrow (T.Sheaf CommRingCat.{u}))
    {V W : (Opens T)ᵒᵖ} (r : V ⟶ W) : sectionArrow f V ⟶ sectionArrow f W :=
  Arrow.homMk' (f.left.obj.map r) (f.right.obj.map r) (f.hom.hom.naturality r)

/-- Sectionwise standard differential complexes, including all restriction maps.
The displayed isomorphisms and the restriction equation determine this presheaf
complex up to its unique coordinate-preserving isomorphism. Source: Stacks 08SX
(blueprint: lem-trf-affine-cotangent-comparison). -/
structure SectionModel (C : Coherence.{u}) {T : TopCat.{u}}
    (f : Arrow (T.Sheaf CommRingCat.{u})) where
  complex : CochainComplex
    (PresheafOfModules.{u} (CategoryTheory.SheafDifferentials.ring f.right).obj) ℤ
  coordinate : ∀ V : (Opens T)ᵒᵖ,
    ((PresheafOfModules.evaluation _ V).mapHomologicalComplex (.up ℤ)).obj complex ≅
      standardComplex C (sectionArrow f V)
  restriction : ∀ {V W : (Opens T)ᵒᵖ} (r : V ⟶ W) (i : ℤ)
    (x : (complex.X i).obj V),
    (coordinate W).hom.f i ((complex.X i).map r x) =
      (standardComplexMap C (restrictionSquare f r)).f i ((coordinate V).hom.f i x)

/-- The actual sheafification of the sectionwise differential complex, with its
sheaf-module structure. Source: Stacks 08SS, 08SW and 08SX
(blueprint: lem-trf-affine-cotangent-comparison). -/
def sheafComplex {C : Coherence.{u}} {T : TopCat.{u}}
    {f : Arrow (T.Sheaf CommRingCat.{u})} (M : SectionModel C f) :=
  ((PresheafOfModules.sheafification
    (𝟙 (CategoryTheory.SheafDifferentials.ring f.right).obj)).mapHomologicalComplex
      (.up ℤ)).obj M.complex

/-- The unit of module sheafification on a specified section. Source: Stacks 08SX
(blueprint: lem-trf-affine-cotangent-comparison). -/
def sectionElement {C : Coherence.{u}} {T : TopCat.{u}}
    {f : Arrow (T.Sheaf CommRingCat.{u})} (M : SectionModel C f)
    (V : (Opens T)ᵒᵖ) (i : ℤ) (x : (standardComplex C (sectionArrow f V)).X i) :
    ((sheafComplex M).X i).val.obj V :=
  (((PresheafOfModules.sheafificationAdjunction
    (𝟙 (CategoryTheory.SheafDifferentials.ring f.right).obj)).unit.app
      (M.complex.X i)).app V) ((M.coordinate V).inv.f i x)

/-- Underlying additive sheaf complex, retaining the specified module complex.
Source: Stacks 08SS (blueprint: lem-trf-affine-cotangent-comparison). -/
def additiveComplex {C : Coherence.{u}} {T : TopCat.{u}}
    {f : Arrow (T.Sheaf CommRingCat.{u})} (M : SectionModel C f) :=
  ((SheafOfModules.toSheaf _).mapHomologicalComplex (.up ℤ)).obj (sheafComplex M)

/-- Evaluation of module complexes on an open. Source: Stacks 08SX
(blueprint: lem-trf-affine-cotangent-comparison). -/
def evaluationComplex {T : TopCat.{u}} (B : T.Sheaf CommRingCat.{u})
    (V : (Opens T)ᵒᵖ) :=
  (SheafOfModules.forget.{u} (CategoryTheory.SheafDifferentials.ring B) ⋙
    PresheafOfModules.evaluation _ V).mapHomologicalComplex (.up ℤ)

/-- A sheafified differential tensor term. Source: Stacks 08SS
(blueprint: lem-trf-affine-cotangent-comparison). -/
def differentialSheaf {T : TopCat.{u}} {A P B : T.Sheaf CommRingCat.{u}}
    (a : A ⟶ P) (b : P ⟶ B) :=
  SheafOfModules.changeOfRings.{u, u, u} b (CategoryTheory.SheafDifferentials.omega a)

/-- The actual local tensor `b ⊗ dx`, followed by module sheafification.
Source: Stacks 08SS (blueprint: lem-trf-affine-cotangent-comparison). -/
def differentialSection {T : TopCat.{u}} {A P B : T.Sheaf CommRingCat.{u}}
    (a : A ⟶ P) (b : P ⟶ B) (V : (Opens T)ᵒᵖ) (y : B.obj.obj V)
    (x : P.obj.obj V) : (differentialSheaf a b).val.obj V :=
  (((PresheafOfModules.sheafificationAdjunction
    (𝟙 (CategoryTheory.SheafDifferentials.ring B).obj)).unit.app
      (SheafOfModules.changeOfRingsPresheaf.{u, u, u} b
        (CategoryTheory.SheafDifferentials.omega a))).app V)
    (y ⊗ₜ[_, (b.hom.app V).hom] (CategoryTheory.SheafDifferentials.derivation a).d x)

/-- The polynomial presheaf `V ↦ A(V)[E(V)]`, on the underlying sets of the
ring sheaf `E`. Restrictions act on both coefficients and variable labels.
Source: Stacks 08SR (blueprint: lem-trf-affine-cotangent-comparison). -/
def freeAlgebraPresheaf {T : TopCat.{u}} (A E : T.Sheaf CommRingCat.{u}) :
    T.Presheaf CommRingCat.{u} where
  obj V := CommRingCat.of (MvPolynomial (E.obj.obj V) (A.obj.obj V))
  map r := CommRingCat.ofHom (MvPolynomial.eval₂Hom
    (MvPolynomial.C.comp (A.obj.map r).hom) (fun e ↦ MvPolynomial.X (E.obj.map r e)))
  map_id V := by
    apply CommRingCat.hom_ext
    ext a e <;> simp
  map_comp r s := by
    apply CommRingCat.hom_ext
    ext a e <;> simp

/-- The actual free sheaf `A[E]`: sheafify the sectionwise polynomial algebra.
Only the underlying set sheaf of `E` is used. This construction is distinct from
sheafifying an entire sectionwise iterated resolution.
Source: Stacks 08SR (blueprint: lem-trf-affine-cotangent-comparison). -/
def freeSheafAlgebra {T : TopCat.{u}} (A E : T.Sheaf CommRingCat.{u}) :
    T.Sheaf CommRingCat.{u} :=
  (presheafToSheaf (Opens.grothendieckTopology T) CommRingCat).obj
    (freeAlgebraPresheaf A E)

/-- The local polynomial map into the free sheaf algebra, so its values on `C a`
and `X e` are the canonical coefficient and generator sections.
Source: Stacks 08SR (blueprint: lem-trf-affine-cotangent-comparison). -/
def freeSheafSection {T : TopCat.{u}} (A E : T.Sheaf CommRingCat.{u})
    (V : (Opens T)ᵒᵖ) : CommRingCat.of (MvPolynomial (E.obj.obj V) (A.obj.obj V)) ⟶
      (freeSheafAlgebra A E).obj.obj V :=
  (CategoryTheory.toSheafify (Opens.grothendieckTopology T)
    (freeAlgebraPresheaf A E)).app V

/-- The standard polynomial algebra in a given degree, before sheafification,
with the prescribed ring-square restrictions. Source: Stacks 08SR and 08SX
(blueprint: lem-trf-affine-cotangent-comparison). -/
structure PolynomialSections {T : TopCat.{u}} (f : Arrow (T.Sheaf CommRingCat.{u}))
    (n : ℕ) where
  presheaf : T.Presheaf CommRingCat.{u}
  coordinate : ∀ V : (Opens T)ᵒᵖ, presheaf.obj V ≅ standardTerm (sectionArrow f V) n
  restriction : ∀ {V W : (Opens T)ᵒᵖ} (r : V ⟶ W),
    presheaf.map r ≫ (coordinate W).hom =
      (coordinate V).hom ≫ standardSquareMap (restrictionSquare f r) n

/-- The local polynomial map into a sheafification, in the fixed standard coordinates.
Source: Stacks 08SR (blueprint: lem-trf-affine-cotangent-comparison). -/
def polynomialSection {T : TopCat.{u}} {f : Arrow (T.Sheaf CommRingCat.{u})}
    {n : ℕ} (P : PolynomialSections f n) {Q : T.Sheaf CommRingCat.{u}}
    (e : (presheafToSheaf (Opens.grothendieckTopology T) CommRingCat).obj P.presheaf ≅ Q)
    (V : (Opens T)ᵒᵖ) : standardTerm (sectionArrow f V) n ⟶ Q.obj.obj V :=
  (P.coordinate V).inv ≫
    (CategoryTheory.toSheafify (Opens.grothendieckTopology T) P.presheaf).app V ≫
      e.hom.hom.app V

/-- The sheaf standard resolution and its differential simplicial module. All
terms are also identified with `A[B]` and the actual successive free sheaf
algebras `A[P_n]`, with coefficient and generator normalizations. All polynomial
maps, faces, degeneracies, base maps and augmentations are fixed in section coordinates.
The complex comparison also fixes every differential generator.
Source: Stacks 08SR, 08SS and 08SX
(blueprint: lem-trf-affine-cotangent-comparison). -/
structure StandardSheafModel (C : Coherence.{u}) {T : TopCat.{u}}
    (f : Arrow (T.Sheaf CommRingCat.{u})) (M : SectionModel C f) where
  polynomial : ∀ n : ℕ, PolynomialSections f n
  algebra : SimplicialObject (T.Sheaf CommRingCat.{u})
  algebraIso : ∀ n : ℕ,
    (presheafToSheaf (Opens.grothendieckTopology T) CommRingCat).obj
      (polynomial n).presheaf ≅ algebra.obj (op ⦋n⦌)
  base : (SimplicialObject.const _).obj f.left ⟶ algebra
  augmentation : algebra ⟶ (SimplicialObject.const _).obj f.right
  initialFreeIso : algebra.obj (op ⦋0⦌) ≅ freeSheafAlgebra f.left f.right
  initialFree_coeff : ∀ (V : (Opens T)ᵒᵖ) (a : f.left.obj.obj V),
    initialFreeIso.hom.hom.app V ((base.app (op ⦋0⦌)).hom.app V a) =
      freeSheafSection f.left f.right V (MvPolynomial.C a)
  initialFree_generator : ∀ (V : (Opens T)ᵒᵖ) (b : f.right.obj.obj V),
    initialFreeIso.hom.hom.app V
      (polynomialSection (polynomial 0) (algebraIso 0) V (MvPolynomial.X b)) =
      freeSheafSection f.left f.right V (MvPolynomial.X b)
  freeTermIso : ∀ n : ℕ, algebra.obj (op ⦋n + 1⦌) ≅
    freeSheafAlgebra f.left (algebra.obj (op ⦋n⦌))
  freeTerm_coeff : ∀ (n : ℕ) (V : (Opens T)ᵒᵖ) (a : f.left.obj.obj V),
    (freeTermIso n).hom.hom.app V ((base.app (op ⦋n + 1⦌)).hom.app V a) =
      freeSheafSection f.left (algebra.obj (op ⦋n⦌)) V (MvPolynomial.C a)
  freeTerm_generator : ∀ (n : ℕ) (V : (Opens T)ᵒᵖ)
    (p : standardTerm (sectionArrow f V) n),
    (freeTermIso n).hom.hom.app V
      (polynomialSection (polynomial (n + 1)) (algebraIso (n + 1)) V (MvPolynomial.X p)) =
      freeSheafSection f.left (algebra.obj (op ⦋n⦌)) V
        (MvPolynomial.X (polynomialSection (polynomial n) (algebraIso n) V p))
  triangle : ∀ n : ℕ, base.app (op ⦋n⦌) ≫ augmentation.app (op ⦋n⦌) = f.hom
  base_formula : ∀ (n : ℕ) (V : (Opens T)ᵒᵖ),
    standardBase (sectionArrow f V) n ≫ polynomialSection (polynomial n) (algebraIso n) V =
      (base.app (op ⦋n⦌)).hom.app V
  augmentation_formula : ∀ (n : ℕ) (V : (Opens T)ᵒᵖ),
    polynomialSection (polynomial n) (algebraIso n) V ≫
      (augmentation.app (op ⦋n⦌)).hom.app V = standardAugmentation (sectionArrow f V) n
  face_formula : ∀ (n : ℕ) (i : Fin (n + 2)) (V : (Opens T)ᵒᵖ),
    polynomialSection (polynomial (n + 1)) (algebraIso (n + 1)) V ≫
      (algebra.δ i).hom.app V =
        standardFace (sectionArrow f V) n i ≫
          polynomialSection (polynomial n) (algebraIso n) V
  degeneracy_formula : ∀ (n : ℕ) (i : Fin (n + 1)) (V : (Opens T)ᵒᵖ),
    polynomialSection (polynomial n) (algebraIso n) V ≫ (algebra.σ i).hom.app V =
      standardDegeneracy (sectionArrow f V) n i ≫
        polynomialSection (polynomial (n + 1)) (algebraIso (n + 1)) V
  differentials : SimplicialObject
    (ringedSiteModules.{u} (CategoryTheory.SheafDifferentials.ring f.right))
  differentialIso : ∀ n : ℕ, differentials.obj (op ⦋n⦌) ≅
    differentialSheaf (base.app (op ⦋n⦌)) (augmentation.app (op ⦋n⦌))
  operator : ∀ (m n : ℕ) (θ : ⦋m⦌ ⟶ ⦋n⦌) (V : (Opens T)ᵒᵖ)
    (b : f.right.obj.obj V) (x : (algebra.obj (op ⦋n⦌)).obj.obj V),
    ((differentials.map θ.op) ≫ (differentialIso m).hom).val.app V
      ((differentialIso n).inv.val.app V
        (differentialSection (base.app (op ⦋n⦌)) (augmentation.app (op ⦋n⦌)) V b x)) =
      differentialSection (base.app (op ⦋m⦌)) (augmentation.app (op ⦋m⦌)) V b
        ((algebra.map θ.op).hom.app V x)
  complexIso : (negativeComplex _).obj differentials ≅ sheafComplex M
  generator : ∀ (n : ℕ) (V : (Opens T)ᵒᵖ) (b : f.right.obj.obj V)
    (x : (C.standard (sectionArrow f V)).algebra.obj (op ⦋n⦌)),
    HEq ((complexIso.hom.f (-(n : ℤ))).val.app V
      ((((AlgebraicTopology.alternatingFaceMapComplex _).obj differentials).extendXIso
        ComplexShape.embeddingDownNat (i := n) rfl).inv.val.app V
        ((differentialIso n).inv.val.app V
          (differentialSection (base.app (op ⦋n⦌)) (augmentation.app (op ⦋n⦌)) V b
            (polynomialSection (polynomial n) (algebraIso n) V
              (eqToHom ((C.standard_spec (sectionArrow f V)).1 n) x))))))
      (sectionElement M V (-(n : ℤ))
        (complexGenerator (C.differentials (C.standard (sectionArrow f V))) n b x))

/-- The section maps are chain maps, and are precisely the sheafification unit
in the specified coordinates. Source: Stacks 08SX
(blueprint: lem-trf-affine-cotangent-comparison). -/
structure SheafModel (C : Coherence.{u}) {T : TopCat.{u}}
    (f : Arrow (T.Sheaf CommRingCat.{u})) where
  sections : SectionModel C f
  standard : StandardSheafModel C f sections
  sectionMap : ∀ V : (Opens T)ᵒᵖ,
    standardComplex C (sectionArrow f V) ⟶
      (evaluationComplex f.right V).obj (sheafComplex sections)
  section_formula : ∀ (V : (Opens T)ᵒᵖ) (i : ℤ)
    (x : (standardComplex C (sectionArrow f V)).X i),
    (sectionMap V).f i x = sectionElement sections V i x
  section_restriction : ∀ {V W : (Opens T)ᵒᵖ} (r : V ⟶ W) (i : ℤ)
    (x : (standardComplex C (sectionArrow f V)).X i),
    ((sheafComplex sections).X i).val.map r ((sectionMap V).f i x) =
      (sectionMap W).f i ((standardComplexMap C (restrictionSquare f r)).f i x)

/-- A square of ring sheaves over a continuous map, in adjoint form.
Source: Stacks 08SV (blueprint: lem-trf-affine-cotangent-comparison). -/
abbrev RingSquare {T T' : TopCat.{u}} (v : T' ⟶ T)
    (f : Arrow (T.Sheaf CommRingCat.{u})) (g : Arrow (T'.Sheaf CommRingCat.{u})) :=
  f ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} v).mapArrow.obj g

/-- The canonical inverse-image arrow of ring sheaves. Source: Stacks 08SV
(blueprint: lem-trf-affine-cotangent-comparison). -/
def inverseImageArrow {T T' : TopCat.{u}} (v : T' ⟶ T)
    (f : Arrow (T.Sheaf CommRingCat.{u})) : Arrow (T'.Sheaf CommRingCat.{u}) :=
  (TopCat.Sheaf.pullback CommRingCat.{u} v).mapArrow.obj f

/-- The canonical ring square given by the inverse-image adjunction unit.
Source: Stacks 08SV (blueprint: lem-trf-affine-cotangent-comparison). -/
def inverseImageSquare {T T' : TopCat.{u}} (v : T' ⟶ T)
    (f : Arrow (T.Sheaf CommRingCat.{u})) : RingSquare v f (inverseImageArrow v f) :=
  Arrow.homMk' ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} v).unit.app
    f.left) ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} v).unit.app f.right)
      ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} v).unit.naturality f.hom).symm

/-- The induced square on sections of an open and its inverse image.
Source: Stacks 08SV, 08SX (blueprint: lem-trf-affine-cotangent-comparison). -/
def sectionSquare {T T' : TopCat.{u}} {v : T' ⟶ T}
    {f : Arrow (T.Sheaf CommRingCat.{u})} {g : Arrow (T'.Sheaf CommRingCat.{u})}
    (q : RingSquare v f g) (V : (Opens T)ᵒᵖ) :
    sectionArrow f V ⟶ sectionArrow g ((Opens.map v).op.obj V) :=
  Arrow.homMk' (q.left.hom.app V) (q.right.hom.app V)
    (congrArg (fun h ↦ h.hom.app V) q.w)

/-- Pushforward on additive complexes. Source: Stacks 08SV
(blueprint: lem-trf-affine-cotangent-comparison). -/
def pushforwardComplex {T T' : TopCat.{u}} (v : T' ⟶ T) :=
  letI : (TopCat.Sheaf.pushforward AddCommGrpCat.{u} v).Additive :=
    { map_add := rfl }
  (TopCat.Sheaf.pushforward AddCommGrpCat.{u} v).mapHomologicalComplex (.up ℤ)

/-- The inverse-image/pushforward adjunction on additive complexes. Its inverse
image is the usual topological inverse image. Source: Stacks 08SV
(blueprint: lem-trf-affine-cotangent-comparison). -/
def inverseAdjunction {T T' : TopCat.{u}} (v : T' ⟶ T) :=
  letI : (TopCat.Sheaf.pushforward AddCommGrpCat.{u} v).Additive :=
    { map_add := rfl }
  letI := (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} v).left_adjoint_additive
  (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} v).mapHomologicalComplex (.up ℤ)

/-- Inverse image on additive complexes. Source: Stacks 08SV
(blueprint: lem-trf-affine-cotangent-comparison). -/
def pullbackComplex {T T' : TopCat.{u}} (v : T' ⟶ T) :=
  letI : (TopCat.Sheaf.pushforward AddCommGrpCat.{u} v).Additive :=
    { map_add := rfl }
  letI := (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} v).left_adjoint_additive
  (TopCat.Sheaf.pullback AddCommGrpCat.{u} v).mapHomologicalComplex (.up ℤ)

/-- A canonical map of cotangent complexes. Its values on all local standard
sections determine it uniquely, and the scalar formula keeps the ring action explicit.
Source: Stacks 08SS, 08SV (blueprint: lem-trf-affine-cotangent-comparison). -/
structure MapModel (C : Coherence.{u}) {T T' : TopCat.{u}} {v : T' ⟶ T}
    {f : Arrow (T.Sheaf CommRingCat.{u})} {g : Arrow (T'.Sheaf CommRingCat.{u})}
    (M : SheafModel C f) (N : SheafModel C g) (q : RingSquare v f g) where
  map : additiveComplex M.sections ⟶ (pushforwardComplex v).obj (additiveComplex N.sections)
  section_formula : ∀ (V : (Opens T)ᵒᵖ) (i : ℤ)
    (x : (standardComplex C (sectionArrow f V)).X i),
    (map.f i).hom.app V (sectionElement M.sections V i x) =
      sectionElement N.sections ((Opens.map v).op.obj V) i
        ((standardComplexMap C (sectionSquare q V)).f i x)
  scalar : ∀ (V : (Opens T)ᵒᵖ) (i : ℤ) (a : f.right.obj.obj V)
    (x : ((sheafComplex M.sections).X i).val.obj V),
    (map.f i).hom.app V (a • x) =
      @SMul.smul (g.right.obj.obj ((Opens.map v).op.obj V))
        (((sheafComplex N.sections).X i).val.obj ((Opens.map v).op.obj V)) inferInstance
          (q.right.hom.app V a) ((map.f i).hom.app V x)

/-- Realization of a sheaf-module complex in its standard derived category.
Source: Stacks 08SS (blueprint: lem-trf-affine-cotangent-comparison). -/
def derivedModuleObject {T : TopCat.{u}} {B : T.Sheaf CommRingCat.{u}}
    (K : CochainComplex (ringedSiteModules.{u}
      (CategoryTheory.SheafDifferentials.ring B)) ℤ) :=
  letI := HasDerivedCategory.standard
    (ringedSiteModules.{u} (CategoryTheory.SheafDifferentials.ring B))
  (DerivedCategory.Q (C := SheafOfModules.{u}
    (CategoryTheory.SheafDifferentials.ring B))).obj K

/-- A complex isomorphism gives the asserted isomorphism in the derived category
of module sheaves. Source: Stacks 08SS, 08SV
(blueprint: lem-trf-affine-cotangent-comparison). -/
def derivedModuleIso {T : TopCat.{u}} {B : T.Sheaf CommRingCat.{u}}
    {K L : CochainComplex (ringedSiteModules.{u}
      (CategoryTheory.SheafDifferentials.ring B)) ℤ} (e : K ≅ L) :=
  letI := HasDerivedCategory.standard
    (ringedSiteModules.{u} (CategoryTheory.SheafDifferentials.ring B))
  (DerivedCategory.Q (C := SheafOfModules.{u}
    (CategoryTheory.SheafDifferentials.ring B))).mapIso e

/-- A module inverse-image complex, its canonical comparison, and its derived
isomorphism. The underlying complex is the actual topological inverse image;
the scalar equation specifies the transported action on the inverse-image unit.
This is a presentation of inverse image, not an additional linearity hypothesis.
Source: Stacks 08SV (blueprint: lem-trf-affine-cotangent-comparison). -/
structure InverseModel (C : Coherence.{u}) {T T' : TopCat.{u}} {v : T' ⟶ T}
    {f : Arrow (T.Sheaf CommRingCat.{u})} {g : Arrow (T'.Sheaf CommRingCat.{u})}
    (M : SheafModel C f) (N : SheafModel C g) (q : RingSquare v f g)
    (m : MapModel C M N q) where
  complex : CochainComplex
    (ringedSiteModules.{u} (CategoryTheory.SheafDifferentials.ring g.right)) ℤ
  underlying : ((SheafOfModules.toSheaf _).mapHomologicalComplex (.up ℤ)).obj complex ≅
    (pullbackComplex v).obj (additiveComplex M.sections)
  comparison : complex ≅ sheafComplex N.sections
  normalization :
    ((SheafOfModules.toSheaf _).mapHomologicalComplex (.up ℤ)).map comparison.hom =
      underlying.hom ≫ ((inverseAdjunction v).homEquiv _ _).symm m.map
  scalar : ∀ (V : (Opens T)ᵒᵖ) (i : ℤ) (a : f.right.obj.obj V)
    (x : ((sheafComplex M.sections).X i).val.obj V),
    (underlying.inv.f i).hom.app ((Opens.map v).op.obj V)
      ((((inverseAdjunction v).unit.app (additiveComplex M.sections)).f i).hom.app V
        (a • x)) =
      @SMul.smul (g.right.obj.obj ((Opens.map v).op.obj V))
        ((complex.X i).val.obj ((Opens.map v).op.obj V)) inferInstance
        (q.right.hom.app V a)
        ((underlying.inv.f i).hom.app ((Opens.map v).op.obj V)
          ((((inverseAdjunction v).unit.app (additiveComplex M.sections)).f i).hom.app V x))
  derived : derivedModuleObject (B := g.right) complex ≅
    derivedModuleObject (B := g.right) (sheafComplex N.sections)
  derived_normalization : derived = derivedModuleIso (B := g.right) comparison

/-- The identity square. Source: Stacks 08SS, functoriality
(blueprint: lem-trf-affine-cotangent-comparison). -/
def identitySquare {T : TopCat.{u}} (f : Arrow (T.Sheaf CommRingCat.{u})) :
    RingSquare (𝟙 T) f f := 𝟙 f

/-- Composite ring-sheaf squares, including the continuous maps.
Source: Stacks 08SS, 08SV (blueprint: lem-trf-affine-cotangent-comparison). -/
def composeSquare {T T' T'' : TopCat.{u}} {v : T' ⟶ T} {w : T'' ⟶ T'}
    {f : Arrow (T.Sheaf CommRingCat.{u})} {g : Arrow (T'.Sheaf CommRingCat.{u})}
    {h : Arrow (T''.Sheaf CommRingCat.{u})}
    (q : RingSquare v f g) (r : RingSquare w g h) : RingSquare (w ≫ v) f h :=
  q ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} v).mapArrow.map r

/-- The arrow of stalk rings. Source: Stacks 08T0
(blueprint: lem-trf-affine-cotangent-comparison). -/
def stalkArrow {T : TopCat.{u}} (f : Arrow (T.Sheaf CommRingCat.{u})) (t : T) :=
  (TopCat.Sheaf.forget CommRingCat.{u} T ⋙
    TopCat.Presheaf.stalkFunctor CommRingCat.{u} t).mapArrow.obj f

/-- The canonical square from sections to germs. Source: Stacks 08T0
(blueprint: lem-trf-affine-cotangent-comparison). -/
def germSquare {T : TopCat.{u}} (f : Arrow (T.Sheaf CommRingCat.{u}))
    (V : Opens T) (t : T) (ht : t ∈ V) : sectionArrow f (op V) ⟶ stalkArrow f t :=
  Arrow.homMk' (TopCat.Presheaf.germ f.left.obj V t ht) (TopCat.Presheaf.germ f.right.obj V t ht)
    (TopCat.Presheaf.stalkFunctor_map_germ V t ht f.hom.hom)

/-- Actual additive stalk complex. Source: Stacks 08T0
(blueprint: lem-trf-affine-cotangent-comparison). -/
def stalkComplex {C : Coherence.{u}} {T : TopCat.{u}}
    {f : Arrow (T.Sheaf CommRingCat.{u})} (M : SectionModel C f) (t : T) :=
  ((TopCat.Sheaf.forget AddCommGrpCat.{u} T ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} t).mapHomologicalComplex (.up ℤ)).obj
      (additiveComplex M)

/-- A germ of a section of the actual module complex. Source: Stacks 08T0
(blueprint: lem-trf-affine-cotangent-comparison). -/
def moduleGerm {C : Coherence.{u}} {T : TopCat.{u}}
    {f : Arrow (T.Sheaf CommRingCat.{u})} (M : SectionModel C f)
    (t : T) (V : Opens T) (ht : t ∈ V) (i : ℤ)
    (x : ((sheafComplex M).X i).val.obj (op V)) : (stalkComplex M t).X i :=
  TopCat.Presheaf.germ ((additiveComplex M).X i).obj V t ht x

/-- The module stalk comparison, normalized by the section-to-germ square.
Its module action is the ordinary germ action, and the derived isomorphism is
literally the image of the complex isomorphism. Source: Stacks 08T0
(blueprint: lem-trf-affine-cotangent-comparison). -/
structure StalkModel (C : Coherence.{u}) {T : TopCat.{u}}
    {f : Arrow (T.Sheaf CommRingCat.{u})} (M : SheafModel C f) (t : T) where
  complex : CochainComplex (ModuleCat.{u} (stalkArrow f t).right) ℤ
  underlying : ((forget₂ (ModuleCat.{u} (stalkArrow f t).right)
    AddCommGrpCat).mapHomologicalComplex (.up ℤ)).obj complex ≅ stalkComplex M.sections t
  scalar : ∀ (V : Opens T) (ht : t ∈ V) (i : ℤ) (a : f.right.obj.obj (op V))
    (x : ((sheafComplex M.sections).X i).val.obj (op V)),
    underlying.inv.f i (moduleGerm M.sections t V ht i (a • x)) =
      @SMul.smul (stalkArrow f t).right (complex.X i) inferInstance
        (TopCat.Presheaf.germ f.right.obj V t ht a)
        (underlying.inv.f i (moduleGerm M.sections t V ht i x))
  comparison : complex ≅ standardComplex C (stalkArrow f t)
  germ_formula : ∀ (V : Opens T) (ht : t ∈ V) (i : ℤ)
    (x : (standardComplex C (sectionArrow f (op V))).X i),
    comparison.hom.f i
      (underlying.inv.f i (moduleGerm M.sections t V ht i
        (sectionElement M.sections (op V) i x))) =
      (standardComplexMap C (germSquare f V t ht)).f i x
  derived : DerivedCategory.Q.obj complex ≅ cotangentComplex C (stalkArrow f t)
  derived_normalization : derived = DerivedCategory.Q.mapIso comparison

/-- The canonical map of stalk rings associated to a square over a continuous
map. Its formula on every germ determines it uniquely. Source: Stacks 08T0
(blueprint: lem-trf-affine-cotangent-comparison). -/
structure StalkRingMap {T T' : TopCat.{u}} {v : T' ⟶ T}
    {f : Arrow (T.Sheaf CommRingCat.{u})} {g : Arrow (T'.Sheaf CommRingCat.{u})}
    (q : RingSquare v f g) (t : T') where
  square : stalkArrow f (v t) ⟶ stalkArrow g t
  germ_formula : ∀ (V : Opens T) (ht : v t ∈ V),
    germSquare f V (v t) ht ≫ square =
      sectionSquare q (op V) ≫ germSquare g ((Opens.map v).obj V) t ht

/-- The canonical comparison for composite topological inverse images, defined
by uniqueness of the left adjoint to the same pushforward. Source: Stacks 08SV
(blueprint: lem-trf-affine-cotangent-comparison). -/
def inverseComposition {T T' T'' : TopCat.{u}} (v : T' ⟶ T) (w : T'' ⟶ T') :
    pullbackComplex (w ≫ v) ≅ pullbackComplex v ⋙ pullbackComplex w :=
  Adjunction.leftAdjointUniq (inverseAdjunction (w ≫ v))
    ((inverseAdjunction v).comp (inverseAdjunction w))

/-- Ordinary tensor extension of the standard complex for a ring square.
Source: Stacks 08SF (blueprint: lem-trf-affine-cotangent-comparison). -/
def baseChangeComplex (C : Coherence.{u}) {f g : Arrow CommRingCat.{u}} (q : f ⟶ g) :=
  ((ModuleCat.extendScalars q.right.hom).mapHomologicalComplex (.up ℤ)).obj
    (standardComplex C f)

/-- The canonical tensor comparison is the transpose of the recorded standard
semilinear map; it is not an arbitrary arrow. Source: Stacks 08QL, 08SF
(blueprint: lem-trf-affine-cotangent-comparison). -/
def baseChangeMap (C : Coherence.{u}) {f g : Arrow CommRingCat.{u}} (q : f ⟶ g) :
    baseChangeComplex C q ⟶ standardComplex C g :=
  ((tensorComplexAdj q.right).homEquiv _ _).symm (standardComplexMap C q)

/-- The induced map of simultaneous localizations, defined by the localization
universal property. Source: Stacks 08SF
(blueprint: lem-trf-affine-cotangent-comparison). -/
def localizationArrow (f : Arrow CommRingCat.{u}) (S : Submonoid f.left)
    (W : Submonoid f.right) (h : S ≤ W.comap f.hom.hom) : Arrow CommRingCat.{u} :=
  Arrow.mk (CommRingCat.ofHom
    (IsLocalization.map (S := Localization S) (Localization W) f.hom.hom h))

/-- The canonical square from a ring map to its simultaneous localization.
Source: Stacks 08SF (blueprint: lem-trf-affine-cotangent-comparison). -/
def localizationSquare (f : Arrow CommRingCat.{u}) (S : Submonoid f.left)
    (W : Submonoid f.right) (h : S ≤ W.comap f.hom.hom) :
    f ⟶ localizationArrow f S W h :=
  Arrow.homMk' (CommRingCat.ofHom (algebraMap f.left (Localization S)))
    (CommRingCat.ofHom (algebraMap f.right (Localization W)))
    (CommRingCat.hom_ext (IsLocalization.map_comp h))

/-- Localization comparison in the derived category, with the actual canonical
quasi-isomorphism and its normalization retained. Source: Stacks 08SF
(blueprint: lem-trf-affine-cotangent-comparison). -/
structure LocalizationModel (C : Coherence.{u}) (f : Arrow CommRingCat.{u})
    (S : Submonoid f.left) (W : Submonoid f.right) (h : S ≤ W.comap f.hom.hom) where
  comparison : DerivedCategory.Q.obj
    (baseChangeComplex C (localizationSquare f S W h)) ≅
      cotangentComplex C (localizationArrow f S W h)
  normalization : comparison.hom = DerivedCategory.Q.map
    (baseChangeMap C (localizationSquare f S W h))
  quasiIso : QuasiIso (baseChangeMap C (localizationSquare f S W h))

/-- The complete comparison assertion, with canonical coordinates on every object
and map. Inverse-image presentations have their actual transported module action;
all naturality and composition equations concern the specified canonical maps.
Source: Stacks 08SR, 08SS, 08SV, 08SW, 08SX, 08T0 and 08SF
(blueprint: lem-trf-affine-cotangent-comparison). -/
structure Comparison (C : Coherence.{u}) where
  sheaves : ∀ (T : TopCat.{u}) (f : Arrow (T.Sheaf CommRingCat.{u})), SheafModel C f
  maps : ∀ {T T' : TopCat.{u}} {v : T' ⟶ T}
    {f : Arrow (T.Sheaf CommRingCat.{u})} {g : Arrow (T'.Sheaf CommRingCat.{u})}
    (q : RingSquare v f g), MapModel C (sheaves T f) (sheaves T' g) q
  map_unique : ∀ {T T' : TopCat.{u}} {v : T' ⟶ T}
    {f : Arrow (T.Sheaf CommRingCat.{u})} {g : Arrow (T'.Sheaf CommRingCat.{u})}
    (q : RingSquare v f g) (m : MapModel C (sheaves T f) (sheaves T' g) q),
    m.map = (maps q).map
  map_id : ∀ (T : TopCat.{u}) (f : Arrow (T.Sheaf CommRingCat.{u}))
    (V : (Opens T)ᵒᵖ) (i : ℤ)
    (x : ((sheafComplex (sheaves T f).sections).X i).val.obj V),
    ((maps (identitySquare f)).map.f i).hom.app V x = x
  map_comp : ∀ {T T' T'' : TopCat.{u}} {v : T' ⟶ T} {w : T'' ⟶ T'}
    {f : Arrow (T.Sheaf CommRingCat.{u})} {g : Arrow (T'.Sheaf CommRingCat.{u})}
    {h : Arrow (T''.Sheaf CommRingCat.{u})} (q : RingSquare v f g) (r : RingSquare w g h)
    (V : (Opens T)ᵒᵖ) (i : ℤ)
    (x : ((sheafComplex (sheaves T f).sections).X i).val.obj V),
    ((maps (composeSquare q r)).map.f i).hom.app V x =
      ((maps r).map.f i).hom.app ((Opens.map v).op.obj V)
        (((maps q).map.f i).hom.app V x)
  inverse : ∀ {T T' : TopCat.{u}} (v : T' ⟶ T)
    (f : Arrow (T.Sheaf CommRingCat.{u})),
    InverseModel C (sheaves T f) (sheaves T' (inverseImageArrow v f))
      (inverseImageSquare v f) (maps (inverseImageSquare v f))
  inverse_comp : ∀ {T T' T'' : TopCat.{u}} {v : T' ⟶ T} {w : T'' ⟶ T'}
    {f : Arrow (T.Sheaf CommRingCat.{u})} {g : Arrow (T'.Sheaf CommRingCat.{u})}
    {h : Arrow (T''.Sheaf CommRingCat.{u})} (q : RingSquare v f g) (r : RingSquare w g h),
    ((inverseAdjunction (w ≫ v)).homEquiv _ _).symm (maps (composeSquare q r)).map =
      (inverseComposition v w).hom.app (additiveComplex (sheaves T f).sections) ≫
        (pullbackComplex w).map
          (((inverseAdjunction v).homEquiv _ _).symm (maps q).map) ≫
            ((inverseAdjunction w).homEquiv _ _).symm (maps r).map
  stalks : ∀ (T : TopCat.{u}) (f : Arrow (T.Sheaf CommRingCat.{u})) (t : T),
    StalkModel C (sheaves T f) t
  stalk_ring : ∀ {T T' : TopCat.{u}} {v : T' ⟶ T}
    {f : Arrow (T.Sheaf CommRingCat.{u})} {g : Arrow (T'.Sheaf CommRingCat.{u})}
    (q : RingSquare v f g) (t : T'), StalkRingMap q t
  stalk_naturality : ∀ {T T' : TopCat.{u}} {v : T' ⟶ T}
    {f : Arrow (T.Sheaf CommRingCat.{u})} {g : Arrow (T'.Sheaf CommRingCat.{u})}
    (q : RingSquare v f g) (t : T') (V : Opens T) (ht : v t ∈ V) (i : ℤ)
    (x : ((sheafComplex (sheaves T f).sections).X i).val.obj (op V)),
    (stalks T' g t).comparison.hom.f i
      ((stalks T' g t).underlying.inv.f i
        (moduleGerm (sheaves T' g).sections t ((Opens.map v).obj V) ht i
          (((maps q).map.f i).hom.app (op V) x))) =
      (standardComplexMap C (stalk_ring q t).square).f i
        ((stalks T f (v t)).comparison.hom.f i
          ((stalks T f (v t)).underlying.inv.f i
            (moduleGerm (sheaves T f).sections (v t) V ht i x)))
  localization : ∀ (f : Arrow CommRingCat.{u}) (S : Submonoid f.left)
    (W : Submonoid f.right) (h : S ≤ W.comap f.hom.hom), LocalizationModel C f S W h
  successive_tensor : ∀ {f g j : Arrow CommRingCat.{u}} (q : f ⟶ g) (r : g ⟶ j)
    (i : ℤ) (x : (standardComplex C f).X i) (b : g.right) (c : j.right),
    (baseChangeMap C r).f i
      (c ⊗ₜ[_, r.right.hom] ((baseChangeMap C q).f i (b ⊗ₜ[_, q.right.hom] x))) =
      (baseChangeMap C (q ≫ r)).f i ((c * r.right b) ⊗ₜ[_, (q ≫ r).right.hom] x)

/-- Sheaf standard cotangent complexes have canonical, natural section, inverse-image,
stalk and simultaneous-localization comparisons, including isomorphisms in the
appropriate derived categories and compatibility with successive inverse images
and localizations. Source: Stacks 08SR, 08SS, 08SV, 08SW, 08SX, 08T0 and 08SF
(blueprint: lem-trf-affine-cotangent-comparison).

Proof:
1. For a geometric inverse image F, the free-algebra universal property gives
   F(A[E]) ≅ (FA)[FE]: the set adjunction restricts to algebra maps because F
   preserves finite products. Coefficients and generators specify the comparison,
   hence it preserves evaluation and unit (def-trf-geometric-morphism).
2. Apply this to sheafification, which is exact on sets
   (lem-weil-pbc-sheafification-sets-exact). The recorded standard ring resolutions
   and square maps (lem-trf-cotangent-resolution-coherence) assemble sectionwise.
   Iterating step 1 identifies their sheafifications with A[B], A[P_0], etc.,
   giving initialFreeIso and freeTermIso with their coefficient and generator
   normalizations. This identifies the evaluation faces and unit degeneracies.
   Inverse image preserves differentials and tensor products
   (lem-trf-topos-inverse-image-differentials,
   lem-weil-pbc-ringed-topoi-module-pullback-tensor). Therefore sheafification of
   their alternating complex is the displayed sheaf standard differential complex.
   Its unit is the section map; unit naturality gives restriction compatibility.
3. For a continuous map, the inverse-open functor preserves finite limits and
   covers. Its inverse image is exact and preserves tensors
   (lem-weil-pbc-left-exact-site-inverse-image-tensor). Repeat step 1 on the
   standard resolution and the differential and tensor comparisons in step 2.
   Alternating faces give an actual module complex isomorphism, hence its derived
   isomorphism. The underlying map is the adjoint of the normalized section map.
4. Coefficients, polynomial generators and differential tensors determine all
   these maps. Both successive and direct inverse images have the same values
   on them. Uniqueness and the adjunction composition comparison give identity,
   naturality in ring squares and compatibility with composition.
5. Apply inverse image to the singleton inclusion. Evaluation is the stalk,
   with unit equal to the germ (lem-weil-pbc-topological-inverse-image-stalk).
   Stalk exactness (lem-weil-pbc-module-stalk-exact) permits passage to the
   derived category. The germ formulas give the ordinary scalar action and
   naturality for ring-sheaf maps and open restrictions.
6. For C = W⁻¹B and D = S⁻¹A, the induced map D → C is the localization map.
   Localization is flat (lem-weil-pbc-localization-flat); flat tensor preserves
   acyclicity (lem-weil-pbc-flat-tensor-exact), so C[0] is K-flat
   (def-pc-module-kflat-complex). The K-flat tensor model identifies ordinary
   tensor with derived tensor (lem-pc-source-kflat-module-tensor-model).
7. In the transitivity triangle for A → B → C
   (lem-trf-cotangent-transitivity-triangle), the last object is zero
   (lem-trf-localization-cotangent-vanishing). The zero-cone criterion
   (lem-kun-distinguished-cone-zero) makes its first map an isomorphism.
8. For A → D → C the first cotangent object is zero by the same vanishing.
   Rotate the triangle and apply the zero-cone criterion again. Composing gives
   the standard map L[B/A] ⊗[B] C → L[C/D]. It is a quasi-isomorphism and the
   corresponding derived isomorphism has exactly this arrow as its hom.
9. For successive localizations, standard square maps compose strictly by
   lem-trf-cotangent-resolution-coherence. Tensor adjunction sends this equality
   to the displayed pure-tensor equation. Pure tensors generate, so this is
   precisely compatibility with the usual tensor associativity comparison. -/
theorem exists_comparison (C : Coherence.{u}) : Nonempty (Comparison C) := by
  sorry

end TopCat.SheafCotangent
