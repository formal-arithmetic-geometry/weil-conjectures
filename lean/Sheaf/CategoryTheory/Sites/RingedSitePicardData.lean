/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import Sheaf.Paper.SequenceSiteCompletionProjection
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.AlgebraicInverseImageOfUniverses
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Sheaf.CategoryTheory.Sites.AbelianInverseImagePresentation
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import WeilConjectures.Mathlib.Algebra.Category.Grp.Adjunctions
public import WeilConjectures.CategoryTheory.Sites.Torsor
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-! # Line classes and normalized Picard comparison data on ringed sites

Source: Stacks Project, Cohomology on Sites, Tags 040E and 03AJ; Modules on Sites,
Section 03EK (blueprint: def-sfb-ringed-site-picard-data).

These are presentations of the actual objects and maps: line classes are an isomorphism
quotient, generators are sections inducing an isomorphism on every slice, and their
cohomology class is normalized by the extension with that generator torsor as fibre over 1.
No final object of the presented site is used.
-/

@[expose] public noncomputable section

attribute [-instance] WeilConjectures.SemilinearSections.hasDerived

universe w h uC vC uD vD

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory

namespace CategoryTheory.RingedSitePicard

set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency false

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{w} C]

/-- Forget commutativity, retaining the actual ring sheaf. Source: Stacks 040E.
(blueprint: def-sfb-ringed-site-picard-data). -/
abbrev ring (A : Sheaf J CommRingCat.{w}) :=
  (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj A

/-- The sectionwise units, written additively; units preserve limits. Source: Stacks 040E.
(blueprint: def-sfb-ringed-site-picard-data). -/
def units (A : Sheaf J CommRingCat.{w}) : Sheaf J AddCommGrpCat.{w} :=
  (sheafCompose J CommRingCat.unitsAddCommGrp.{w}).obj A

/-- Underlying sets of an abelian sheaf. Source: Stacks 03AJ.
(blueprint: def-sfb-ringed-site-picard-data). -/
abbrev abSets (F : Sheaf J AddCommGrpCat.{w}) :=
  (sheafCompose J (forget AddCommGrpCat.{w})).obj F

/-- Underlying sets of a commutative-ring sheaf. Source: Stacks 040E.
(blueprint: def-sfb-ringed-site-picard-data). -/
abbrev ringSets (A : Sheaf J CommRingCat.{w}) :=
  (sheafCompose J (forget CommRingCat.{w})).obj A

/-- Inclusion of the actual unit values. Source: Stacks 040E.
(blueprint: def-sfb-ringed-site-picard-data). -/
def unitValues (A : Sheaf J CommRingCat.{w}) : abSets (units A) ⟶ ringSets A :=
  ⟨{ app := fun U ↦ TypeCat.ofHom (fun x ↦ (Additive.toMul x).val)
     naturality := by intros; rfl }⟩

variable [HasSheafify J AddCommGrpCat.{w}]

/-- The sheafified constant integers; morphisms out of it are global sections.
Source: Stacks 03AJ (blueprint: def-sfb-ringed-site-picard-data). -/
abbrev integers (J : GrothendieckTopology C) : Sheaf J AddCommGrpCat.{w} :=
  (constantSheaf J AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift.{w} ℤ))

/-- The section 1 of the integer sheaf on a site object. Source: Stacks 03AJ.
(blueprint: def-sfb-ringed-site-picard-data). -/
def integerOne (U : Cᵒᵖ) : (integers.{w} J).obj.obj U :=
  (toSheafify J ((Functor.const Cᵒᵖ).obj
    (AddCommGrpCat.of (ULift.{w} ℤ)))).app U (ULift.up 1)

/-- The global section 1 as a morphism from the final sheaf. Source: Stacks 03AJ.
(blueprint: def-sfb-ringed-site-picard-data). -/
def oneSection : (⊤_ (Sheaf J (Type w))) ⟶ abSets (integers.{w} J) :=
  ⟨{ app := fun U ↦ TypeCat.ofHom (fun _ ↦ integerOne U)
     naturality := by
       intro U V a
       ext x
       exact (ConcreteCategory.congr_hom
         ((toSheafify J ((Functor.const Cᵒᵖ).obj
           (AddCommGrpCat.of (ULift.{w} ℤ)))).naturality a) (ULift.up 1)) }⟩

variable [∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{w}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The existing locally free rank-one notion, with no local-ring hypothesis.
Source: Stacks 040E (blueprint: def-sfb-ringed-site-picard-data). -/
abbrev Line (A : Sheaf J CommRingCat.{w}) :=
  { M : ringedSiteModules.{w} (ring A) // SheafOfModules.IsInvertible M }

/-- Isomorphism of line modules. Source: Stacks 040E.
(blueprint: def-sfb-ringed-site-picard-data). -/
def lineSetoid (A : Sheaf J CommRingCat.{w}) : Setoid (Line A) where
  r M N := Nonempty (M.val ≅ N.val)
  iseqv := ⟨fun M ↦ ⟨Iso.refl M.val⟩,
    fun ⟨e⟩ ↦ ⟨e.symm⟩, fun ⟨e⟩ ⟨f⟩ ↦ ⟨e ≪≫ f⟩⟩

/-- Isomorphism classes of actual line modules. Source: Stacks 040E.
(blueprint: def-sfb-ringed-site-picard-data). -/
abbrev Pic (A : Sheaf J CommRingCat.{w}) := _root_.Quotient (lineSetoid A)

/-- The class of a line module. Source: Stacks 040E.
(blueprint: def-sfb-ringed-site-picard-data). -/
def lineClass {A : Sheaf J CommRingCat.{w}} (M : Line A) : Pic A :=
  _root_.Quotient.mk (lineSetoid A) M

/-- A section is a generator precisely when its scalar-multiplication map is invertible
on every object over U. This is Isom(A|U,M|U), via evaluation at 1. Source: Stacks 040E.
(blueprint: def-sfb-ringed-site-picard-data). -/
def Frame {A : Sheaf J CommRingCat.{w}} (M : ringedSiteModules.{w} (ring A)) (U : C) :=
  { s : M.val.obj (op U) // ∀ (V : C) (a : V ⟶ U),
    Function.Bijective (fun r : A.obj.obj (op V) ↦ r • @id (M.val.obj (op V)) (M.val.map a.op s)) }

/-- A presentation of the generator torsor, fixed on sections, restriction and action.
Source: Stacks 040E (blueprint: def-sfb-ringed-site-picard-data). -/
structure GeneratorTorsor {A : Sheaf J CommRingCat.{w}} (M : Line A) where
  torsor : Sheaf.Torsor (units A)
  frames (U : C) : torsor.sheaf.obj.obj (op U) ≃ Frame M.val U
  restriction : ∀ (U V : C) (a : V ⟶ U) (t : torsor.sheaf.obj.obj (op U)),
    (frames V (torsor.sheaf.obj.map a.op t)).val =
      @id (M.val.val.obj (op V)) (M.val.val.map a.op (frames U t).val)
  action : ∀ (U : C) (g : (units A).obj.obj (op U))
    (t : torsor.sheaf.obj.obj (op U)),
    (frames U (torsor.vadd (op U) g t)).val =
      (Additive.toMul g).val • (frames U t).val

/-- An extension whose fibre over 1 is exactly the generator torsor. Its extension class
is its connecting image of 1. Source: Stacks 03AJ and 040E.
(blueprint: def-sfb-ringed-site-picard-data). -/
structure GeneratorExtension {A : Sheaf J CommRingCat.{w}} (M : Line A) where
  middle : Sheaf J AddCommGrpCat.{w}
  inclusion : units A ⟶ middle
  projection : middle ⟶ integers J
  zero : inclusion ≫ projection = 0
  exact : (ShortComplex.mk inclusion projection zero).ShortExact
  frames (U : C) : Frame M.val U ≃
    { x : middle.obj.obj (op U) // projection.hom.app (op U) x = integerOne (op U) }
  restriction : ∀ (U V : C) (a : V ⟶ U) (t : Frame M.val U) (t' : Frame M.val V),
    t'.val = @id (M.val.val.obj (op V)) (M.val.val.map a.op t.val) →
      (frames V t').val = @id (middle.obj.obj (op V)) (middle.obj.map a.op (frames U t).val)
  action : ∀ (U : C) (g : (A.obj.obj (op U))ˣ) (t t' : Frame M.val U),
    t'.val = g.val • t.val →
      (frames U t').val = inclusion.hom.app (op U) (Additive.ofMul g) + (frames U t).val

variable [HasExt.{h} (Sheaf J AddCommGrpCat.{w})]

/-- The already constructed sheafified tensor product. Source: Stacks 03EK.
(blueprint: def-sfb-ringed-site-picard-data). -/
def tensor (A : Sheaf J CommRingCat.{w})
    (M N : ringedSiteModules.{w} (ring A)) :=
  (SheafOfModules.cochainModulesMonoidal A).tensorObj M N

/-- Tensor and generator normalization of a Picard comparison. Source: Stacks 040E, 03AJ.
(blueprint: def-sfb-ringed-site-picard-data). -/
def IsComparison (A : Sheaf J CommRingCat.{w}) (group : AddCommGroup (Pic A))
    (e : @AddEquiv (Pic A) (Sheaf.H (units A) 1) group.toAdd inferInstance) : Prop :=
  (∀ M : Line A, Nonempty (M.val ≅ SheafOfModules.unit (ring A)) →
    lineClass M = group.zero) ∧
  (∀ M N Q : Line A, Nonempty (Q.val ≅ tensor A M.val N.val) →
    lineClass Q = group.add (lineClass M) (lineClass N)) ∧
  (∀ M N : Line A, ∃ Q : Line A, Nonempty (Q.val ≅ tensor A M.val N.val)) ∧
  (∀ M : Line A, Nonempty (GeneratorTorsor M)) ∧
  (∀ M : Line A, Nonempty (GeneratorExtension M)) ∧
  (∀ (M : Line A) (E : GeneratorExtension M), e (lineClass M) = E.exact.extClass)

/-- The actual tensor group on line classes, with the normalized H1 equivalence.
Source: Stacks 040E and 03AJ (blueprint: def-sfb-ringed-site-picard-data). -/
structure Comparison (A : Sheaf J CommRingCat.{w}) where
  group : AddCommGroup (Pic A)
  comparison : @AddEquiv (Pic A) (Sheaf.H (units A) 1) group.toAdd inferInstance
  normalized : IsComparison A group comparison


section Transport

variable {D : Type uD} [Category.{vD} D] {K : GrothendieckTopology D}
  [EssentiallySmall.{w} D] [HasSheafify K AddCommGrpCat.{w}]
  {A : Sheaf J CommRingCat.{w}} {B : Sheaf K CommRingCat.{w}}

/-- The abelian inverse image and its canonical identification of constant integers.
The image of 1 fixes the latter; an arbitrary automorphism of the integer sheaf is excluded.
Source: Stacks 03AJ and the geometric inverse-image construction, 00YV.
(blueprint: def-sfb-ringed-site-picard-data). -/
structure CohomologyTransport (f : RingedToposMorphismOfUniverses (ring B) (ring A)) where
  abelian : AbelianInverseImagePresentation f.inverse
  additive : abelian.functor.Additive
  finiteLimits : PreservesFiniteLimits abelian.functor
  finiteColimits : PreservesFiniteColimits abelian.functor
  integerIso : integers K ≅ abelian.functor.obj (integers.{w} J)
  finalIso : (⊤_ (Sheaf K (Type w))) ≅ f.inverse.obj (⊤_ (Sheaf J (Type w)))
  one : oneSection (J := K) ≫
      (sheafCompose K (forget AddCommGrpCat.{w})).map integerIso.hom ≫
        abelian.underlying.hom.app (integers.{w} J) =
      finalIso.hom ≫ f.inverse.map (oneSection (J := J))

attribute [instance] CohomologyTransport.additive CohomologyTransport.finiteLimits
  CohomologyTransport.finiteColimits

variable [HasExt.{h} (Sheaf K AddCommGrpCat.{w})]

/-- Pullback on derived global cohomology, computed by the exact inverse image and its
normalized constant-integer comparison. Its resolution formula is recorded separately.
Source: Stacks 03AJ and 00YV (blueprint: def-sfb-ringed-site-picard-data). -/
def pullback {f : RingedToposMorphismOfUniverses (ring B) (ring A)}
    (P : CohomologyTransport f) {F : Sheaf J AddCommGrpCat.{w}} (n : ℕ)
    (x : Sheaf.H F n) : Sheaf.H (P.abelian.functor.obj F) n :=
  (Ext.mk₀ P.integerIso.hom).comp
    (x.mapExactFunctor P.abelian.functor) (zero_add n)

/-- The resolution description of pullback. A global cocycle a:Z→I¹ is sent to
Z→LZ→LI¹→J¹. The first two arrows are precisely unit plus global-section adjunction.
All resolutions and all comparison maps under LF are quantified, so this includes
choice independence. Source: Stacks 03AJ and 00YV.
(blueprint: def-sfb-ringed-site-picard-data). -/
def ComputesByResolutions {f : RingedToposMorphismOfUniverses (ring B) (ring A)}
    (P : CohomologyTransport f) (F : Sheaf J AddCommGrpCat.{w}) : Prop :=
  ∀ (I : InjectiveResolution F)
    (T : InjectiveResolution (P.abelian.functor.obj F)),
    (∃ β : (P.abelian.functor.mapHomologicalComplex (.up ℕ)).obj I.cocomplex ⟶
        T.cocomplex,
      P.abelian.functor.map (I.ι.f 0) ≫ β.f 0 = T.ι.f 0) ∧
    ∀ (β : (P.abelian.functor.mapHomologicalComplex (.up ℕ)).obj I.cocomplex ⟶
        T.cocomplex),
      P.abelian.functor.map (I.ι.f 0) ≫ β.f 0 = T.ι.f 0 →
      ∀ (a : integers J ⟶ I.cocomplex.X 1) (ha : a ≫ I.cocomplex.d 1 2 = 0),
        ∃ hb : (P.integerIso.hom ≫ P.abelian.functor.map a ≫ β.f 1) ≫
            T.cocomplex.d 1 2 = 0,
          pullback P 1 (I.extMk a 2 rfl ha) =
            T.extMk (P.integerIso.hom ≫ P.abelian.functor.map a ≫ β.f 1) 2 rfl hb

/-- The map on units is induced by the structural ring map, as an equation on actual
underlying sheaves, rather than an arbitrary coefficient homomorphism.
Source: Stacks 040E (blueprint: def-sfb-ringed-site-picard-data). -/
def IsStructuralUnitsMap {f : RingedToposMorphismOfUniverses (ring B) (ring A)}
    (P : CohomologyTransport f) (ρ : P.abelian.functor.obj (units A) ⟶ units B) : Prop :=
  P.abelian.underlying.hom.app (units A) ≫ f.inverse.map (unitValues A) ≫ f.ringMap =
    (sheafCompose K (forget AddCommGrpCat.{w})).map ρ ≫ unitValues B

end Transport

end CategoryTheory.RingedSitePicard
