/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.Topology.SquareZeroSheafAlgebra
public import Sheaf.Topology.SheafCotangentComparison
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor
import Sheaf.CategoryTheory.Sites.SheafifiedDifferentialsCokernel
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal
import WeilConjectures.AlgebraicGeometry.InverseImageModuleFunctor

/-!
# Square-zero sheaf-algebra extensions and cotangent Ext

Source: Stacks Project, Deformation Theory, Tags 0GPZ, 0GQ0, 0GQ1, 0GQ2 and
08U8; Cotangent Complex, Tags 08US and 08UR
(blueprint: lem-sfb-zariski-sheaf-algebra-extension-ext).

The class function is stated on extensions, is surjective, and has equal values
exactly on isomorphic extensions. This is the bijection on isomorphism classes
without making an additional choice of quotient representatives. The coefficient,
Baer and restriction diagrams retain their actual ring and section maps. Both
class maps are normalized by cochain representatives on standard coordinates:
the conormal class of the canonical polynomial lift, and the universal derivation.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option genSizeOfSpec false
set_option genInjectivity false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Algebra.CotangentResolution Simplicial

namespace TopCat.SquareZeroSheaf

/-- Ext with a coefficient sheaf placed in degree zero. The localization is the
standard localization supplied by Mathlib, as in the recorded cotangent interface.
Source: Stacks 0GPZ, 08US (blueprint: lem-sfb-zariski-sheaf-algebra-extension-ext). -/
abbrev Ext {T : TopCat.{u}} {A : T.Sheaf CommRingCat.{u}}
    (L : CochainComplex (Modules A) ℤ) (G : Modules A) (n : ℤ) :=
  letI := HasDerivedCategory.standard (Modules A)
  DerivedCategory.Q.obj L ⟶ ((DerivedCategory.singleFunctor (Modules A) 0).obj G)⟦n⟧

/-- Postcomposition on Ext by the actual shifted coefficient map.
Source: Stacks 0GQ2 (blueprint: lem-sfb-zariski-sheaf-algebra-extension-ext). -/
def coefficientMap {T : TopCat.{u}} {A : T.Sheaf CommRingCat.{u}}
    {L : CochainComplex (Modules A) ℤ} {G H : Modules A} (v : G ⟶ H)
    (n : ℤ) (x : Ext L G n) : Ext L H n :=
  letI := HasDerivedCategory.standard (Modules A)
  x ≫ (shiftFunctor (DerivedCategory (Modules A)) n).map
    ((DerivedCategory.singleFunctor (Modules A) 0).map v)

/-- Exactness evidence for the specified sectionwise open restriction, not a
choice of a functor or an extra hypothesis of the classification.
Source: Stacks 0GQ2 (blueprint: lem-sfb-zariski-sheaf-algebra-extension-ext). -/
structure OpenExact {T : TopCat.{u}} (A : T.Sheaf CommRingCat.{u}) (U : Opens T) : Prop where
  additive : (openModules A U).Additive
  limits : PreservesFiniteLimits (openModules A U)
  colimits : PreservesFiniteColimits (openModules A U)

/-- Termwise restriction of complexes, using the additivity evidence for the
specified restriction functor. Source: Stacks 0GQ2
(blueprint: lem-sfb-zariski-sheaf-algebra-extension-ext). -/
def openComplex {T : TopCat.{u}} {A : T.Sheaf CommRingCat.{u}}
    {U : Opens T} (h : OpenExact A U) :=
  letI := h.additive
  (openModules A U).mapHomologicalComplex (.up ℤ)

/-- The map on Ext induced by exact restriction and the specified cotangent
complex isomorphism. Its remaining factors are Mathlib's localization, single
complex and shift comparisons. Source: Stacks 0GQ2 and 08US
(blueprint: lem-sfb-zariski-sheaf-algebra-extension-ext). -/
def restrictionMap {T : TopCat.{u}} {A : T.Sheaf CommRingCat.{u}}
    {L : CochainComplex (Modules A) ℤ} {G : Modules A} (U : Opens T)
    (h : OpenExact A U)
    {L' : CochainComplex (Modules (T := TopCat.of U)
      ((U.sheafRestrict (C := CommRingCat.{u})).obj A)) ℤ}
    (e : (openComplex h).obj L ≅ L')
    (n : ℤ) (x : Ext L G n) : Ext L' ((openModules A U).obj G) n :=
  letI := h.additive
  letI := h.limits
  letI := h.colimits
  letI := HasDerivedCategory.standard (Modules A)
  letI := HasDerivedCategory.standard
    (Modules (T := TopCat.of U) ((U.sheafRestrict (C := CommRingCat.{u})).obj A))
  (DerivedCategory.Q.mapIso e).inv ≫
    (openModules A U).mapDerivedCategoryFactors.inv.app L ≫
    (openModules A U).mapDerivedCategory.map x ≫
    ((openModules A U).mapDerivedCategory.commShiftIso n).hom.app
      ((DerivedCategory.singleFunctor (Modules A) 0).obj G) ≫
    (shiftFunctor _ n).map (((openModules A U).mapDerivedCategorySingleFunctor 0).hom.app G)

variable [∀ B : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} B)]

/-- The full standard sheaf cotangent complex, using the dependency's recorded
polynomial sheaf model. Source: Stacks 08US
(blueprint: lem-sfb-zariski-sheaf-algebra-extension-ext). -/
abbrev cotangent (C : Coherence.{u}) (S : TopCat.SheafCotangent.Comparison C)
    {T : TopCat.{u}} {R A : T.Sheaf CommRingCat.{u}} (f : R ⟶ A) :=
  TopCat.SheafCotangent.sheafComplex (S.sheaves T (Arrow.mk f)).sections

/-- The canonical open comparison is fixed on every sectionwise standard
coordinate. This is a complex isomorphism, not a family of term isomorphisms.
Source: Stacks 08US and 0GQ2
(blueprint: lem-sfb-zariski-sheaf-algebra-extension-ext). -/
structure OpenCotangent (C : Coherence.{u}) (S : TopCat.SheafCotangent.Comparison C)
    {T : TopCat.{u}} {R A : T.Sheaf CommRingCat.{u}}
    (f : R ⟶ A) (U : Opens T) (h : OpenExact A U) where
  iso : (openComplex h).obj (cotangent C S f) ≅
    cotangent C S ((U.sheafRestrict (C := CommRingCat.{u})).map f)
  coordinate : ∀ (V : (Opens (TopCat.of U))ᵒᵖ) (i : ℤ)
    (x : (standardComplex C (TopCat.SheafCotangent.sectionArrow (Arrow.mk f)
      (U.isOpenEmbedding.isOpenMap.functor.op.obj V))).X i),
    (iso.hom.f i).val.app V
      (TopCat.SheafCotangent.sectionElement (S.sheaves T (Arrow.mk f)).sections
        (U.isOpenEmbedding.isOpenMap.functor.op.obj V) i x) =
      TopCat.SheafCotangent.sectionElement
        (S.sheaves (TopCat.of U)
          (Arrow.mk ((U.sheafRestrict (C := CommRingCat.{u})).map f))).sections V i x

/-- Evaluation of a local polynomial on the prescribed generators. Source: Stacks
0GQ0 (blueprint: lem-sfb-zariski-sheaf-algebra-extension-ext). -/
def polynomialEval {T : TopCat.{u}} {R A B : T.Sheaf CommRingCat.{u}}
    (f : R ⟶ A) (α : B ⟶ A) (V : (Opens T)ᵒᵖ) :=
  MvPolynomial.eval₂Hom (f.hom.app V).hom (fun b ↦ α.hom.app V b)

/-- A compatible linear family on presentation relations. These are exactly the
relations defining the sheafified conormal module: additivity and
`[qj] = ev(q)[j]` imply that products of two kernel elements vanish.
Source: Stacks 0GQ0 and 08TY
(blueprint: lem-sfb-zariski-sheaf-algebra-extension-ext). -/
structure ConormalFamily {T : TopCat.{u}} {R A B : T.Sheaf CommRingCat.{u}}
    (f : R ⟶ A) (α : B ⟶ A) (M : Modules A) where
  value : ∀ (V : (Opens T)ᵒᵖ) (j : MvPolynomial (B.obj.obj V) (R.obj.obj V)),
    polynomialEval f α V j = 0 → M.val.obj V
  add : ∀ (V : (Opens T)ᵒᵖ) (j k : MvPolynomial (B.obj.obj V) (R.obj.obj V))
    (hj : polynomialEval f α V j = 0) (hk : polynomialEval f α V k = 0)
    (hs : polynomialEval f α V (j + k) = 0),
    value V (j + k) hs = value V j hj + value V k hk
  smul : ∀ (V : (Opens T)ᵒᵖ) (q j : MvPolynomial (B.obj.obj V) (R.obj.obj V))
    (hj : polynomialEval f α V j = 0) (hm : polynomialEval f α V (q * j) = 0),
    value V (q * j) hm = polynomialEval f α V q • value V j hj
  naturality : ∀ {V W : (Opens T)ᵒᵖ} (r : V ⟶ W)
    (j : MvPolynomial (B.obj.obj V) (R.obj.obj V))
    (hj : polynomialEval f α V j = 0)
    (hr : polynomialEval f α W ((SheafCotangent.freeAlgebraPresheaf R B).map r j) = 0),
    value W ((SheafCotangent.freeAlgebraPresheaf R B).map r j) hr =
      M.val.map r (value V j hj)

/-- A coordinate presentation of the actual two-term polynomial conormal complex.
The degree minus one term represents compatible conormal families, so its data
are determined up to the unique isomorphism preserving every local `[j]`.
Degree zero is the existing differential sheaf, with its actual tensor sections;
the displayed boundary and vanishing fix the whole complex. This universal
property also covers evaluations that are only locally surjective.
Source: Stacks 0GQ0, 08TY and 08TP
(blueprint: lem-sfb-zariski-sheaf-algebra-extension-ext). -/
structure ConormalCoordinates {T : TopCat.{u}} {R A B : T.Sheaf CommRingCat.{u}}
    (f : R ⟶ A) (α : B ⟶ A) where
  base : R ⟶ SheafCotangent.freeSheafAlgebra R B
  base_formula : ∀ (V : (Opens T)ᵒᵖ) (r : R.obj.obj V),
    base.hom.app V r = SheafCotangent.freeSheafSection R B V (MvPolynomial.C r)
  evaluation : SheafCotangent.freeSheafAlgebra R B ⟶ A
  evaluation_formula : ∀ (V : (Opens T)ᵒᵖ)
    (q : MvPolynomial (B.obj.obj V) (R.obj.obj V)),
    evaluation.hom.app V (SheafCotangent.freeSheafSection R B V q) =
      polynomialEval f α V q
  complex : CochainComplex (Modules A) ℤ
  zero : ∀ i : ℤ, i ≠ -1 → i ≠ 0 → IsZero (complex.X i)
  relation : ConormalFamily f α (complex.X (-1))
  universal : ∀ (M : Modules A) (k : ConormalFamily f α M),
    ∃! h : complex.X (-1) ⟶ M, ∀ (V : (Opens T)ᵒᵖ)
      (j : MvPolynomial (B.obj.obj V) (R.obj.obj V))
      (hj : polynomialEval f α V j = 0), h.val.app V (relation.value V j hj) = k.value V j hj
  zeroIso : complex.X 0 ≅ SheafCotangent.differentialSheaf base evaluation
  boundary : ∀ (V : (Opens T)ᵒᵖ)
    (j : MvPolynomial (B.obj.obj V) (R.obj.obj V))
    (hj : polynomialEval f α V j = 0),
    zeroIso.hom.val.app V ((complex.d (-1) 0).val.app V (relation.value V j hj)) =
      SheafCotangent.differentialSection base evaluation V 1
        (SheafCotangent.freeSheafSection R B V j)

/-- Convert a standard-resolution section to its literal polynomial coordinates.
Source: Stacks 08UP (blueprint: lem-sfb-zariski-sheaf-algebra-extension-ext). -/
def standardPolynomial (C : Coherence.{u}) {T : TopCat.{u}}
    {R A : T.Sheaf CommRingCat.{u}} (f : R ⟶ A) (V : (Opens T)ᵒᵖ) (n : ℕ)
    (x : (C.standard (SheafCotangent.sectionArrow (Arrow.mk f) V)).algebra.obj (op ⦋n⦌)) :
    standardTerm (SheafCotangent.sectionArrow (Arrow.mk f) V) n :=
  eqToHom ((C.standard_spec (SheafCotangent.sectionArrow (Arrow.mk f) V)).1 n) x

/-- The difference of the first two faces in polynomial coordinates.
Source: Stacks 08UP (blueprint: lem-sfb-zariski-sheaf-algebra-extension-ext). -/
def boundaryPolynomial (C : Coherence.{u}) {T : TopCat.{u}}
    {R A : T.Sheaf CommRingCat.{u}} (f : R ⟶ A) (V : (Opens T)ᵒᵖ)
    (x : (C.standard (SheafCotangent.sectionArrow (Arrow.mk f) V)).algebra.obj (op ⦋1⦌)) :=
  standardPolynomial C f V 0
    ((C.standard (SheafCotangent.sectionArrow (Arrow.mk f) V)).algebra.δ (0 : Fin 2) x -
      (C.standard (SheafCotangent.sectionArrow (Arrow.mk f) V)).algebra.δ (1 : Fin 2) x)

/-- The standard chain projection, fixed in degrees zero and minus one by the
polynomial differential and face-difference formulas. No free sign remains.
Source: Stacks 08UP (blueprint: lem-sfb-zariski-sheaf-algebra-extension-ext). -/
structure ConormalProjection (C : Coherence.{u}) (S : SheafCotangent.Comparison C)
    {T : TopCat.{u}} {R A : T.Sheaf CommRingCat.{u}} (f : R ⟶ A)
    (P : ConormalCoordinates f (𝟙 A)) where
  map : cotangent C S f ⟶ P.complex
  zero : ∀ (V : (Opens T)ᵒᵖ) (b : A.obj.obj V)
    (x : (C.standard (SheafCotangent.sectionArrow (Arrow.mk f) V)).algebra.obj (op ⦋0⦌)),
    P.zeroIso.hom.val.app V ((map.f 0).val.app V
      (SheafCotangent.sectionElement (S.sheaves T (Arrow.mk f)).sections V 0
        (complexGenerator (C.differentials
          (C.standard (SheafCotangent.sectionArrow (Arrow.mk f) V))) 0 b x))) =
      SheafCotangent.differentialSection P.base P.evaluation V b
        (SheafCotangent.freeSheafSection R A V (standardPolynomial C f V 0 x))
  neg_one : ∀ (V : (Opens T)ᵒᵖ) (b : A.obj.obj V)
    (x : (C.standard (SheafCotangent.sectionArrow (Arrow.mk f) V)).algebra.obj (op ⦋1⦌))
    (hx : polynomialEval f (𝟙 A) V (boundaryPolynomial C f V x) = 0),
    (map.f (-1)).val.app V
      (SheafCotangent.sectionElement (S.sheaves T (Arrow.mk f)).sections V (-1)
        (complexGenerator (C.differentials
          (C.standard (SheafCotangent.sectionArrow (Arrow.mk f) V))) 1 b x)) =
      b • P.relation.value V (boundaryPolynomial C f V x) hx

/-- Localization of a cochain map to a single complex, followed by Mathlib's
canonical single/shift isomorphism. Source: Stacks 0GQ0 and 08US
(blueprint: lem-sfb-zariski-sheaf-algebra-extension-ext). -/
def singleClass {T : TopCat.{u}} {A : T.Sheaf CommRingCat.{u}}
    {L : CochainComplex (Modules A) ℤ} {G : Modules A} (n : ℤ)
    (m : L ⟶ (CochainComplex.singleFunctor (Modules A) (-n)).obj G) : Ext L G n :=
  letI := HasDerivedCategory.standard (Modules A)
  DerivedCategory.Q.map m ≫
    ((DerivedCategory.singleFunctors (Modules A)).shiftIso n (-n) 0
      (add_neg_cancel n)).inv.app G

/-- The conormal representative in Ext, using the actual localization inverse
of the polynomial comparison and the canonical single/shift comparison.
Source: Stacks 0GQ0 (blueprint: lem-sfb-zariski-sheaf-algebra-extension-ext). -/
def conormalRepresentative {T : TopCat.{u}} {A : T.Sheaf CommRingCat.{u}}
    {L K N : CochainComplex (Modules A) ℤ} {G : Modules A}
    (π : L ⟶ K) (comparison : N ⟶ K) (h : QuasiIso comparison)
    (δ : N ⟶ (CochainComplex.singleFunctor (Modules A) (-1)).obj G) : Ext L G 1 :=
  letI := HasDerivedCategory.standard (Modules A)
  letI := h
  DerivedCategory.Q.map π ≫ inv (DerivedCategory.Q.map comparison) ≫ singleClass 1 δ

/-- A normalized representative of the class of an extension. The comparison
relabels each polynomial variable `e` by `p(e)`; its derived inverse is unique.
The degree minus one map is the conormal map of the canonical lift
`R[E] → E`, evaluated by `C r ↦ base(r)` and `X e ↦ e`.
Source: Stacks 0GQ0 and 08U8
(blueprint: lem-sfb-zariski-sheaf-algebra-extension-ext). -/
structure ConormalClass (C : Coherence.{u}) (S : SheafCotangent.Comparison C)
    {T : TopCat.{u}} {R A : T.Sheaf CommRingCat.{u}} {f : R ⟶ A}
    {G : Modules A} (E : Extension f G) (P : ConormalCoordinates f (𝟙 A))
    (π : ConormalProjection C S f P) (N : ConormalCoordinates f E.p)
    (c : Ext (cotangent C S f) G 1) where
  comparison : N.complex ⟶ P.complex
  conormal : ∀ (V : (Opens T)ᵒᵖ)
    (j : MvPolynomial (E.ring.obj.obj V) (R.obj.obj V))
    (hj : polynomialEval f E.p V j = 0)
    (hp : polynomialEval f (𝟙 A) V (MvPolynomial.rename (fun e ↦ E.p.hom.app V e) j) = 0),
    (comparison.f (-1)).val.app V (N.relation.value V j hj) =
      P.relation.value V (MvPolynomial.rename (fun e ↦ E.p.hom.app V e) j) hp
  differential : ∀ (V : (Opens T)ᵒᵖ) (a : A.obj.obj V)
    (q : MvPolynomial (E.ring.obj.obj V) (R.obj.obj V)),
    P.zeroIso.hom.val.app V ((comparison.f 0).val.app V
      (N.zeroIso.inv.val.app V
        (SheafCotangent.differentialSection N.base N.evaluation V a
          (SheafCotangent.freeSheafSection R E.ring V q)))) =
      SheafCotangent.differentialSection P.base P.evaluation V a
        (SheafCotangent.freeSheafSection R A V
          (MvPolynomial.rename (fun e ↦ E.p.hom.app V e) q))
  quasiIso : QuasiIso comparison
  map : N.complex ⟶ (CochainComplex.singleFunctor (Modules A) (-1)).obj G
  formula : ∀ (V : (Opens T)ᵒᵖ)
    (j : MvPolynomial (E.ring.obj.obj V) (R.obj.obj V))
    (hj : polynomialEval f E.p V j = 0),
    E.i V (((HomologicalComplex.singleObjXSelf (.up ℤ) (-1) G).hom).val.app V
      ((map.f (-1)).val.app V (N.relation.value V j hj))) =
      MvPolynomial.eval₂Hom (E.base.hom.app V).hom (fun e ↦ e) j
  class_eq : c = conormalRepresentative π.map comparison quasiIso map

/-- A derivation class is normalized by the universal differential in degree zero:
`b ⊗ dx ↦ b d(ev(x))`. Higher components land in zero terms of the single complex.
Source: Stacks 08U8 and 08UR
(blueprint: lem-sfb-zariski-sheaf-algebra-extension-ext). -/
structure DerivationClass (C : Coherence.{u}) (S : SheafCotangent.Comparison C)
    {T : TopCat.{u}} {R A : T.Sheaf CommRingCat.{u}} {f : R ⟶ A}
    {G : Modules A} (d : G.val.Derivation' f.hom)
    (c : Ext (cotangent C S f) G 0) where
  map : cotangent C S f ⟶ (CochainComplex.singleFunctor (Modules A) 0).obj G
  formula : ∀ (V : (Opens T)ᵒᵖ) (b : A.obj.obj V)
    (x : (C.standard (SheafCotangent.sectionArrow (Arrow.mk f) V)).algebra.obj (op ⦋0⦌)),
    ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 G).hom).val.app V
      ((map.f 0).val.app V
        (SheafCotangent.sectionElement (S.sheaves T (Arrow.mk f)).sections V 0
          (complexGenerator (C.differentials
            (C.standard (SheafCotangent.sectionArrow (Arrow.mk f) V))) 0 b x))) =
      b • d.d (polynomialEval f (𝟙 A) V (standardPolynomial C f V 0 x))
  class_eq : c = singleClass 0 map

/-- All clauses of the square-zero extension classification, simultaneously for
all spaces, ring maps and coefficients. The derivations are Mathlib's actual
additive presheaf derivations, with Leibniz, naturality and vanishing on the base.
The class maps include their conormal and universal-differential normalizations;
naturality and additivity alone are not used to specify these maps.
Source: Stacks 0GPZ--0GQ2, 08U8, 08UR and 08US
(blueprint: lem-sfb-zariski-sheaf-algebra-extension-ext). -/
structure Classification (C : Coherence.{u}) (S : TopCat.SheafCotangent.Comparison C) where
  standardPresentation : ∀ {T : TopCat.{u}} {R A : T.Sheaf CommRingCat.{u}}
    (f : R ⟶ A), ConormalCoordinates f (𝟙 A)
  projection : ∀ {T : TopCat.{u}} {R A : T.Sheaf CommRingCat.{u}}
    (f : R ⟶ A), ConormalProjection C S f (standardPresentation f)
  extensionPresentation : ∀ {T : TopCat.{u}} {R A : T.Sheaf CommRingCat.{u}}
    {f : R ⟶ A} {G : Modules A} (E : Extension f G), ConormalCoordinates f E.p
  cl : ∀ {T : TopCat.{u}} {R A : T.Sheaf CommRingCat.{u}} (f : R ⟶ A)
    (G : Modules A), Extension f G → Ext (cotangent C S f) G 1
  cl_normalization : ∀ {T : TopCat.{u}} {R A : T.Sheaf CommRingCat.{u}}
    {f : R ⟶ A} {G : Modules A} (E : Extension f G),
    Nonempty (ConormalClass C S E (standardPresentation f) (projection f)
      (extensionPresentation E) (cl f G E))
  onto : ∀ {T : TopCat.{u}} {R A : T.Sheaf CommRingCat.{u}} (f : R ⟶ A)
    (G : Modules A), Function.Surjective (cl f G)
  classes : ∀ {T : TopCat.{u}} {R A : T.Sheaf CommRingCat.{u}} {f : R ⟶ A}
    {G : Modules A} (E F : Extension f G), cl f G E = cl f G F ↔ Nonempty (Iso E F)
  split_exists : ∀ {T : TopCat.{u}} {R A : T.Sheaf CommRingCat.{u}} (f : R ⟶ A)
    (G : Modules A), ∃ E : Extension f G, IsSplit E
  split : ∀ {T : TopCat.{u}} {R A : T.Sheaf CommRingCat.{u}} {f : R ⟶ A}
    {G : Modules A} (E : Extension f G), IsSplit E → cl f G E = 0
  pushout_exists : ∀ {T : TopCat.{u}} {R A : T.Sheaf CommRingCat.{u}} {f : R ⟶ A}
    {G H : Modules A} (v : G ⟶ H) (E : Extension f G),
    ∃ F : Extension f H, Nonempty (Hom E F v)
  coefficient : ∀ {T : TopCat.{u}} {R A : T.Sheaf CommRingCat.{u}} {f : R ⟶ A}
    {G H : Modules A} (v : G ⟶ H) (E : Extension f G) (F : Extension f H),
    Hom E F v → cl f H F = coefficientMap v 1 (cl f G E)
  baer_exists : ∀ {T : TopCat.{u}} {R A : T.Sheaf CommRingCat.{u}} {f : R ⟶ A}
    {G : Modules A} (E F : Extension f G),
    ∃ H : Extension f G, Nonempty (Baer E F H)
  baer : ∀ {T : TopCat.{u}} {R A : T.Sheaf CommRingCat.{u}} {f : R ⟶ A}
    {G : Modules A} (E F H : Extension f G),
    Baer E F H → cl f G H = cl f G E + cl f G F
  open_exact : ∀ {T : TopCat.{u}} (A : T.Sheaf CommRingCat.{u}) (U : Opens T), OpenExact A U
  open_cotangent : ∀ {T : TopCat.{u}} {R A : T.Sheaf CommRingCat.{u}}
    (f : R ⟶ A) (U : Opens T), OpenCotangent C S f U (open_exact A U)
  restriction_exists : ∀ {T : TopCat.{u}} {R A : T.Sheaf CommRingCat.{u}} {f : R ⟶ A}
    {G : Modules A} (E : Extension f G) (U : Opens T),
    ∃ F : Extension (T := TopCat.of U)
      ((U.sheafRestrict (C := CommRingCat.{u})).map f) ((openModules A U).obj G),
      Nonempty (OpenRestriction E U F)
  restriction : ∀ {T : TopCat.{u}} {R A : T.Sheaf CommRingCat.{u}} {f : R ⟶ A}
    {G : Modules A} (E : Extension f G) (U : Opens T)
    (F : Extension (T := TopCat.of U)
      ((U.sheafRestrict (C := CommRingCat.{u})).map f) ((openModules A U).obj G)),
    OpenRestriction E U F →
      cl _ _ F = restrictionMap U (open_exact A U) (open_cotangent f U).iso 1 (cl f G E)
  derivation_ext : ∀ {T : TopCat.{u}} {R A : T.Sheaf CommRingCat.{u}}
    (f : R ⟶ A) (G : Modules A), G.val.Derivation' f.hom ≃ Ext (cotangent C S f) G 0
  derivation_normalization : ∀ {T : TopCat.{u}} {R A : T.Sheaf CommRingCat.{u}}
    {f : R ⟶ A} {G : Modules A} (d : G.val.Derivation' f.hom),
    Nonempty (DerivationClass C S d (derivation_ext f G d))
  derivation_add : ∀ {T : TopCat.{u}} {R A : T.Sheaf CommRingCat.{u}} {f : R ⟶ A}
    {G : Modules A} (d e k : G.val.Derivation' f.hom),
    (∀ (V : (Opens T)ᵒᵖ) (a : A.obj.obj V), k.d a = d.d a + e.d a) →
      derivation_ext f G k = derivation_ext f G d + derivation_ext f G e
  derivation_coefficient : ∀ {T : TopCat.{u}} {R A : T.Sheaf CommRingCat.{u}} {f : R ⟶ A}
    {G H : Modules A} (v : G ⟶ H) (d : G.val.Derivation' f.hom),
    derivation_ext f H (d.postcomp v.val) = coefficientMap v 0 (derivation_ext f G d)
  automorphism : ∀ {T : TopCat.{u}} {R A : T.Sheaf CommRingCat.{u}} {f : R ⟶ A}
    {G : Modules A} (E : Extension f G), G.val.Derivation' f.hom ≃ Iso E E
  automorphism_formula : ∀ {T : TopCat.{u}} {R A : T.Sheaf CommRingCat.{u}} {f : R ⟶ A}
    {G : Modules A} (E : Extension f G) (d : G.val.Derivation' f.hom)
    (V : (Opens T)ᵒᵖ) (e : E.ring.obj.obj V),
    (automorphism E d).ringIso.hom.hom.app V e = e + E.i V (d.d (E.p.hom.app V e))
  automorphism_add : ∀ {T : TopCat.{u}} {R A : T.Sheaf CommRingCat.{u}} {f : R ⟶ A}
    {G : Modules A} (E : Extension f G) (d e k : G.val.Derivation' f.hom),
    (∀ (V : (Opens T)ᵒᵖ) (a : A.obj.obj V), k.d a = d.d a + e.d a) →
      (automorphism E k).ringIso.hom =
        (automorphism E d).ringIso.hom ≫ (automorphism E e).ringIso.hom
  automorphism_coefficient : ∀ {T : TopCat.{u}} {R A : T.Sheaf CommRingCat.{u}}
    {f : R ⟶ A} {G H : Modules A} (v : G ⟶ H) (E : Extension f G)
    (F : Extension f H) (q : Hom E F v) (d : G.val.Derivation' f.hom),
    (automorphism E d).ringIso.hom ≫ q.map =
      q.map ≫ (automorphism F (d.postcomp v.val)).ringIso.hom
  derivation_restriction_exists : ∀ {T : TopCat.{u}} {R A : T.Sheaf CommRingCat.{u}}
    {f : R ⟶ A} {G : Modules A} (U : Opens T) (d : G.val.Derivation' f.hom),
    ∃ d' : ((openModules A U).obj G).val.Derivation'
      ((U.sheafRestrict (C := CommRingCat.{u})).map f).hom,
      ∀ (V : (Opens (TopCat.of U))ᵒᵖ)
        (a : A.obj.obj (U.isOpenEmbedding.isOpenMap.functor.op.obj V)), d'.d a = d.d a
  derivation_restriction : ∀ {T : TopCat.{u}} {R A : T.Sheaf CommRingCat.{u}}
    {f : R ⟶ A} {G : Modules A} (U : Opens T) (d : G.val.Derivation' f.hom)
    (d' : ((openModules A U).obj G).val.Derivation'
      ((U.sheafRestrict (C := CommRingCat.{u})).map f).hom),
    (∀ (V : (Opens (TopCat.of U))ᵒᵖ)
      (a : A.obj.obj (U.isOpenEmbedding.isOpenMap.functor.op.obj V)), d'.d a = d.d a) →
      derivation_ext _ _ d' =
        restrictionMap U (open_exact A U) (open_cotangent f U).iso 0 (derivation_ext f G d)
  automorphism_restriction : ∀ {T : TopCat.{u}} {R A : T.Sheaf CommRingCat.{u}}
    {f : R ⟶ A} {G : Modules A} (E : Extension f G) (U : Opens T)
    (F : Extension (T := TopCat.of U)
      ((U.sheafRestrict (C := CommRingCat.{u})).map f) ((openModules A U).obj G))
    (r : OpenRestriction E U F) (d : G.val.Derivation' f.hom)
    (d' : ((openModules A U).obj G).val.Derivation'
      ((U.sheafRestrict (C := CommRingCat.{u})).map f).hom),
    (∀ (V : (Opens (TopCat.of U))ᵒᵖ)
      (a : A.obj.obj (U.isOpenEmbedding.isOpenMap.functor.op.obj V)), d'.d a = d.d a) →
      (U.sheafRestrict (C := CommRingCat.{u})).map (automorphism E d).ringIso.hom ≫
        r.ringIso.hom = r.ringIso.hom ≫ (automorphism F d').ringIso.hom

/-- Square-zero extensions are classified by additive cotangent Ext, with the
split origin, coefficient pushouts, Baer sum, open restriction, and additive
natural automorphism identifications specified by `Classification`.
Source: Stacks 0GPZ, 0GQ0--0GQ2 and 08U8; 08US and 08UR
(blueprint: lem-sfb-zariski-sheaf-algebra-extension-ext).

Proof:
1. Project the sectionwise standard polynomial cotangent complex to the naive
   two-term complex, using the chain-projection and boundary-cokernel nodes.
   Exact module sheafification commutes with good truncation, ideal squares,
   tensor products and differentials, giving the sheaf comparison `L → NL`.
2. The standard truncation triangle has fibre in degrees at most -2.
   T-structure orthogonality and exact Hom for distinguished triangles identify
   Hom(NL,G[j]) with Hom(L,G[j]) for j = 0,1, additively and naturally.
3. For an extension use its underlying sheaf of sets as polynomial generators.
   Its conormal map to G and the two-term connecting map give its class.
   Common coproduct presentations and boundary naturality prove independence.
   The conormal universal property determines the degree minus one module;
   universal differentials determine degree zero, and `[j] ↦ dj ⊗ 1` is its
   boundary. The standard projection is fixed on differential tensors and
   face differences. Relabeling e by p(e) gives a quasi-isomorphism of the
   two-term presentations. Its localization inverse and the canonical
   single/shift comparison give exactly `ConormalClass.class_eq`.
4. Equal classes differ by a derivation on a common polynomial presentation.
   Subtract that derivation from one lift; local lifts then give an extension
   isomorphism fixing both ends. This proves injectivity on isomorphism classes.
5. Represent any class by a conormal map δ. The quotient of (R[V]/J²) ⋉ G by
   the graph (m,-δ(m)) has kernel G, quotient A and the prescribed action, and
   has class δ. Exact sheafification justifies the local calculation.
6. The split lift has zero conormal map. Coefficient pushout replaces δ by vδ;
   the fibre product followed by addition replaces (δ₁,δ₂) by δ₁+δ₂.
7. Open restriction preserves polynomial presentations, kernels, ideal squares,
   quotients, differentials and the connecting triangle. The section formulas
   determine the displayed complex comparison and all restriction squares.
8. The map e ↦ e+i(d(p(e))) is an algebra automorphism with inverse T_{-d}.
   Conversely an automorphism minus identity vanishes on the kernel and locally
   descends to a unique derivation on A. Composition gives addition.
9. Universal differentials identify derivations with Hom(Ω,G), then the degree
   zero two-term calculation and Step 2 identify them with Hom(L,G[0]).
   On every standard degree-zero tensor b ⊗ dx this map is b • d(ev(x));
   its image under Q with the canonical shift-zero comparison is the specified
   `DerivationClass.class_eq`. Thus both class maps have their canonical signs.
10. All these formulas commute with restriction. In a coefficient pushout,
    qi_G=i_Hv implies qT_d=T_{vd}q. Boundary and differential naturality give
    the same identities on Ext. No finiteness or quasi-coherence is used. -/
theorem exists_classification (C : Coherence.{u})
    (S : TopCat.SheafCotangent.Comparison C) : Nonempty (Classification C S) := by
  sorry

end TopCat.SquareZeroSheaf
